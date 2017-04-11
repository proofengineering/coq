{
  open Printf
  open Lexing

  let modname = ref ""
  let seen_thm = ref false
  let curr_thm = ref None
  let in_proof = ref None
  let delim = ref ""

  (* helper functions *)

  let backtrack lexbuf =
    lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  (* count the number of spaces at the beginning of a string *)
  let count_spaces s =
    let n = String.length s in
    let rec count c i =
      if i == n then c,i else match s.[i] with
	| '\t' -> count (c + (8 - (c mod 8))) (i + 1)
	| ' ' -> count (c + 1) (i + 1)
	| _ -> c,i
    in
      count 0 0

  let printf s =
    Printf.fprintf !(Cdglobals.out_channel) "%s" s

  let reset () = 
    ()

  let digest s = Digest.to_hex (Digest.string s)

  let normalize_path p =
  (* We use the Unix subsystem to normalize a physical path (relative
     or absolute) and get rid of symbolic links, relative links (like
     ./ or ../ in the middle of the path; it's tricky but it
     works... *)
  (* Rq: Sys.getcwd () returns paths without '/' at the end *)
    let orig = Sys.getcwd () in
    Sys.chdir p;
    let res = Sys.getcwd () in
    Sys.chdir orig;
    res

  let normalize_filename f =
    let basename = Filename.basename f in
    let dirname = Filename.dirname f in
    normalize_path dirname, basename

  let buf = Buffer.create 1000
}

(*s Regular expressions *)

let space = [' ' '\t']
let space_nl = [' ' '\t' '\n' '\r']
let nl = "\r\n" | '\n'

let firstchar =
  ['A'-'Z' 'a'-'z' '_'] |
  (* superscript 1 *)
  '\194' '\185' |
  (* utf-8 latin 1 supplement *)
  '\195' ['\128'-'\150'] |
  '\195' ['\152'-'\182'] |
  '\195' ['\184'-'\191'] |
  (* utf-8 letterlike symbols *)
  '\206' (['\145'-'\161'] | ['\163'-'\191']) |
  '\207' (['\145'-'\191']) |
  '\226' ('\130' [ '\128'-'\137' ] (* subscripts *)
    | '\129' [ '\176'-'\187' ] (* superscripts *)
    | '\132' ['\128'-'\191'] | '\133' ['\128'-'\143'])
let identchar =
  firstchar | ['\'' '0'-'9' '@' ]
let id = firstchar identchar*
let pfx_id = (id '.')*
let identifier =
  id | pfx_id id

let printing_token = [^ ' ' '\t']*

let thm_token =
  "Theorem"
  | "Lemma"
  | "Fact"
  | "Remark"
  | "Corollary"
  | "Proposition"
  | "Property"
  | "Goal"

let prf_token =
  "Next" space+ "Obligation"
  | "Proof"
(* (space+ "with" | space+ "using")?*)

let immediate_prf_token =
  (* Approximation of a proof term, if not in the prf_token case *)
  (* To be checked after prf_token *)
  "Proof" space* [^ '.' 'w' 'u']

let def_token =
  "Definition"
  | "Let"
  | "Class"
  | "SubClass"
  | "Example"
  | "Fixpoint"
  | "Function"
  | "Boxed"
  | "CoFixpoint"
  | "Record"
  | "Variant"
  | "Structure"
  | "Scheme"
  | "Inductive"
  | "CoInductive"
  | "Equations"
  | "Instance"
  | "Declare" space+ "Instance"
  | "Global" space+ "Instance"
  | "Functional" space+ "Scheme"

let decl_token =
  "Hypothesis"
  | "Hypotheses"
  | "Parameter" 's'?
  | "Axiom" 's'?
  | "Conjecture"

let gallina_ext =
  "Module"
  | "Declare" space+ "Module"
  | "Include" space+ "Type"
  | "Include"
  | "Transparent"
  | "Opaque"
  | "Canonical"
  | "Coercion"
  | "Identity"
  | "Implicit"
  | "Tactic" space+ "Notation"
  | "Section"
  | "Context"
  | "Variable" 's'?
  | ("Hypothesis" | "Hypotheses")
  | "End"

let notation_kw =
  "Notation"
  | "Infix"
  | "Reserved" space+ "Notation"

let commands =
  "Pwd"
  | "Cd"
  | "Drop"
  | "ProtectedLoop"
  | "Quit"
  | "Restart"
  | "Load"
  | "Add"
  | "Remove" space+ "Loadpath"
  | "Print"
  | "Inspect"
  | "About"
  | "SearchAbout"
  | "SearchRewrite"
  | "Search"
  | "Locate"
  | "Eval"
  | "Reset"
  | "Check"
  | "Type"
  | "Section"
  | "Chapter"
  | "Variable" 's'?
  | ("Hypothesis" | "Hypotheses")
  | "End"

let prf_not_opaque_end_kw =
  "Defined" | "Abort"
  (*immediate_prf_token | "Defined" | "Abort"*)

let prf_opaque_end_kw =
  "Qed" | "Save" | "Admitted"

let extraction =
  "Extraction"
  | "Recursive" space+ "Extraction"
  | "Extract"

let gallina_kw = thm_token | def_token | decl_token | gallina_ext | commands | extraction

let prog_kw =
  "Program" space+ gallina_kw
  | "Obligation"
  | "Obligations"
  | "Solve"

let hint_kw = 
  "Extern" | "Rewrite" | "Resolve" | "Immediate" | "Transparent" | "Opaque" | "Unfold" | "Constructors"

let set_kw =
    "Printing" space+ ("Coercions" | "Universes" | "All")
  | "Implicit" space+ "Arguments"

let gallina_kw_to_hide =
    "Implicit" space+ "Arguments"
  | ("Local" space+)? "Ltac"
  | "Require"
  | "Import"
  | "Export"
  | "Load"
  | "Hint" space+ hint_kw
  | "Open"
  | "Close"
  | "Delimit"
  | "Transparent"
  | "Opaque"
  | ("Declare" space+ ("Morphism" | "Step") )
  | ("Set" | "Unset") space+ set_kw
  | "Declare" space+ ("Left" | "Right") space+ "Step"
  | "Debug" space+ ("On" | "Off")

(* Scanning Coq, at beginning of line *)

rule coq_bol = parse
  | space* nl+
      { coq_bol lexbuf }
  | space* thm_token
      { (*Printf.printf "thm_token\n";*)
	seen_thm := true;
	Buffer.clear buf;
        let eol = body lexbuf in
	(*Printf.printf "%B\n" eol;*)
	in_proof := Some eol;
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_token
      { in_proof := Some true;
	let eol = skip_to_dot lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_opaque_end_kw
      {
	let s = lexeme lexbuf in
	let is_admitted = s = "Admitted" in
	let thm = match !curr_thm with Some t -> t | None -> "" in
	let prf = String.trim (Buffer.contents buf) in
	let row =
	  Printf.sprintf "%s { \"name\": \"%s.%s\", \"isAdmitted\": %B, \"body\": \"%s\", \"bodyDigest\": \"%s\" }"
	    !delim !modname thm is_admitted prf (digest prf)
	in
	Printf.printf "%s" row;
	let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	delim := ",\n";
	Buffer.reset buf;
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_not_opaque_end_kw
      { let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	if eol then coq_bol lexbuf else coq lexbuf }
  | eof
      { () }
  | _
      {
	let eol = begin backtrack lexbuf; body_bol lexbuf end in
	if eol then coq_bol lexbuf else coq lexbuf
      }

(* Scanning Coq elsewhere *)

and coq = parse
  | nl
      { coq_bol lexbuf }
  | eof
      { () }
  | prf_token
      { in_proof := Some true;
	let eol = skip_to_dot lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | prf_opaque_end_kw
      { let s = lexeme lexbuf in
	let is_admitted = s = "Admitted" in
	let thm = match !curr_thm with Some t -> t | None -> "" in
	let prf = String.trim (Buffer.contents buf) in
	let row =
	  Printf.sprintf "%s { \"name\": \"%s.%s\", \"isAdmitted\": %B, \"body\": \"%s\", \"bodyDigest\": \"%s\" }"
	    !delim !modname thm is_admitted prf (digest prf)
	in
	Printf.printf "%s" row;
	let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	delim := ",\n";
	Buffer.reset buf;
	if eol then coq_bol lexbuf else coq lexbuf }
  | prf_not_opaque_end_kw
      { let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	if eol then coq_bol lexbuf else coq lexbuf }
  | _ {	let eol = begin backtrack lexbuf; body lexbuf end in
	if eol then coq_bol lexbuf else coq lexbuf }

and body_bol = parse
  | space+
      { body lexbuf }
  | _ { backtrack lexbuf; body lexbuf }

and body = parse
  | nl
      { Lexing.new_line lexbuf;
	if !in_proof = Some true then Buffer.add_string buf "\n";
	body_bol lexbuf }
  | eof
      { false }
  | '.' space* nl
      { if !in_proof = Some true then Buffer.add_string buf ".\n" ;
	true }
  | '.' space* eof
      { if !in_proof = Some true then Buffer.add_char buf '.';
	true }
  | '.' space+
      { if !in_proof = Some true then Buffer.add_string buf ". ";
	false }
  | identifier
      { let s = lexeme lexbuf in
	if !seen_thm then begin
	  curr_thm := Some s;
	  seen_thm := false;
	  skip_to_dot lexbuf
	end
        else begin
	  if !in_proof = Some true then Buffer.add_string buf s;
          body lexbuf
	end
      }
  | space
      { if !in_proof = Some true then Buffer.add_char buf (lexeme_char lexbuf 0);
	body lexbuf }

  | _ { if !in_proof = Some true then Buffer.add_char buf (lexeme_char lexbuf 0);
	body lexbuf }

and skip_to_dot = parse
  | '.' space* nl { true }
  | eof | '.' space+ { false }
  | _ { skip_to_dot lexbuf }

(* Applying the scanners to files *)

{

  let coq_file f m =
    reset ();
    let bfname = Filename.chop_suffix f ".v" in
    let dirname, fname = normalize_filename bfname in
    modname := fname;
    let c = open_in f in
    let lb = from_channel c in
    Printf.printf "%s" "[\n";
    coq_bol lb;
    Printf.printf "%s" "\n]\n";
    close_in c

}
