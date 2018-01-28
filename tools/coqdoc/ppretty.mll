{
  open Printf
  open Lexing

  module Op =
  struct
    let ( >> ) = Int32.shift_right
    let ( << ) = Int32.shift_left
    let ( && ) = Int32.logand
    let ( || ) = Int32.logor

    let ( ! ) x = Int32.of_int !x
  end

  let _base = 65521
  let _nmax = 5552

 let adler32 buf adler32 off len =
  let a = ref (Int32.to_int Op.((adler32 >> 16) && 0xFFFFl)) in
  let b = ref (Int32.to_int Op.(adler32 && 0xFFFFl)) in
  let l = ref len in
  let o = ref off in

  if len = 0
  then adler32
  else if len = 1
  then begin
    b := !b + (Char.code @@ String.get buf !o);
    if !b >= _base then b := !b - _base;
    a := !a + !b;
    if !a >= _base then a := !a - _base;

    Op.(!b || (!a << 16))
  end else if len < 16
  then begin
    while !l <> 0
    do b := !b + (Char.code @@ String.get buf !o);
       a := !a + !b;
       incr o;
       decr l;
    done;

    if !b >= _base then b := !b - _base;
    a := !a mod _base;

    Op.(!b || (!a << 16))
  end else begin
    while !l >= _nmax
    do l := !l - _nmax;

       for _ = _nmax / 16 downto 1
       do b := !b + (Char.code @@ String.get buf !o);
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 1));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 2));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 3));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 4));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 5));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 6));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 7));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 8));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 9));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 10));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 11));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 12));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 13));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 14));
          a := !a + !b;
          b := !b + (Char.code @@ String.get buf (!o + 15));
          a := !a + !b;

          o := !o + 16
       done;

       b := !b mod _base;
       a := !a mod _base;
    done;

    if !l > 0
    then begin
      while !l >= 16
      do l := !l - 16;

         b := !b + (Char.code @@ String.get buf !o);
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 1));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 2));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 3));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 4));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 5));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 6));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 7));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 8));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 9));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 10));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 11));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 12));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 13));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 14));
         a := !a + !b;
         b := !b + (Char.code @@ String.get buf (!o + 15));
         a := !a + !b;

         o := !o + 16;
      done;

      while !l > 0
      do b := !b + (Char.code @@ String.get buf !o);
         a := !a + !b;
         decr l;
         incr o;
      done;

      b := !b mod _base;
      a := !a mod _base;
    end;

    Op.(!b || (!a << 16))
  end

  let adler32_digest s =
    let d = adler32 s Int32.one 0 (String.length s) in
    Printf.sprintf "%lX" d

  let md5_digest s = Digest.to_hex (Digest.string s)

  let digest = ref md5_digest

  let modname = ref ""
  let namespace = ref ""

  let seen_thm = ref false
  let seen_mod = ref false
  let seen_end = ref false
  let seen_let = ref false

  let curr_thm = ref None
  let curr_mod = ref None
  let in_proof = ref None

  let delim = ref ""

  let show_body = ref false

  let comment_level = ref 0
  let paren_level = ref 0
  let brace_level = ref 0

  (* helper functions *)

  let backtrack lexbuf =
    lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let printf s =
    Printf.fprintf !(Cdglobals.out_channel) "%s" s

  let reset () =
    comment_level := 0;
    paren_level := 0;
    brace_level := 0;
    delim := "";
    seen_thm := false;
    seen_mod := false;
    seen_end := false;
    seen_let := false;
    curr_thm := None;
    curr_mod := None;
    in_proof := None

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
  | "Definition"
  | "Example"
(*  | "Instance" *)

let mod_token =
  "Module"

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

let mod_end_kw =
  "End"

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
  | space* mod_token
      { seen_mod := true;
	let eol = body lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* thm_token
      { seen_thm := true;
	Buffer.clear buf;
        let eol = body lexbuf in
	in_proof := Some eol;
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_token
      { in_proof := Some true;
	let eol = skip_to_dot lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* mod_end_kw
      { seen_end := true;
	let eol = body lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_opaque_end_kw
      { begin match !curr_thm with
        | None -> ()
        | Some thm ->
	  begin
	    let s = lexeme lexbuf in
	    let is_admitted = s = "Admitted" in
	    let mo = match !curr_mod with Some m -> (Printf.sprintf "%s." m) | None -> "" in
	    let prf = String.trim (Buffer.contents buf) in
	    let prf_digest = !digest prf in
	    let row =
	      if !show_body then
		Printf.sprintf "%s { \"name\": \"%s%s.%s%s\", \"isAdmitted\": %B, \"body\": \"%s\", \"bodyDigest\": \"%s\" }"
		  !delim !namespace !modname mo thm is_admitted prf prf_digest
	      else
		Printf.sprintf "%s { \"name\": \"%s%s.%s%s\", \"isAdmitted\": %B, \"bodyDigest\": \"%s\" }"
		  !delim !namespace !modname mo thm is_admitted prf_digest
	    in
	    printf row;
	    delim := ",\n"
	  end
        end;
	let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	Buffer.reset buf;
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_not_opaque_end_kw
      { let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	Buffer.reset buf;
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* "(*"
      { comment_level := 1;
	let eol = skipped_comment lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf
      }
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
  | "(*"
      { comment_level := 1;
	let eol = skipped_comment lexbuf in
        if eol then coq_bol lexbuf else coq lexbuf }
  | eof
      { () }
  | prf_token
      { in_proof := Some true;
	let eol = skip_to_dot lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | mod_end_kw
      { seen_end := true;
	let eol = body lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf
      }
  | prf_opaque_end_kw
      { begin match !curr_thm with
        | None -> ()
        | Some thm ->
	  begin
	    let s = lexeme lexbuf in
	    let is_admitted = s = "Admitted" in
	    let mo = match !curr_mod with Some m -> (Printf.sprintf "%s." m) | None -> "" in
	    let prf = String.trim (Buffer.contents buf) in
	    let prf_digest = !digest prf in
	    let row =
	      if !show_body then
		Printf.sprintf "%s { \"name\": \"%s%s.%s%s\", \"isAdmitted\": %B, \"body\": \"%s\", \"bodyDigest\": \"%s\" }"
		  !delim !namespace !modname mo thm is_admitted prf prf_digest
	      else
		Printf.sprintf "%s { \"name\": \"%s%s.%s%s\", \"isAdmitted\": %B, \"bodyDigest\": \"%s\" }"
		  !delim !namespace !modname mo thm is_admitted prf_digest
	    in
	    printf row;
	    delim := ",\n"
	  end
        end;
	let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	Buffer.reset buf;
	if eol then coq_bol lexbuf else coq lexbuf }
  | prf_not_opaque_end_kw
      { let eol = skip_to_dot lexbuf in
	in_proof := None;
	curr_thm := None;
	Buffer.reset buf;
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
  | "{|" { if !in_proof = Some true then Buffer.add_string buf "{|";
	   body lexbuf }
  | '{'
      {
	if !curr_thm <> None && !in_proof = Some true then
	  begin
	    Buffer.add_char buf (lexeme_char lexbuf 0);
	    brace_level := 1;
	    skip_to_right_brace_in_proof lexbuf
	  end
	else
	  body lexbuf
      }
  | identifier
      { let s = lexeme lexbuf in
	if !seen_thm then
	  begin
	    curr_thm := Some s;
	    seen_thm := false;
	    paren_level := 0;
	    brace_level := 0;
	    seen_let := false;
	    skip_to_thm_assignment_and_dot lexbuf
	  end
	else if !seen_mod && s <> "Import" then
	  begin
	    curr_mod := if s = "Type" then None else Some s;
	    seen_mod := false;
	    paren_level := 0;
	    skip_to_mod_assignment_and_dot lexbuf
	  end
	else if !seen_mod && s = "Import" then
          body lexbuf
	else if !seen_end then
	  begin
	    begin match !curr_mod with None -> () | Some m -> if m = s then curr_mod := None end;
	    seen_end := false;
	    skip_to_dot lexbuf
	  end
        else
	  begin
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

and skip_to_mod_assignment_and_dot = parse
  | "(" { incr paren_level;
	  skip_to_mod_assignment_and_dot lexbuf }
  | ")" { decr paren_level;
	  skip_to_mod_assignment_and_dot lexbuf }
  | ":=" { if !paren_level = 0 then
             begin
              curr_mod := None;
              skip_to_dot lexbuf
	     end
           else
             skip_to_mod_assignment_and_dot lexbuf }
  | '.' space* nl { true }
  | eof | '.' space+ { false }
  | _ { skip_to_mod_assignment_and_dot lexbuf }

and skip_to_thm_assignment_and_dot = parse
  | "let" { if !paren_level = 0 then seen_let := true;
	    skip_to_thm_assignment_and_dot lexbuf }
  | "{|" { incr brace_level;
	  skip_to_thm_assignment_and_dot lexbuf }
  | "|}" { decr brace_level;
	  skip_to_thm_assignment_and_dot lexbuf }
  | "(" { incr paren_level;
	  skip_to_thm_assignment_and_dot lexbuf }
  | ")" { decr paren_level;
	  skip_to_thm_assignment_and_dot lexbuf }
  | ":=" { if !paren_level = 0 && !brace_level = 0 && not !seen_let then
             begin
              curr_thm := None;
              skip_to_dot lexbuf
	     end
           else if !seen_let then
	     begin
	       seen_let := false;
	       skip_to_thm_assignment_and_dot lexbuf
	     end
	   else
             skip_to_thm_assignment_and_dot lexbuf }
  | '.' space* nl { true }
  | eof | '.' space+ { false }
  | _ { skip_to_thm_assignment_and_dot lexbuf }

and skipped_comment = parse
  | "(*"
      { incr comment_level;
	skipped_comment lexbuf }
  | "*)" space* nl
      { decr comment_level;
        if !comment_level > 0 then skipped_comment lexbuf else true }
  | "*)"
      { decr comment_level;
        if !comment_level > 0 then skipped_comment lexbuf else false }
  | eof { false }
  | _ { skipped_comment lexbuf }

and skip_to_right_brace_in_proof = parse
  | '{'
      { Buffer.add_char buf (lexeme_char lexbuf 0);
	incr brace_level;
	skip_to_right_brace_in_proof lexbuf }
  | '}' space* nl
      { Buffer.add_char buf '}';
	Buffer.add_char buf '\n';
	decr brace_level;
	if !brace_level = 0 then true else skip_to_right_brace_in_proof lexbuf
      }
  | '}' space+
      { Buffer.add_char buf '}';
	Buffer.add_char buf ' ';
	decr brace_level;
	if !brace_level = 0 then false else skip_to_right_brace_in_proof lexbuf }
  | '}'
      { Buffer.add_char buf '}';
	decr brace_level;
	if !brace_level = 0 then false else skip_to_right_brace_in_proof lexbuf }
  | eof { false }
  | _ { Buffer.add_char buf (lexeme_char lexbuf 0); skip_to_right_brace_in_proof lexbuf }


(* Applying the scanners to files *)

{

  let coq_file f m ns b a32 =
    reset ();
    modname := m;
    begin match ns with
    | None -> ()
    | Some n ->
      namespace := Printf.sprintf "%s." n
    end;
    show_body := b;
    digest := if a32 then adler32_digest else md5_digest;
    let c = open_in f in
    let lb = from_channel c in
    printf "[\n";
    coq_bol lb;
    printf "\n]\n";
    close_in c

}
