{
  open Printf
  open Lexing

  (* helper functions *)

  let backtrack lexbuf = lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let reset () = 
    ()

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
  | "Proof" (space* "." | space+ "with" | space+ "using")

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

let proof_end_kw =
  immediate_prf_token | "Qed" | "Defined" | "Save" | "Admitted" | "Abort"

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
      { let s = lexeme lexbuf in
	(* output s lexbuf *)
        let eol = body lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_token
      { let eol =
	  begin backtrack lexbuf; body_bol lexbuf end
	in if eol then coq_bol lexbuf else coq lexbuf }
  | eof
      { () }
  | _
      { () }

(* Scanning Coq elsewhere *)

and coq = parse
  | nl
      { coq_bol lexbuf }

and body_bol = parse
  | space+
      { body lexbuf }
  | _ { backtrack lexbuf; body lexbuf }

and body = parse
  | nl { Tokens.flush_sublexer(); Lexing.new_line lexbuf; body_bol lexbuf }

(* Applying the scanners to files *)

{

  let coq_file f m =
    reset ();
    let c = open_in f in
    let lb = from_channel c in
    coq_bol lb;
    close_in c

}
