open Cdglobals
open Printf

let usage () =
  prerr_endline "";
  prerr_endline "Usage: coqdigest <options and files>";
  prerr_endline "  -o <file>            write output in file <file>";
  prerr_endline "  -d <dir>             output files into directory <dir>";
  prerr_endline "  --stdout             write output to stdout";
  prerr_endline "  -n <string>          set namespace <string>";
  prerr_endline "  -b                   show proof bodies (for debugging)";
  prerr_endline "";
  exit 1

let banner () =
  eprintf "This is coqdigest version %s, compiled on %s\n"
    Coq_config.version Coq_config.compile_date;
  flush stderr

let check_if_file_exists f =
  if not (Sys.file_exists f) then begin
    eprintf "coqdigest: %s: no such file\n" f;
    exit 1
  end

(* [paths] maps a physical path to a name *)
let paths = ref []

let namespace = ref None
let show_body = ref false

let add_path dir name =
  let p = normalize_path dir in
  paths := (p,name) :: !paths

(* turn A/B/C into A.B.C *)
let rec name_of_path p name dirname suffix =
  if p = dirname then String.concat "." (if name = "" then suffix else (name::suffix))
  else
    let subdir = Filename.dirname dirname in
    if subdir = dirname then raise Not_found
    else name_of_path p name subdir (Filename.basename dirname::suffix)

let coq_module filename =
  let bfname = Filename.chop_extension filename in
  let dirname, fname = normalize_filename bfname in
  let rec change_prefix = function
    (* Follow coqc: if in scope of -R, substitute logical name *)
    (* otherwise, keep only base name *)
    | [] -> fname
    | (p, name) :: rem ->
	try name_of_path p name dirname [fname]
	with Not_found -> change_prefix rem
  in
  change_prefix !paths

let what_file f =
  check_if_file_exists f;
  if Filename.check_suffix f ".v" then
    Vernac_file (f, coq_module f)
  else
     (eprintf "\ncoqdigest: don't know what to do with %s\n" f; exit 1)

let parse () =
  let files = ref [] in
  let add_file f = files := f :: !files in
  let rec parse_rec = function
    | [] -> ()

    | ("-stdout" | "--stdout") :: rem ->
	out_to := StdOut; parse_rec rem
    | ("-o" | "--output") :: f :: rem ->
	out_to := File (Filename.basename f); output_dir := Filename.dirname f; parse_rec rem
    | ("-o" | "--output") :: [] ->
	usage ()
    | ("-d" | "--directory") :: dir :: rem ->
	output_dir := dir; parse_rec rem
    | ("-d" | "--directory") :: [] ->
	usage ()

    | ("-h" | "-help" | "-?" | "--help") :: rem ->
	banner (); usage ()

    | ("-b" | "-body" | "--body") :: rem ->
	show_body := true; parse_rec rem

    | ("-n" | "-namespace" | "--namespace") :: n :: rem ->
        namespace := Some n; parse_rec rem

    | ("-n" | "-namespace" | "--namespace") :: [] ->
        usage ()

    | f :: rem ->
	add_file (what_file f); parse_rec rem
  in
    parse_rec (List.tl (Array.to_list Sys.argv));
    List.rev !files

let gen_one_file l =
  let file = function
    | Vernac_file (f,m) ->
        Ppretty.coq_file f m !namespace !show_body
    | _ -> ()
  in
  List.iter file l

let gen_mult_files l =
  let file = function
    | Vernac_file (f,m) ->
        let hf = Printf.sprintf "%s.json" m in
        open_out_file hf;
        Ppretty.coq_file f m !namespace !show_body;
        close_out_file ()
    | _ -> ()
  in
  List.iter file l

let produce_output l =
  match !out_to with
    | StdOut ->
	Cdglobals.out_channel := stdout;
	gen_one_file l
    | File f ->
	open_out_file f;
	gen_one_file l;
	close_out_file ()
    | MultFiles ->
        gen_mult_files l

let _ =
  let files = parse () in
  if not !quiet then banner ();
  if files <> [] then produce_output files
