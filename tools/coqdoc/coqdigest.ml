open Cdglobals
open Printf

let usage () =
  prerr_endline "";
  prerr_endline "Usage: coqdigest <options and files>"

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
  if Filename.check_suffix f ".v" || Filename.check_suffix f ".g" then
    Vernac_file (f, coq_module f)
  else
     (eprintf "\ncoqdigest: don't know what to do with %s\n" f; exit 1)

let index_module = function
  | Vernac_file (f,m) ->
      Index.add_module m
  | _ -> ()

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

    | ("-h" | "-help" | "-?" | "--help") :: rem ->
	banner (); usage ()

    | ("-q" | "-quiet" | "--quiet") :: rem ->
	quiet := true; parse_rec rem

    | f :: rem ->
	add_file (what_file f); parse_rec rem
  in
    parse_rec (List.tl (Array.to_list Sys.argv));
    List.rev !files

let gen_one_file l =
  let file = function
    | Vernac_file (f,m) ->
      Ppretty.coq_file f m
    | _ -> ()
  in
  List.iter file l

let produce_output l =
  List.iter index_module l;
  match !out_to with
    | StdOut ->
	Cdglobals.out_channel := stdout;
	gen_one_file l
    | File f ->
	open_out_file f;
	gen_one_file l;
	close_out_file ()
    | _ ->
      ()

let _ =
  let files = parse () in
    Index.init_coqlib_library ();
    if not !quiet then banner ();
    if files <> [] then begin
      produce_output files;
    end
