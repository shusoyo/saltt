open Saltt
open Errors

let prog_name = Filename.basename Sys.argv.(0)

(* ── help messages ─────────────────────────────────────── *)

let usage = Printf.sprintf "usage: %s <command> [<args>]\n" prog_name

let general_help =
  String.concat "\n"
    [
      usage;
      "commands:";
      "  check <file>  check and elaborate all definitions in the file";
      "  toplevel      start interactive toplevel";
      "  help          show this message";
      "";
      "options:";
      "  -h, --help    show this message";
    ]

let command_help cmd =
  match cmd with
  | "check" ->
      String.concat "\n"
        [
          Printf.sprintf "usage: %s check <file>" prog_name;
          "";
          "Read and type-check all definitions, axioms, and theorems from <file>.";
        ]
  | "toplevel" | "repl" ->
      String.concat "\n"
        [
          Printf.sprintf "usage: %s toplevel" prog_name;
          "";
          "Start interactive mode. Enter commands ending with '.'";
          "Special commands: :q, :quit, :help";
        ]
  | _ -> general_help

let die fmt =
  Printf.ksprintf
    (fun msg ->
      Printf.eprintf "%s: %s\n" prog_name msg;
      exit 1)
    fmt

let die_usage fmt =
  Printf.ksprintf
    (fun msg ->
      Printf.eprintf "%s: %s\n%s" prog_name msg usage;
      exit 1)
    fmt

(* ── run ───────────────────────────────────────────────── *)

let run_check filename = Repl.check_file filename
let run_toplevel () = Repl.run ~help_message:(command_help "toplevel") ()

(* ── argument parsing ──────────────────────────────────── *)

type cmd = Check of string | Toplevel | Help of string option

let is_help_flag s = s = "-h" || s = "--help"

let parse_args argv =
  (* drop the program name *)
  let args = Array.to_list argv |> List.tl in
  (* strip leading help flags *)
  match args with
  | [] -> Toplevel
  | [ flag ] when is_help_flag flag -> Help None
  | [ "help" ] -> Help None
  | [ "help"; sub ] -> Help (Some sub)
  | cmd :: rest -> (
      (* if the subcommand itself is followed by --help, show command help *)
      match (cmd, rest) with
      | _, [ flag ] when is_help_flag flag -> Help (Some cmd)
      | "check", [] -> die_usage "%s: missing <file> argument" cmd
      | "check", [ _; _ ] -> die_usage "%s: too many arguments" cmd
      | "check", [ file ] -> Check file
      | ("toplevel" | "repl"), [] -> Toplevel
      | unknown, _ -> die_usage "unknown command '%s'" unknown)

(* ── dispatch ──────────────────────────────────────────── *)

let run cmd =
  match cmd with
  | Help sub -> print_endline (command_help (Option.value sub ~default:""))
  | Check filename -> run_check filename
  | Toplevel -> run_toplevel ()

(* ── entry point ───────────────────────────────────────── *)

let () =
  let cmd = parse_args Sys.argv in
  try run cmd
  with exn when Errors.is_domain_error exn ->
    Printf.eprintf "%s: %s\n" prog_name (Errors.exn_to_string exn);
    exit 1
