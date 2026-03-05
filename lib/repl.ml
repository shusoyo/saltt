open Errors
open Parser
open Toplevel

let parse_commands src =
  match Parser.parse src with
  | Ok (_, commands) -> commands
  | Error _ -> failwith "parse error"

let command_name = function
  | Definition (name, _, _) | Theorem (name, _, _) | Axiom (name, _) -> name

let process_commands commands =
  List.iter
    (fun cmd ->
      process_command cmd;
      Printf.printf "Checked: %s\n" (command_name cmd))
    commands

let read_file filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let check_source src =
  let commands = parse_commands src in
  process_commands commands

let check_file filename =
  check_source (read_file filename);
  print_endline "OK."

let run ~help_message () =
  print_endline "saltt toplevel. End each command with '.'; use :q to quit.";
  let rec loop () =
    print_string "saltt> ";
    flush stdout;
    match read_line () with
    | exception End_of_file -> print_endline ""
    | line ->
        let input = String.trim line in
        if input = "" then loop ()
        else if input = ":q" || input = ":quit" then ()
        else if input = ":help" then (
          print_endline help_message;
          loop ())
        else
          let () =
            try check_source input
            with exn when Errors.is_domain_error exn ->
              Printf.eprintf "%s\n" (Errors.exn_to_string exn)
          in
          loop ()
  in
  loop ()
