open Oscar
open Saltt
open Parser
open Syntax
open Evaluation

let test_string =
  make_input
    "let λ λ 1 (1 (1 (1 (1 0)))) in    -- five = λ s z. s (s (s (s (s z))))\n\
     let λ λ λ λ 3 1 (2 1 0) in        -- add  = λ a b s z. a s (b s z)\n\
     let λ λ λ λ 3 (2 1) 0 in          -- mul  = λ a b s z. a (b s) z\n\
     let 1 2 2 in                      -- ten  = add five five\n\
     let 1 0 0 in                      -- hundred = mul ten ten\n\
     let 2 1 0 in                      -- thousand = mul ten hundred\n\
     2                                 -- ten"

let () =
  test_string |> parser.run |> Result.get_ok |> snd |> to_string
  |> print_endline

let () =
  test_string |> parser.run |> Result.get_ok |> snd |> normalize [] |> to_string
  |> print_endline
