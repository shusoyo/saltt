open Saltt
open Oscar
open Parser
open Evaluation
open Elaboration
open Context
open Pretty

let ex0 =
  "-- the identity function\n\
   let id : (A : U) -> A -> A = λ A x. x in\n\
   -- a constant function\n\
   let foo : U = U in\n\
   let bar : (A : U) -> A -> A = id ((A : U) -> A -> A) id in     -- we cannot \
   apply any function to itself (already true in simple TT)\n\
   id"

let ex1 =
  "-- identity\n\
   let id : (A : U) -> A -> A = λ A x. x in\n\
   -- first projection\n\
   let const : (A : U) -> (B : U) -> A -> B -> A = λ A B x y. x in\n\
   -- apply id to const\n\
   id ((A : U) -> (B : U) -> A -> B -> A) const"

let ex2 =
  "-- natural numbers à la Church\n\
   let Nat  : U = (N : U) -> (N -> N) -> N -> N in\n\n\
   -- 5\n\
   let five : Nat = λ N s z. s (s (s (s (s z)))) in\n\n\
   -- addition\n\
   let add  : Nat -> Nat -> Nat = λ a b N s z. a N s (b N s z) in\n\
   let mul  : Nat -> Nat -> Nat = λ a b N s z. a N (b N s) z in\n\
   let ten      : Nat = add five five in\n\
   let hundred  : Nat = mul ten ten in\n\
   let thousand : Nat = mul ten hundred in\n\
   thousand"

let ex3 =
  "let Bool : U = (B : U) -> B -> B -> B in\n\
   let true : Bool = λ B t f. t in\n\
   let false : Bool = λ B t f. f in\n\
   let not : Bool -> Bool = λ b B t f. b B f t in\n\
   not"

let tests = [ ex0; ex1; ex2; ex3 ]
let get_raw file = file |> make_input |> parser.run |> Result.get_ok |> snd

let test_unit test =
  let open Result in
  let raw = test |> get_raw in
  Printf.printf "Raw term:\n%s\n" (raw_to_string raw);
  (* Printf.printf "Raw term:\n%s\n" (R.show_term raw); *)
  match raw |> infer_type empty_ctx with
  | Ok (tm, ty) ->
      let tm, ty = raw |> infer_type empty_ctx |> get_ok in
      (* Printf.printf "inferred type:\n%s\n" (Value.show_ty ty); *)
      Printf.printf "core term:\n%s\n" (syntax_to_string tm);
      (* Printf.printf "core term:\n%s\n" (S.show_term tm); *)
      let norm = normalize [] tm in
      Printf.printf "normalized term:\n%s\n" (syntax_to_string norm)
      (* Printf.printf "normalized term:\n%s\n" (S.show_term norm) *)
  | Error msg -> Printf.printf "%s\n" msg

let () = List.iter test_unit tests
