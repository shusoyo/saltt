open Saltt
open Oscar
open Parser
open Evaluation
open Elaboration
open Context
open Pretty

let ex4 =
  {|
let id : (A : _) -> A -> A
  = \A x. x;

let List : U -> U
  = \A. (L : _) -> (A -> L -> L) -> L -> L;

let nil : (A : _) -> List A
  = \A L cons nil. nil;

let cons : (A : _) -> A -> List A -> List A
  = \A x xs L cons nil. cons x (xs _ cons nil);

let Bool : U
  = (B : _) -> B -> B -> B;

let true : Bool
  = \B t f. t;

let false : Bool
  = \B t f. f;

let not : Bool -> Bool
  = \b B t f. b B f t;

let list1 : List Bool
  = cons _ (id _ true) (nil _);

let Eq : (A : _) -> A -> A -> U
  = \A x y. (P : A -> U) -> P x -> P y;

let refl : (A : _)(x : A) -> Eq A x x
  = \A x P px. px;

let list1 : List Bool
  = cons _ true (cons _ false (nil _));

let Nat  : U = (N : U) -> (N -> N) -> N -> N;
let five : Nat = \N s z. s (s (s (s (s z))));
let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;

let ten      : Nat = add five five;
let hundred  : Nat = mul ten ten;
let thousand : Nat = mul ten hundred;

let eqTest : Eq _ hundred hundred = refl _ _;

id
|}

let ex0 =
  {|
let id : (A : U) -> A -> A = \A x. x;

let Bool : U
  = (B : _) -> B -> B -> B;

let true : Bool
  = \B t f. t;

let false : Bool
  = \B t f. f;

id _ true
|}

let get_raw file = file |> make_input |> parser.run |> Result.get_ok |> snd
let tests = [ ex4; ex0 ]

let test_unit test =
  let open Result in
  let raw = test |> get_raw in
  Printf.printf "Raw term:\n%s\n" (raw_to_string raw);
  Printf.printf "Raw term:\n%s\n" (R.show_term raw);
  match raw |> infer_type empty_ctx with
  | Ok (tm, ty) ->
      Printf.printf "inferred type:\n%s\n" (Value.show_ty (force ty));
      Printf.printf "inferred type syntax:\n%s\n" (syntax_to_string (quote (Lvl 0) ty));
      Printf.printf "core term:\n%s\n" (syntax_to_string tm);
      let norm = normalize [] tm in
      Printf.printf "normalized term:\n%s\n" (syntax_to_string norm)
      (* Printf.printf "normalized term:\n%s\n" (S.show_term norm) *)
  | Error msg -> Printf.printf "%s\n" msg

let () = List.iter test_unit tests
