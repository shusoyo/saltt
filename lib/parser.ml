open Oscar
open Syntax
open Common

module P = struct
  let is_space = function ' ' | '\t' -> true | _ -> false
  let is_digit = Char.Ascii.is_digit
  let is_alphanum = Char.Ascii.is_alphanum
end

let single_line_comment : unit parser =
  string "--" *> skip_while (( <> ) '\n')
  <* (char '\n' *> return () <|> end_of_file)

let ws = skip_many (single_line_comment <|> skip_while1 P.is_space)
let lex p = p <* ws
let symbol s = lex (string s)
let char c = lex (char c)
let parens p = char '(' *> p <* char ')'
let ( let* ) = Oscar.bind

let keyword s =
  let* kw = string s in
  let* x = peek_char in
  match x with Some c when P.is_alphanum c -> empty | _ -> lex (return kw)

let digits = lex (int_of_string <$> take_while1 P.is_digit)
let index = lex ((fun x -> Ix x) <$> digits)

let term_parser =
  let mk_let x y = Let (x, y) in
  let mk_app x xs = List.fold_left (fun acc t -> App (acc, t)) x xs in
  fix (fun term ->
    let atom = (fun x -> Var x) <$> index <|> parens term in
    let spine = mk_app <$> atom <*> many atom in
    let lam = (symbol "\\" <|> symbol "λ") *> ((fun x -> Lam x) <$> term) in
    let let_ = mk_let <$> keyword "let" *> term <*> keyword "in" *> term in

    lam <|> let_ <|> spine)

let parser = ws *> term_parser <* end_of_file
