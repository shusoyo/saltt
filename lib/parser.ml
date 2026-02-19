open Oscar
open Raw
open Common

module P = struct
  let is_space = function ' ' | '\t' | '\n' -> true | _ -> false
  let is_digit = Char.Ascii.is_digit
  let is_alphanum = Char.Ascii.is_alphanum
end

let single_line_comment : unit parser =
  string "--" *> skip_while (( <> ) '\n') <* (char '\n' *> return () <|> end_of_file)

let ws = skip_many (single_line_comment <|> skip_while1 P.is_space)
let lex p = p <* ws
let symbol s = lex (string s)
let char c = lex (char c)
let parens p = char '(' *> p <* char ')'
let arrow = symbol "->" <|> symbol "→"
let ( let* ) = Oscar.bind
let keyword s = List.mem s [ "let"; "Type"; "Π"; "λ"; "U" ]

let parse_ident : name parser =
  let* x = take_while1 (fun c -> P.is_alphanum c) in
  if keyword x then empty else lex (return x)

let parse_keywrod s =
  let* kw = string s in
  let* x = peek_char in
  match x with Some c when P.is_alphanum c -> empty | _ -> lex (return kw)

let digits = lex (int_of_string <$> take_while1 P.is_digit)

let term_parser =
  let mk_let n x y z = Let (n, x, y, z) in
  let mk_app x xs = List.fold_left (fun acc t -> App (acc, t)) x xs in
  let mk_var n = Var n in
  let mk_universe _ = Universe in
  let mk_lam names body = List.fold_right (fun n b -> Lam (n, b)) names body in
  let mk_pair x y = (x, y) in
  let mk_pi name a body = Pi (name, a, body) in
  let mk_hole _ = Hole in
  let lambda = symbol "\\" <|> symbol "λ" in
  fix (fun raw ->
    let parse_atom =
      mk_var <$> parse_ident
      <|> (mk_universe <$> symbol "U")
      <|> (mk_hole <$> symbol "_")
      <|> parens raw
    in

    let parse_spine = mk_app <$> parse_atom <*> many parse_atom in

    let parse_binder = parse_ident <|> symbol "_" in

    let parse_lam = mk_lam <$> lambda *> many1 parse_binder <*> char '.' *> raw in

    let parse_pi =
      (fun dom codom -> List.fold_right (fun (n, a) b -> mk_pi n a b) dom codom)
      <$> many1 (parens (mk_pair <$> parse_binder <* char ':' <*> raw))
      <* arrow <*> raw
    in

    let parse_fun_or_spine =
      let* sp = parse_spine in
      optional arrow >>= fun arr ->
      match arr with Some _ -> mk_pi "_" sp <$> raw | None -> return sp
    in

    let parse_let =
      (fun n a b d -> mk_let n a b d)
      <$> parse_keywrod "let" *> parse_binder
      <* char ':' <*> raw <* symbol "=" <*> raw <* symbol ";" <*> raw
    in

    parse_lam <|> parse_let <|> parse_pi <|> parse_fun_or_spine)

let parser = ws *> term_parser <* end_of_file
