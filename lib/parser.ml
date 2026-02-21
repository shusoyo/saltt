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
let braces p = char '{' *> p <* char '}'
let arrow = symbol "->" <|> symbol "→"
let ( let* ) = Oscar.bind
let keyword s = List.mem s [ "let"; "Type"; "λ"; "U" ]

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
  let mk_app x xs = List.fold_left (fun acc (i, t) -> App (acc, t, i)) x xs in
  let mk_var n = Var n in
  let mk_universe _ = Universe in
  let mk_hole _ = Hole in
  let lambda = symbol "\\" <|> symbol "λ" in
  fix (fun raw ->
    let parse_atom =
      mk_var <$> parse_ident
      <|> (mk_universe <$> symbol "U")
      <|> (mk_hole <$> symbol "_")
      <|> parens raw
    in

    let parser_args =
      braces ((fun n t -> (Left n, t)) <$> parse_ident <* char '=' <*> raw)
      <|> ((fun t -> (Right Explicit, t)) <$> parens raw)
      <|> ((fun t -> (Right Implicit, t)) <$> braces raw)
    in

    let parse_spine = mk_app <$> parse_atom <*> many parser_args in

    let parse_binder = parse_ident <|> symbol "_" in

    let parse_lam_binder =
      (fun x -> (x, Right Explicit))
      <$> parse_ident
      <|> ((fun x -> (x, Right Implicit)) <$> braces parse_binder)
      <|> braces ((fun n t -> (t, Left n)) <$> parse_ident <* char '=' <*> parse_binder)
    in

    let parse_lam =
      (fun names body -> List.fold_right (fun (n, i) b -> Lam (n, i, b)) names body)
      <$> lambda *> many1 parse_lam_binder
      <*> char '.' *> raw
    in

    let parse_pi_binder : (name list * ty * implicit) parser =
      braces
        ((fun x y -> (x, y, Implicit))
        <$> many1 parse_binder
        <*> (char ':' *> raw <|> return Hole))
      <|> parens ((fun x y -> (x, y, Explicit)) <$> many1 parse_binder <*> char ':' *> raw)
    in

    let parse_pi =
      let mk_pi i a ns b = List.fold_right (fun n acc -> Pi (n, i, a, acc)) ns b in
      (fun dom codom -> List.(fold_right (fun (ns, a, i) b -> mk_pi i a ns b) dom codom))
      <$> many1 parse_pi_binder <* arrow <*> raw
    in

    let parse_fun_or_spine =
      let* sp = parse_spine in
      optional arrow >>= fun arr ->
      match arr with
      | Some _ -> (fun x -> Pi ("_", Explicit, sp, x)) <$> raw
      | None -> return sp
    in

    let parse_let =
      (fun n a b d -> mk_let n a b d)
      <$> parse_keywrod "let" *> parse_binder
      <* char ':' <*> raw <* symbol "=" <*> raw <* symbol ";" <*> raw
    in

    parse_lam <|> parse_let <|> parse_pi <|> parse_fun_or_spine)

let parser = ws *> term_parser <* end_of_file
