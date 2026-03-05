open Oscar
open Raw
open Common
open Toplevel

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
let lambda = symbol "\\" <|> symbol "λ"
let ( let* ) = Oscar.bind

(*
  Ebnf:
  (* 基础项 *)
  atom ::= identifier | 'U' (Universe) | '_' (Hole) | '(' term ')'

  (* 绑定参数 *)
  binder ::= identifier | '_'

  (* lam 参数绑定 *)
  lam_binder ::= binder | '{' binder '}' | '{' identifier '=' binder '}'

  (* Pi 类型绑定 *)
  pi_binder ::= '{' binder+ (':' term)? '}' | '(' binder+ ':' term ')'

  (* 核心语法 *)
  term ::= 
      | '\' lam_binder+ '.' term               (* Lambda 抽象 *)
      | 'let' binder (':' term)? '=' term ';' term  (* Let 表达式 *)
      | pi_binder+ '->' term                   (* Pi 类型 (显式/隐式) *)
      | spine ('->' term)?                     
      (* 函数箭头或普通调用: spine 的优先级要大于普通函数类型，因此将 普通函数类型 与 Π-type 分层处理 *)

  (* 应用 (Spine) *)
  spine ::= atom (arg)*
  arg   ::= '{' identifier '=' term '}' | atom | '{' term '}'
*)

let is_keyword s =
  List.mem s [ "let"; "Type"; "λ"; "U"; "theorem"; "lemma"; "axiom"; "def"; "in" ]

let parse_ident : name parser =
  let* x = take_while1 (fun c -> P.is_alphanum c) in
  if is_keyword x then empty else lex (return x)

let parse_binder = parse_ident <|> symbol "_"

let parse_keywrod s =
  let* kw = string s in
  let* x = peek_char in
  match x with Some c when P.is_alphanum c -> empty | _ -> lex (return kw)

let digits = lex (int_of_string <$> take_while1 P.is_digit)
let dot = symbol "."

let term_parser =
  let mk_app x xs = List.fold_left (fun acc (i, t) -> App (acc, t, i)) x xs in
  let mk_var n = Var n in
  let mk_universe _ = Universe in
  let mk_hole _ = Hole in
  fix (fun raw ->
    (* U (Universe), x (identifier), t (raw term) *)
    let parse_atom =
      mk_var <$> parse_ident
      <|> (mk_universe <$> char 'U')
      <|> (mk_hole <$> char '_')
      <|> parens raw
    in

    (* {x = t}, {y}, z *)
    let parser_args =
      braces ((fun n t -> (Left n, t)) <$> parse_ident <* char '=' <*> raw)
      <|> ((fun t -> (Right Explicit, t)) <$> parse_atom)
      <|> ((fun t -> (Right Implicit, t)) <$> braces raw)
    in

    (* a {x = t} {y} z  *)
    let parse_spine = mk_app <$> parse_atom <*> many parser_args in

    let parse_lam_binder =
      (fun x -> (x, Right Explicit))
      <$> parse_binder
      <|> ((fun x -> (x, Right Implicit)) <$> braces parse_binder)
      <|> braces ((fun n t -> (t, Left n)) <$> parse_ident <* char '=' <*> parse_binder)
    in

    (* \{x = a} {y} z . t *)
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
      (fun n x y z -> Let (n, Option.value x ~default:Hole, y, z))
      <$> parse_keywrod "let" *> parse_binder
      <*> optional (char ':' *> raw)
      <* symbol "=" <*> raw
      <* (symbol ";" <|> symbol "in")
      <*> raw
    in

    parse_lam <|> parse_let <|> parse_pi <|> parse_fun_or_spine)

let def_parser =
  (fun n x y -> Definition (n, Option.value x ~default:Hole, y))
  <$> parse_keywrod "def" *> parse_ident
  <*> optional (char ':' *> term_parser)
  <* symbol "=" <*> term_parser <* dot

let thm_parser =
  (fun n x y -> Theorem (n, Option.value x ~default:Hole, y))
  <$> (parse_keywrod "theorem" <|> parse_keywrod "lemma") *> parse_ident
  <*> optional (char ':' *> term_parser)
  <* symbol "=" <*> term_parser <* dot

let axiom_parser =
  (fun n x -> Axiom (n, x))
  <$> parse_keywrod "axiom" *> parse_ident
  <*> char ':' *> term_parser
  <* dot

let top_level = many (axiom_parser <|> thm_parser <|> def_parser)
let parser = ws *> top_level <* end_of_file
let parse s = parser.run (make_input s)
