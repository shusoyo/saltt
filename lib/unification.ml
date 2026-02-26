open Context
open Common
open Meta
open Syntax
open Value
open Evaluation
open Display

(*
  - 必须是变量: spine 里的每一项都必须是局部变量 (VVar)。
    不能写 ?α (f x) = ...，只能写 ?α x = ...。

  - 必须互不相同 (Distinct): spine 里的变量不能重复。不能写 ?α x x = ...，
    因为这样不知道右边的 x 到底对应左边的第1个还是第2个。

  - 必须包含所有依赖: 虽然不在 invert 里检查，但后续的 rename 会检查。
    如果在 RHS 里用了 spine 里没出现的变量，那就是非法。
*)

(* Level Map *)
module LvlMap = Map.Make (struct
  type t = level

  let compare (Lvl l) (Lvl r) = Int.compare l r
end)

(* `partial` 意味着并不是 Δ 中的所有变量都能在 Γ 中找到对应 *)
type partial_renaming = { dom : level; cod : level; ren : level LvlMap.t }
(** partial renaming
    - [dom]: size of Γ
    - [cod]: size of Δ
    - [ren]: mapping from Δ vars (key) to Γ vars (value) *)

(** [lift pren] using when go under a binder, 
      add map with the (cod, dom) to pren.ren, 
      and set {dom, cod} to the next avaliable value
    - Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[[σ]]) (Δ, x : A)) 
        (Γ, x : A[[σ]]) 为 A 应用当前 σ 重命名 *)
let lift (pren : partial_renaming) : partial_renaming =
  {
    dom = next_level pren.dom;
    cod = next_level pren.cod;
    ren = LvlMap.add pren.cod pren.dom pren.ren;
  }

let unify_error e = raise (UnifyError (DS "Unify Error" :: e))

(** [invert gamma spine] return the spine⁻¹ (pren (Γ Δ))
    - spine is map Δ → Γ (spine is [value list], key is list index (from 0), value is
      debruijn level (from gamma))
    - spine⁻¹ is map Γ → Δ (key is debruijn level (gamma), value is
      list index (from 0)] *)
let invert (gamma : level) (spine : spine) : partial_renaming =
  let dom, ren =
    List.fold_right
      (fun (x, _) (dom, ren) ->
        match force x with
        | VNe (NVar l, _) when not (LvlMap.mem l ren) ->
            (next_level dom, LvlMap.add l dom ren)
        | _ -> unify_error [ DS "can't invert"; DV (vvar gamma) ])
      spine (Lvl 0, LvlMap.empty)
  in
  { dom; cod = gamma; ren }

(** [rename m pren v] apply the pren to a value and quote this value to a term *)
let rename (m : meta_var) (pren : partial_renaming) (v : value) : term =
  let rec go_spine pren t sp =
    List.fold_right
      (fun (x, icit) f ->
        let a = go pren x in
        App (f, a, icit))
      sp t
  and go pren t =
    match force t with
    | VNe (NMeta m', sp) ->
        (* checking for "m" occurrences *)
        if m' = m then
          unify_error [ DS "Rename failed, Occurs check failed, recursive metavariable" ]
        else go_spine pren (Meta m') sp
    | VNe (NVar l, sp) -> begin
        match LvlMap.find_opt l pren.ren with
        | Some l' -> go_spine pren (Var (index_of_level pren.dom l')) sp
        | None -> unify_error [ DS "Rename failed, Variable not in scope" ]
      end
    | VLam (name, icit, f_clos) ->
        let t = go (lift pren) (f_clos $$ vvar pren.cod) in
        Lam (name, icit, t)
    | VPi (name, icit, a_ty_val, b_clos) ->
        let a_ty = go pren a_ty_val in
        let b_tm = go (lift pren) (b_clos $$ vvar pren.cod) in
        Pi (name, icit, a_ty, b_tm)
    | VUniverse -> Universe
  in
  go pren v

let solve (gamma : level) (mv : meta_var) (spine : spine) (rhs : value) : unit =
  let pren = invert gamma spine in
  let rhs = rename mv pren rhs in
  let sp_len = List.length spine in
  let res = ref rhs in
  for i = 0 to sp_len - 1 do
    assert (i < sp_len);
    (* sp_len - i - 1 (i : 0 ... sp_len - 1) : sp_len - 1 ... 0  *)
    let _, icit = List.nth spine (sp_len - i - 1) in
    res := Lam ("x" ^ string_of_int (sp_len - i), icit, !res)
  done;
  let solution = eval [] !res in
  Hashtbl.replace mcxt mv (Solved solution)

let rec unify (l : level) (v1 : value) (v2 : value) : unit =
  match (force v1, force v2) with
  | VLam (_, _, a_body_clos), VLam (_, _, b_body_clos) ->
      unify (next_level l) (a_body_clos $$ vvar l) (b_body_clos $$ vvar l)
  (* η-unify *)
  (* \x. g x ?= g *)
  | VLam (_, icit, body_clos), t ->
      unify (next_level l) (body_clos $$ vvar l) (eval_app t (vvar l) icit)
  (* g ?= \x. g x *)
  | t, VLam (_, icit, body_clos) ->
      unify (next_level l) (eval_app t (vvar l) icit) (body_clos $$ vvar l)
  | VUniverse, VUniverse -> ()
  | VPi (_, a_icit, a_ty, a_clos), VPi (_, b_icit, b_ty, b_clos) when a_icit = b_icit ->
      unify l a_ty b_ty;
      unify (next_level l) (a_clos $$ vvar l) (b_clos $$ vvar l)
  (* Neutral value *)
  | VNe (x_nv, x_sp), VNe (y_nv, y_sp) when x_nv = y_nv ->
      let judge (x, _) (y, _) =
        match unify l x y with () -> true | exception TypeError _ -> false
      in
      begin match List.for_all2 judge x_sp y_sp with
      | true -> ()
      | false -> raise (TypeError [ DS "Unify Error: spine mismatch" ])
      | exception Invalid_argument err -> raise (TypeError [ DS ("Unify Error: " ^ err) ])
      end
  | VNe (NMeta m, sp), t -> solve l m sp t
  | t, VNe (NMeta m, sp) -> solve l m sp t
  | _ -> unify_error [ DS "values do not match"; DV v1; DV v2 ]
