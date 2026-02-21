type name = string

(* index *)
and index = Ix of int

(* level *)
and level = Lvl of int

(* arguments kind *)
and implicit = Implicit | Explicit

(* meta variable *)
and meta_var = MetaVar of int

(* bound or defined *)
and bd = Bound | Defined [@@deriving show { with_path = false }]

(* Pp aux *)
let index_of_level (Lvl l : level) (Lvl x : level) : index = Ix (l - x - 1) [@@inline]
let next_level (Lvl l) : level = Lvl (l + 1) [@@inline]
let int_of_level (Lvl l) = l [@@inline]
let int_of_index (Ix i) = i [@@inline]
