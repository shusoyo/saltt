type name = string
type index = Ix of int
type level = Lvl of int

let index_of_level (Lvl l : level) (Lvl x : level) : index = Ix (l - x - 1)
let next_level (Lvl l) : level = Lvl (l + 1)

(* Pp aux *)
let pp_index (fmt : Format.formatter) (Ix i : index) : unit = Format.fprintf fmt "Ix %d" i

let pp_level (fmt : Format.formatter) (Lvl l : level) : unit =
  Format.fprintf fmt "Lvl %d" l

let pp_name (fmt : Format.formatter) (n : name) : unit = Format.fprintf fmt "%s" n
let int_of_level (Lvl l) = l [@@inline]
let int_of_index (Ix i) = i [@@inline]
let rec repeat n f acc = if n <= 0 then acc else repeat (n - 1) f (f acc)
