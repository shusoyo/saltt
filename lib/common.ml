type name = string
type index = Ix of int
type level = Lvl of int

let index_of_level (Lvl l : level) (Lvl x : level) : index = Ix (l - x - 1)
let next_level (Lvl l) : level = Lvl (l + 1)
