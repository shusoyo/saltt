open Common
open Value

let length (env : env) : level = Lvl (List.length env)
let lookup (env : env) (Ix l : index) : value = List.nth env l
let extend_env (env : env) (v : value) : env = v :: env
