(* Terms *)
type term =
 | Lit of int
 | Var of string
 | Lam of string * term
 | App of term * term
 | Rcd of (string * term) list
 | Sel of term * string
 | Let of bool * string * term * term
type pgrm = (bool * string * term) list
