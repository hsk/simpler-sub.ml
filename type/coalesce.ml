open Ty
open SimpleType
let asTV(stv:stv):tv = ("α", uid stv)
let asTypeVar(stv:stv) = TypeVariable(asTV stv)
type polarVariable = stv * bool

(** Convert an inferred SimpleType into the immutable Type representation. *)
let coalesceType (st: simpleType): ty =
  let recursive:((stv * bool)*tv) list ref = ref [] in
  let rec go((st: simpleType), (polarity: bool))(inProcess: polarVariable list): ty =
    match st with
    | STVariable(tv) ->
      let tv_pol = (tv, polarity) in
      if inProcess|>List.mem tv_pol then (
        match !recursive|>List.assoc_opt tv_pol with
        | Some v -> TypeVariable(v)
        | None ->
          let v = asTV (fresh_var ()) in
          recursive := (tv_pol,v)::!recursive;
          TypeVariable(v)
      ) else (
        let bound = if (polarity) then lowerBound(tv) else upperBound(tv) in
        let boundType = go(bound, polarity)(tv_pol::inProcess) in
        let res =
          if (polarity && bound == STBot || bound == STTop) then asTypeVar tv
          else if polarity then Union(asTypeVar tv, boundType)
          else Inter(asTypeVar tv, boundType)
        in
        !recursive|>List.assoc_opt tv_pol|>function None->res | Some((x, i))->RecursiveType((x,i), res)
      )
    | STFunction(l, r) -> FunctionType(go(l, not polarity)(inProcess), go(r, polarity)(inProcess))
    | STRecord(fs) -> RecordType(fs|>List.map(fun (k,v)->(k,go(v, polarity)(inProcess))))
    | Primitive(n) -> PrimitiveType(n)
    | STTop -> PrimitiveType("⊤")
    | STBot -> PrimitiveType("⊥")
  in
  go(st, true)([])

let show_simple_ty(s:simpleType): string = show(coalesceType(s))
