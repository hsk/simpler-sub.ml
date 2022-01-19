open Ty
type simpleType =
  | STTop
  | STBot
  | STFunction of simpleType * simpleType
  | STRecord of (string * simpleType) list
  | Primitive of string
  | STVariable of stv
and stv = {
  (*private*) mutable _lowerBound: simpleType;
  _uid: int;
  (*private*) mutable _upperBound: simpleType;
  (*private*) mutable _representative: stv option;
}

type typeScheme =
  | Poly of simpleType
  | Simple of simpleType

let rec representative(s:stv): stv =
  match s._representative with
  | Some(v) ->
      let rep = representative(v) in
      if rep <> v then s._representative <- Some(rep);
      rep
  | None -> s

let uid(s:stv): int = (representative s)._uid
let rec show_simple_ty = function
  | STTop -> "⊤"
  | STBot -> "⊥"
  | STFunction(l,r) -> Printf.sprintf "(%s,%s)" (show_simple_ty l)  (show_simple_ty r)
  | STRecord(fs) -> fs|>List.map(fun (k,v)->k^": "^show_simple_ty v)
                      |>String.concat ","|> Printf.sprintf"{%s}"
  | Primitive(x) -> x
  | STVariable(stv) -> Printf.sprintf "α%d" (uid stv)

let lowerBound(v:stv): simpleType = (representative v)._lowerBound
let upperBound(v:stv): simpleType = (representative v)._upperBound
let equals((t:simpleType), (s: simpleType)): bool =
  match t,s with
  | STVariable t, STVariable s -> (uid t) = (uid s)
  | _ -> false
let freshCount = ref 0
let new_stv (l,b):stv = {
  _lowerBound=l;
  _upperBound=b;
  _uid= (let n = !freshCount in incr freshCount; n);
  _representative=None;
}
let new_stvar(l,t) = STVariable(new_stv(l,t))
let freshVar(): stv = new_stv (STBot,STTop)
let asTypeVar(stv:stv) = TypeVariable("α", uid stv)
let asTV(stv:stv) = ("α", uid stv)

module STyVar = struct
  type t = stv
  let compare x y = (uid x)-(uid y)
  let equal x y = (uid x)=(uid y)
  let hash t = uid t
end

module TyVarTbl = Hashtbl.Make(STyVar)
module TyVarSet = Set.Make(STyVar)
module TyVarMap = Map.Make(STyVar)

let simplifyType(st: simpleType): simpleType =
  let pos = ref TyVarSet.empty in
  let neg = ref TyVarSet.empty in
  let rec analyze((st: simpleType), (pol: bool)): unit =
    match st with
    | STRecord(fs) -> fs|>List.iter(fun (_,v) -> analyze(v, pol))
    | STFunction(l, r) -> analyze(l, not pol); analyze(r, pol)
    | STVariable(v) ->
      if pol then pos:= TyVarSet.add v !pos else neg:= TyVarSet.add v !neg;
      analyze((if pol then lowerBound v else upperBound v), pol)
    | _ -> ()
  in
  analyze(st, true);
  let mapping = TyVarTbl.create 16 in
  let rec transformConcrete((st: simpleType), (pol: bool)): simpleType =
    match st with
    | STRecord(fs) -> STRecord(fs|>List.map(fun (k,v) -> k,transform(v, pol)))
    | STFunction(l, r) -> STFunction(transform(l, not pol), transform(r, pol))
    | _ -> st
  and transform((st: simpleType), (pol: bool)): simpleType = match st with
    | STVariable(v) ->
      begin match TyVarTbl.find_opt mapping v with
      | Some v -> v
      | None ->
        let st =
          if lowerBound v = upperBound v then transformConcrete(lowerBound v, pol)
          else if pol && not (!neg|>TyVarSet.mem v) then transformConcrete(lowerBound v, pol)
          else if not pol && not (!pos|>TyVarSet.mem v) then transformConcrete(upperBound v, pol)
          else new_stvar(transformConcrete(lowerBound v, true),
                        transformConcrete(upperBound v, false))
        in
        TyVarTbl.add mapping v st;
        st
      end
    | c -> transformConcrete(c, pol)
  in
  transform(st, true)

type polarVariable = stv * bool

(** Convert an inferred SimpleType into the immutable Type representation. *)
let coalesceType (st: simpleType): ty =
  let recursive:((stv * bool)*tv) list ref = ref [] in
  let rec go((st: simpleType), (polarity: bool))(inProcess: polarVariable list): ty =
    match st with
    | STVariable(tv) ->
      let tv_pol = (tv, polarity) in
      if inProcess|>List.mem tv_pol then
        begin match !recursive|>List.assoc_opt tv_pol with
        | Some v -> TypeVariable(v)
        | None ->
          let v = asTV (freshVar ()) in
          recursive := (tv_pol,v)::!recursive;
          TypeVariable(v)
        end
      else (
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

let children(s:simpleType): simpleType list =
  match s with
  | STVariable(stv) -> [lowerBound stv; upperBound stv]
  | STFunction(l, r) -> [l; r]
  | STRecord(fs) -> fs |> List.map snd
  | _ -> []

let show(s:simpleType): string = show(coalesceType(s))
