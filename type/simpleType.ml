type simpleType =
  | STTop
  | STBot
  | STFunction of simpleType * simpleType
  | STRecord of (string * simpleType) list
  | Primitive of string
  | STVariable of stv
and stv = {
  mutable _lowerBound: simpleType;
  _uid: int;
  mutable _upperBound: simpleType;
  mutable _representative: stv option;
}

let rec representative(s:stv): stv =
  match s._representative with
  | Some(v) ->
      let rep = representative(v) in
      if rep <> v then s._representative <- Some(rep);
      rep
  | None -> s

let uid(s:stv): int = (representative s)._uid
let lowerBound(v:stv): simpleType = (representative v)._lowerBound
let upperBound(v:stv): simpleType = (representative v)._upperBound
let freshCount = ref 0
let new_stv (l,b):stv = {
  _lowerBound=l;
  _upperBound=b;
  _uid= (let n = !freshCount in incr freshCount; n);
  _representative=None;
}
let fresh_var(): stv = new_stv (STBot,STTop)
let new_stvar(l,t): simpleType = STVariable(new_stv(l,t))
let fresh_stvar(): simpleType = STVariable(fresh_var())

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
  (* 型をトラバースして型変数が pos か neg か判定しsetに追加 *)
  (* pos と neg に分けたほうがサイズが1/2になるので1つのmapより検索効率が2倍速い *)
  let pos = ref TyVarSet.empty in
  let neg = ref TyVarSet.empty in
  let rec analyze((st: simpleType), (pol: bool)): unit =
    match st with
    | STRecord(fs) -> fs|>List.iter(fun (_,v) -> analyze(v, pol))
    | STFunction(l, r) -> analyze(l, not pol); analyze(r, pol)
    | STVariable(v) when pol ->
                       pos:= TyVarSet.add v !pos; analyze(lowerBound v, pol)
    | STVariable(v) -> neg:= TyVarSet.add v !neg; analyze(upperBound v, pol)
    | _ -> ()
  in
  analyze(st, true);
  let mapping = TyVarTbl.create 16 in
  let add v st = TyVarTbl.add mapping v st; st in
  let rec go((vl: bool), (st: simpleType), (pol: bool)): simpleType =
    match vl, st with
    | true, STVariable v when TyVarTbl.mem mapping v-> TyVarTbl.find mapping v
    | true, STVariable v when lowerBound v = upperBound v
                           || pol && not (TyVarSet.mem v !neg) ->
        add v (go(false, lowerBound v, pol))
    | true, STVariable v when not pol && not (TyVarSet.mem v !pos) ->
        add v (go(false, upperBound v, pol))
    | true, STVariable v -> add v (new_stvar(go(false, lowerBound v, true),
                                             go(false, upperBound v, false)))
    | _, STRecord(fs) -> STRecord(fs|>List.map(fun (k,v) -> k,go(true, v, pol)))
    | _, STFunction(l, r) -> STFunction(go(true, l, not pol), go(true, r, pol))
    | _, _ -> st
  in
  go(true, st, true)
