open SimpleType
(** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification (see TypeSimplifier.scala).
 *  In order to turn the resulting CompactType into a simplesub.Type, we use `coalesceCompactType`.
 *)

let dbg: bool ref = ref false
module StringMap = Map.Make(String)
type ctx = typeScheme StringMap.t

let boolType: simpleType = Primitive("bool")
let intType: simpleType = Primitive("int")

let builtins: ctx = StringMap.of_seq (List.to_seq [
  "true", Simple(boolType);
  "false", Simple(boolType);
  "not", Simple(STFunction(boolType, boolType));
  "succ", Simple(STFunction(intType, intType));
  "add", Simple(STFunction(intType, STFunction(intType, intType)));
  "if",
    let v = STVariable(freshVar()) in
    Poly(STFunction(boolType, STFunction(v, STFunction(v, v))))
  ])

let builtinsSize = builtins|>StringMap.cardinal

let getVars(s:simpleType): TyVarSet.t =
  let res = ref TyVarSet.empty in
  let rec go(queue: simpleType list): unit = match queue with
    | STVariable(tv) :: tys ->
      if !res|>TyVarSet.mem tv then go(tys)
      else (res := !res|>TyVarSet.add tv; go((children (STVariable tv)) @ tys))
    | ty :: tys -> go((children ty) @ tys)
    | [] -> ()
  in
  go([s]);
  !res

let rec showBounds(s:simpleType): string =
  getVars s |> TyVarSet.to_seq|> Seq.filter(fun tv -> upperBound(tv) <> STTop || lowerBound(tv) <> STBot)
    |> List.of_seq |> List.map(fun tv ->
      let lb,ub = lowerBound tv,upperBound tv in
      show (STVariable tv)
        ^ (if lb = STBot then "" else " :> " ^ show lb)
        ^ (if ub = STTop then "" else " <: " ^ show ub)
    )|> String.concat ", "

let freshenType(ty: simpleType): simpleType =
  let freshened = ref TyVarMap.empty in
  let rec freshen(ty: simpleType): simpleType = match ty with
    | STVariable(tv) ->
      begin match !freshened |> TyVarMap.find_opt tv with
      | Some(tv) -> tv
      | None ->
        let v = new_stvar(
          freshenConcrete(lowerBound(tv)),
          freshenConcrete(upperBound(tv))) in
        freshened := !freshened |> TyVarMap.add tv v;
        v
      end
    | c -> freshenConcrete(c)
  and freshenConcrete(ty: simpleType): simpleType =
    match ty with
    | STFunction(l, r) -> STFunction(freshen(l), freshen(r))
    | STRecord(fs) -> STRecord(fs|>List.map(fun(k,v) -> (k,freshen v)))
    | _ -> ty
  in
  freshen ty

let instantiate(ts:typeScheme): simpleType =
  match ts with
  | Poly(body) -> freshenType(body)
  | Simple(st) -> st

let occursCheck((v:stv), (ty: simpleType), (dir: bool)): unit = 
  if getVars ty |> TyVarSet.mem (representative v) then
    let boundsStr = showBounds(ty) in
    failwith (Printf.sprintf "Illegal cyclic constraint: %s %s %s%s"
      (show (STVariable v))
      (if dir then "<:" else ":>")
      (show_simple_ty ty)
      (if boundsStr = "" then "" else "\n\t\twhere: " ^ boundsStr))
  else ()

let mergeMap (a, b) f =
  let a = a|>List.to_seq|>StringMap.of_seq in
  let b = b|>List.to_seq|>StringMap.of_seq in
  StringMap.union (fun _ a b -> Some(f(a, b))) a b |> StringMap.to_seq |> List.of_seq

let rec constrain((lhs: simpleType), (rhs: simpleType)): unit =
  (*Typer.trace(s"C $lhs <: $rhs")*)
  match (lhs, rhs) with
  | lhs,rhs when lhs = rhs -> ()
  | (STBot, _) | (_, STTop) -> ()
  | (STFunction(l0, r0), STFunction(l1, r1)) ->
    constrain(l1, l0); constrain(r0, r1)
  | (STRecord(fs0), STRecord(fs1)) ->
    fs1|> List.iter (fun (n1, t1) ->
      match fs0 |> List.assoc_opt n1 with
      | None -> failwith (Printf.sprintf "missing field: %s in %s"
                          n1 (SimpleType.show lhs))
      | Some(t0) -> constrain(t0, t1)
    )
  | (STVariable(lhs), STVariable(rhs)) -> unifyWith(lhs,rhs)
  | (STVariable(lhs), rhs) -> newUpperBound(lhs,rhs)
  | (lhs, STVariable(rhs)) -> newLowerBound(rhs,lhs)
  | _ -> failwith (Printf.sprintf "cannot constrain %s <: %s"
                   (SimpleType.show lhs) (SimpleType.show rhs))
and newUpperBound((v:stv), (ub: simpleType)): unit =
(** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. *)
  occursCheck(v, ub, true);
  let rep = representative(v) in
  rep._upperBound <- glbConcrete(rep._upperBound, ub);
  constrain(rep._lowerBound, ub)
and newLowerBound((v:stv), (lb: simpleType)): unit =
  occursCheck(v, lb, false);
  let rep = representative(v) in
  rep._lowerBound <- lubConcrete(rep._lowerBound, lb);
  constrain(lb, rep._upperBound)
and unifyWith((v:stv), (that: stv)): unit = 
  let rep0 = representative(v) in
  let rep1 = representative(that) in
  if (rep0 <> rep1) then (
    (* Note: these is occursCheck calls (and the following ones from addXBound are pretty *)
    (* inefficient as they will incur repeated computation of type variables through getVars: *)
    occursCheck(v, rep1._lowerBound, false);
    occursCheck(v, rep1._upperBound, true);
    newLowerBound(rep1, rep0._lowerBound);
    newUpperBound(rep1, rep0._upperBound);
    rep0._representative <- Some(rep1);
  ) else ()
and glbConcrete((lhs: simpleType), (rhs: simpleType)): simpleType =
  match (lhs, rhs) with
  | (STTop, _) -> rhs
  | (_, STTop) -> lhs
  | (STBot, _) | (_, STBot) -> STBot
  | (STFunction(l0, r0), STFunction(l1, r1)) -> STFunction(lub(l0, l1), glb(r0, r1))
  | (STRecord(fs0), STRecord(fs1)) -> STRecord(mergeMap(fs0, fs1)(glb))
  | (Primitive(n0), Primitive(n1)) when n0 = n1 -> Primitive(n0)
  | _ -> STBot
and lubConcrete((lhs: simpleType), (rhs: simpleType)): simpleType =
  match (lhs, rhs) with
  | (STBot, _) -> rhs
  | (_, STBot) -> lhs
  | (STTop, _) | (_, STTop) -> STTop
  | (STFunction(l0, r0), STFunction(l1, r1)) -> STFunction(glb(l0, l1), lub(r0, r1))
  | (STRecord(fs0), STRecord(fs1)) ->
    let fs1m = StringMap.of_seq (List.to_seq fs1) in
    STRecord(fs0 |> List.concat_map (fun (n, t0) ->
      match StringMap.find_opt n fs1m with
      | Some(t1) -> [n,lub(t0, t1)] | None -> [] ))
  | (Primitive(n0), Primitive(n1)) when n0 = n1 -> Primitive(n0)
  | _ -> STTop
and glb((lhs: simpleType), (rhs: simpleType)): simpleType =
  match (lhs, rhs) with
  | (STVariable(v0), STVariable(v1)) -> unifyWith(v0,v1); rhs
  | (c0, STVariable(v1)) -> newUpperBound(v1,c0); rhs
  | (STVariable(v0), c1) -> newUpperBound(v0,c1); lhs
  | (c0, c1) -> glbConcrete(c0, c1)
and lub((lhs: simpleType), (rhs: simpleType)): simpleType =
  match (lhs, rhs) with
  | (STVariable(v0), STVariable(v1)) -> unifyWith(v0,v1); rhs
  | (c0, STVariable(v1)) -> newLowerBound(v1,c0); rhs
  | (STVariable(v0), c1) -> newLowerBound(v0,c1); lhs
  | (c0, c1) -> lubConcrete(c0, c1)

(** Infer the type of a term. *)
let rec typeTerm(term: Syntax.term)(ctx: ctx): simpleType =
  match term with
  | Var(name) ->
    begin match ctx|>StringMap.find_opt name with
    | Some(v) -> instantiate(v)
    | None -> failwith("identifier not found: " ^ name)
    end
  | Lam(name, body) ->
    let param = STVariable(freshVar ()) in
    let body_ty = typeTerm(body)(ctx|>StringMap.add name (Simple param)) in
    STFunction(param, body_ty)
  | App(f, a) ->
    let f_ty = typeTerm(f)(ctx) in
    let a_ty = typeTerm(a)(ctx) in
    let res = STVariable(freshVar ()) in
    constrain(f_ty, STFunction(a_ty, res));
    res
  | Lit(n) ->
    intType
  | Sel(obj, name) ->
    let obj_ty = typeTerm obj ctx in
    let res = STVariable(freshVar ()) in
    constrain(obj_ty, STRecord([name, res]));
    res
  | Rcd(fs) ->
    STRecord(fs |> List.map (fun (n, t) -> (n, typeTerm(t)(ctx))))
  | Let(isrec, nme, rhs, bod) ->
    if isrec then
      if (StringMap.cardinal ctx <= builtinsSize) then
        let n_ty = typeLetRhs(isrec, nme, rhs) ctx in
        typeTerm(bod)(ctx |> StringMap.add nme n_ty)
      else failwith("Unsupported: local recursive let binding")
    else typeTerm(App(Lam(nme, bod), rhs))(ctx)
  (*trace(s"T $term")*)
  (* trace (res -> ": " + res) *)

(** Infer the type of a let binding right-hand side. *)
and typeLetRhs((isrec: bool), (nme: string), (rhs: Syntax.term))(ctx: ctx): typeScheme =
  let res = if isrec then ( 
    let e_ty = STVariable(freshVar ()) in
    let ty = typeTerm(rhs)(ctx|>StringMap.add nme (Simple e_ty)) in
    constrain(ty, e_ty);
    e_ty
   ) else typeTerm(rhs)(ctx) in
  Poly(res)

let inferType ?(ctx: ctx = builtins) (term: Syntax.term): simpleType =
  typeTerm(term)(ctx)


(** The main type inference function *)
let rec inferTypes ?(ctx: ctx = builtins) (pgrm: Syntax.pgrm): (string, typeScheme) Either.t list =
  match pgrm with
    | (isrec, nme, rhs) :: defs ->
      let ty_sch = try Either.right(typeLetRhs(isrec, nme, rhs) ctx) with Failure err -> Left(err) in
      let v = match ty_sch|>Either.find_right with Some(v)->v | None ->Simple(STVariable(freshVar())) in
      ty_sch :: inferTypes ~ctx:(ctx|>StringMap.add nme v) defs
    | [] -> []
