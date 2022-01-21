open Coalesce
include SimpleType

module StringMap = Map.Make(String)

let occursCheck((v:stv), (ty: simpleType), (dir: string)): unit = 
  let getVars(s:simpleType): TyVarSet.t =
    let res = ref TyVarSet.empty in
    let rec go(t: simpleType): unit = match t with
      | STVariable(tv) when TyVarSet.mem tv !res -> ()
      | STVariable(tv) ->
        res := TyVarSet.add tv !res;
        go (lowerBound tv); go(upperBound tv)
      | STFunction(l, r) -> go l; go r
      | STRecord(fs) -> List.iter (fun (k,v)-> go v) fs
      | _ -> ()
      in
    go(s);
    !res
  in
  if not (TyVarSet.mem (representative v) (getVars ty)) then () else
  let rec showBounds(s:simpleType): string =
    getVars s |> TyVarSet.to_seq|> Seq.filter(fun tv -> upperBound(tv) <> STTop || lowerBound(tv) <> STBot)
      |> List.of_seq |> List.map(fun tv ->
        let lb,ub = lowerBound tv,upperBound tv in
        show_simple_ty (STVariable tv)
          ^ (if lb = STBot then "" else " :> " ^ show_simple_ty lb)
          ^ (if ub = STTop then "" else " <: " ^ show_simple_ty ub)
      )|> String.concat ", "
  in
  let rec show = function
    | STTop -> "⊤"
    | STBot -> "⊥"
    | STFunction(l,r) -> Printf.sprintf "(%s,%s)" (show l)  (show r)
    | STRecord(fs) -> fs|>List.map(fun (k,v)->k^": "^show v)
                        |>String.concat ","|> Printf.sprintf"{%s}"
    | Primitive(x) -> x
    | STVariable(stv) -> Printf.sprintf "α%d" (uid stv)
  in
  let boundsStr = showBounds(ty) in
  failwith (Printf.sprintf "Illegal cyclic constraint: %s %s %s%s"
    (show_simple_ty (STVariable v))
    dir
    (show ty)
    (if boundsStr = "" then "" else "\n\t\twhere: " ^ boundsStr))

(** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. *)
let subtype((lhs: simpleType), (rhs: simpleType)): unit =
  let to_map a = a|>List.to_seq|>StringMap.of_seq in
  let to_list a = a |> StringMap.to_seq |> List.of_seq in
  let union_map f (a, b) =
    StringMap.union (fun _ a b -> Some(f(a, b))) (to_map a) (to_map b) |> to_list
  in
  let intersection_map f (a, b) =
    StringMap.merge (fun _ a b -> match a,b with
      | Some a,Some b -> Some(f(a, b))
      | _,_ -> None
    ) (to_map a) (to_map b) |> to_list
  in
  let rec subtype((lhs: simpleType), (rhs: simpleType)): unit =
    match (lhs, rhs) with
    | lhs,rhs when lhs = rhs -> ()
    | (STBot, _) | (_, STTop) -> ()
    | (STFunction(l0, r0), STFunction(l1, r1)) ->
      subtype(l1, l0); subtype(r0, r1)
    | (STRecord(fs0), STRecord(fs1)) ->
      List.iter (fun (n1, t1) ->
        match List.assoc_opt n1 fs0 with
        | None -> failwith (Printf.sprintf "missing field: %s in %s"
                            n1 (show_simple_ty lhs))
        | Some(t0) -> subtype(t0, t1)
      ) fs1
    | (STVariable(lhs), STVariable(rhs)) -> unifyWith(lhs,rhs)
    | (STVariable(lhs), rhs) -> newUpperBound(lhs,rhs)
    | (lhs, STVariable(rhs)) -> newLowerBound(rhs,lhs)
    | _ -> failwith (Printf.sprintf "cannot constrain %s <: %s"
                    (show_simple_ty lhs) (show_simple_ty rhs))
  and newUpperBound((v:stv), (ub: simpleType)): unit =
    occursCheck(v, ub, "<:");
    let rep = representative v in
    rep._upperBound <- glb true (rep._upperBound, ub);
    subtype(rep._lowerBound, ub)
  and newLowerBound((v:stv), (lb: simpleType)): unit =
    occursCheck(v, lb, ":>");
    let rep = representative v in
    rep._lowerBound <- lub true (rep._lowerBound, lb);
    subtype(lb, rep._upperBound)
  and unifyWith((v:stv), (u: stv)): unit = 
    let rep0 = representative v in
    let rep1 = representative u in
    if rep0 = rep1 then () else (
      (* Note: these is occursCheck calls (and the following ones from addXBound are pretty *)
      (* inefficient as they will incur repeated computation of type variables through getVars: *)
      occursCheck(v, rep1._lowerBound, ":>");
      occursCheck(v, rep1._upperBound, "<:");
      newLowerBound(rep1, rep0._lowerBound);
      newUpperBound(rep1, rep0._upperBound);
      rep0._representative <- Some(rep1);
    )
  and glb con ((lhs: simpleType), (rhs: simpleType)): simpleType =
    match (con, lhs, rhs) with
    | (false, STVariable(v0), STVariable(v1)) -> unifyWith(v0,v1); rhs
    | (false, c0, STVariable(v1)) -> newUpperBound(v1,c0); rhs
    | (false, STVariable(v0), c1) -> newUpperBound(v0,c1); lhs
    | (_,STTop, _) -> rhs
    | (_,_, STTop) -> lhs
    | (_,STFunction(l0, r0), STFunction(l1, r1)) -> STFunction(lub false (l0, l1), glb false(r0, r1))
    | (_,STRecord(fs0), STRecord(fs1)) -> STRecord(union_map (glb false) (fs0, fs1))
    | (_,Primitive(n0), Primitive(n1)) when n0 = n1 -> Primitive(n0)
    | _,_,_ -> STBot
  and lub con ((lhs: simpleType), (rhs: simpleType)): simpleType =
    match (con, lhs, rhs) with
    | (false, STVariable(v0), STVariable(v1)) -> unifyWith(v0,v1); rhs
    | (false, c0, STVariable(v1)) -> newLowerBound(v1,c0); rhs
    | (false, STVariable(v0), c1) -> newLowerBound(v0,c1); lhs
    | (_, STBot, _) -> rhs
    | (_, _, STBot) -> lhs
    | (_, STFunction(l0, r0), STFunction(l1, r1)) -> STFunction(glb false(l0, l1), lub false (r0, r1))
    | (_, STRecord(fs0), STRecord(fs1)) -> STRecord(intersection_map (lub false) (fs0,fs1))
    | (_, Primitive(n0), Primitive(n1)) when n0 = n1 -> Primitive(n0)
    | _ -> STTop
  in
  subtype (lhs,rhs)

type typeScheme =
  | Poly of simpleType
  | Simple of simpleType

let instantiate(ts:typeScheme): simpleType =
  match ts with
  | Simple(st) -> st
  | Poly(body) ->
    let res = ref TyVarMap.empty in
    let rec go = function
      | false, STVariable(tv) when TyVarMap.mem tv !res -> TyVarMap.find tv !res
      | false, STVariable(tv) ->
        let v = new_stvar(go(true,lowerBound tv), go(true, upperBound tv)) in
        res := TyVarMap.add tv v !res;
        v
      | _,STFunction(l, r) -> STFunction(go(false, l), go(false, r))
      | _,STRecord(fs) -> STRecord(fs|>List.map(fun(k,v) -> (k,go(false, v))))
      | _,ty -> ty
    in
    go(false, body)
