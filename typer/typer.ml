open SimpleTyper

let dbg: bool ref = ref false

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
    let v = fresh_stvar() in
    Poly(STFunction(boolType, STFunction(v, STFunction(v, v))))
  ])

let builtinsSize = builtins|>StringMap.cardinal
(** Infer the type of a term. *)
let rec typeTerm(term: Syntax.term)(ctx: ctx): simpleType =
  match term with
  | Var(name) when not(StringMap.mem name ctx) ->
    failwith("identifier not found: " ^ name)
  | Var(name) -> instantiate(StringMap.find name ctx)
  | Lam(name, body) ->
    let param = fresh_stvar() in
    let body_ty = typeTerm body (StringMap.add name (Simple param) ctx) in
    STFunction(param, body_ty)
  | App(f, a) ->
    let f_ty = typeTerm f ctx in
    let a_ty = typeTerm a ctx in
    let res = fresh_stvar() in
    subtype(f_ty, STFunction(a_ty, res));
    res
  | Lit(n) ->
    intType
  | Sel(obj, name) ->
    let obj_ty = typeTerm obj ctx in
    let res = fresh_stvar() in
    subtype(obj_ty, STRecord([name, res]));
    res
  | Rcd(fs) ->
    STRecord(fs |> List.map (fun (n, t) -> n, typeTerm t ctx))
  | Let(true, nme, rhs, bod) when StringMap.cardinal ctx > builtinsSize ->
    failwith("Unsupported: local recursive let binding")
  | Let(true, nme, rhs, bod) ->
    let n_ty = typeLetRhs(true, nme, rhs) ctx in
    typeTerm(bod)(ctx |> StringMap.add nme n_ty)
  | Let(false, nme, rhs, bod) ->
    typeTerm(App(Lam(nme, bod), rhs))(ctx)

(** Infer the type of a let binding right-hand side. *)
and typeLetRhs((isrec: bool), (nme: string), (rhs: Syntax.term))(ctx: ctx): typeScheme =
  match isrec with
  | true ->
    let e_ty = fresh_stvar() in
    let ty = typeTerm rhs (StringMap.add nme (Simple e_ty) ctx) in
    subtype(ty, e_ty);
    Poly(e_ty)
  | false -> Poly(typeTerm rhs ctx)

let inferType ?(ctx: ctx = builtins) (term: Syntax.term): simpleType =
  typeTerm term ctx

(** The main type inference function *)
let rec inferTypes ?(ctx: ctx = builtins) (pgrm: Syntax.pgrm): (string, typeScheme) Either.t list =
  let (l, _) = List.fold_left (fun (ls,ctx) (isrec, nme, rhs) ->
    try
      let v = typeLetRhs(isrec, nme, rhs) ctx in
      (Either.Right v::ls, StringMap.add nme v ctx)
    with Failure err ->
      (Either.Left err::ls, StringMap.add nme (Simple(fresh_stvar())) ctx)
  ) ([], ctx) pgrm in
  List.rev l
