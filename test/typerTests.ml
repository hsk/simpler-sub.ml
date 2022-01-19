let doTest(a,b) = true
let error(a,b) = true
let parse(str: string) =
    let lexbuf = Lexing.from_string str in
    Parser.expr Lexer.token lexbuf
let doTest(str, expected) =
  try
    let term = parse(str) in
    let tyv = Typer.inferType(term) in
    let res = SimpleType.simplifyType(tyv) in
    let res = Ty.show(SimpleType.coalesceType(res)) in
    if res<>expected then Printf.printf "test error %s" res;
    res=expected
  with Failure msg ->
    if expected<>"" && msg<>expected then Printf.printf "test error %s" msg;
    expected="" || msg=expected
  | Parser.MenhirBasics.Error ->
    expected=""

let error(str, msg) = doTest(str, msg)

let basic =
  assert(doTest("42", "int"));
  assert(doTest("fun x -> 42", "⊤ -> int"));
  assert(doTest("fun x -> x", "'a -> 'a"));
  assert(doTest("fun x -> x 42", "(int -> 'a) -> 'a"));
  assert(doTest("(fun x -> x) 42", "int"));
  assert(doTest("fun f -> fun x -> f (f x)", "('a -> 'a) -> 'a -> 'a"));
  assert(doTest("let twice = fun f -> fun x -> f (f x) in twice", "('a -> 'a) -> 'a -> 'a"))

let booleans =
  assert(doTest("true", "bool"));
  assert(doTest("not true", "bool"));
  assert(doTest("fun x -> not x", "bool -> bool"));
  assert(doTest("(fun x -> not x) true", "bool"));
  assert(doTest("fun x -> fun y -> fun z -> if x then y else z",
    "bool -> 'a -> 'a -> 'a"));
  assert(doTest("fun x -> fun y -> if x then y else x",
    "'a ∧ bool -> 'a ∧ bool -> 'a"));
  assert(doTest("fun x -> { u = not x; v = x }", "'a ∧ bool -> {u: bool, v: 'a}"));
  assert(error("succ true",
    "cannot constrain bool <: int"));
  assert(error("fun x -> succ (not x)",
    "cannot constrain bool <: int"));
  assert(error("(fun x -> not x.f) { f = 123 }",
    "cannot constrain int <: bool"));
  assert(error("(fun f -> fun x -> not (f x.u)) false",
    "cannot constrain bool <: 'a -> 'b"))

let records =
  assert(doTest("fun x -> x.f", "{f: 'a} -> 'a"));
  assert(doTest("{}", "{}"));
  assert(doTest("{ f = 42 }", "{f: int}"));
  assert(doTest("{ f = 42 }.f", "int"));
  assert(doTest("(fun x -> x.f) { f = 42 }", "int"));
  assert(doTest("fun f -> { x = f 42 }.x", "(int -> 'a) -> 'a"));
  assert(doTest("fun f -> { x = f 42; y = 123 }.y", "(int -> ⊤) -> int"));
  assert(doTest("if true then { a = 1; b = true } else { b = false; c = 42 }", "{b: bool}"));
  assert(doTest("if true then { u = 1; v = 2; w = 3 } else { u = true; v = 4; x = 5 }", "{u: ⊤, v: int}"));
  assert(doTest("if true then fun x -> { u = 1; v = x } else fun y -> { u = y; v = y }", "'a -> {u: 'a ∨ int, v: 'a ∨ int}"));
  assert(error("{ a = 123; b = true }.c",
    "missing field: c in {a: int, b: bool}"));
  assert(error("fun x -> { a = x }.b",
    "missing field: b in {a: 'a}"))
let self_app =
  assert(error("fun x -> x x", ""));
  
  assert(error("fun x -> x x x", ""));
  assert(error("fun x -> fun y -> x y x",""));
  assert(error("fun x -> fun y -> x x y",""));
  assert(error("(fun x -> x x) (fun x -> x x)",""));
  assert(error("fun x -> {l = x x; r = x }",""));
  assert(error("(fun f -> (fun x -> f (x x)) (fun x -> f (x x)))",""));
  assert(error("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v)))",""));
  assert(error("(fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v))) (fun f -> fun x -> f)",""));
  assert(error("let rec trutru = fun g -> trutru (g true) in trutru",""));
  assert(error("fun i -> if ((i i) true) then true else true",""));
  ()

let let_poly =
  assert(doTest("let f = fun x -> x in {a = f 0; b = f true}", "{a: ⊤, b: ⊤}"));
  assert(doTest("fun y -> let f = fun x -> x in {a = f y; b = f true}",
    "'a -> {a: 'a ∨ bool, b: 'a ∨ bool}"));
  assert(doTest("fun y -> let f = fun x -> y x in {a = f 0; b = f true}",
    "(⊤ -> 'a) -> {a: 'a, b: 'a}"));
  assert(doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> true)}",
    "'a -> {a: 'a ∨ bool, b: 'a ∨ bool}"));
  assert(doTest("fun y -> let f = fun x -> x y in {a = f (fun z -> z); b = f (fun z -> succ z)}",
    "int -> {a: int, b: int}"));
  assert(error("(fun k -> k (fun x -> let tmp = add x 1 in x)) (fun f -> f true)",
    "cannot constrain bool <: int"));
  assert(error("(fun k -> let test = k (fun x -> let tmp = add x 1 in x) in test) (fun f -> f true)",
    "cannot constrain bool <: int"))

let recursion =
  assert(error("let rec f = fun x -> f x.u in f",""));
  assert(error("let rec consume = fun strm -> add strm.head (consume strm.tail) in consume",""));
  assert(error("let rec r = fun a -> r in if true then r else r",""));
  assert(error("let rec l = fun a -> l in let rec r = fun a -> fun a -> r in if true then l else r",""));
  assert(error("let rec l = fun a -> fun a -> fun a -> l in let rec r = fun a -> fun a -> r in if true then l else r",""));
  assert(error("let rec recursive_monster = fun x -> { thing = x; self = recursive_monster x } in recursive_monster",""))

let random =
  assert(error("(let rec x = {a = x; b = x} in x)", ""));
  assert(error("(let rec x = fun v -> {a = x v; b = x v} in x)", ""));
  assert(error("let rec x = (let rec y = {u = y; v = (x y)} in 0) in 0", ""));
  assert(error("(fun x -> (let y = (x x) in 0))", ""));
  assert(error("(let rec x = (fun y -> (y (x x))) in x)", ""));
  assert(doTest("fun next -> 0",                                               "⊤ -> int"));
  assert(error("((fun x -> (x x)) (fun x -> x))", ""));
  assert(error("(let rec x = (fun y -> (x (y y))) in x)", ""));
  assert(error("fun x -> (fun y -> (x (y y)))", ""));
  assert(error("(let rec x = (let y = (x x) in (fun z -> z)) in x)", ""));
  assert(error("(let rec x = (fun y -> (let z = (x x) in y)) in x)", ""));
  assert(error("(let rec x = (fun y -> {u = y; v = (x x)}) in x)", ""));
  assert(error("(let rec x = (fun y -> {u = (x x); v = y}) in x)", ""));
  assert(error("(let rec x = (fun y -> (let z = (y x) in y)) in x)", ""));
  assert(doTest("(fun x -> (let y = (x x.v) in 0))",                           "⊥ -> int"));
  assert(error("let rec x = (let y = (x x) in (fun z -> z)) in (x (fun y -> y.u))", ""))

let occurs_check =
  assert(error("fun x -> x.u x", ""));
  assert(error("fun x -> x.u {v=x}", ""));
  assert(doTest("fun x -> x.u x.v", "{u: 'a -> 'b, v: 'a} -> 'b"));
  assert(error("fun x -> x.u.v x", ""))
