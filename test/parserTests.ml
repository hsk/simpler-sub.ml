let doTest(str: string) =
  try
    let lexbuf = Lexing.from_string str in
    let _ = Parser.expr Lexer.token lexbuf in
    true
  with _ -> false
let doError(str) = not (doTest str)
let basics =
    assert (doTest "1");
    assert (doTest "a");
    assert (doTest "1 2 3");
    assert (doTest "a b c");
    assert (doTest "true")
let _let =
    assert (doTest "let a = b in c");
    assert (doTest "let a = 1 in 1");
    assert (doTest "let a = (1) in 1");
    assert (doError "let true = 0 in true")
let records =
    assert (doTest "{ a = 1; b = 2 }");
    assert (doError "{ a = 1; b = 2; a = 3 }")