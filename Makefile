test:
	menhir typer/parser.mly
	rm typer/parser.mli
	ocamllex typer/lexer.mll
	ocamlc -o simpler-sub-test -I type -I typer \
		type/ty.ml type/simpleType.ml type/coalesce.ml type/simpleTyper.ml typer/syntax.ml typer/parser.ml typer/lexer.ml typer/typer.ml \
		test/parserTests.ml test/typerTests.ml
	rm -rf type/*.cm* typer/*.cm* test/*.cm* typer/parser.ml typer/lexer.ml
	./simpler-sub-test
clean:
	rm -rf type/*.cm* typer/*.cm* test/*.cm* typer/parser.ml typer/lexer.ml simpler-sub-test

.PHONY: test
