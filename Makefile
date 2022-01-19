test:
	menhir src/parser.mly
	rm src/parser.mli
	ocamllex src/lexer.mll
	ocamlc -o simpler-sub-test -I src \
		src/syntax.ml src/parser.ml src/lexer.ml src/ty.ml src/simpleType.ml src/typer.ml \
		test/parserTests.ml test/typerTests.ml
	rm -rf src/*.cm* test/*.cm* src/parser.ml src/lexer.ml
	./simpler-sub-test
clean:
	rm -rf src/*.cm* test/*.cm* src/parser.ml src/lexer.ml simpler-sub-test

.PHONY: test
