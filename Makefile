main:
	ocamlbuild -use-ocamlfind -pkg num src/InvarGenT.native
	cp _build/src/InvarGenT.native invargent

test:
	ocamlbuild -use-ocamlfind -pkg num -pkg ounit2 src/Tests.d.byte --

testnative:
	ocamlbuild -use-ocamlfind -pkg num -pkg ounit2 src/Tests.native --

docs:
	ocamlbuild src/InvarGenT.docdir/index.html
	rm -f -R doc/code
	mv _build/src/InvarGenT.docdir doc/code
	texmacs -c doc/invargent-article.tm doc/invargent.pdf -q
	texmacs -c doc/invargent-manual-article.tm doc/invargent-manual.pdf -q

.PHONY: clean

clean:
	ocamlbuild -clean
	rm -f src/*.annot *~ src/*~ InvarGenT src/a.out
	rm -f examples/*.ml examples/*.cmi examples/*.cmo examples/*.gadti
	cd src; ocamlbuild -clean
