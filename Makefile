all:
	ocamlbuild src/InvarGenT.native
	cp _build/src/InvarGenT.native InvarGenT

test:
	ocamlbuild src/Tests.d.byte -pkg oUnit --

docs:
	ocamlbuild src/InvarGenT.docdir/index.html
	rm -f doc/code
	mv _build/src/InvarGenT.docdir doc/code
	texmacs -c doc/invargent.tm doc/invargent.pdf -q

.PHONY: clean

clean:
	ocamlbuild -clean
	rm -f src/*.annot *~ src/*~ InvarGenT
	cd src; ocamlbuild -clean