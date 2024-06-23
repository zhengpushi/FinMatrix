# Copyright 2024 Zhengpu Shi
# This file is part of FinMatrix. It is distributed under the MIT
# "expat license". You should have recieved a LICENSE file with it.

matrix : matrix.byte matrix.opt

# byte-code version
matrix.byte : matrix.ml
	@ocamlc -c matrix.mli
	@ocamlfind ocamlc -o $@ -linkpkg matrix.ml -package unix

# opt version
matrix.opt : matrix.ml
	@ocamlc.opt -c matrix.mli
	@ocamlfind opt -o $@ -linkpkg matrix.ml -package unix

clean :
	rm -f *.cmi *.cmo *.o
	rm -f matrix

.PHONY : clean
