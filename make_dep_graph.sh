#!/bin/sh

# Purpose: generate dependent graph from _CoqProject by coqdep and dot.
# Remark:
# 1. genemrate dot file need "coqdep -dumpgraph" command, but this option is removed
# after coq 8.12. How to install an old version coq?
# (1) Query ocaml version from "https://ocaml.org/p/coq/8.10.0"
# (2) Install special version
# opam switch create 4.08.0
# eval $(opam env)
# opam pin add coq 8.10.0
# 2. The manual of dot is: https://www.graphviz.org/pdf/dotguide.pdf

project_file=_CoqProject
name=doc/dep_graph
dot_file=${name}.dot
pdf_file=${name}.pdf
png_file=${name}.png

# Generate "dot" file with module dependencies
# `coqdep` is a standard utility distributed with Coq system
coqdep -f ${project_file} -dumpgraph ${dot_file} > /dev/null

# Modify node style in dot file: add backcolor, add URL
sed -i -E 's/"([^"]+)"\[label="([^"]+)"\]/"\1"[label="\2"\
	, style=filled, fillcolor=lightblue \
	, URL="\1.html"]/g' ${dot_file}

# Generate a pdf with toposorted graph from the dot file
# `dot` utility is distributed with graphviz utility collection
# One can usually install it using a package manager like homebrew on macOS:
#    brew install graphviz
dot -Tpdf ${dot_file} -o ${pdf_file}
dot -Tpng ${dot_file} -o ${png_file}
rm ${dot_file}
