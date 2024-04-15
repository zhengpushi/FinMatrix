#!/bin/sh

# 说明
# 1. coqdep 8.12 开始删除了 -dumpgraph 选项，不知何时恢复，所以暂用旧的版本
# 如何安装旧的coq？
# (1) https://ocaml.org/p/coq/8.10.0 查询某个版本的 ocaml 依赖
# (2) 安装特定版本
# opam switch create 4.08.0
# eval $(opam env)
# opam pin add coq 8.10.0
# 2. dot 是 graphviz 的一部分，解释 dot 语言写的图像
# dot语法的标准在 https://www.graphviz.org/pdf/dotguide.pdf

project_file=../../_CoqProject
name=dependency_graph
dot_file=${name}.dot
pdf_file=${name}.pdf

# Generate "dot" file with module dependencies
# `coqdep` is a standard utility distributed with Coq system
coqdep -f ${project_file} -dumpgraph ${dot_file} > /dev/null

# 修改dot文件，比如为所有的对象增加底色。例如如下：
# "VFCS/CoqExt/StrExt"[label="StrExt"]
# "VFCS/CoqExt/RExt"[label="RExt",style=filled,fillcolor="#8888FF"]

# Generate a pdf with toposorted graph from the dot file
# `dot` utility is distributed with graphviz utility collection
# One can usually install it using a package manager like homebrew on macOS:
#    brew install graphviz
dot -Tpdf ${dot_file} -o ${pdf_file}
