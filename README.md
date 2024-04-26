# FinMatrix
Matrix by fin (finite set over nat) in Coq.
* [Project Homepage](https://zhengpushi.github.io/projects/FinMatrix)
* [Source Code in Github](https://github.com/zhengpushi/FinMatrix)

## Introduction
We develop a formal matrix library `FinMatrix` in Coq, which contains : vector and matrix type, all basic vector operations and matrix operations, and lots of properties about them. It is designed polymorphic and hierarchy depended on element type and structure, and is computational supported for Coq to quick evaluate results of vector (or matrix) operations. The core idea and features are following:
* `fin n` type means a finite set with `n` elements. It is defined as `Inductive fin (n : nat) := Fin (i : nat) (H : i < n).`. Thus, `fin 3` type will have only 3 inhabitants `Fin 3 0 _, Fin 3 1 _,, Fin 3 2 _`.
* `vec A n` type means a `n-` dimensional vector over `A`. It is defined as a function `fin n -> A`, where `A` is any type. The Leibniz equal (i.e. built-in "=") could be used for vector equality, which is easier than that use Setoid equal when with general function model. Because the later way have proof burden for equality preservation by any new operation, in order to support rewriting.
* `mat A r c` type means a $r\times c$ matrix over `A` type. It is defined as `vec (vec A c) r`, i.e., a `r` dimensional vector over `vec A c`. This design have many good features:
  * The vector theory is reused.
  * `mat A r c` is $\alpha-conversion$ to `fin r -> fin c -> A`, which made a matrix is just a function from row and column index to element.
  * High rank of vectors is supported with no burden. For example, `vec (vec (vec A n3) n2) n1` is a $n_1\times n_2\times n_3$ "matrix" over `A`.
* The element type is organized by two technologies both `Typeclass` and `Module`. We use `Typeclass` to develop polymorphic theories of vector or matrix, and organized the hierarchy with `monoid`, `ring`, `orderedRing`, `field`, `orderedField`, `normedOrderedField`. We also use `Module` to encapsulate this hierarchy. Thus, usual number fields such as `nat`, `Z`, `Q`, `Qc`, `R` and `C` type could be used easily.
* The main operations or predications of vectors contain: 
  * get/insert/remove elements of vector: `vnth: v.[i], vinsertH, vinsertT, vremoveH, vremoveT`
  * converting between function/list to vector: `v2f, f2v, v2l, l2v`
  * addition: `vadd: v1 + v2`
  * scalar multiplication: `vcmul: c \.* v`
  * dot product: `vdot: <v1, v2>`
  * sum of a vector: `vsum`
  * orthogonal: `vorth: v1 _|_ v2`
  * projection/perpendicular component: `vperp, vproj`
  * collinear: `vcoll: v1 // v2`
  * parallel: `vpara: v1 //+ v2`
  * anti parallel: `vantipara: v1 //- v2`
* The main operations or predications of matrix contain: 
  * get/insert/remove elements/rows/columns of a matrix: `mnth: M.[i].[j], mrow: M.[i], mcol: M&[j]`
  * converting between function/list to matrix: `m2f, f2m, m2l, l2m`
  * addition: `madd: M1 + M2`
  * scalar multiplication: `mcmul: c \.* M`
  * multiplication: `mmul: M1 * M2`
  * left/right multiply vector: `mmulv: M *v a, mvmul: a v* M`
  * transpose: `mtrans: M\T`
  * trace: `mtrace: tr M`
  * determinant: `mdet: |M|`
  * invertible matrix: `minvertible`
  * inversion by gauss elimination: `minvGE: M\-1`
  * inversion by adjoint matrix: `minvAM: M\-1`
  * Orthogonal matrix, SO(n)

## Related works
`FinMatrix` is different with existing works.
* [CoqMatrix](https://github.com/zhengpushi/CoqMatrix/) is a recent formal matrix library which is contain 6 different models, and it is aiming to integration and comparison. This library is a good place for experimenting variety of different models. However, there have not too much rich vector / matrix theories are developed.
* [matrix](https://math-comp.github.io/htmldoc_2_2_0/mathcomp.algebra.matrix.html) in [Mathcomp](https://math-comp.github.io/) is a popular formal matrix library which have rich theories. However, this library also has some drawbacks.
  * There are two kinds of vector, row vector is a $1\times n$ matrix, column vector is a $n\times 1$ matrix. That means, vector is a derived concept from matrix. But our `FinMatrix` library provided a standalone vector type, and related vector theory.
  * High rank matrix is not supported. For example, $n_1\times n_2\times n_3$ matrix is not supoorted.
  * Most of matrix operations are not computational. For example, `Compute` command cannot get a friendly simple result when we want get an element from a constant matrix, and it just return a complicated expression. I guess it is related with its `lock` mechanism which I not very familiar. Another possible reason is due to its complicated hierarchy.
* `nat-index-matrix` is a formal matrix library used in Verified Quantum Computing by Robert Rand. An old website is [University of Maryland](https://www.cs.umd.edu/~rrand/vqc/index.html), and a newer website is [University of Chicago](https://rand.cs.uchicago.edu/vqc/index.html). It uses a simple matrix type definition which is `Definition mat (r c : nat) := nat -> nat -> C`. Here, they use complex number (`C` type) as element type. Another thing is that the matrix equality must be Setoid equal, thus bring many proof burden to enable rewriting. Moreover, because `r` and `c` are dummy type parameters, such that `mat 3 4` and `mat 2 5` could not be distinguished by Coq type system.

## Installation
* From `opam`
  We are happy to announced that `FinMatrix` has been submitted to `Coq-Package Index`
  ```
  opam install coq-finmatrix
  ```
* From source code
  ```
  make
  make install
  ```

## Usage
1. example usage can be found in `./FinMatrix/examples/`
