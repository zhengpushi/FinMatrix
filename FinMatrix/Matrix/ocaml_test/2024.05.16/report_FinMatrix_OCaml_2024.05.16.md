
# Performance of OCaml program of FinMatrix by extraction
date: 2024.05.16
 
## Introduction
This is a test for ocaml program of FinMatrix by Coq extraction, which contain matrix multiplication, inversion by GE and inversion by AM.
We use randomly generated matrices of floating point numbers.
The source code are located in [Here](https://github.com/zhengpushi/FinMatrix/tree/main/FinMatrix/Matrix/ocaml_test)

## Environment
PC: Thinkbook 14 G2-ITL
OS: Debian 12.5

## Usage
* there are two version programs
  `./matrix.byte`, byte-code version
  `./matrix.opt`, opt version
* options
  -n=10, size of input matrix
  -mmul=true, enable multiplication
  -GE=true, enable matrix inversion by GE
  -AM=true, enable matrix inversion by AM
* examples
  * opt version, matrix multiplication with two 100*100 matrices
	`./matrix.opt -mmul=true -n=10`
  * byte-code version, matrix inversion by GE with one 5*5 matrix
	`./matrix.byte -GE=true -n=5`
  * opt-code version, matrix inversion by AM with one 5*5 matrix
	`./matrix.byte -AM=true -n=5`

## Result
* matrix multiplication: `A(float,n,n) * B(float,n,n)`
  time ./matrix.byte -mmul=true -n=64
  time ./matrix.opt -mmul=true -n=64
  ```
  n    time(s)-byte  time(s)-OPT
  64   0.047         0.033
  128  0.264         0.086
  256  1.814         0.387
  512  13.869        2.654
  1024               22.215
  ```
  time = O(n^3)

* matrix inversion by GE `invGE (A(float,n,n))`
  time ./matrix.byte -GE=true -n=5
  time ./matrix.opt -GE=true -n=5
  ```
  n    time(s)-byte  time(s)-OPT
  5    0.006         0.003
  6    0.009         0.005
  7    0.017         0.008
  8    0.075         0.020
  9    0.329         0.075
  10   1.537         0.341
  11   7.163         1.638
  12                 7.322
  ```

* matrix inversion by AM `invAM (A(float,n,n))`
  time ./matrix.byte -AM=true -n=5
  time ./matrix.opt -AM=true -n=5
  ```
  n    time(s)-byte  time(s)-OPT
  5    0.008         0.004
  6    0.017         0.007
  7    0.101         0.024
  8    0.968         0.187
  9    10.32         2.042
  10                 26.608
  ```

# Conclusion
* The performance of matrix multiplication is same as "Dependent Record by List" model.
* The performance of matrix inversion is too bad, due to the "function" model.

# Future work
* We plan to use a better model, such as axiomized way of "Array.array",
  Note that, this way have strong similarity of FinMatrix, we are doing it...
