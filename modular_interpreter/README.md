# Experimental Interpreter for Shadow Semantics

## How to Build and Test

We have built this submission using:
```sh
OCaml 4.14.2
```
Installation of `dune` and `menhir` is needed:
```sh
opam install dune menhir
```
The interpreter can be built with:
```sh
dune build
```
and executed with
```sh
./run -result 10 ./test/addonetwo.l
```

Examples are in the [test](./test) folder.
- Example 1.1 and 1.2 corresponds to [addonetwo](./test/addonetwo.l)
- Example 1.3 and 1.4 corresponds to [sum](./test/sum.l)
- The parity testing function in Section 7 corresponds to [oddeven](./test/oddeven.l)
- Other examples ([mult](./test/mult.l), [stream](./test/stream.l), [recfunctor](./test/recfunctor.l)) illustrate the ability to define recursive functions/data/functors.
