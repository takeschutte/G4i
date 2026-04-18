# G4i

Attempted formalisation of cut and contraction admissibility for the first-order Intuitionistic Sequent Calculus G4i presented in [Admissibility of Structural Rules for Contraction-Free Systems
of Intuitionistic Logic](http://www.jstor.org/stable/2695061) using code from [Formalized Uniform Interpolation](https://github.com/hferee/UIML/tree/main).

## Documentation

See [Releases](https://github.com/takeschutte/G4i/releases/download/v0.0.0/docs.pdf) for documentation.

## Dependencies

Currently the only dependency is:

* [`Rocq-std++`](https://gitlab.mpi-sws.org/iris/stdpp) - An extended "Standard Library" for Rocq.

To install this run:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stdpp
```

## Building

To build run:

```sh
coq_makefile -f _CoqProject -o makefile
make
```
