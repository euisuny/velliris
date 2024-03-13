# Velliris Coq development
This repository contains the Coq development of Velliris.

## Setup
This project is known to build with [Coq 8.13.2](https://coq.inria.fr/).
It depends on recent development versions of [std++](https://gitlab.mpi-sws.org/iris/stdpp) and [Iris](https://gitlab.mpi-sws.org/iris/iris), as well as [coq-equations](https://github.com/mattam82/Coq-Equations).


We recommend using [opam](https://opam.ocaml.org/) (version >= 2.0, tested on 2.0.8) for the installation.

Please execute the following instructions in the folder containing this README, replacing `N` with the number of jobs you'd like to use for compilation.
```
opam switch create velliris 4.11.1
opam switch link velliris .
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make -jN builddep
make -jN

```

### Setup for ITree and Vellvm-related dependencies

This branch builds with coq `8.17.0` and ocaml `4.12.0`.

When cloning this directory, use the `--recurse-submodule` flag:
```
git clone --recurse-submodule https://gitlab.mpi-sws.org/iris/velliris
```

Install the `dev` version of the `ITree` library using the following commands
```
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-itree.dev
opam install coq-itree-extra
```

To build the Vellvm dependency, make sure to install all the dependencies of the
Vellvm project as per instructions here: https://github.com/vellvm/vellvm

Note that `coq-flocq` needs to be pinned to `4.1.3`.
N.B. You will need to go under `lib/vellvm/lib/` and `make` each of the
directories.
