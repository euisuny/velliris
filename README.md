# Velliris Coq development
This repository contains the Coq development of Velliris.

## Setup
This project is known to build with [Coq 8.17.0](https://coq.inria.fr/).
For the installation of dependencies, [opam](https://opam.ocaml.org/) (version >= 2.0, tested on 2.1.4) is required.

First, clone this repository using the `--recurse-submodule` flag:
```
git clone --recurse-submodule https://gitlab.mpi-sws.org/iris/velliris
```
(alternatively, if you have already cloned it, run `git submodule update --init --recursive`).

Then, change into the directory containing this README, and run the setup script:
```
./scripts/setup.sh
```
This script sets up a new `opam` switch `velliris`, links it to the current directory, and installs all the dependencies necessary for VellVM, finally compiling VellVM itself.

Finally, compile the Velliris project with `make -jN`, replacing `N` with the number of jobs you'd like to use for compilation.
