#!/bin/bash

opam switch create velliris --packages=ocaml-variants.4.14.1+options,ocaml-option-flambda
opam switch link velliris .
opam switch velliris
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
# 8.17.1 does not work because of QuickChick
opam pin add coq 8.17.0 $OPAMFLAGS
# this version is required
opam pin add coq-mathcomp-ssreflect 2.0.0 $OPAMFLAGS
#make -C vellvm/src opam
opam install coq-ext-lib coq-paco coq-flocq coq-ceres coq-mathcomp-ssreflect coq-simple-io coq-quickchick ocamlbuild dune menhir qcheck cppo $OPAMFLAGS
opam install coq-itree.dev $OPAMFLAGS
opam install coq-itree-extra $OPAMFLAGS
make builddep
make -C vellvm/src -j
