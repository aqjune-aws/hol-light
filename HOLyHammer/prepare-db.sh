#!/bin/bash

if [ ! -d "$HOLLIGHT_DIR" ]; then
  echo "Environment variable HOLLIGHT_DIR is not set."
  echo "Please do 'export HOLLIGHT_DIR=<the path to your hol-light>"
  exit 1
fi

if [ "$#" -ne 1 ]; then
  echo "prepare-db.sh <HOL Light command you want to run without double semicolons (e.g., 'loadt \"Library/words.ml\"')>"
  exit 1
fi

cd ${HOLLIGHT_DIR}

echo "---- Calling write_symbols_theorems () ----"

(echo "$1;;";
 echo 'loadt "update_database.ml";;';
 echo '#use "HOLyHammer/hh_symbols.ml";;';
 echo 'write_symbols_theorems ();;') | hol.sh

echo "---- Building HOL Light with the fusion.diff patch applied ----"

patch < HOLyHammer/fusion.diff
eval $(opam env --set-switch)
export HOLLIGHT_USE_MODULE=1
make

echo "---- Running hol.sh to collect proofs ----"

(echo "$1;;") | hol.sh

echo "---- Building dep ----"

(cd HOLyHammer; ocamlopt str.cmxa dep.ml -o dep; ./dep)

echo "---- Checking out the original fusion.ml ----"

git checkout -- fusion.ml
export HOLLIGHT_USE_MODULE=1
make
