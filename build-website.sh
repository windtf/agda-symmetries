#!/bin/bash
# This script is meant to be run by Cloudflare Pages to build the website

pip install agda

mkdir ~/.agda/
echo $HOME/.agda/cubical/cubical.agda-lib > ~/.agda/libraries

git clone https://github.com/agda/cubical ~/.agda/cubical
cd ~/.agda/cubical
git checkout v0.6

cd -
chmod +x ./create-everything.sh
./create-everything.sh

agda --html --html-dir=public index.agda