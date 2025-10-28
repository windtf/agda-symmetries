#!/bin/bash
# This script is meant to be run by Cloudflare Pages to build the website

wget https://github.com/agda/agda/releases/download/v2.8.0/Agda-v2.8.0-linux.tar.xz
tar -xf Agda-v2.8.0-linux.tar.xz
chmod +x agda

mkdir ~/.agda/
echo $HOME/.agda/cubical/cubical.agda-lib > ~/.agda/libraries

git clone https://github.com/agda/cubical ~/.agda/cubical
cd ~/.agda/cubical
git checkout v0.6

cd -
chmod +x ./create-everything.sh
./create-everything.sh

./agda --html --html-dir=public index.agda