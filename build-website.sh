#!/bin/bash
# This script is meant to be run by Cloudflare Pages to build the website

wget https://github.com/agda/agda/releases/download/v2.7.0.1/Agda-v2.7.0.1-linux.tar.xz -O Agda.tar.xz
tar -xf Agda.tar.xz
export Agda_datadir=$(pwd)/Agda-v2.7.0.1/data
mv Agda-v2.7.0.1/bin/agda . 
chmod +x agda
./agda --version

mkdir ~/.agda/
echo $HOME/.agda/cubical/cubical.agda-lib > ~/.agda/libraries

git clone https://github.com/agda/cubical ~/.agda/cubical
cd ~/.agda/cubical
git checkout v0.6

cd -
chmod +x ./create-everything.sh
./create-everything.sh

./agda --html --html-dir=public index.agda