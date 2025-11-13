#!/bin/bash

everything="everything.agda"
echo "module everything where" > $everything
echo "" >> $everything

find . -type f \
  \( -name '*.agda' -mindepth 2 \) \
  -print0 | sort -z | while read -d $'\0' file
do
  module=$(echo "$file" | sed -e "s|./||" -e 's|\.agda$||' -e 's|/|.|g')
  echo "import ${module}" >> $everything
done
