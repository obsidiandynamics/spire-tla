#!/bin/sh

if [ $# -ne 1 ]; then
  echo "Usage: makepdf.sh <module>"
  exit 1
fi

which pdflatex
if [ $? -eq 1 ]; then
  echo "Application pdflatex is not installed"
  exit 1
fi

module=$1

# To get a list of command line options, run `java -cp  $tools_path tla2tex.TLA -info`

tools_path=~/.vscode/extensions/alygin.vscode-tlaplus-1.5.1/tools/tla2tools.jar
opts=" -number -shade -grayLevel .95"
java -cp  $tools_path tla2tex.TLA $opts $module.tla
java -cp  $tools_path tla2tex.TeX $module.tex
pdflatex -interaction scrollmode $module.tex || echo "Done with exit code $?"