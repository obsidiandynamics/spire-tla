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

java -cp  ~/.vscode/extensions/alygin.vscode-tlaplus-1.5.1/tools/tla2tools.jar tla2tex.TLA $module.tla
java -cp  ~/.vscode/extensions/alygin.vscode-tlaplus-1.5.1/tools/tla2tools.jar tla2tex.TeX $module.tex
pdflatex -interaction scrollmode $module.tex || echo "Done with exit code $?"