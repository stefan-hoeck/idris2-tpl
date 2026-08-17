#!/usr/bin/env bash

TTC=$(idris2 --ttc-version)
BUILD="build/ttc/$TTC"

mkdir -p pdf

pack install-app katla-typst
pack typecheck tpl

cp -v doc/main.typ pdf/main.typ
cp -v doc/template.typ pdf/template.typ

katla-typst src/TPL/BoolExp/Term.typ "$BUILD"/TPL/BoolExp/Term.ttm >pdf/bool_term.typ
katla-typst src/TPL/BoolExp/Parser.typ "$BUILD"/TPL/BoolExp/Parser.ttm >pdf/bool_parser.typ
katla-typst src/TPL/ArExp/Term.typ "$BUILD"/TPL/ArExp/Term.ttm >pdf/arith_term.typ

typst c pdf/main.typ pdf/doc.pdf
