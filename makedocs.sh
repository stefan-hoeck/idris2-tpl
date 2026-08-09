#!/usr/bin/env bash

pack install-app katla-typst
pack typecheck tpl

cp -v doc/main.typ pdf/main.typ
cp -v doc/template.typ pdf/template.typ

katla-typst src/TPL/BoolExp/Term.typ build/ttc/*/TPL/BoolExp/Term.ttm > pdf/bool_term.typ
katla-typst src/TPL/BoolExp/Parser.typ build/ttc/*/TPL/BoolExp/Parser.ttm > pdf/bool_parser.typ

typst c pdf/main.typ pdf/doc.pdf
