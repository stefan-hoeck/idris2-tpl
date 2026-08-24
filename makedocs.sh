#!/usr/bin/env bash

TTC=$(idris2 --ttc-version)
BUILD="build/ttc/$TTC"

mkdir -p pdf

pack install-app katla-typst
pack typecheck tpl

cp -v doc/* pdf/

katla-typst src/TPL/Parser/Util.typ "$BUILD"/TPL/Parser/Util.ttm >pdf/parser.typ

katla-typst src/TPL/BoolExp/Term.typ "$BUILD"/TPL/BoolExp/Term.ttm >pdf/bool_term.typ
katla-typst src/TPL/BoolExp/Parser.typ "$BUILD"/TPL/BoolExp/Parser.ttm >pdf/bool_parser.typ

katla-typst src/TPL/ArExp/Term.typ "$BUILD"/TPL/ArExp/Term.ttm >pdf/arith_term.typ
katla-typst src/TPL/ArExp/Parser.typ "$BUILD"/TPL/ArExp/Parser.ttm >pdf/arith_parser.typ
katla-typst src/TPL/ArExp/TT.typ "$BUILD"/TPL/ArExp/TT.ttm >pdf/arith_tt.typ
katla-typst src/TPL/ArExp/Example.typ "$BUILD"/TPL/ArExp/Example.ttm >pdf/arith_example.typ

katla-typst src/TPL/Name.typ "$BUILD"/TPL/Name.ttm >pdf/lambda_name.typ
katla-typst src/TPL/Name/Scope.typ "$BUILD"/TPL/Name/Scope.ttm >pdf/lambda_scope.typ
katla-typst src/TPL/Name/Var.typ "$BUILD"/TPL/Name/Var.ttm >pdf/lambda_var.typ
katla-typst src/TPL/Env.typ "$BUILD"/TPL/Env.ttm >pdf/lambda_env.typ
katla-typst src/TPL/Lambda/Term.typ "$BUILD"/TPL/Lambda/Term.ttm >pdf/lambda_term.typ

typst c pdf/main.typ pdf/doc.pdf
