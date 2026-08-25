#import "template.typ": *
#show: template

#include("title.typ")
#include("intro.typ")
#include("parser.typ")

#include("bool_term.typ")
#include("bool_parser.typ")

#include("arith_term.typ")
#include("arith_parser.typ")
#include("arith_tt.typ")
#include("arith_example.typ")

#include("lambda_name.typ")
#include("lambda_scope.typ")
#include("lambda_var.typ")
#include("lambda_env.typ")
#include("lambda_term.typ")
#include("lambda_parser.typ")

#bibliography("bib.yaml")
