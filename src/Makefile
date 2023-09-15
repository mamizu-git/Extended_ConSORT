SOURCES = lexer.mll parser.mly syntax.ml tySyntax.ml tyConstraintSolver.ml simpleTyping.ml convert.ml util.ml collectConstraint.ml emit.ml z3Lexer.mll z3Parser.mly z3Syntax.ml CHCcollectConstraint.ml CHCemit.ml z3Lexer2.mll z3Parser2.mly z3Syntax2.ml ownership.ml main.ml
DOC_FILES := $(filter %.ml, $(SOURCES))
DOC_FILES := $(DOC_FILES) parser.ml z3Parser.ml z3Parser2.ml
RESULT  = main

YFLAGS = -v 

all: byte-code byte-code-library

-include OCamlMakefile

