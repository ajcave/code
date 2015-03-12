all:
	bnfc -ocaml Syntax.bnfc
	ocamlyacc ParSyntax.mly
	ocamllex LexSyntax.mll
	latex DocSyntax.tex; dvips DocSyntax.dvi -o DocSyntax.ps
	ocamlc -o TestSyntax BNFC_Util.ml AbsSyntax.ml SkelSyntax.ml ShowSyntax.ml PrintSyntax.ml ParSyntax.mli ParSyntax.ml LexSyntax.ml IntSyntax.ml Desugar.ml Error.ml Whnf.ml TestSyntax.ml
	ocamlc -g -o Main BNFC_Util.ml AbsSyntax.ml SkelSyntax.ml ShowSyntax.ml PrintSyntax.ml ParSyntax.mli ParSyntax.ml LexSyntax.ml IntSyntax.ml Desugar.ml Error.ml Whnf.ml Value.ml Typecheck.ml Main.ml

clean:
	-rm -f *.log *.aux *.cmi *.cmo *.o *.dvi
	-rm -f DocSyntax.ps

distclean: clean
	-rm -f DocSyntax.* LexSyntax.* ParSyntax.* LayoutSyntax.* SkelSyntax.* PrintSyntax.* ShowSyntax.* TestSyntax.* AbsSyntax.* TestSyntax BNFC_Util.ml Makefile*
