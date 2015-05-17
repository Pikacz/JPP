all:
	happy -gca Parabc.y
	alex -g Lexabc.x
	ghc --make Testabc.hs -o Testabc
	ghc --make Main.hs -o interpreter

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f Docabc.ps

distclean: clean
	-rm -f Docabc.* Lexabc.* Parabc.* Layoutabc.* Skelabc.* Printabc.* Testabc.* Absabc.* Testabc ErrM.* SharedString.* ComposOp.* abc.dtd XMLabc.* Makefile*
	

