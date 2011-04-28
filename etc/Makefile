
all: tct.tex tct.hs tct.pdf tct clean
tct.tex: tct.lhs
	lhs2TeX --poly -o tct.tex tct.lhs

tct.pdf: tct.tex
	pdflatex tct.tex
	pdflatex tct.tex

tct.hs: tct.lhs
	lhs2TeX --code -o tct.hs tct.lhs

tct: tct.hs
	ghc tct.hs -o tct

clean:
	rm -f *.log
	rm -f *.aux
	rm -f *.ptb
	rm -f *.toc
	rm -f *.hi
	rm -f *.o
	rm -f *.out

distclean: clean
	rm -f tct.pdf
	rm -f tct.tex
	rm -f tct.hs