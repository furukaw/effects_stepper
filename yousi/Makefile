.SUFFIXES: .tex .pdf

all :
	@echo usage: make filename.pdf / make clean

.tex.pdf :
	platex $<
	pbibtex $*
	platex $<
	platex $<
	dvipdfmx $*

clean :
	rm -f *.ps *.bak *.dvi *.aux *.log *.toc *.bbl *.blg *.out *.ptb *.pag

include .depend
