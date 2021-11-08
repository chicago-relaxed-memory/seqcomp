PAPER=paper
paper:
	rm  -f ${PAPER}.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error ${PAPER}.tex
	killall Skim
appendix:
	rm  -f appendix.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error appendix.tex
	killall Skim
diff:
	git latexdiff --main ${PAPER}.tex 89c1d7b06 --
talk:
	rm  -f talk.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error talk.tex
	killall Skim
clean:
	latexmk -c

publish:
	cp main.pdf ${HOME}/Public/papers/.pdf && cp talk.pdf ${HOME}/Public/papers/talk.pdf && (cd ${HOME}/Public; make)

ZIP=${HOME}/1seq/main.zip
DIR=/tmp
SRC=main
DST=main_arXiv
# https://github.com/google-research/arxiv-latex-cleaner/
zip:
	rm -f ${ZIP}
	rm -rf ${DIR}/${SRC} ${DIR}/${DST}
	mkdir ${DIR}/${SRC}
	cp ${PAPER}.tex bib.bib ACM-Reference-Format.bst abstract.tex c11.tex definitions.tex fig-addr.tex fig-ca-addr.tex fig-ca.tex fig-def.tex fig-pwter.tex fig-seq.tex intro.tex mca1.tex mca2.tex outro.tex related.tex results.tex tool.tex variants.tex ${DIR}/${SRC}
	cp macros.sty ${PAPER}.bbl acmart.cls ${DIR}/${SRC}
	bash -c 'cd ${DIR} && arxiv_latex_cleaner --keep_bib ${SRC}'
	bash -c 'cd ${DIR}/${DST} && zip ${ZIP} * && pdflatexn ${PAPER} && open ${PAPER}.pdf && zip ${ZIP} ${PAPER}.pdf'
	grep '\(Error\|Warning\)' ${DIR}/${DST}/${PAPER}.log

#	cp  ${DIR}/${DST}
present:
	presentation.py -p 0 -d 15 talk.pdf 2>/dev/null

## From Mark and Simon:

all:
	pdflatex ${PAPER}
	bibtex ${PAPER}
	pdflatex ${PAPER}
	pdflatex ${PAPER}

zclean:
	rm -f *.log *.out *.aux *.dvi *.bbl *.blg *.fdb_latexmk *.fls *.synctex.gz *.cb *.cb2
	rm -f ${PAPER}.pdf

