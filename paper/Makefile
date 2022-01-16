PAPER=paper
paper:
	rm  -f ${PAPER}.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error ${PAPER}.tex
	killall Skim
draft:
	pdflatexn ${PAPER}
	cp ${PAPER}.pdf DRAFT.pdf
	cp ${PAPER}.pdf ~/Public/papers/2022-popl.pdf
	pdflatexn combo
	cp combo.pdf DRAFT-APPENDIX.pdf
appendix:
	rm  -f appendix.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error appendix.tex
	killall Skim
diff:
	git latexdiff --main ${PAPER}.tex 89c1d7b06 --

TALK=talk
talk:
	rm  -f ${TALK}.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error ${TALK}.tex
	killall Skim
pngs:
	rm -f ~/Desktop/page-[0-9][0-9].png
	open -a "PDF Save Pages as Images" ${TALK}.pdf
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

