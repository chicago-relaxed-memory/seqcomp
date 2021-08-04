paper:
	rm  -f paper.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error paper.tex
	killall Skim
diff:
	git latexdiff --main paper.tex 89c1d7b06 --
z:
	rm  -f z.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error z.tex
	killall Skim
appendix:
	rm  -f appendix.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error appendix.tex
	killall Skim
talk:
	rm  -f talk.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error talk.tex
	killall Skim
zclean:
	latexmk -c

publish:
	cp main.pdf ${HOME}/Public/papers/.pdf && cp talk.pdf ${HOME}/Public/papers/talk.pdf && (cd ${HOME}/Public; make)

zip:
	zip main.zip abstract.tex paper.tex intro.tex 
	rm -rf /tmp/main; mkdir /tmp/main; 
	bash -c 'cd /tmp/main; unzip ~/1mm/main.zip; pdflatexn paper'

present:
	presentation.py -p 0 -d 15 talk.pdf 2>/dev/null

## From Mark and Simon:

all:
	pdflatex paper
	bibtex paper
	pdflatex paper
	pdflatex paper

clean:
	rm -f *.log *.out *.aux *.dvi *.bbl *.blg *.fdb_latexmk *.fls *.synctex.gz
	rm -f paper.pdf
