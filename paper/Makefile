paper:
	rm  -f paper.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error paper.tex
	killall Skim
diff:
	git latexdiff --main paper.tex HEAD --
main:
	rm  -f main.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error main.tex
	killall Skim
appendix:
	rm  -f appendix.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error appendix.tex
	killall Skim
talk:
	rm  -f talk.pdf
	latexmk -xelatex --pvc --pdf --halt-on-error talk.tex
	killall Skim
clean:
	latexmk -c

publish:
	cp main.pdf ${HOME}/Public/papers/.pdf && cp talk.pdf ${HOME}/Public/papers/talk.pdf && (cd ${HOME}/Public; make)

zip:
	zip main.zip abstract.tex paper.tex intro.tex 
	rm -rf /tmp/main; mkdir /tmp/main; 
	bash -c 'cd /tmp/main; unzip ~/1mm/main.zip; pdflatexn paper'

present:
	presentation.py -p 0 -d 15 talk.pdf 2>/dev/null
