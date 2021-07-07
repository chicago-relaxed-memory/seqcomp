## This is useful for Mark and Simon, but perhaps not the canonical way to build the paper

all:
	pdflatex paper
	bibtex paper
	pdflatex paper
	pdflatex paper

clean:
	rm -f *.log *.out *.aux *.dvi *.bbl *.blg *.fdb_latexmk *.fls *.synctex.gz
	rm -f paper.pdf
