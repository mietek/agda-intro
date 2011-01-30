default : dtp.dvi

dtp.tex : dtp.lagda VecFin.lagda Lambda.lagda View.lagda
	lhs2Tex --agda dtp.lagda > dtp.tex

dtp.aux : dtp.tex
	latex dtp

dtp.blg : dtp.aux
	bibtex dtp

dtp.dvi : dtp.tex dtp.blg
	latex dtp
	latex dtp

dtp.pdf : dtp.tex dtp.blg
	latex dtp
	pdflatex dtp
