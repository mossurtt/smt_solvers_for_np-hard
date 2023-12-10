SRC = magisterska.tex
AUX = magisterska

magisterska.pdf: $(SRC)
	lualatex $<
	lualatex $<
	biber $(AUX)
	lualatex $<
	lualatex $<

clean:
	rm -f *~ *.{pdf,log,lof,lol,lot,aux,blg,bbl,bcf,toc,nav,out,snm,xml}

