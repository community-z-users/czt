TARGET=main
REFERENCES=bib/*.bib
WORDCOUNT=
FIG=fig/z-types.fig
INCLUDES=*.tex fig/*
BASEFIG=$(subst .fig,,$(FIG))
EPS=$(subst .fig,.eps,$(FIG))

all: $(TARGET).dvi
pdf: $(TARGET).pdf
ps: $(TARGET).ps
dvi: $(TARGET).dvi

$(TARGET).pdf: $(TARGET).ps
	ps2pdf -dPDFsettings=/prepress $(TARGET).ps $(TARGET).pdf

$(TARGET).ps: $(TARGET).dvi
	dvips -o $(TARGET).ps $(TARGET).dvi

$(TARGET).dvi: $(TARGET).tex $(INCLUDES) $(BIBLIOGRAPHY) $(FIGURES) $(REFERENCES) $(EPS)
	latex $(TARGET)
	bibtex $(TARGET)
	latex $(TARGET)
	latex $(TARGET)

%.eps: %.fig
	cd fig;\
	for i in *.fig; do\
		(figtex2eps $$i);\
	done

clean:
	rm -f *.aux *.log *.toc *.bbl *.blg *.plg *.dvi *.bak *.tex~

CLEAN: clean
	rm -f $(TARGET).dvi
	rm -f $(TARGET).ps
	rm -f $(TARGET).pdf

wc: $(WORDCOUNT)
	wc -w $(WORDCOUNT)
