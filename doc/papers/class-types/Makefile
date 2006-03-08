TARGET=main
REFERENCES=bib/*.bib
WORDCOUNT=
FIG=fig/z-types.fig
INCLUDES=*.tex fig/*
BASEFIG=$(subst .fig,,$(FIG))
EPS=$(subst .fig,.eps,$(FIG))
FIG2EPS=fig2dev -L eps -l 0

all: $(TARGET).dvi
pdf: $(TARGET).pdf
ps: $(TARGET).ps
dvi: $(TARGET).dvi

$(TARGET).pdf: $(TARGET).ps
	ps2pdf -dPDFsettings=/prepress $(TARGET).ps $(TARGET).pdf

$(TARGET).ps: $(TARGET).dvi
	dvips -Ppdf -G0 $(TARGET).dvi -o $(TARGET).ps

$(TARGET).dvi: $(TARGET).tex $(INCLUDES) $(BIBLIOGRAPHY) $(FIGURES) $(REFERENCES) $(EPS)
	latex $(TARGET)
	bibtex $(TARGET)
	latex $(TARGET)
	latex $(TARGET)

%.eps: %.fig
	for i in *.fig; do\
		($(FIG2EPS) $< $@);\
	done

clean:
	rm -f *.aux *.log *.toc *.bbl *.blg *.plg *.dvi *.bak *.tex~
	rm -f $(EPS)

CLEAN: clean
	rm -f $(TARGET).dvi
	rm -f $(TARGET).ps
	rm -f $(TARGET).pdf

wc: $(WORDCOUNT)
	wc -w $(WORDCOUNT)
