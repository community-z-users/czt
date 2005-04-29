#############################################################################
#
# Makefile for $(PROJECT).dvi
#
#############################################################################

#############################################################################
# List of sources

PROJECT		= ifm
BIB		= $(PROJECT).bib
AUX		= $(PROJECT).aux
AUXBAK		= $(AUX).bak 

TEX		= 
STY		= 
FIGEPS		= tc-design.eps
FIGEEPIC	= 
EEPIC           = $(FIGEEPIC:%.fig=%.eepic)
EPS		= $(FIGEPS:%.fig=%.eps) $(EEPIC:%.eepic=%.eps)

TEMPFILES	= $(AUXBAK) $(PROJECT).ps $(PROJECT).blg \
		  *.fig.bak *.log *~ texput.* mfput.*
FIGTMP          = $(EPS)

# Commands

LATEX		= latex
BIBTEX		= bibtex
PREVIEW		= xdvi
FIG2EEPIC       = fig2dev -L eepic -l 0 -W
FIG2EPS         = fig2dev -L eps -l 0
DVI2PS		= dvips -ta4 -X600 -Y600 -Ppdf -G0
EEPIC2EPS       = eepic2eps.tcl
PS2PDF		= ps2pdf -sPAPERSIZE=a4 -dMaxSubsetPct=100 \
                    -dCompatibilityLevel=1.2 -dSubsetFonts=true \
                    -dEmbedAllFonts=true
TCL             = tclsh
TTGZ		= tar czf


#############################################################################
# General Rules

# compile the main file

all:			$(PROJECT).dvi

$(PROJECT).dvi $(PROJECT).bbl:	$(PROJECT).tex $(TEX) $(STY) $(EEPIC)\
			$(EPS) $(BIB)
			-cp $(AUX) $(AUXBAK)
			$(LATEX) $(PROJECT).tex
			$(BIBTEX) $(PROJECT)

new::
			$(LATEX) $(PROJECT).tex 
			$(BIBTEX) $(PROJECT)

twice::			all new

# restore previous .aux file

oldaux::
			cp $(AUXBAK) $(AUX)


# Word counting

wc:			all wordcount

wordcount::
			sed -f wc.sed $(PROJECT).tex | wc


# Packaging

pack:			$(PROJECT).tgz

$(PROJECT).tgz:		$(PROJECT).tex $(TEX) $(STY) $(FIG) \
                        $(PROJECT).bbl Makefile
			tar czf $@ $^


# Translation of figures

.SUFFIXES:
.SUFFIXES:		.dvi .eepic .eps .fig .tex .bib $(SUFFIXES)

.fig.eps:
			$(FIG2EPS) $< $@

.fig.eepic:
			$(FIG2EEPIC) $< $@

.eepic.eps:
			$(TCL) $(EEPIC2EPS) $<

.tex.bib:
			latex $<
			$(BIBTEX) $(<:%.tex=%)


# Further translation from DVI to PostScript and PDF

ps:			$(PROJECT).ps

$(PROJECT).ps:		$(PROJECT).dvi $(PS)
			$(DVI2PS) -o$(PROJECT).ps $(PROJECT).dvi

pdf:			$(PROJECT).pdf

$(PROJECT).pdf:		$(PROJECT).ps
			$(PS2PDF) $< $@


# Viewing and printing

view::			$(PROJECT).dvi $(PS)
			$(PREVIEW) $(PROJECT).dvi &

print::			$(PROJECT).ps
			lpr $(PROJECT).ps


# deleting intermediates

clean::			nolog
			rm -f $(PROJECT).dvi $(PROJECT).ps $(PROJECT).pdf \
                              $(FIGTMP)

nolog::
			rm -f $(TEMPFILES)
