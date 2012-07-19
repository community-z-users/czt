@echo off

rem Create the font tables based on font-tables input.
rem Rename the output created to font-tables.dvi.
rem Finally, generate a PDF file as font-tables.pdf.
rem
rem Make sure the first line is a CR+LF for nfssfont to work
rem that is because we need to skip the \currfontname=
rem and go directly to the remainder parameters requested.

del nfssfont.log
del nfssfont.dvi
del font-lucida.dvi
del font-lucida.pdf

rem for yandy installation
rem c:\yandy\YANDYTEX\latex nfssfont.tex < lucida-bright.in

latex nfssfont.tex < lucida-bright.in
ren nfssfont.dvi font-lucida.dvi
ren nfssfont.log font-lucida.log
del nfssfont.dvi

rem c:\yandy\YANDYTEX\dvipdfm font-lucida.dvi
dvipdfm font-lucida.dvi

@echo on
