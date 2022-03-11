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
del oz-symbols.dvi
del oz-symbols.pdf
del font-symbols.dvi
del font-symbols.pdf

rem from oz.dtx
latex nfssfont < oz-symbols.in
ren nfssfont.dvi oz-symbols.dvi
del nfssfont.dvi
del nfssfont.log
dvipdfm oz-symbols.dvi

rem from various .map files in LaTeX dist
latex nfssfont < font-symbols.in
ren nfssfont.dvi font-symbols.dvi
del nfssfont.dvi
del nfssfont.log
dvipdfm font-symbols.dvi

@echo on
