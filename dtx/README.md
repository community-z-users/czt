# CZT LaTeX

The CZT LaTeX has been developed to ensure correct support of LaTeX symbols no Standard Z and all its extensions. 
Download the following style files and install them to your system to display LaTeX specifications in 
Community Z Tools and IDEs. 

-   [Download **CZT Z** LaTeX style](z/czt.sty)
-   [Download **CZT Circus** LaTeX style](circus/circus.sty)

The _CZT Z_ style is the greatest common denominator of previous known Z style files (e.g. _oz.sty, fuzz.sty, zed.sty, zeves.sty, cadiz.sty, zed-csp.sty_ etc).
These original Z styles had various design decisions, many of which are conflicting, yet necessary to have for Standard Z.
For instance, _fuzz.sty_ was the first and contains important macros yet is not compatible with ISO-Z Standard, and it was
for older versions of LaTeX. _zed.sty_ and _zed-csp.sty_ were an Oxford version that improved on _fuzz.sty_ by adding modern
and Lucida fonts, yet lacked ISO-Z standard features. _oz.sty_ added more support for Unicode symbol correspondence with 
the use of AMS fonts and it was for newer versions of LaTeX and closer to ISO-Z. _zeves.sty_ added support for theorem environments.
Unfortunately, all these styles had some form of incompatibility and needed sorting out. That's what _czt.sty_ is the result of.

## Installing CZT LaTeX

Refer to the documentation of your operating system on installing LaTeX packages.
This usually means adding them to a directory (i.e. /usr/local/tex/localtextmf/latex/) 
where your LaTeX distribution is installed.

## CZT Reference cards

For Z, we have a cheat-sheet available

-   [Download **CZT Z** Reference card](z/zrefcard.pdf)

TODO: one for Circus!

## CZT LaTeX guides

After installing the style files, we can use the LaTeX to compile your specifications. 
To learn how to typeset using Z-LaTeX or Circus-LaTeX, say, please refer to the guides available.

-   [Download **CZT Z** LaTeX guide](z/czt-guide.pdf)
-   [Download **CZT Circus** LaTeX guide](circus/circus-guide.pdf)

You can also inspect how the files themselves were typeset. This can be useful to know
more details about the style file itself.

-   [Download **CZT Z** LaTeX guide source](z/czt-guide.tex)
-   [Download **CZT Z** LaTeX guide bib](z/czt-guide.bib)
-   [Download **CZT Circus** LaTeX guide source](circus/circus-guide.tex)

## Complete specifications example

For Z 

-   [Download **CZT Z** Scheduler specification](z/scheduler.pdf)
-   [Download **CZT Z** Scheduler specification source](z/scheduler.tex)

For Circus

-   [Download **CZT Circus** Buffer refinement specification](circus/buffer-refinement-multienv.pdf)
-   [Download **CZT Circus** Buffer refinement specification source](circus/buffer-refinement-multienv.tex)

