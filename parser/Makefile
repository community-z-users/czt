JAVA = java
JFLEX=jflex
CUP=$(JAVA) java_cup.Main <

all: src/net/sourceforge/czt/scanner/UnicodeLexer.java src/net/sourceforge/czt/scanner/LatexLexer.java

src/net/sourceforge/czt/scanner/UnicodeLexer.java: src/net/sourceforge/czt/scanner/unicode.jflex
	$(JFLEX) -d src/net/sourceforge/czt/scanner $<

src/net/sourceforge/czt/scanner/LatexLexer.java: src/net/sourceforge/czt/scanner/latex.jflex
	$(JFLEX) -d src/net/sourceforge/czt/scanner $<

clean:
	rm -f src/net/sourceforge/czt/scanner/UnicodeLexer.java
	rm -f src/net/sourceforge/czt/scanner/UnicodeLexer.java~
	rm -f src/net/sourceforge/czt/scanner/LatexLexer.java
	rm -f src/net/sourceforge/czt/scanner/LatexLexer.java~
