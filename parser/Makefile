JFLEX=jflex
CUP=$(JAVA) java_cup.Main <

XALAN_LIBS = $(XALAN_HOME)/bin
XALAN_CP = $(XALAN_LIBS)/xalan.jar:$(XALAN_LIBS)/xml-apis.jar:$(XALAN_LIBS)/xercesImpl.jar

XALAN = -Xbootclasspath/p:$(XALAN_CP)

run: tests/scanner/Main.class
	java -classpath build:tests/scanner Main tests/scanner/bbook.utf8

tests/scanner/Main.class: tests/scanner/Main.java
	javac -classpath build tests/scanner/Main.java

build/src/net/sourceforge/czt/scanner/Lexer.class build/src/net/sourceforge/czt/parser.class: src/net/sourceforge/czt/scanner/Lexer.java src/net/sourceforge/czt/scanner/parser.java
	javac -d build src/net/sourceforge/czt/scanner/*.java

src/net/sourceforge/czt/scanner/Lexer.java: src/net/sourceforge/czt/scanner/unicode.jflex
	$(JFLEX) -d src/net/sourceforge/czt/scanner $<

src/net/sourceforge/czt/scanner/parser.java: src/net/sourceforge/czt/scanner/parser.cup
	cd src/net/sourceforge/czt/scanner; $(CUP) parser.cup

src/net/sourceforge/czt/scanner/unicode.jflex: xsl/zchar.xml xsl/unicode_scanner.xsl src/net/sourceforge/czt/scanner
	java $(XALAN) org.apache.xalan.xslt.Process \
			-in $< \
			-xsl xsl/unicode_scanner.xsl \
			-out $@

src/net/sourceforge/czt/scanner/parser.cup: xsl/zchar.xml xsl/cup.xsl src/net/sourceforge/czt/scanner
	java $(XALAN) org.apache.xalan.xslt.Process \
			-in $< \
			-xsl xsl/cup.xsl \
			-out $@

src/net/sourceforge/czt/scanner:
	mkdir src/net/sourceforge/czt/scanner

clean:
	rm -rf src/net/sourceforge/czt/scanner
