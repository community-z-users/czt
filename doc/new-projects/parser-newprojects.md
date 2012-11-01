================================================================================
example: creating CircusTime in parser
================================================================================

1) created the parser directory and changed file names accordingly
2) adjusted the code to reflect the "CircusTime" for Circus etc
3) change pom files just like in the corejava case
4) look into parser-src files what to change. this will depend on what your parse does
5) add your production rules within parser-src

PS: this is nowhere near complete and require a lot of work on adding/adjusting 
existing code to cope with the new parser. I've added it to the repository but it's
not part of the build cycle. Neeraj, please attend to it?

ADDED FILES: note that some had to do with cleaning the circus typechecker from circus time as well
corejava/pom.xml
doc/new-projects/corejava-newprojects.txt
doc/new-projects/parser-newprojects.md
parser/parser-circus/src/main/java/net/sourceforge/czt/parser/circus/CircusKeyword.java
parser/parser-circus/src/main/java/net/sourceforge/czt/parser/circus/CircusToken.java
parser/parser-circus/src/main/java/net/sourceforge/czt/print/circus/CircusPrintVisitor.java
parser/parser-circustime/pom.xml
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/CircusTimeKeyword.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/CircusTimeParseError.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/CircusTimeParseMessage.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/CircusTimeParseResources.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/CircusTimeSymMap.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/CircusTimeToken.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/ParserState.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/SpecialLatexParser.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/SpecialLatexScanner.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/WarningManager.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/parser/circustime/WarningMessage.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/AstToPrintTreeVisitor.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/CircusTimePrintMessage.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/CircusTimePrintResources.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/CircusTimePrintVisitor.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/LatexPrinterCommand.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/NewlineScanner.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/PrintUtils.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/TokenSequenceVisitor.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/UnicodePrinter.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/UnicodePrinterCommand.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/WarningManager.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/XmlPrinterCommand.java
parser/parser-circustime/src/main/java/net/sourceforge/czt/print/circustime/ZmlScanner.java
parser/parser-circustime/src/main/resources/lib/circustime_prelude.tex
parser/parser-circustime/src/main/resources/lib/circustime_toolkit.tex
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/AbstractParserTest.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/CyclicParentParserTest.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/ParseErrorLogging.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/ParserFailTest.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/ParserTest.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/ParserUtilsTest.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/SectionManagerCircusTimeParserTest.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/parser/circustime/SimpleCircusTimeFormatter.java
parser/parser-circustime/src/test/java/net/sourceforge/czt/print/circustime/PrintTest.java
parser/parser-circustime/src/test/resources/tests/circustime/README.txt
parser/parser-src/src/main/resources/templates/ContextFreeScanner.xml
parser/parser-src/src/main/resources/templates/KeywordScanner.xml
parser/parser-src/src/main/resources/templates/Parser.xml
parser/parser-src/src/main/resources/templates/Unicode2Latex.xml
parser/pom.xml
typechecker/typechecker-circus/src/main/java/net/sourceforge/czt/typecheck/circus/ActionChecker.java
typechecker/typechecker-circus/src/test/resources/tests/circus/circustime-CircusTimeExprDontUnify.error
typechecker/typechecker-circus/src/test/resources/tests/circus/circustime.tex