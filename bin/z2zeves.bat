@echo off
call "%~f0\..\settings.bat"
set ZEVES="%CZT_HOME%\lib\zeves.jar"
java -enableassertions -classpath "%TYPECHECKER%;%PARSER%;%COREJAVA%;%JWSDP%;%JAVA_CUP%";"%ZEVES%" net.sourceforge.czt.zeves.CZT2ZEves %1 %2 %3 %4 %5 %6 %7 %8 %9
