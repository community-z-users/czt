@echo off
call "%~f0\..\settings.bat"
java -enableassertions -classpath "%SESSION%;%PARSER%;%JAVA_CUP%;%GAFFE%;%COREJAVA%;%JWSDP%;%Z2B%" net.sourceforge.czt.z2b.Main %1 %2 %3 %4 %5 %6 %7 %8 %9
