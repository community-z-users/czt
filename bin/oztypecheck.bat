@echo off
call "%~f0\..\settings.bat"
java -classpath "%TYPECHECKER%;%SESSION%;%PARSER%;%COREJAVA%;%JWSDP%;%JAVA_CUP%" net.sourceforge.czt.typecheck.oz.TypeCheckUtils %1 %2 %3 %4 %5 %6 %7 %8 %9
