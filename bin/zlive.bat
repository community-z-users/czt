@echo off
call "%~f0\..\settings.bat"
java -enableassertions -classpath "%ZLIVE%;%RULES%;%SESSION%;%TYPECHECKER%;%PARSER%;%GAFFE%;%COREJAVA%;%JAVA_CUP%;%JWSDP%" net.sourceforge.czt.animation.eval.TextUI %1 %2 %3 %4 %5 %6 %7 %8 %9
