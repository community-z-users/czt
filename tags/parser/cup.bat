call ..\bin\settings.bat

set BatchPath=%~f0\..
cd %BatchPath%\build\src\net\sourceforge\czt\parser\z
java -classpath "%JAVA_CUP%" java_cup.Main -parser Parser -symbols Sym Parser.cup
cd %BatchPath%\build\src\net\sourceforge\czt\parser\oz
java -classpath "%JAVA_CUP%" java_cup.Main -parser Parser -symbols Sym Parser.cup
cd %BatchPath%\src\net\sourceforge\czt\scanner
java -classpath "%JAVA_CUP%" java_cup.Main -parser Unicode2Latex -symbols Sym unicode2latex.cup

cd %BatchPath%
