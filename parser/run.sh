source ../bin/settings.sh

java -cp $COREJAVA:$JWSDP:$PARSER:$JAVA_CUP net.sourceforge.czt.parser.oz.Main $*
