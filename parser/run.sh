source ../bin/settings.sh

java -cp $COREJAVA:$JWSDP:$PARSER:$JAVA_CUP -Dczt.lib=$CZT_LIB net.sourceforge.czt.parser.oz.Main $*
