CZTLIB=../../lib/
JAVA_CUP=/usr/java/java_cup/

JWSDP=/usr/java/jwsdp-1.3/

CP=$CZTLIB/corejavaZ.jar:$CZTLIB/corejavaBase.jar:$CZTLIB/corejavaJaxb.jar
CP=$CP:$CZTLIB/corejavaOZ.jar:/usr/java/java_cup

CP=$CP:$JWSDP/jaxb/lib/jaxb-xjc.jar
CP=$CP:$JWSDP/jaxb/lib/jaxb-impl.jar
CP=$CP:$JWSDP/jaxb/lib/jaxb-api.jar
CP=$CP:$JWSDP/jaxb/lib/jaxb-libs.jar
CP=$CP:$JWSDP/jaxp/lib/jaxp-api.jar
CP=$CP:$JWSDP/jaxp/lib/endorsed/xalan.jar
CP=$CP:$JWSDP/jaxp/lib/endorsed/xercesImpl.jar
CP=$CP:$JWSDP/jaxp/lib/endorsed/dom.jar
CP=$CP:$JWSDP/jaxp/lib/endorsed/sax.jar
CP=$CP:$JWSDP/jwsdp-shared/lib/namespace.jar
CP=$CP:$JWSDP/jwsdp-shared/lib/jax-qname.jar
CP=$CP:$JWSDP/jwsdp-shared/lib/relaxngDatatype.jar
CP=$CP:$JWSDP/jwsdp-shared/lib/xsdlib.jar

java -cp $CP:build/ net.sourceforge.czt.parser.oz.Main $*
