//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2003.12.24 at 11:29:45 NZDT 
//


package net.sourceforge.czt.oz.jaxb.gen.impl;

public class ClassParaElementImpl
    extends net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl
    implements net.sourceforge.czt.oz.jaxb.gen.ClassParaElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.oz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.oz.jaxb.gen.ClassParaElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/object-z";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "ClassPara";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/object-z", "ClassPara");
        super.serializeURIs(context);
        context.endNamespaceDecls();
        super.serializeAttributes(context);
        context.endAttributes();
        super.serializeBody(context);
        context.endElement();
    }

    public void serializeAttributes(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
    }

    public void serializeURIs(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.oz.jaxb.gen.ClassParaElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\'\u00beTTp"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\'\u00beTIppsq\u0000~\u0000\u0007%N\u00e8Tppsq\u0000~\u0000\u0007 1\u00b1\u00f4ppsq\u0000~\u0000\u0007\u001c\u0010<\u001appsq\u0000~\u0000\u0007\u0017N\u008a:ppsq\u0000~"
+"\u0000\u0007\u0012\u00e54]ppsq\u0000~\u0000\u0007\r\u00fa\u00d2\u00e3ppsq\u0000~\u0000\u0007\t\u00ec\u00ba\u00a5ppsq\u0000~\u0000\u0007\u0006]\u00e7appsr\u0000\u001dcom.sun.msv."
+"grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0003I\u00a3\u00a5ppsq\u0000~\u0000\u0000\u0003I\u00a3\u009asr\u0000\u0011java.l"
+"ang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0003I\u00a3\u008fppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000"
+"sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0001"
+"/\u00b0\u00bbq\u0000~\u0000\u0016psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003e"
+"xpq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0001/\u00b0\u00b8q\u0000~\u0000\u0016psr\u00002com.sun.msv.gram"
+"mar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000"
+"\u0015\u0001q\u0000~\u0000 sr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dco"
+"m.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gram"
+"mar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000!q\u0000"
+"~\u0000&sr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tloca"
+"lNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000(xq\u0000~\u0000#t\u0000-net.s"
+"ourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.c"
+"om/jaxb/xjc/dummy-elementssq\u0000~\u0000\u0012\u0002\u0019\u00f2\u00b9ppsq\u0000~\u0000\u001d\u0002\u0019\u00f2\u00aeq\u0000~\u0000\u0016psr\u0000\u001bco"
+"m.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/dat"
+"atype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/Str"
+"ingPair;xq\u0000~\u0000\u0004\u0000\u00fa9\u00e7ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnames"
+"paceUriq\u0000~\u0000(L\u0000\btypeNameq\u0000~\u0000(L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/dat"
+"atype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3.org/2001/XM"
+"LSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.WhiteSpaceProces"
+"sor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteSpa"
+"ceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$N"
+"ullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\nq\u0000~\u0000\u0016psr\u0000\u001bcom.sun.msv.u"
+"til.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000(L\u0000\fnamespaceURIq\u0000~"
+"\u0000(xpq\u0000~\u00009q\u0000~\u00008sq\u0000~\u0000\'t\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSche"
+"ma-instanceq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/z"
+"mlq\u0000~\u0000&sq\u0000~\u0000\u0000\u0003\u0014C\u00b7pp\u0000sq\u0000~\u0000\u0007\u0003\u0014C\u00acppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000"
+"~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000\'net.sou"
+"rceforge.czt.z.jaxb.gen.DeclNameq\u0000~\u0000+sq\u0000~\u0000\u0012\u0001\u00e4\u0092\u00d6ppsq\u0000~\u0000\u001d\u0001\u00e4\u0092\u00cbq"
+"\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u0004Namet\u0000#http://czt.so"
+"urceforge.net/object-zsq\u0000~\u0000\u0012\u0003\u008e\u00d3?ppsq\u0000~\u0000\u0012\u0003\u008e\u00d34q\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001/\u00b0\u00d1"
+"q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000"
+"$q\u0000~\u0000&sq\u0000~\u0000\'t\u00007net.sourceforge.czt.oz.jaxb.gen.FormalParamet"
+"ersElementq\u0000~\u0000+sq\u0000~\u0000\u0000\u0002_\"aq\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0002_\"Vppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000"
+"~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~"
+"\u0000\'t\u00000net.sourceforge.czt.oz.jaxb.gen.FormalParametersq\u0000~\u0000+sq"
+"\u0000~\u0000\u0012\u0001/q\u0080ppsq\u0000~\u0000\u001d\u0001/quq\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000"
+"\u0010FormalParametersq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0004\u000e\u00189ppsq\u0000~\u0000\u0000\u0004\u000e\u0018.q\u0000~\u0000\u0016p\u0000sq\u0000~"
+"\u0000\u0007\u0004\u000e\u0018#ppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q"
+"\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000.net.sourceforge.czt.oz.jaxb.gen"
+".StringListTypeq\u0000~\u0000+sq\u0000~\u0000\u0012\u0002\u00degMppsq\u0000~\u0000\u001d\u0002\u00degBq\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q"
+"\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u000eVisibilityListq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0004\u00eaaupps"
+"q\u0000~\u0000\u001a\u0004\u00eaajq\u0000~\u0000\u0016psq\u0000~\u0000\u0012\u0004\u00eaagq\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001/\u00b0\u00d1q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6pp"
+"sq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u00005net."
+"sourceforge.czt.oz.jaxb.gen.InheritedClassElementq\u0000~\u0000+sq\u0000~\u0000\u0000"
+"\u0003\u00ba\u00b0\u0094q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0003\u00ba\u00b0\u0089ppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000"
+"~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000.net.sourceforge."
+"czt.oz.jaxb.gen.InheritedClassq\u0000~\u0000+sq\u0000~\u0000\u0012\u0002\u008a\u00ff\u00b3ppsq\u0000~\u0000\u001d\u0002\u008a\u00ff\u00a8q\u0000~"
+"\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u000eInheritedClassq\u0000~\u0000Tq\u0000~"
+"\u0000&sq\u0000~\u0000\u0012\u0004iU\u00d8ppsq\u0000~\u0000\u0012\u0004iU\u00cdq\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001/\u00b0\u00d1q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6pps"
+"q\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000/net.s"
+"ourceforge.czt.oz.jaxb.gen.LocalDefElementq\u0000~\u0000+sq\u0000~\u0000\u0000\u00039\u00a4\u00faq\u0000~"
+"\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u00039\u00a4\u00efppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000"
+"~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000(net.sourceforge.czt.oz."
+"jaxb.gen.LocalDefq\u0000~\u0000+sq\u0000~\u0000\u0012\u0002\t\u00f4\u0019ppsq\u0000~\u0000\u001d\u0002\t\u00f4\u000eq\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000"
+"\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\bLocalDefq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0004\u00c1\u00b1\u00dbppsq\u0000~\u0000"
+"\u0012\u0004\u00c1\u00b1\u00d0q\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001/\u00b0\u00d1q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~"
+"\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000,net.sourceforge.czt.oz.j"
+"axb.gen.StateElementq\u0000~\u0000+sq\u0000~\u0000\u0000\u0003\u0092\u0000\u00fdq\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0003\u0092\u0000\u00f2ppsq\u0000~\u0000\u0000"
+"\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000"
+"$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000%net.sourceforge.czt.oz.jaxb.gen.Stateq\u0000~\u0000+sq\u0000"
+"~\u0000\u0012\u0002bP\u001cppsq\u0000~\u0000\u001d\u0002bP\u0011q\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u0005"
+"Stateq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0004!u\u00d5ppsq\u0000~\u0000\u0012\u0004!u\u00caq\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001/\u00b0\u00d1q\u0000~\u0000\u0016p\u0000"
+"sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&s"
+"q\u0000~\u0000\'t\u00003net.sourceforge.czt.oz.jaxb.gen.InitialStateElementq"
+"\u0000~\u0000+sq\u0000~\u0000\u0000\u0002\u00f1\u00c4\u00f7q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0002\u00f1\u00c4\u00ecppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq"
+"\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000,net.so"
+"urceforge.czt.oz.jaxb.gen.InitialStateq\u0000~\u0000+sq\u0000~\u0000\u0012\u0001\u00c2\u0014\u0016ppsq\u0000~\u0000"
+"\u001d\u0001\u00c2\u0014\u000bq\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\fInitialStateq\u0000"
+"~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0005\u001d6[ppsq\u0000~\u0000\u001a\u0005\u001d6Pq\u0000~\u0000\u0016psq\u0000~\u0000\u0012\u0005\u001d6Mq\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001/"
+"\u00b0\u00d1q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000"
+"~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u00000net.sourceforge.czt.oz.jaxb.gen.OperationEl"
+"ementq\u0000~\u0000+sq\u0000~\u0000\u0000\u0003\u00ed\u0085zq\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0003\u00ed\u0085oppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u0012\u0001/"
+"\u00b0\u00c6ppsq\u0000~\u0000\u001a\u0001/\u00b0\u00bbq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001/\u00b0\u00b8q\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000)"
+"net.sourceforge.czt.oz.jaxb.gen.Operationq\u0000~\u0000+sq\u0000~\u0000\u0012\u0002\u00bd\u00d4\u0099ppsq"
+"\u0000~\u0000\u001d\u0002\u00bd\u00d4\u008eq\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\tOperationq\u0000"
+"~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0002ok\u00f0ppsq\u0000~\u0000\u001d\u0002ok\u00e5q\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~"
+"\u0000&sq\u0000~\u0000\'t\u0000\tClassParaq\u0000~\u0000Tsr\u0000\"com.sun.msv.grammar.ExpressionP"
+"ool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionP"
+"ool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$Clos"
+"edHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000\u00e9[\u0000\u0005tablet"
+"\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000J\u0000\u0000\u0000rpur\u0000![Lcom.sun."
+"msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0001\u007fppppppppq\u0000~\u0000\u00d7pppq\u0000~\u0000"
+"\u00b3pppppppppq\u0000~\u0000\u000eppppppppppppq\u0000~\u0000\u00e3ppq\u0000~\u0000^pq\u0000~\u0000\u008fq\u0000~\u0000\u0082pppppppppq"
+"\u0000~\u0000\u008eppppq\u0000~\u0000\u00c4q\u0000~\u0000\u00bcq\u0000~\u0000\u00afq\u0000~\u0000\u00a7q\u0000~\u0000\u009aq\u0000~\u0000\u0092q\u0000~\u0000\u0085q\u0000~\u0000}q\u0000~\u0000oq\u0000~\u0000aq\u0000"
+"~\u0000Yq\u0000~\u0000\u00c3q\u0000~\u0000\u00bbq\u0000~\u0000\u00aeq\u0000~\u0000\u00a6q\u0000~\u0000\u0099q\u0000~\u0000\u0091q\u0000~\u0000\u0084q\u0000~\u0000|q\u0000~\u0000nq\u0000~\u0000`q\u0000~\u0000Xq\u0000"
+"~\u0000\rq\u0000~\u0000Jq\u0000~\u0000\u0019q\u0000~\u0000Kq\u0000~\u0000\u001cq\u0000~\u0000\u00c1q\u0000~\u0000\u000bq\u0000~\u0000\u00d2q\u0000~\u0000\u00d1q\u0000~\u0000\u00daq\u0000~\u0000\u00d9ppppppq"
+"\u0000~\u0000\u00acpppq\u0000~\u0000\u00cfppq\u0000~\u0000\u00ceppppppppppq\u0000~\u0000\u00cdpppppppppppppppq\u0000~\u0000Vpq\u0000~\u0000z"
+"ppq\u0000~\u0000ypppppq\u0000~\u0000Uppppq\u0000~\u0000xppppppppq\u0000~\u0000\u00b9ppppppppppq\u0000~\u0000\u00b8pppppp"
+"ppq\u0000~\u0000sppppppppppq\u0000~\u0000\nq\u0000~\u0000\u00a4q\u0000~\u0000Opppppppppq\u0000~\u0000\u00a3ppppq\u0000~\u0000,ppppp"
+"pq\u0000~\u0000\u0011pppppppppppppppq\u0000~\u0000\tpppppppppppppppppppppppq\u0000~\u0000\u009epppppq"
+"\u0000~\u0000\u000fpq\u0000~\u0000lpppppppppppq\u0000~\u0000Hpppppppppq\u0000~\u0000jq\u0000~\u0000\fppppq\u0000~\u0000\u0017pppppp"
+"pppppppppppppppq\u0000~\u0000\u0013q\u0000~\u0000\u00depppppppppppppppppppppppq\u0000~\u0000\u0097pppppq\u0000"
+"~\u0000epq\u0000~\u0000\u0089pppppppppppppq\u0000~\u0000\u0010ppppppppq\u0000~\u0000\u00c8ppppppppppppppppppp"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.oz.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "----");
        }

        protected Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  0 :
                        if (("ClassPara" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  1 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                }
                super.enterElement(___uri, ___local, ___qname, __atts);
                break;
            }
        }

        public void leaveElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  2 :
                        if (("ClassPara" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                }
                super.leaveElement(___uri, ___local, ___qname);
                break;
            }
        }

        public void enterAttribute(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  3 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  1 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                }
                super.enterAttribute(___uri, ___local, ___qname);
                break;
            }
        }

        public void leaveAttribute(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  3 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  1 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                }
                super.leaveAttribute(___uri, ___local, ___qname);
                break;
            }
        }

        public void handleText(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                try {
                    switch (state) {
                        case  3 :
                            revertToParentFromText(value);
                            return ;
                        case  1 :
                            spawnHandlerFromText((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, value);
                            return ;
                    }
                } catch (java.lang.RuntimeException e) {
                    handleUnexpectedTextException(value, e);
                }
                break;
            }
        }

    }

}
