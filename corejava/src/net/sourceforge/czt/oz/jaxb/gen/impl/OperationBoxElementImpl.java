//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.07.01 at 10:48:15 NZST 
//


package net.sourceforge.czt.oz.jaxb.gen.impl;

public class OperationBoxElementImpl
    extends net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl
    implements net.sourceforge.czt.oz.jaxb.gen.OperationBoxElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.oz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.oz.jaxb.gen.OperationBoxElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/object-z";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "OperationBox";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/object-z", "OperationBox");
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
        return (net.sourceforge.czt.oz.jaxb.gen.OperationBoxElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\u0004Z\\\u00cfp"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\u0004Z\\\u00c4ppsq\u0000~\u0000\u0007\u0002cF\u0000ppsq\u0000~\u0000\u0007\u0001\u00df\u00dc\u0010ppsq\u0000~\u0000\u0007\u0001\u00c8\u00ab2ppsr\u0000\u001dcom.sun.msv."
+"grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0000\u00e5\u0000\u00aeppsq\u0000~\u0000\u0000\u0000\u00e5\u0000\u00a3sr\u0000\u0011java.l"
+"ang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0000\u00e5\u0000\u0098ppsq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edpp\u0000"
+"sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0000"
+"\u0007\u00ba\u00d7q\u0000~\u0000\u0011psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003e"
+"xpq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011psr\u00002com.sun.msv.gram"
+"mar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000"
+"\u0010\u0001q\u0000~\u0000\u001bsr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dco"
+"m.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gram"
+"mar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001cq\u0000"
+"~\u0000!sr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tloca"
+"lNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000#xq\u0000~\u0000\u001et\u0000-net.s"
+"ourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.c"
+"om/jaxb/xjc/dummy-elementssq\u0000~\u0000\r\u0000\u00ddE\u00a6ppsq\u0000~\u0000\u0018\u0000\u00ddE\u009bq\u0000~\u0000\u0011psr\u0000\u001bco"
+"m.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/dat"
+"atype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/Str"
+"ingPair;xq\u0000~\u0000\u0004\u0000\f\u00bf\u00a2ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnames"
+"paceUriq\u0000~\u0000#L\u0000\btypeNameq\u0000~\u0000#L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/dat"
+"atype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3.org/2001/XM"
+"LSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.WhiteSpaceProces"
+"sor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteSpa"
+"ceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$N"
+"ullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\nq\u0000~\u0000\u0011psr\u0000\u001bcom.sun.msv.u"
+"til.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000#L\u0000\fnamespaceURIq\u0000~"
+"\u0000#xpq\u0000~\u00004q\u0000~\u00003sq\u0000~\u0000\"t\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSche"
+"ma-instanceq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/z"
+"mlq\u0000~\u0000!sq\u0000~\u0000\r\u0000\u00e3\u00aa\u007fppsq\u0000~\u0000\u0000\u0000\u00e3\u00aatq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\u0007\u0000\u00e3\u00aaippsq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edpp"
+"\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!"
+"sq\u0000~\u0000\"t\u0000+net.sourceforge.czt.oz.jaxb.gen.RefNameListq\u0000~\u0000&sq\u0000"
+"~\u0000\r\u0000\u00db\u00efwppsq\u0000~\u0000\u0018\u0000\u00db\u00eflq\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\"q\u0000~\u0000=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\t"
+"DeltaListt\u0000#http://czt.sourceforge.net/object-zq\u0000~\u0000!sq\u0000~\u0000\r\u0000\u0017"
+"0\u00d9ppsq\u0000~\u0000\u0015\u0000\u00170\u00ceq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000\u00170\u00cbq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000\u000fu\u00dcq\u0000~\u0000\u0011psq\u0000~\u0000\u0000\u0000\u0007"
+"\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000"
+"~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.net.sourceforge.czt.z.jaxb.gen.InclDeclElem"
+"entq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000"
+"\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb."
+"gen.VarDeclElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007"
+"\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000/net.sourcefo"
+"rge.czt.z.jaxb.gen.ConstDeclElementq\u0000~\u0000&q\u0000~\u0000!sq\u0000~\u0000\r\u0000\u0083i\u00ebppsq\u0000"
+"~\u0000\u0015\u0000\u0083i\u00e0q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000\u0083i\u00ddq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000{\u00ae\u00eeq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000s\u00f3\u00ffq\u0000~\u0000\u0011"
+"psq\u0000~\u0000\r\u0000l9\u0010q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000d~!q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000\\\u00c32q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000U\bCq"
+"\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000MMTq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000E\u0092eq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000=\u00d7vq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000"
+"6\u001c\u0087q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000.a\u0098q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000&\u00a6\u00a9q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000\u001e\u00eb\u00baq\u0000~\u0000\u0011psq\u0000"
+"~\u0000\r\u0000\u00170\u00cbq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000\u000fu\u00dcq\u0000~\u0000\u0011psq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq"
+"\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.so"
+"urceforge.czt.z.jaxb.gen.Exists1Predq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq"
+"\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000"
+"~\u0000\"t\u0000.net.sourceforge.czt.z.jaxb.gen.ExprPredElementq\u0000~\u0000&sq\u0000"
+"~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000"
+"~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb.gen.NegPred"
+"Elementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000"
+"~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.j"
+"axb.gen.QntPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~"
+"\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00003net.sour"
+"ceforge.czt.zpatt.jaxb.gen.JokerPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000"
+"~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq"
+"\u0000~\u0000!sq\u0000~\u0000\"t\u0000+net.sourceforge.czt.z.jaxb.gen.Pred2Elementq\u0000~\u0000"
+"&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000"
+"\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sourceforge.czt.z.jaxb.gen.Fac"
+"tElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq"
+"\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sourceforge.czt.z."
+"jaxb.gen.ImpliesPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015"
+"\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000(net.source"
+"forge.czt.z.jaxb.gen.FalsePredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007"
+"\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00007"
+"net.sourceforge.czt.oz.jaxb.gen.PromotedInitPredElementq\u0000~\u0000&"
+"sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011"
+"pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourceforge.czt.z.jaxb.gen.Exis"
+"tsPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~"
+"\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.ja"
+"xb.gen.MemPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000"
+"\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourc"
+"eforge.czt.z.jaxb.gen.AndPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq"
+"\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000"
+"~\u0000\"t\u0000&net.sourceforge.czt.z.jaxb.gen.IffPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq"
+"\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001f"
+"q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\'net.sourceforge.czt.z.jaxb.gen.TruePredq\u0000~\u0000&sq"
+"\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq"
+"\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourceforge.czt.z.jaxb.gen.Forall"
+"Predq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u0007\u00ba\u00edq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000\u0007\u00ba\u00e2ppsq\u0000~\u0000\u0015\u0000\u0007\u00ba\u00d7q\u0000~\u0000\u0011psq\u0000~\u0000\u0018"
+"\u0000\u0007\u00ba\u00d4q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000%net.sourceforge.czt.z.jaxb"
+".gen.OrPredq\u0000~\u0000&q\u0000~\u0000!sq\u0000~\u0000\r\u0001\u00f7\u0016\u00bfppsq\u0000~\u0000\u0018\u0001\u00f7\u0016\u00b4q\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\""
+"q\u0000~\u0000=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\fOperationBoxq\u0000~\u0000Psr\u0000\"com.sun.msv.gra"
+"mmar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/gra"
+"mmar/ExpressionPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.Exp"
+"ressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006pare"
+"ntq\u0000~\u0000\u00e5[\u0000\u0005tablet\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000M\u0000\u0000\u0000"
+"rpur\u0000![Lcom.sun.msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0001\u007fq\u0000~\u0000"
+"kppppppppppppppppppppppppq\u0000~\u0000opppq\u0000~\u0000\tpppppppppppq\u0000~\u0000\u0012pppppp"
+"ppq\u0000~\u0000sppppppppppppq\u0000~\u0000\u000epppppppppppq\u0000~\u0000wq\u0000~\u0000Spq\u0000~\u0000Rppppppppp"
+"pq\u0000~\u0000Qppppppppppppq\u0000~\u0000lppppppppppppppppppppppppq\u0000~\u0000ppppppppp"
+"ppppq\u0000~\u0000\'pppppppq\u0000~\u0000\nq\u0000~\u0000Dppq\u0000~\u0000tppppppppppppppppppq\u0000~\u0000Bpppp"
+"pq\u0000~\u0000xq\u0000~\u0000Tq\u0000~\u0000ippq\u0000~\u0000hppppppppppq\u0000~\u0000gppppppppppq\u0000~\u0000mppppppp"
+"pppppppppppppppppq\u0000~\u0000qpppppppppq\u0000~\u0000\fppppppppq\u0000~\u0000Kpppppq\u0000~\u0000up"
+"pq\u0000~\u0000\u00bdq\u0000~\u0000\u00b7q\u0000~\u0000\u00b1q\u0000~\u0000\u00abq\u0000~\u0000\u00a5q\u0000~\u0000\u009fq\u0000~\u0000\u0099q\u0000~\u0000\u0093q\u0000~\u0000\u008dq\u0000~\u0000\u0087q\u0000~\u0000\u0081q\u0000~\u0000"
+"\u00bcq\u0000~\u0000\u00b6q\u0000~\u0000\u00b0q\u0000~\u0000\u00aaq\u0000~\u0000\u00a4q\u0000~\u0000\u009eq\u0000~\u0000\u0098q\u0000~\u0000\u0092q\u0000~\u0000\u008cq\u0000~\u0000\u0086q\u0000~\u0000\u0080q\u0000~\u0000zq\u0000~\u0000"
+"bq\u0000~\u0000\\q\u0000~\u0000Vq\u0000~\u0000Fq\u0000~\u0000\u0014q\u0000~\u0000{q\u0000~\u0000cq\u0000~\u0000]q\u0000~\u0000Wq\u0000~\u0000Gq\u0000~\u0000\u0017q\u0000~\u0000\u00c3q\u0000~\u0000"
+"\u00c2q\u0000~\u0000\u00c9q\u0000~\u0000\u00c8q\u0000~\u0000\u00cfq\u0000~\u0000\u00ceq\u0000~\u0000\u00d5q\u0000~\u0000\u00d4q\u0000~\u0000jq\u0000~\u0000\u00dbq\u0000~\u0000\u00daq\u0000~\u0000\u00dfpppq\u0000~\u0000np"
+"pppppppppppppppppppppppq\u0000~\u0000rpq\u0000~\u0000\u000bppppppppppppppppppppppq\u0000~\u0000"
+"vpppppppppppppppppppppppppp"));
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
            return net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  0 :
                        if (("OperationBox" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
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
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("DeltaList" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InclDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ConstDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Decl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Decl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Exists1Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExprPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("QntPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("JokerPred" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred2" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Fact" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ImpliesPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("FalsePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("PromotedInitPred" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExistsPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("MemPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IffPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("TruePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ForallPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("OrPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
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
                        if (("OperationBox" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationBoxElementImpl.this).new Unmarshaller(context)), 2, value);
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
