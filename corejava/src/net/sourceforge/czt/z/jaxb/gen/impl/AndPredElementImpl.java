//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class AndPredElementImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl
    implements net.sourceforge.czt.z.jaxb.gen.AndPredElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.AndPredElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/zml";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "AndPred";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/zml", "AndPred");
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
        return (net.sourceforge.czt.z.jaxb.gen.AndPredElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\u000b\u00ccR7p"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\u000b\u00ccR,ppsq\u0000~\u0000\u0007\nC\u00c6\u0096ppsq\u0000~\u0000\u0007\u0007\u0015\u00d1\nppsq\u0000~\u0000\u0007\u0004e\u00d5\u0082ppsr\u0000\u001dcom.sun.msv."
+"grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0001\u00b5\u00d9\u00fappsq\u0000~\u0000\u0000\u0001\u00b5\u00d9\u00efsr\u0000\u0011java.l"
+"ang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0001\u00b5\u00d9\u00e4ppsq\u0000~\u0000\u0000\u0000(x3pp\u0000"
+"sq\u0000~\u0000\r\u0000(x(ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0000"
+"(x\u001dq\u0000~\u0000\u0011psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003e"
+"xpq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0000(x\u001aq\u0000~\u0000\u0011psr\u00002com.sun.msv.gram"
+"mar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000"
+"\u0010\u0001q\u0000~\u0000\u001bsr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dco"
+"m.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gram"
+"mar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001cq\u0000"
+"~\u0000!sr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tloca"
+"lNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000#xq\u0000~\u0000\u001et\u0000-net.s"
+"ourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.c"
+"om/jaxb/xjc/dummy-elementssq\u0000~\u0000\r\u0001\u008da\u00acppsq\u0000~\u0000\u0018\u0001\u008da\u00a1q\u0000~\u0000\u0011psr\u0000\u001bco"
+"m.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/dat"
+"atype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/Str"
+"ingPair;xq\u0000~\u0000\u0004\u0001[\u0001,ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000"
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
+"mlq\u0000~\u0000!sq\u0000~\u0000\r\u0002\u00af\u00fb\u0083ppsq\u0000~\u0000\r\u0002\u0087\u0083Nppsq\u0000~\u0000\r\u0002_\u000b\u0019ppsq\u0000~\u0000\r\u00026\u0092\u00e4ppsq\u0000~\u0000"
+"\r\u0002\u000e\u001a\u00afppsq\u0000~\u0000\r\u0001\u00e5\u00a2zppsq\u0000~\u0000\r\u0001\u00bd*Eppsq\u0000~\u0000\r\u0001\u0094\u00b2\u0010ppsq\u0000~\u0000\r\u0001l9\u00dbppsq\u0000~\u0000"
+"\r\u0001C\u00c1\u00a6ppsq\u0000~\u0000\r\u0001\u001bIqppsq\u0000~\u0000\r\u0000\u00f2\u00d1<ppsq\u0000~\u0000\r\u0000\u00caY\u0007ppsq\u0000~\u0000\r\u0000\u00a1\u00e0\u00d2ppsq\u0000~\u0000"
+"\r\u0000yh\u009dppsq\u0000~\u0000\r\u0000P\u00f0hppsq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011p"
+"sq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.net.sourceforge.czt."
+"z.jaxb.gen.ExprPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~"
+"\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sour"
+"ceforge.czt.z.jaxb.gen.ImpliesPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000("
+"x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)"
+"net.sourceforge.czt.z.jaxb.gen.ForallPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000s"
+"q\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq"
+"\u0000~\u0000\"t\u0000*net.sourceforge.czt.z.jaxb.gen.Exists1Predq\u0000~\u0000&sq\u0000~\u0000\u0000"
+"\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000"
+"\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000&net.sourceforge.czt.z.jaxb.gen.IffPredq\u0000~\u0000&sq"
+"\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001b"
+"q\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00007net.sourceforge.czt.oz.jaxb.gen.PromotedI"
+"nitPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011p"
+"sq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt."
+"z.jaxb.gen.MemPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000"
+"\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourc"
+"eforge.czt.z.jaxb.gen.QntPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r"
+"\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t"
+"\u0000+net.sourceforge.czt.z.jaxb.gen.Pred2Elementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3"
+"pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~"
+"\u0000!sq\u0000~\u0000\"t\u0000%net.sourceforge.czt.z.jaxb.gen.OrPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000"
+"(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001f"
+"q\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourceforge.czt.z.jaxb.gen.ExistsPredq\u0000~\u0000&"
+"sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~"
+"\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sourceforge.czt.z.jaxb.gen.FactElem"
+"entq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq"
+"\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00003net.sourceforge.czt.zpatt.jaxb."
+"gen.JokerPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001d"
+"q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\'net.sourceforg"
+"e.czt.z.jaxb.gen.TruePredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000"
+"\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000(net.sourc"
+"eforge.czt.z.jaxb.gen.FalsePredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(p"
+"psq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net"
+".sourceforge.czt.z.jaxb.gen.AndPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000"
+"sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!s"
+"q\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb.gen.NegPredElementq\u0000~\u0000&sq"
+"\u0000~\u0000\r\u0002\u00af\u00fb\u0083ppsq\u0000~\u0000\r\u0002\u0087\u0083Nppsq\u0000~\u0000\r\u0002_\u000b\u0019ppsq\u0000~\u0000\r\u00026\u0092\u00e4ppsq\u0000~\u0000\r\u0002\u000e\u001a\u00afppsq"
+"\u0000~\u0000\r\u0001\u00e5\u00a2zppsq\u0000~\u0000\r\u0001\u00bd*Eppsq\u0000~\u0000\r\u0001\u0094\u00b2\u0010ppsq\u0000~\u0000\r\u0001l9\u00dbppsq\u0000~\u0000\r\u0001C\u00c1\u00a6ppsq"
+"\u0000~\u0000\r\u0001\u001bIqppsq\u0000~\u0000\r\u0000\u00f2\u00d1<ppsq\u0000~\u0000\r\u0000\u00caY\u0007ppsq\u0000~\u0000\r\u0000\u00a1\u00e0\u00d2ppsq\u0000~\u0000\r\u0000yh\u009dppsq"
+"\u0000~\u0000\r\u0000P\u00f0hppsq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x"
+"\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000Wq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x"
+"(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000"
+"]q\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~"
+"\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000cq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(pps"
+"q\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000iq\u0000~"
+"\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq"
+"\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000oq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000"
+"\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000uq\u0000~\u0000&sq"
+"\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001b"
+"q\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000{q\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x"
+"\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000\u0081q\u0000~\u0000&sq\u0000~\u0000\u0000"
+"\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000"
+"\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000\u0087q\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~"
+"\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000\u008dq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3"
+"pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~"
+"\u0000!sq\u0000~\u0000\"q\u0000~\u0000\u0093q\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011ps"
+"q\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000\u0099q\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000s"
+"q\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq"
+"\u0000~\u0000\"q\u0000~\u0000\u009fq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000"
+"\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000\u00a5q\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000"
+"\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\""
+"q\u0000~\u0000\u00abq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x"
+"\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000\u00b1q\u0000~\u0000&sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\r\u0000(x"
+"(ppsq\u0000~\u0000\u0015\u0000(x\u001dq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000(x\u001aq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000"
+"\u00b7q\u0000~\u0000&sq\u0000~\u0000\r\u0003-\u00f5\u0087ppsq\u0000~\u0000\u0018\u0003-\u00f5|q\u0000~\u0000\u0011psq\u0000~\u0000)\u0001\u0097\u0083Nppsr\u0000)com.sun.ms"
+"v.datatype.xsd.EnumerationFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0006valuest\u0000\u000fLjava/"
+"util/Set;xr\u00009com.sun.msv.datatype.xsd.DataTypeWithValueConst"
+"raintFacet\"\u00a7Ro\u00ca\u00c7\u008aT\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.DataTypeWi"
+"thFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0005Z\u0000\fisFacetFixedZ\u0000\u0012needValueCheckFlagL\u0000\bbas"
+"eTypet\u0000)Lcom/sun/msv/datatype/xsd/XSDatatypeImpl;L\u0000\fconcrete"
+"Typet\u0000\'Lcom/sun/msv/datatype/xsd/ConcreteType;L\u0000\tfacetNameq\u0000"
+"~\u0000#xq\u0000~\u00000q\u0000~\u0000At\u0000\u0002Opsr\u00005com.sun.msv.datatype.xsd.WhiteSpacePr"
+"ocessor$Preserve\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u00006\u0000\u0000sr\u0000#com.sun.msv.datatype."
+"xsd.StringType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001Z\u0000\risAlwaysValidxq\u0000~\u0000.q\u0000~\u00003t\u0000\u0006strin"
+"gq\u0000~\u0001)\u0001q\u0000~\u0001+t\u0000\u000benumerationsr\u0000\u0011java.util.HashSet\u00baD\u0085\u0095\u0096\u00b8\u00b74\u0003\u0000\u0000xp"
+"w\f\u0000\u0000\u0000\u0010?@\u0000\u0000\u0000\u0000\u0000\u0004t\u0000\u0002NLt\u0000\u0003Andt\u0000\u0004Semit\u0000\u0005Chainxq\u0000~\u00009sq\u0000~\u0000:q\u0000~\u0001\'q\u0000~"
+"\u0000Asq\u0000~\u0000\"t\u0000\u0002Opt\u0000\u0000q\u0000~\u0000!sq\u0000~\u0000\r\u0001\u0088\u008b\u0091ppsq\u0000~\u0000\u0018\u0001\u0088\u008b\u0086q\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\""
+"q\u0000~\u0000=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0007AndPredq\u0000~\u0000Asr\u0000\"com.sun.msv.grammar."
+"ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/"
+"ExpressionPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.Expressi"
+"onPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~"
+"\u0001>[\u0000\u0005tablet\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000o\u0000\u0000\u0000rpur\u0000"
+"![Lcom.sun.msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0001\u007fppppppq\u0000~"
+"\u0000\fppq\u0000~\u0000Mq\u0000~\u0000\u00c3pppppppppq\u0000~\u0000Gq\u0000~\u0000\u00bdppppppppppppppppppppppppppp"
+"ppppppppppppppppppppppq\u0000~\u0000Nq\u0000~\u0000\u00c4pppppppppq\u0000~\u0000Hq\u0000~\u0000\u00beppppppppp"
+"q\u0000~\u0000Bq\u0000~\u0000\u00b8pppppppppq\u0000~\u0000\u000bpppppppppq\u0000~\u00018ppppppppppppppppppq\u0000~\u0000"
+"Oq\u0000~\u0000\u00c5pppppppppq\u0000~\u0000Iq\u0000~\u0000\u00bfpppq\u0000~\u0001\u001dpppppq\u0000~\u0000Cq\u0000~\u0000\u00b9pppppppppppp"
+"ppppppppppppppppppppppppppq\u0000~\u0000Pq\u0000~\u0000\u00c6pppppppppq\u0000~\u0000Jq\u0000~\u0000\u00c0ppppp"
+"ppppq\u0000~\u0000Dq\u0000~\u0000\u00bappppppppppppppppppppppppppppppppppppppq\u0000~\u0000Qq\u0000~"
+"\u0000\u00c7q\u0000~\u0000\nppppppppq\u0000~\u0000Kq\u0000~\u0000\u0012q\u0000~\u0000\u00c1ppppppppq\u0000~\u0000Eq\u0000~\u0000\u00bbppppppppppq\u0000"
+"~\u0000\u000epppppq\u0000~\u0000\u00aeq\u0000~\u0000\u00a8q\u0000~\u0000\u00a2q\u0000~\u0000\u009cq\u0000~\u0000\u0096q\u0000~\u0000\u0090q\u0000~\u0000\u008aq\u0000~\u0000\u0084q\u0000~\u0000~q\u0000~\u0000xq\u0000"
+"~\u0000rq\u0000~\u0000\u00adq\u0000~\u0000\u00a7q\u0000~\u0000\u00a1q\u0000~\u0000\u009bq\u0000~\u0000\u0095q\u0000~\u0000\u008fq\u0000~\u0000\u0089q\u0000~\u0000\u0083q\u0000~\u0000}q\u0000~\u0000wq\u0000~\u0000qq\u0000"
+"~\u0000kq\u0000~\u0000eq\u0000~\u0000_q\u0000~\u0000Yq\u0000~\u0000Sq\u0000~\u0000\u0014q\u0000~\u0000lq\u0000~\u0000fq\u0000~\u0000`q\u0000~\u0000Zq\u0000~\u0000Tq\u0000~\u0000\u0017q\u0000"
+"~\u0000\'q\u0000~\u0000Lq\u0000~\u0000\u00caq\u0000~\u0000\u00b3q\u0000~\u0000\u00b4q\u0000~\u0000\u00c9q\u0000~\u0000\u00cfq\u0000~\u0000\u00ceq\u0000~\u0000\u00d4q\u0000~\u0000\u00d3q\u0000~\u0000Fq\u0000~\u0000\u00d9q\u0000"
+"~\u0000\u00d8q\u0000~\u0000\u00deq\u0000~\u0000\u00ddq\u0000~\u0000\u00e3q\u0000~\u0000\u00e2q\u0000~\u0000\u00e8q\u0000~\u0000\u00e7q\u0000~\u0000\u00c2q\u0000~\u0000\u00edq\u0000~\u0000\u00ecq\u0000~\u0000\u00f2q\u0000~\u0000\u00f1q\u0000"
+"~\u0000\u00f7q\u0000~\u0000\u00f6q\u0000~\u0000\u00fcq\u0000~\u0000\u00fbq\u0000~\u0001\u0001q\u0000~\u0001\u0000q\u0000~\u0001\u0006q\u0000~\u0001\u0005q\u0000~\u0000\u00bcq\u0000~\u0001\u000bq\u0000~\u0001\nq\u0000~\u0001\u0010q\u0000"
+"~\u0001\u000fq\u0000~\u0001\u0015q\u0000~\u0001\u0014q\u0000~\u0001\u001aq\u0000~\u0001\u0019pppppq\u0000~\u0000\tppppp"));
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
            return net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  1 :
                        attIdx = context.getAttribute("", "Op");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().enterElement(___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExprPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ImpliesPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ForallPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Exists1Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IffPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("PromotedInitPred" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("MemPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("QntPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred2" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("OrPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExistsPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Fact" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("JokerPred" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("TruePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("FalsePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
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
                    case  1 :
                        attIdx = context.getAttribute("", "Op");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveElement(___uri, ___local, ___qname);
                            return ;
                        }
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
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
                    case  1 :
                        if (("Op" == ___local)&&("" == ___uri)) {
                            spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                            return ;
                        }
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                    case  3 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
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
                    case  1 :
                        attIdx = context.getAttribute("", "Op");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveAttribute(___uri, ___local, ___qname);
                            return ;
                        }
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                    case  3 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
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
                        case  1 :
                            attIdx = context.getAttribute("", "Op");
                            if (attIdx >= 0) {
                                context.consumeAttribute(attIdx);
                                context.getCurrentHandler().text(value);
                                return ;
                            }
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.AndPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.this).new Unmarshaller(context)), 2, value);
                            return ;
                        case  3 :
                            revertToParentFromText(value);
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
