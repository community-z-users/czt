//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2003.11.03 at 03:50:09 NZDT 
//


package net.sourceforge.czt.oz.jaxb.gen.impl;

public class StateElementImpl
    extends net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl
    implements net.sourceforge.czt.oz.jaxb.gen.StateElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.oz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.oz.jaxb.gen.StateElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/object-z";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "State";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/object-z", "State");
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
        return (net.sourceforge.czt.oz.jaxb.gen.StateElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\f\u009fqmp"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\f\u009fqbppsq\u0000~\u0000\u0007\u000b\u0012\u0088\u00c2ppsq\u0000~\u0000\u0007\u0004\u0090F\u0011ppsq\u0000~\u0000\u0007\u0003\\s\u00e6ppsr\u0000\u001dcom.sun.msv."
+"grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0002$\u0007bppsq\u0000~\u0000\u0000\u0002$\u0007Wsr\u0000\u0011java.l"
+"ang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0002$\u0007Lppsq\u0000~\u0000\u0000\u0000h$(pp\u0000"
+"sq\u0000~\u0000\r\u0000h$\u001dppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0000"
+"h$\u0012q\u0000~\u0000\u0011psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003e"
+"xpq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0000h$\u000fq\u0000~\u0000\u0011psr\u00002com.sun.msv.gram"
+"mar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000"
+"\u0010\u0001q\u0000~\u0000\u001bsr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dco"
+"m.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gram"
+"mar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001cq\u0000"
+"~\u0000!sr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tloca"
+"lNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000#xq\u0000~\u0000\u001et\u0000-net.s"
+"ourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.c"
+"om/jaxb/xjc/dummy-elementssq\u0000~\u0000\r\u0001\u00bb\u00e3\u001fppsq\u0000~\u0000\u0018\u0001\u00bb\u00e3\u0014q\u0000~\u0000\u0011psr\u0000\u001bco"
+"m.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/dat"
+"atype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/Str"
+"ingPair;xq\u0000~\u0000\u0004\u0000\u0014t\u00fappsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000"
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
+"mlq\u0000~\u0000!sq\u0000~\u0000\u0015\u00018l\u007fppsq\u0000~\u0000\r\u00018l|ppsq\u0000~\u0000\r\u0000\u00d0HRppsq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~"
+"\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000"
+"\"t\u0000.net.sourceforge.czt.z.jaxb.gen.InclDeclElementq\u0000~\u0000&sq\u0000~\u0000"
+"\u0000\u0000h$(pp\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~"
+"\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb.gen.VarDeclElemen"
+"tq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~"
+"\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000/net.sourceforge.czt.z.jaxb.gen.Co"
+"nstDeclElementq\u0000~\u0000&sq\u0000~\u0000\r\u00013\u00d2&ppsq\u0000~\u0000\u0015\u00013\u00d2\u001bq\u0000~\u0000\u0011psq\u0000~\u0000\r\u00013\u00d2\u0018q\u0000~"
+"\u0000\u0011psq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000"
+"~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000:net.sourceforge.czt.oz.jaxb.gen."
+"SecondaryAttributesElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000\u00cb\u00ad\u00eeq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\u0007\u0000\u00cb\u00ad\u00e3pp"
+"sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~"
+"\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00003net.sourceforge.czt.oz.jaxb.gen.Seconda"
+"ryAttributesq\u0000~\u0000&sq\u0000~\u0000\r\u0000c\u0089\u00b6ppsq\u0000~\u0000\u0018\u0000c\u0089\u00abq\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\"q\u0000~\u0000"
+"=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0013SecondaryAttributest\u0000#http://czt.sourcef"
+"orge.net/object-zq\u0000~\u0000!sq\u0000~\u0000\r\u0006\u0082B\u00acppsq\u0000~\u0000\u0015\u0006\u0082B\u00a1q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0006\u0082B\u009e"
+"q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0006\u001a\u001etq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0005\u00b1\u00faJq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0005I\u00d6 q\u0000~\u0000\u0011psq\u0000~\u0000\r"
+"\u0004\u00e1\u00b1\u00f6q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0004y\u008d\u00ccq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0004\u0011i\u00a2q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0003\u00a9Exq\u0000~\u0000\u0011psq"
+"\u0000~\u0000\r\u0003A!Nq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0002\u00d8\u00fd$q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0002p\u00d8\u00faq\u0000~\u0000\u0011psq\u0000~\u0000\r\u0002\b\u00b4\u00d0q\u0000~\u0000"
+"\u0011psq\u0000~\u0000\r\u0001\u00a0\u0090\u00a6q\u0000~\u0000\u0011psq\u0000~\u0000\r\u00018l|q\u0000~\u0000\u0011psq\u0000~\u0000\r\u0000\u00d0HRq\u0000~\u0000\u0011psq\u0000~\u0000\u0000\u0000h$("
+"q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000"
+"\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\'net.sourceforge.czt.z.jaxb.gen.TruePredq\u0000~\u0000&s"
+"q\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011p"
+"q\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourceforge.czt.z.jaxb.gen.Exist"
+"sPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000"
+"\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jax"
+"b.gen.QntPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015"
+"\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00003net.source"
+"forge.czt.zpatt.jaxb.gen.JokerPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000"
+"\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~"
+"\u0000!sq\u0000~\u0000\"t\u0000%net.sourceforge.czt.z.jaxb.gen.OrPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000"
+"h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq"
+"\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000+net.sourceforge.czt.z.jaxb.gen.Pred2Elemen"
+"tq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$"
+"\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourceforge.czt.z.jaxb.ge"
+"n.ForallPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000"
+"\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000(net.sourceforge.cz"
+"t.z.jaxb.gen.FalsePredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~"
+"\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.net.sour"
+"ceforge.czt.z.jaxb.gen.ExprPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000"
+"sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!s"
+"q\u0000~\u0000\"t\u0000*net.sourceforge.czt.z.jaxb.gen.Exists1Predq\u0000~\u0000&sq\u0000~\u0000"
+"\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000"
+"\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb.gen.NegPredEl"
+"ementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000"
+"\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jax"
+"b.gen.AndPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015"
+"\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000&net.source"
+"forge.czt.z.jaxb.gen.IffPredq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001d"
+"ppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-ne"
+"t.sourceforge.czt.z.jaxb.gen.MemPredElementq\u0000~\u0000&sq\u0000~\u0000\u0000\u0000h$(q\u0000"
+"~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq"
+"\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sourceforge.czt.z.jaxb.gen.ImpliesPredq\u0000~\u0000&"
+"sq\u0000~\u0000\u0000\u0000h$(q\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\r\u0000h$\u001dppsq\u0000~\u0000\u0015\u0000h$\u0012q\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0000h$\u000fq\u0000~\u0000\u0011"
+"pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sourceforge.czt.z.jaxb.gen.Fact"
+"Elementq\u0000~\u0000&q\u0000~\u0000!sq\u0000~\u0000\r\u0001\u008c\u00e8\u009bppsq\u0000~\u0000\u0018\u0001\u008c\u00e8\u0090q\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\"q\u0000~\u0000"
+"=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0005Stateq\u0000~\u0000msr\u0000\"com.sun.msv.grammar.Expres"
+"sionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/Expres"
+"sionPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool"
+"$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000\u00e5[\u0000\u0005t"
+"ablet\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000M\u0000\u0000\u0000rpur\u0000![Lcom"
+".sun.msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0001\u007fpppppppq\u0000~\u0000aq\u0000~"
+"\u0000\fpq\u0000~\u0000sppppppppppppppppppppppq\u0000~\u0000zppppppppppppppppppppppppp"
+"pppq\u0000~\u0000hpppppq\u0000~\u0000tppppppppppppppppppppppq\u0000~\u0000{ppppppppppppppp"
+"pppppppppppppppppppq\u0000~\u0000uppppppppppppppppppppppq\u0000~\u0000|ppppq\u0000~\u0000\u0012"
+"pppppppppppppppppppppq\u0000~\u0000\u000epppppppq\u0000~\u0000vppppppppppppppppppppq\u0000"
+"~\u0000\tpq\u0000~\u0000}q\u0000~\u0000Cq\u0000~\u0000\'q\u0000~\u0000Bppppppppq\u0000~\u0000pppq\u0000~\u0000oppq\u0000~\u0000\npppppppq\u0000"
+"~\u0000nppppppppq\u0000~\u0000wppppppppppppppppppppppq\u0000~\u0000~q\u0000~\u0000Dppppppppppq\u0000"
+"~\u0000qppppppppppppppppppppppq\u0000~\u0000xq\u0000~\u0000\u008dq\u0000~\u0000\u0087q\u0000~\u0000\u0081q\u0000~\u0000dq\u0000~\u0000\\q\u0000~\u0000S"
+"q\u0000~\u0000Mq\u0000~\u0000Gq\u0000~\u0000\u0017q\u0000~\u0000\u00bdq\u0000~\u0000\u00b7q\u0000~\u0000\u008cq\u0000~\u0000\u0086q\u0000~\u0000\u0080q\u0000~\u0000cq\u0000~\u0000[q\u0000~\u0000Rq\u0000~\u0000L"
+"q\u0000~\u0000Fq\u0000~\u0000\u0014q\u0000~\u0000\u00bcq\u0000~\u0000\u00b6q\u0000~\u0000\u00b0q\u0000~\u0000\u00b1q\u0000~\u0000\u00aaq\u0000~\u0000\u00abq\u0000~\u0000\u00a4q\u0000~\u0000\u00a5q\u0000~\u0000\u009eq\u0000~\u0000\u009f"
+"q\u0000~\u0000\u0098q\u0000~\u0000\u0099q\u0000~\u0000\u0092q\u0000~\u0000\u0093q\u0000~\u0000\u00c3q\u0000~\u0000\u00c2q\u0000~\u0000\u00c9q\u0000~\u0000\u00c8q\u0000~\u0000\u00cfq\u0000~\u0000\u00ceq\u0000~\u0000rq\u0000~\u0000\u00d5"
+"q\u0000~\u0000Yq\u0000~\u0000\u00d4q\u0000~\u0000\u00dbq\u0000~\u0000Xq\u0000~\u0000\u00dapppppppppq\u0000~\u0000Wq\u0000~\u0000yq\u0000~\u0000\u00dfppppppppppq"
+"\u0000~\u0000\u000bpppppppppppp"));
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
            return net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  0 :
                        if (("State" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
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
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InclDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ConstDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Decl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Decl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
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
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("State" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.oz.jaxb.gen.impl.StateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.StateElementImpl.this).new Unmarshaller(context)), 2, value);
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
