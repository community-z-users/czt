//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.zpatt.jaxb.gen.impl;

public class DefnSequentElementImpl
    extends net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl
    implements net.sourceforge.czt.zpatt.jaxb.gen.DefnSequentElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.zpatt.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.DefnSequentElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/zpatt";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "DefnSequent";
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/zpatt", "DefnSequent");
        super.serializeURIs(context);
        context.endNamespaceDecls();
        super.serializeAttributes(context);
        context.endAttributes();
        super.serializeBody(context);
        context.endElement();
    }

    public void serializeAttributes(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
    }

    public void serializeURIs(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.DefnSequentElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0002L\u0000\u0013epsilonReducibilityt\u0000\u0013Lj"
+"ava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xppp\u0000sr\u0000\u001fcom.sun.msv.gra"
+"mmar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.BinaryExp"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~\u0000\u0004ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007pps"
+"q\u0000~\u0000\u0007ppsr\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\bpps"
+"q\u0000~\u0000\u0000sr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007ppsq"
+"\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004q\u0000~\u0000\u0011psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003ex"
+"pq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004q\u0000~\u0000\u0011psr\u00002com.sun.msv.grammar.E"
+"xpression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004sq\u0000~\u0000\u0010\u0001q\u0000~\u0000\u001bsr"
+"\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv"
+".grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expre"
+"ssion$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u001cq\u0000~\u0000!sr\u0000#com.su"
+"n.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava"
+"/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000#xq\u0000~\u0000\u001et\u0000-net.sourceforge.cz"
+"t.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/d"
+"ummy-elementssq\u0000~\u0000\rppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011psr\u0000\u001bcom.sun.msv.grammar.Dat"
+"aExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Datatype;L\u0000\u0006exc"
+"eptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~\u0000\u0004ppsr\u0000\"c"
+"om.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv."
+"datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.dat"
+"atype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xs"
+"d.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000#L\u0000\btypeNameq\u0000"
+"~\u0000#L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/datatype/xsd/WhiteSpaceProce"
+"ssor;xpt\u0000 http://www.w3.org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.su"
+"n.msv.datatype.xsd.WhiteSpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000,com.sun.msv.datatype.xsd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xps"
+"r\u00000com.sun.msv.grammar.Expression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u0011psr\u0000\u001bcom.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tl"
+"ocalNameq\u0000~\u0000#L\u0000\fnamespaceURIq\u0000~\u0000#xpq\u0000~\u00004q\u0000~\u00003sq\u0000~\u0000\"t\u0000\u0004typet\u0000"
+")http://www.w3.org/2001/XMLSchema-instanceq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0004Anns"
+"t\u0000\u001ehttp://czt.sourceforge.net/zmlq\u0000~\u0000!sq\u0000~\u0000\rppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000"
+"\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00008net.sourc"
+"eforge.czt.zpatt.jaxb.gen.SequentContextElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp"
+"\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001f"
+"q\u0000~\u0000!sq\u0000~\u0000\"t\u00001net.sourceforge.czt.zpatt.jaxb.gen.SequentCont"
+"extq\u0000~\u0000&sq\u0000~\u0000\rppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000,q\u0000~\u0000<q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u000eSequentC"
+"ontextt\u0000 http://czt.sourceforge.net/zpattsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000"
+"~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t"
+"\u0000.net.sourceforge.czt.z.jaxb.gen.DeclNameElementq\u0000~\u0000&sq\u0000~\u0000\u0000p"
+"p\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000"
+"\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\'net.sourceforge.czt.z.jaxb.gen.DeclNameq\u0000~\u0000&s"
+"q\u0000~\u0000\rppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000,q\u0000~\u0000<q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\bDeclNameq\u0000~\u0000Asq\u0000~"
+"\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000"
+"3net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElementq\u0000~\u0000&sq\u0000"
+"~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rp"
+"psq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000"
+"~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rp"
+"psq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000"
+"~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rp"
+"psq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000"
+"~\u0000\"t\u0000\'net.sourceforge.czt.z.jaxb.gen.ProdExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000s"
+"q\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.net.s"
+"ourceforge.czt.z.jaxb.gen.HideExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000"
+"\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourc"
+"eforge.czt.z.jaxb.gen.SchExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq"
+"\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00003net.sourceforg"
+"e.czt.zpatt.jaxb.gen.JokerExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rpps"
+"q\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourcefor"
+"ge.czt.z.jaxb.gen.ForallExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000"
+"\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000%net.sourceforge.czt.z."
+"jaxb.gen.MuExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011"
+"pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb.gen.NumE"
+"xprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000"
+"\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000&net.sourceforge.czt.z.jaxb.gen.AndExprq\u0000"
+"~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!s"
+"q\u0000~\u0000\"t\u0000(net.sourceforge.czt.z.jaxb.gen.TupleExprq\u0000~\u0000&sq\u0000~\u0000\u0000p"
+"p\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000/ne"
+"t.sourceforge.czt.z.jaxb.gen.ThetaExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000s"
+"q\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000(net.s"
+"ourceforge.czt.oz.jaxb.gen.PolyExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000"
+"~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000/net.sourceforge"
+".czt.oz.jaxb.gen.ContainmentExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015"
+"q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00004net.sourceforge.cz"
+"t.tcoz.jaxb.gen.ChannelExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~"
+"\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\'net.sourceforge."
+"czt.z.jaxb.gen.PipeExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000"
+"~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000&net.sourceforge.czt.z.jaxb."
+"gen.SetExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~"
+"\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000/net.sourceforge.czt.z.jaxb.gen.DecorExp"
+"rElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq"
+"\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sourceforge.czt.z.jaxb.gen.Exists1Expr"
+"q\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000"
+"!sq\u0000~\u0000\"t\u0000.net.sourceforge.czt.z.jaxb.gen.CondExprElementq\u0000~\u0000"
+"&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000"
+"~\u0000\"t\u00007net.sourceforge.czt.zpatt.jaxb.gen.JokerExprListElemen"
+"tq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~"
+"\u0000!sq\u0000~\u0000\"t\u0000\'net.sourceforge.czt.z.jaxb.gen.ProjExprq\u0000~\u0000&sq\u0000~\u0000"
+"\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000."
+"net.sourceforge.czt.oz.jaxb.gen.ClassUnionExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000"
+"sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00002net."
+"sourceforge.czt.z.jaxb.gen.TupleSelExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000"
+"sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net."
+"sourceforge.czt.z.jaxb.gen.ImpliesExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rpp"
+"sq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000%net.sourcefo"
+"rge.czt.z.jaxb.gen.OrExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011ps"
+"q\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.net.sourceforge.czt.z.jax"
+"b.gen.BindExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00001net.sourceforge.czt.z.jaxb.ge"
+"n.BindSelExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018"
+"q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000(net.sourceforge.czt.z.jaxb.gen"
+".PowerExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000"
+"\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000/net.sourceforge.czt.oz.jaxb.gen.PredExpr"
+"Elementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000"
+"~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourceforge.czt.z.jaxb.gen.LambdaExprq\u0000"
+"~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!s"
+"q\u0000~\u0000\"t\u0000&net.sourceforge.czt.z.jaxb.gen.PreExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000"
+"sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\'net."
+"sourceforge.czt.z.jaxb.gen.CompExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000"
+"~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000&net.sourceforge"
+".czt.z.jaxb.gen.LetExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000"
+"~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb."
+"gen.RefExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000"
+"~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000)net.sourceforge.czt.z.jaxb.gen.E"
+"xistsExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001b"
+"q\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.net.sourceforge.czt.z.jaxb.gen.ApplExprEl"
+"ementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000"
+"\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000&net.sourceforge.czt.z.jaxb.gen.IffExprq\u0000~\u0000&sq"
+"\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\""
+"t\u0000&net.sourceforge.czt.z.jaxb.gen.NegExprq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000"
+"\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00000net.sourc"
+"eforge.czt.z.jaxb.gen.RenameExprElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rp"
+"psq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000*net.sourcef"
+"orge.czt.z.jaxb.gen.SetCompExprq\u0000~\u0000&sq\u0000~\u0000\rppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000"
+",q\u0000~\u0000<q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u000bDefnSequentq\u0000~\u0000Usr\u0000\"com.sun.msv.grammar."
+"ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/"
+"ExpressionPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.Expressi"
+"onPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006paren"
+"tt\u0000$Lcom/sun/msv/grammar/ExpressionPool;xp\u0000\u0000\u0000\u008f\u0001pq\u0000~\u0000vq\u0000~\u0000\nq\u0000"
+"~\u0000\u0081q\u0000~\u0000\u000eq\u0000~\u0000\tq\u0000~\u0001Lq\u0000~\u0001Fq\u0000~\u0001@q\u0000~\u0001:q\u0000~\u00014q\u0000~\u0001.q\u0000~\u0001(q\u0000~\u0001\"q\u0000~\u0001\u001cq\u0000"
+"~\u0001\u0016q\u0000~\u0001\u0010q\u0000~\u0001\nq\u0000~\u0001\u0004q\u0000~\u0000\u00feq\u0000~\u0000\u00f8q\u0000~\u0000\u00f2q\u0000~\u0000\u00ecq\u0000~\u0000\u00e6q\u0000~\u0000\u00e0q\u0000~\u0000\u0017q\u0000~\u0000\u0085q\u0000"
+"~\u0000Eq\u0000~\u0000Mq\u0000~\u0000\u0089q\u0000~\u0000Zq\u0000~\u0000bq\u0000~\u0000lq\u0000~\u0000\u0098q\u0000~\u0000\u009eq\u0000~\u0000\u00a4q\u0000~\u0000\u00aaq\u0000~\u0000|q\u0000~\u0000\u00b0q\u0000"
+"~\u0000\u00b6q\u0000~\u0000\u00bcq\u0000~\u0000\u00c2q\u0000~\u0000\u00c8q\u0000~\u0000\u00ceq\u0000~\u0000\u00d4q\u0000~\u0000\u00daq\u0000~\u0000\fq\u0000~\u0001Rq\u0000~\u0001Xq\u0000~\u0001^q\u0000~\u0001dq\u0000"
+"~\u0001jq\u0000~\u0001pq\u0000~\u0001vq\u0000~\u0001|q\u0000~\u0000\u008fq\u0000~\u0000\u008eq\u0000~\u0000~q\u0000~\u0001Eq\u0000~\u0001?q\u0000~\u00019q\u0000~\u00013q\u0000~\u0001-q\u0000"
+"~\u0000Bq\u0000~\u0000Wq\u0000~\u0001\'q\u0000~\u0001!q\u0000~\u0001\u001bq\u0000~\u0001\u0015q\u0000~\u0001\u000fq\u0000~\u0001\tq\u0000~\u0001\u0003q\u0000~\u0000\u00fdq\u0000~\u0000\u00f7q\u0000~\u0000\u00f1q\u0000"
+"~\u0000\u00ebq\u0000~\u0000\u00e5q\u0000~\u0000\u00dfq\u0000~\u0000\u00d9q\u0000~\u0000Dq\u0000~\u0000Lq\u0000~\u0000Yq\u0000~\u0000aq\u0000~\u0000kq\u0000~\u0000\u0097q\u0000~\u0000\u009dq\u0000~\u0000\u00a3q\u0000"
+"~\u0000\u00a9q\u0000~\u0000\u00afq\u0000~\u0000\u00b5q\u0000~\u0000\u00bbq\u0000~\u0000\u00c1q\u0000~\u0000\u00c7q\u0000~\u0000\u00cdq\u0000~\u0000\u00d3q\u0000~\u0000\u0014q\u0000~\u0000\u008dq\u0000~\u0000\u0080q\u0000~\u0000\u0093q\u0000"
+"~\u0001Kq\u0000~\u0001Qq\u0000~\u0001Wq\u0000~\u0001]q\u0000~\u0001cq\u0000~\u0001iq\u0000~\u0001oq\u0000~\u0001uq\u0000~\u0001{q\u0000~\u0000\u0092q\u0000~\u0000\u0094q\u0000~\u0000Vq\u0000"
+"~\u0000\u0086q\u0000~\u0000\u0082q\u0000~\u0000\u0084q\u0000~\u0000rq\u0000~\u0000pq\u0000~\u0000{q\u0000~\u0000yq\u0000~\u0000wq\u0000~\u0000\u008cq\u0000~\u0000\u0091q\u0000~\u0000\u0083q\u0000~\u0000\u0087q\u0000"
+"~\u0000\u0090q\u0000~\u0000\u0012q\u0000~\u0000Jq\u0000~\u0000_q\u0000~\u0000\u008aq\u0000~\u0000uq\u0000~\u0000qq\u0000~\u0000\u008bq\u0000~\u0000}q\u0000~\u0000\u000bq\u0000~\u0000\'q\u0000~\u0000Qq\u0000"
+"~\u0000fq\u0000~\u0001\u0080q\u0000~\u0000\u0095q\u0000~\u0000tq\u0000~\u0000\u0088q\u0000~\u0000zq\u0000~\u0000xq\u0000~\u0000sq\u0000~\u0000\u007fx"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.circus.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "----");
        }

        protected Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("DefnSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
                    case  1 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SequentContext" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SequentContext" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
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
                        if (("DefnSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.this).new Unmarshaller(context)), 2, value);
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
