//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.04.21 at 09:33:05 GMT 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class NameExprPairElementImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairImpl
    implements net.sourceforge.czt.z.jaxb.gen.NameExprPairElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.NameExprPairElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/zml";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "NameExprPair";
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/zml", "NameExprPair");
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
        return (net.sourceforge.czt.z.jaxb.gen.NameExprPairElement.class);
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
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~\u0000\u0004ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0000pp\u0000"
+"sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0000pp\u0000sr\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000"
+"\u0000xq\u0000~\u0000\bppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001c"
+"com.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004sr\u0000\u0011"
+"java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000psr\u0000 com.sun.msv.gram"
+"mar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000"
+"\u0004q\u0000~\u0000\u0014psr\u00002com.sun.msv.grammar.Expression$AnyStringExpressio"
+"n\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004sq\u0000~\u0000\u0013\u0001q\u0000~\u0000\u0018sr\u0000 com.sun.msv.grammar.AnyNam"
+"eClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000"
+"\u0000xpsr\u00000com.sun.msv.grammar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u0019q\u0000~\u0000\u001esr\u0000#com.sun.msv.grammar.SimpleNameClas"
+"s\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURI"
+"q\u0000~\u0000 xq\u0000~\u0000\u001bt\u0000\'net.sourceforge.czt.z.jaxb.gen.DeclNamet\u0000+http"
+"://java.sun.com/jaxb/xjc/dummy-elementssq\u0000~\u0000\u000eppsq\u0000~\u0000\u0015q\u0000~\u0000\u0014ps"
+"r\u0000\u001bcom.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxn"
+"g/datatype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/uti"
+"l/StringPair;xq\u0000~\u0000\u0004ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fname"
+"spaceUriq\u0000~\u0000 L\u0000\btypeNameq\u0000~\u0000 L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/da"
+"tatype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3.org/2001/X"
+"MLSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.WhiteSpaceProce"
+"ssor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteSp"
+"aceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$"
+"NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u0014psr\u0000\u001bcom.sun.msv.util"
+".StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000 L\u0000\fnamespaceURIq\u0000~\u0000 x"
+"pq\u0000~\u00001q\u0000~\u00000sq\u0000~\u0000\u001ft\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSchema-"
+"instanceq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\u0004Namet\u0000\u001ehttp://czt.sourceforge.net/zmls"
+"q\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000"
+"\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000epps"
+"q\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000"
+"\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000epps"
+"q\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000"
+"\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u000eppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014p"
+"q\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.jaxb.gen.NegEx"
+"prq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000"
+"~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.jaxb.gen.PreExprq\u0000~\u0000#sq\u0000~\u0000"
+"\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\'"
+"net.sourceforge.czt.z.jaxb.gen.CompExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000ep"
+"psq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000/net.sourcef"
+"orge.czt.z.jaxb.gen.ThetaExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq"
+"\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforg"
+"e.czt.z.jaxb.gen.AndExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq"
+"\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000-net.sourceforge.czt.z.jaxb"
+".gen.RefExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q"
+"\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z.jaxb.gen."
+"CondExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014"
+"pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00005net.sourceforge.czt.tcoz.jaxb.gen.A"
+"ctuatorExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000"
+"~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z.jaxb.gen.B"
+"indExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014p"
+"q\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00004net.sourceforge.czt.tcoz.jaxb.gen.Ch"
+"annelExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000"
+"\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00007net.sourceforge.czt.zpatt.jaxb.gen"
+".JokerExprListElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000"
+"\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000/net.sourceforge.czt.oz.jaxb.g"
+"en.PredExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000"
+"~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.jaxb.gen.S"
+"etExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~"
+"\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\'net.sourceforge.czt.z.jaxb.gen.ProdExprq\u0000~\u0000#"
+"sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~"
+"\u0000\u001ft\u0000-net.sourceforge.czt.z.jaxb.gen.NumExprElementq\u0000~\u0000#sq\u0000~\u0000"
+"\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000*"
+"net.sourceforge.czt.z.jaxb.gen.ImpliesExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~"
+"\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000/net.sour"
+"ceforge.czt.oz.jaxb.gen.ContainmentExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000ep"
+"psq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourcef"
+"orge.czt.z.jaxb.gen.IffExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014"
+"psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.j"
+"axb.gen.LetExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014"
+"pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\'net.sourceforge.czt.z.jaxb.gen.Proj"
+"Exprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001c"
+"q\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00000net.sourceforge.czt.z.jaxb.gen.RenameExprEleme"
+"ntq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000"
+"~\u0000\u001esq\u0000~\u0000\u001ft\u0000%net.sourceforge.czt.z.jaxb.gen.MuExprq\u0000~\u0000#sq\u0000~\u0000\u0000"
+"pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.n"
+"et.sourceforge.czt.z.jaxb.gen.HideExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000s"
+"q\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000(net.s"
+"ourceforge.czt.oz.jaxb.gen.PolyExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000"
+"~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00002net.sourceforge"
+".czt.z.jaxb.gen.TupleSelExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000"
+"~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000*net.sourceforge"
+".czt.z.jaxb.gen.SetCompExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014"
+"psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z.j"
+"axb.gen.ApplExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000"
+"~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000)net.sourceforge.czt.z.jaxb."
+"gen.ForallExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014p"
+"q\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\'net.sourceforge.czt.z.jaxb.gen.PipeE"
+"xprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq"
+"\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00003net.sourceforge.czt.zpatt.jaxb.gen.JokerExprEle"
+"mentq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001c"
+"q\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000(net.sourceforge.czt.z.jaxb.gen.TupleExprq\u0000~\u0000#s"
+"q\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000"
+"\u001ft\u0000%net.sourceforge.czt.z.jaxb.gen.OrExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000"
+"\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000)net.sourc"
+"eforge.czt.z.jaxb.gen.LambdaExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010"
+"q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000)net.sourceforge.cz"
+"t.z.jaxb.gen.ExistsExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000"
+"~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00001net.sourceforge.czt.z.jaxb."
+"gen.BindSelExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~"
+"\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.oz.jaxb."
+"gen.ClassUnionExprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000"
+"~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000*net.sourceforge.czt.z.jaxb.gen.E"
+"xists1Exprq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000(net.sourceforge.czt.z.jaxb.gen.PowerExpr"
+"q\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000"
+"\u001esq\u0000~\u0000\u001ft\u00003net.sourceforge.czt.tcoz.jaxb.gen.SensorExprElemen"
+"tq\u0000~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~"
+"\u0000\u001esq\u0000~\u0000\u001ft\u0000/net.sourceforge.czt.z.jaxb.gen.DecorExprElementq\u0000"
+"~\u0000#sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0010q\u0000~\u0000\u0014psq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001es"
+"q\u0000~\u0000\u001ft\u0000-net.sourceforge.czt.z.jaxb.gen.SchExprElementq\u0000~\u0000#sq"
+"\u0000~\u0000\u000eppsq\u0000~\u0000\u0015q\u0000~\u0000\u0014pq\u0000~\u0000)q\u0000~\u00009q\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\fNameExprPairq\u0000~\u0000>s"
+"r\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet"
+"\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHash;xpsr\u0000-com.s"
+"un.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB"
+"\u0000\rstreamVersionL\u0000\u0006parentt\u0000$Lcom/sun/msv/grammar/ExpressionPo"
+"ol;xp\u0000\u0000\u0000\u0081\u0001pq\u0000~\u0000Kq\u0000~\u0000Oq\u0000~\u0000Hq\u0000~\u0000Xq\u0000~\u0000\fq\u0000~\u0000Tq\u0000~\u0000Vq\u0000~\u0000Pq\u0000~\u0000`q\u0000~\u0000"
+"?q\u0000~\u0000Jq\u0000~\u0000Mq\u0000~\u0000^q\u0000~\u0000Uq\u0000~\u0000Iq\u0000~\u0000Rq\u0000~\u0000bq\u0000~\u0000]q\u0000~\u0000Lq\u0000~\u0000\\q\u0000~\u0000cq\u0000~\u0000"
+"Zq\u0000~\u0000[q\u0000~\u0000Yq\u0000~\u0000aq\u0000~\u0000Qq\u0000~\u0000dq\u0000~\u0000\tq\u0000~\u0000fq\u0000~\u0001@q\u0000~\u0001:q\u0000~\u00014q\u0000~\u0001.q\u0000~\u0001"
+"(q\u0000~\u0001\"q\u0000~\u0001\u001cq\u0000~\u0001\u0016q\u0000~\u0001\u0010q\u0000~\u0001\nq\u0000~\u0001\u0004q\u0000~\u0000\u00feq\u0000~\u0000\u00f8q\u0000~\u0000\u00f2q\u0000~\u0000\u00ecq\u0000~\u0000\u00e6q\u0000~\u0000"
+"\u00e0q\u0000~\u0000\u00daq\u0000~\u0000\u00d4q\u0000~\u0000\u000fq\u0000~\u0000hq\u0000~\u0000nq\u0000~\u0000tq\u0000~\u0000zq\u0000~\u0000\u0080q\u0000~\u0000\u0086q\u0000~\u0000\u008cq\u0000~\u0000\u0092q\u0000~\u0000"
+"\u0098q\u0000~\u0000\u009eq\u0000~\u0000\u00a4q\u0000~\u0000\u00aaq\u0000~\u0000\u00b0q\u0000~\u0000\u00b6q\u0000~\u0000\u00bcq\u0000~\u0000\u00c2q\u0000~\u0000\u00c8q\u0000~\u0000\u00ceq\u0000~\u0001Fq\u0000~\u0001Lq\u0000~\u0001"
+"Rq\u0000~\u0000@q\u0000~\u0001Xq\u0000~\u0000Dq\u0000~\u0000Cq\u0000~\u0000\nq\u0000~\u0001Aq\u0000~\u0001;q\u0000~\u00015q\u0000~\u0001/q\u0000~\u0001)q\u0000~\u0001#q\u0000~\u0001"
+"\u001dq\u0000~\u0001\u0017q\u0000~\u0001\u0011q\u0000~\u0001\u000bq\u0000~\u0001\u0005q\u0000~\u0000\u00ffq\u0000~\u0000\u00f9q\u0000~\u0000\u00f3q\u0000~\u0000\u00edq\u0000~\u0000\u00e7q\u0000~\u0000\u00e1q\u0000~\u0000\u00dbq\u0000~\u0000"
+"\u00d5q\u0000~\u0000\u0012q\u0000~\u0000iq\u0000~\u0000oq\u0000~\u0000uq\u0000~\u0000{q\u0000~\u0000\u0081q\u0000~\u0000\u0087q\u0000~\u0000\u008dq\u0000~\u0000\u0093q\u0000~\u0000\u0099q\u0000~\u0000Gq\u0000~\u0000"
+"\u009fq\u0000~\u0000\u00a5q\u0000~\u0000\u00abq\u0000~\u0000\u00b1q\u0000~\u0000\u00b7q\u0000~\u0000\u00bdq\u0000~\u0000\u00c3q\u0000~\u0000\u00c9q\u0000~\u0000\u00cfq\u0000~\u0000Fq\u0000~\u0001Gq\u0000~\u0001Mq\u0000~\u0001"
+"Sq\u0000~\u0001Yq\u0000~\u0000Bq\u0000~\u0000eq\u0000~\u0000Aq\u0000~\u0000Sq\u0000~\u0000Nq\u0000~\u0000_q\u0000~\u0000Eq\u0000~\u0000Wq\u0000~\u0000$q\u0000~\u0001]x"));
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
            return net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  0 :
                        if (("NameExprPair" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  1 :
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairImpl)net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
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
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("NameExprPair" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
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
                    }
                } catch (java.lang.RuntimeException e) {
                    handleUnexpectedTextException(value, e);
                }
                break;
            }
        }

    }

}
