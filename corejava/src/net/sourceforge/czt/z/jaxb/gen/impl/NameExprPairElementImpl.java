//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2003.12.24 at 11:29:45 NZDT 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class NameExprPairElementImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairImpl
    implements net.sourceforge.czt.z.jaxb.gen.NameExprPairElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
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

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
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

    public void serializeAttributes(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
    }

    public void serializeURIs(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
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
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp4\u00fa\u00a5\u00a8p"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u00044\u00fa\u00a5\u009dppsq\u0000~\u0000\u00072\u0001\u00e4\u0091ppsq\u0000~\u0000\u0000\u0002\u008eC\u0096pp\u0000sq\u0000~\u0000\u0007\u0002\u008eC\u008bppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sr"
+"\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0001/\u00b0\u00c6ppsr\u0000 co"
+"m.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.gra"
+"mmar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0001/\u00b0\u00bbsr\u0000\u0011java.lang.B"
+"oolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000psr\u0000 com.sun.msv.grammar.Attribu"
+"teExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0001/\u00b0\u00b8q\u0000~\u0000\u0014p"
+"sr\u00002com.sun.msv.grammar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000\u0013\u0001q\u0000~\u0000\u0018sr\u0000 com.sun.msv.grammar.AnyNameCl"
+"ass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xp"
+"sr\u00000com.sun.msv.grammar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001"
+"\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u0019q\u0000~\u0000\u001esr\u0000#com.sun.msv.grammar.SimpleNameCla"
+"ss\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceUR"
+"Iq\u0000~\u0000 xq\u0000~\u0000\u001bt\u0000\'net.sourceforge.czt.z.jaxb.gen.DeclNamet\u0000+htt"
+"p://java.sun.com/jaxb/xjc/dummy-elementssq\u0000~\u0000\u000e\u0001^\u0092\u00b5ppsq\u0000~\u0000\u0015\u0001^"
+"\u0092\u00aaq\u0000~\u0000\u0014psr\u0000\u001bcom.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLo"
+"rg/relaxng/datatype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/su"
+"n/msv/util/StringPair;xq\u0000~\u0000\u0004\u0000\u00fa9\u00e7ppsr\u0000\"com.sun.msv.datatype.x"
+"sd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinA"
+"tomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteTyp"
+"e\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000 L\u0000\btypeNameq\u0000~\u0000 L\u0000\nwhiteSpacet\u0000.Lc"
+"om/sun/msv/datatype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www."
+"w3.org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.Wh"
+"iteSpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatyp"
+"e.xsd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gramma"
+"r.Expression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\nq\u0000~\u0000\u0014psr\u0000"
+"\u001bcom.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000 L\u0000\fn"
+"amespaceURIq\u0000~\u0000 xpq\u0000~\u00001q\u0000~\u00000sq\u0000~\u0000\u001ft\u0000\u0004typet\u0000)http://www.w3.or"
+"g/2001/XMLSchema-instanceq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\u0004Namet\u0000\u001ehttp://czt.sou"
+"rceforge.net/zmlsq\u0000~\u0000\u000e/s\u00a0\u00f6ppsq\u0000~\u0000\u000e.C\u00f0#ppsq\u0000~\u0000\u000e-\u0014?Pppsq\u0000~\u0000\u000e+\u00e4"
+"\u008e}ppsq\u0000~\u0000\u000e*\u00b4\u00dd\u00aappsq\u0000~\u0000\u000e)\u0085,\u00d7ppsq\u0000~\u0000\u000e(U|\u0004ppsq\u0000~\u0000\u000e\'%\u00cb1ppsq\u0000~\u0000\u000e%\u00f6"
+"\u001a^ppsq\u0000~\u0000\u000e$\u00c6i\u008bppsq\u0000~\u0000\u000e#\u0096\u00b8\u00b8ppsq\u0000~\u0000\u000e\"g\u0007\u00e5ppsq\u0000~\u0000\u000e!7W\u0012ppsq\u0000~\u0000\u000e \u0007"
+"\u00a6?ppsq\u0000~\u0000\u000e\u001e\u00d7\u00f5lppsq\u0000~\u0000\u000e\u001d\u00a8D\u0099ppsq\u0000~\u0000\u000e\u001cx\u0093\u00c6ppsq\u0000~\u0000\u000e\u001bH\u00e2\u00f3ppsq\u0000~\u0000\u000e\u001a\u0019"
+"2 ppsq\u0000~\u0000\u000e\u0018\u00e9\u0081Mppsq\u0000~\u0000\u000e\u0017\u00b9\u00d0zppsq\u0000~\u0000\u000e\u0016\u008a\u001f\u00a7ppsq\u0000~\u0000\u000e\u0015Zn\u00d4ppsq\u0000~\u0000\u000e\u0014*"
+"\u00be\u0001ppsq\u0000~\u0000\u000e\u0012\u00fb\r.ppsq\u0000~\u0000\u000e\u0011\u00cb\\[ppsq\u0000~\u0000\u000e\u0010\u009b\u00ab\u0088ppsq\u0000~\u0000\u000e\u000fk\u00fa\u00b5ppsq\u0000~\u0000\u000e\u000e<"
+"I\u00e2ppsq\u0000~\u0000\u000e\r\f\u0099\u000fppsq\u0000~\u0000\u000e\u000b\u00dc\u00e8<ppsq\u0000~\u0000\u000e\n\u00ad7ippsq\u0000~\u0000\u000e\t}\u0086\u0096ppsq\u0000~\u0000\u000e\bM"
+"\u00d5\u00c3ppsq\u0000~\u0000\u000e\u0007\u001e$\u00f0ppsq\u0000~\u0000\u000e\u0005\u00eet\u001dppsq\u0000~\u0000\u000e\u0004\u00be\u00c3Jppsq\u0000~\u0000\u000e\u0003\u008f\u0012wppsq\u0000~\u0000\u000e\u0002_"
+"a\u00a4ppsq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014"
+"pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000-net.sourceforge.czt.z.jaxb.gen.QntE"
+"xprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~"
+"\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z.ja"
+"xb.gen.ApplExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/"
+"\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourcefo"
+"rge.czt.z.jaxb.gen.SchExpr2Elementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/"
+"\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&"
+"net.sourceforge.czt.z.jaxb.gen.NegExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~"
+"\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000"
+"\u001ft\u0000%net.sourceforge.czt.z.jaxb.gen.MuExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000s"
+"q\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq"
+"\u0000~\u0000\u001ft\u0000\'net.sourceforge.czt.z.jaxb.gen.ProdExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0"
+"\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000"
+"~\u0000\u001esq\u0000~\u0000\u001ft\u0000*net.sourceforge.czt.z.jaxb.gen.ImpliesExprq\u0000~\u0000#s"
+"q\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00000net.sourceforge.czt.z.jaxb.gen.RenameExp"
+"rElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015"
+"\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00003net.sourceforge.czt.zpatt."
+"jaxb.gen.JokerExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000"
+"\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourc"
+"eforge.czt.z.jaxb.gen.Qnt1ExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000"
+"\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001f"
+"t\u00001net.sourceforge.czt.z.jaxb.gen.BindSelExprElementq\u0000~\u0000#sq\u0000"
+"~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q"
+"\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000(net.sourceforge.czt.z.jaxb.gen.TupleExprq\u0000"
+"~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014p"
+"q\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000/net.sourceforge.czt.z.jaxb.gen.Decor"
+"ExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000"
+"~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.j"
+"axb.gen.PreExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014"
+"psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000%net.sourceforge.czt"
+".z.jaxb.gen.OrExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000"
+"~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\'net.sourceforge."
+"czt.z.jaxb.gen.PipeExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001"
+"/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourcef"
+"orge.czt.z.jaxb.gen.AndExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000"
+"~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000*net.sou"
+"rceforge.czt.z.jaxb.gen.Exists1Exprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001"
+"/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000"
+"2net.sourceforge.czt.z.jaxb.gen.TupleSelExprElementq\u0000~\u0000#sq\u0000~"
+"\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000"
+"~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000,net.sourceforge.czt.z.jaxb.gen.Expr2NElemen"
+"tq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~"
+"\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000)net.sourceforge.czt.z.jaxb.gen.Ex"
+"istsExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015"
+"\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000+net.sourceforge.czt.z.jaxb"
+".gen.Expr2Elementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~"
+"\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000)net.sourceforge.c"
+"zt.z.jaxb.gen.ForallExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010"
+"\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000-net.source"
+"forge.czt.z.jaxb.gen.SchExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001"
+"/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000"
+"(net.sourceforge.czt.z.jaxb.gen.PowerExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000s"
+"q\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq"
+"\u0000~\u0000\u001ft\u0000)net.sourceforge.czt.z.jaxb.gen.LambdaExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001"
+"/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001c"
+"q\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000+net.sourceforge.czt.z.jaxb.gen.Expr1Elementq\u0000~"
+"\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq"
+"\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.jaxb.gen.SetExp"
+"rq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~"
+"\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z.jaxb.gen.Co"
+"ndExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014ps"
+"q\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z"
+".jaxb.gen.BindExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000"
+"\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000*net.sourc"
+"eforge.czt.z.jaxb.gen.SetCompExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0"
+"\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000/n"
+"et.sourceforge.czt.z.jaxb.gen.ThetaExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0"
+"\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000"
+"~\u0000\u001esq\u0000~\u0000\u001ft\u0000-net.sourceforge.czt.z.jaxb.gen.RefExprElementq\u0000~"
+"\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq"
+"\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\'net.sourceforge.czt.z.jaxb.gen.CompEx"
+"prq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000"
+"~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.jaxb.gen.L"
+"etExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/"
+"\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z.jaxb.g"
+"en.HideExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000"
+"~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000-net.sourceforge."
+"czt.z.jaxb.gen.NumExprElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6pps"
+"q\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000,net.s"
+"ourceforge.czt.z.jaxb.gen.Expr0NElementq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1pp\u0000sq\u0000"
+"~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~"
+"\u0000\u001ft\u0000\'net.sourceforge.czt.z.jaxb.gen.ProjExprq\u0000~\u0000#sq\u0000~\u0000\u0000\u0001/\u00b0\u00d1p"
+"p\u0000sq\u0000~\u0000\u000e\u0001/\u00b0\u00c6ppsq\u0000~\u0000\u0010\u0001/\u00b0\u00bbq\u0000~\u0000\u0014psq\u0000~\u0000\u0015\u0001/\u00b0\u00b8q\u0000~\u0000\u0014pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000"
+"\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.jaxb.gen.IffExprq\u0000~\u0000#sq\u0000~\u0000\u000e\u0002"
+"\u00f8\u00c1\u0007ppsq\u0000~\u0000\u0015\u0002\u00f8\u00c0\u00fcq\u0000~\u0000\u0014pq\u0000~\u0000)sq\u0000~\u0000\u001fq\u0000~\u0000:q\u0000~\u0000;q\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\fName"
+"ExprPairq\u0000~\u0000>sr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHa"
+"sh;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8"
+"\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0001\\[\u0000\u0005tablet\u0000![Lcom/sun/"
+"msv/grammar/Expression;xp\u0000\u0000\u0000~\u0000\u0000\u0000\u00e6pur\u0000![Lcom.sun.msv.grammar."
+"Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0002\u00ffpppppppppppq\u0000~\u0000\\ppppppppppppq\u0000~\u0000"
+"Qppppppppppppq\u0000~\u0000Fppppppppppppppppppppppppppppppppppppppq\u0000~\u0000"
+"`ppppppppppppq\u0000~\u0000Uppppppppppppq\u0000~\u0000Jppppppppppppq\u0000~\u0000?pppppppp"
+"pppppppppppppppppq\u0000~\u0000dppppppppppppq\u0000~\u0000Yppppppppppppq\u0000~\u0000Npppp"
+"ppppppppq\u0000~\u0000Cppppppppppppppppppppppppppppppppppppppq\u0000~\u0000]pppp"
+"ppppppppq\u0000~\u0000Rpq\u0000~\u0000\fppppppq\u0000~\u0001Vpppq\u0000~\u0000Gpppppppppppppppppppppp"
+"ppppppppppppppppq\u0000~\u0000appppppppppppq\u0000~\u0000Vppppppppppppq\u0000~\u0000Kppppp"
+"pppppppq\u0000~\u0000@pppppppppppppppppppppppppq\u0000~\u0000eppppppppppppq\u0000~\u0000Zp"
+"pq\u0000~\u0000\npppppppppq\u0000~\u0000Oppppppppppppq\u0000~\u0000Dppppppppppppppppppppppp"
+"pppppppppppppppq\u0000~\u0000^pppppppppppq\u0000~\u0000$q\u0000~\u0000Sppppppppppppq\u0000~\u0000Hpp"
+"ppppppppppppppppppppppppppppppppppppq\u0000~\u0000bppppppppppppq\u0000~\u0000Wpp"
+"ppppppppppq\u0000~\u0000Lppppppppppppq\u0000~\u0000Apppq\u0000~\u0001@q\u0000~\u0001:q\u0000~\u00014q\u0000~\u0001.q\u0000~\u0001("
+"q\u0000~\u0001\"q\u0000~\u0001\u001cq\u0000~\u0001\u0016q\u0000~\u0001\u0010q\u0000~\u0001\nq\u0000~\u0001\u0004q\u0000~\u0001?q\u0000~\u00019q\u0000~\u00013q\u0000~\u0001-q\u0000~\u0001\'q\u0000~\u0001!"
+"q\u0000~\u0001\u001bq\u0000~\u0001\u0015q\u0000~\u0001\u000fq\u0000~\u0001\tq\u0000~\u0001\u0003q\u0000~\u0000\u00fdq\u0000~\u0000\u00feq\u0000~\u0000\u00f7q\u0000~\u0000\u00f8q\u0000~\u0000\u00f1q\u0000~\u0000\u00f2q\u0000~\u0000\u00eb"
+"q\u0000~\u0000\u00ecq\u0000~\u0000\u00e5q\u0000~\u0000\u00e6q\u0000~\u0000\u00dfq\u0000~\u0000\u00e0q\u0000~\u0000\u00d9q\u0000~\u0000[q\u0000~\u0000\u00daq\u0000~\u0000\u00d3q\u0000~\u0000\u00d4q\u0000~\u0000\u0012q\u0000~\u0000h"
+"q\u0000~\u0000nq\u0000~\u0000tq\u0000~\u0000zq\u0000~\u0000\u0080q\u0000~\u0000\u0086q\u0000~\u0000\u008cq\u0000~\u0000\u000fq\u0000~\u0000Pq\u0000~\u0000gq\u0000~\u0000mq\u0000~\u0000sq\u0000~\u0000y"
+"q\u0000~\u0000\u007fq\u0000~\u0000\u0085q\u0000~\u0000\u008bq\u0000~\u0000\u0091q\u0000~\u0000\u0097q\u0000~\u0000\u009dq\u0000~\u0000\u00a3q\u0000~\u0000\u00a9q\u0000~\u0000\u00afq\u0000~\u0000\u00b5q\u0000~\u0000\u00bbq\u0000~\u0000\u00c1"
+"q\u0000~\u0000\u00c7q\u0000~\u0000\u00cdq\u0000~\u0000\u0092q\u0000~\u0000\u0098q\u0000~\u0000\u009eq\u0000~\u0000\u00a4q\u0000~\u0000\u00aaq\u0000~\u0000\u00b0q\u0000~\u0000\u00b6q\u0000~\u0000\u00bcq\u0000~\u0000\u00c2q\u0000~\u0000\u00c8"
+"q\u0000~\u0000\u00ceq\u0000~\u0000Eq\u0000~\u0001Fq\u0000~\u0001Eq\u0000~\u0001Lq\u0000~\u0001Kq\u0000~\u0001Rq\u0000~\u0001Qq\u0000~\u0000\tppppppppppppppq"
+"\u0000~\u0000_ppppppppppppq\u0000~\u0000Tppppppppppppq\u0000~\u0000Ipppppppppppppppppppppp"
+"ppppppppppppppppq\u0000~\u0000cppppppppppppq\u0000~\u0000Xppppppppppppq\u0000~\u0000Mppppp"
+"pppppppq\u0000~\u0000Bppppppppppppppppppppppppppp"));
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
            return net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairElementImpl.this;
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
                    case  1 :
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairImpl)net.sourceforge.czt.z.jaxb.gen.impl.NameExprPairElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        break;
                    case  0 :
                        if (("NameExprPair" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
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
