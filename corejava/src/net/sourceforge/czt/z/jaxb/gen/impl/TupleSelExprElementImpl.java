//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.13 at 03:14:32 NZST 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class TupleSelExprElementImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.TupleSelExprImpl
    implements net.sourceforge.czt.z.jaxb.gen.TupleSelExprElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.TupleSelExprElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/zml";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "TupleSelExpr";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.TupleSelExprElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/zml", "TupleSelExpr");
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
        return (net.sourceforge.czt.z.jaxb.gen.TupleSelExprElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp`\u00b8\u00b7\tp"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004`\u00b8\u00b6\u00feppsq\u0000~\u0000\u0007^\u00baI\u0083ppsq\u0000~\u0000\u0007\\%+\u00e4ppsr\u0000\u001dcom.sun.msv.grammar.Choi"
+"ceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0003\u00bd\"`ppsq\u0000~\u0000\u0000\u0003\u00bd\"Usr\u0000\u0011java.lang.Boolean\u00cd"
+" r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0003\u00bd\"Jppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018pp"
+"sr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.m"
+"sv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psr\u0000"
+" com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tna"
+"meClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010psr\u00002com.sun.msv.grammar.Expressi"
+"on$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000\u000f\u0001q\u0000~\u0000\u001asr\u0000 c"
+"om.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.gr"
+"ammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expressi"
+"on$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001bq\u0000~\u0000 sr\u0000#com.s"
+"un.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljav"
+"a/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000\"xq\u0000~\u0000\u001dt\u0000-net.sourceforge.c"
+"zt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/"
+"dummy-elementssq\u0000~\u0000\f\u0001\u00c63\"ppsq\u0000~\u0000\u0017\u0001\u00c63\u0017q\u0000~\u0000\u0010psr\u0000\u001bcom.sun.msv.gr"
+"ammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Dataty"
+"pe;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~"
+"\u0000\u0004\u0000O;\u00b2ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000"
+"*com.sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%co"
+"m.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.ms"
+"v.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000\""
+"L\u0000\btypeNameq\u0000~\u0000\"L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/datatype/xsd/Wh"
+"iteSpaceProcessor;xpt\u0000 http://www.w3.org/2001/XMLSchemat\u0000\u0005QN"
+"amesr\u00005com.sun.msv.datatype.xsd.WhiteSpaceProcessor$Collapse"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteSpaceProcessor\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$NullSetExpres"
+"sion\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\nq\u0000~\u0000\u0010psr\u0000\u001bcom.sun.msv.util.StringPa"
+"ir\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000\"L\u0000\fnamespaceURIq\u0000~\u0000\"xpq\u0000~\u00003q\u0000~"
+"\u00002sq\u0000~\u0000!t\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSchema-instanceq"
+"\u0000~\u0000 sq\u0000~\u0000!t\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/zmlq\u0000~\u0000 sq\u0000~\u0000"
+"\fXh\t\u007fppsq\u0000~\u0000\fVq\u001aZppsq\u0000~\u0000\fTz+5ppsq\u0000~\u0000\fR\u0083<\u0010ppsq\u0000~\u0000\fP\u008cL\u00ebppsq\u0000~\u0000"
+"\fN\u0095]\u00c6ppsq\u0000~\u0000\fL\u009en\u00a1ppsq\u0000~\u0000\fJ\u00a7\u007f|ppsq\u0000~\u0000\fH\u00b0\u0090Wppsq\u0000~\u0000\fF\u00b9\u00a12ppsq\u0000~\u0000"
+"\fD\u00c2\u00b2\rppsq\u0000~\u0000\fB\u00cb\u00c2\u00e8ppsq\u0000~\u0000\f@\u00d4\u00d3\u00c3ppsq\u0000~\u0000\f>\u00dd\u00e4\u009eppsq\u0000~\u0000\f<\u00e6\u00f5yppsq\u0000~\u0000"
+"\f:\u00f0\u0006Tppsq\u0000~\u0000\f8\u00f9\u0017/ppsq\u0000~\u0000\f7\u0002(\nppsq\u0000~\u0000\f5\u000b8\u00e5ppsq\u0000~\u0000\f3\u0014I\u00c0ppsq\u0000~\u0000"
+"\f1\u001dZ\u009bppsq\u0000~\u0000\f/&kvppsq\u0000~\u0000\f-/|Qppsq\u0000~\u0000\f+8\u008d,ppsq\u0000~\u0000\f)A\u009e\u0007ppsq\u0000~\u0000"
+"\f\'J\u00ae\u00e2ppsq\u0000~\u0000\f%S\u00bf\u00bdppsq\u0000~\u0000\f#\\\u00d0\u0098ppsq\u0000~\u0000\f!e\u00e1sppsq\u0000~\u0000\f\u001fn\u00f2Nppsq\u0000~\u0000"
+"\f\u001dx\u0003)ppsq\u0000~\u0000\f\u001b\u0081\u0014\u0004ppsq\u0000~\u0000\f\u0019\u008a$\u00dfppsq\u0000~\u0000\f\u0017\u00935\u00bappsq\u0000~\u0000\f\u0015\u009cF\u0095ppsq\u0000~\u0000"
+"\f\u0013\u00a5Wpppsq\u0000~\u0000\f\u0011\u00aehKppsq\u0000~\u0000\f\u000f\u00b7y&ppsq\u0000~\u0000\f\r\u00c0\u008a\u0001ppsq\u0000~\u0000\f\u000b\u00c9\u009a\u00dcppsq\u0000~\u0000"
+"\f\t\u00d2\u00ab\u00b7ppsq\u0000~\u0000\f\u0007\u00db\u00bc\u0092ppsq\u0000~\u0000\f\u0005\u00e4\u00cdmppsq\u0000~\u0000\f\u0003\u00ed\u00deHppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~"
+"\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000"
+"!t\u0000.net.sourceforge.czt.z.jaxb.gen.SchExpr2Elementq\u0000~\u0000%sq\u0000~\u0000"
+"\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~"
+"\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000*net.sourceforge.czt.z.jaxb.gen.ImpliesExprq\u0000"
+"~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010p"
+"q\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000(net.sourceforge.czt.oz.jaxb.gen.Self"
+"Exprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\n"
+"q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000,net.sourceforge.czt.z.jaxb.gen"
+".Expr2NElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010p"
+"sq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000,net.sourceforge.czt."
+"z.jaxb.gen.Expr0NElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014"
+"\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000/net.source"
+"forge.czt.z.jaxb.gen.DecorExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000"
+"\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!"
+"t\u0000*net.sourceforge.czt.z.jaxb.gen.SetCompExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#"
+"pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~"
+"\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb.gen.BindExprElementq\u0000~"
+"\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq"
+"\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.czt.z.jaxb.gen.SchExp"
+"rElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017"
+"\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb"
+".gen.HideExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\r"
+"q\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000(net.sourceforg"
+"e.czt.oz.jaxb.gen.PolyExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~"
+"\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000)net.sour"
+"ceforge.czt.z.jaxb.gen.ForallExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef"
+"\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&n"
+"et.sourceforge.czt.z.jaxb.gen.LetExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000"
+"\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!"
+"t\u0000&net.sourceforge.czt.z.jaxb.gen.SetExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000s"
+"q\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq"
+"\u0000~\u0000!t\u0000*net.sourceforge.czt.z.jaxb.gen.Exists1Exprq\u0000~\u0000%sq\u0000~\u0000\u0000"
+"\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000"
+"\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.czt.z.jaxb.gen.NumExprElement"
+"q\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000"
+"\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00001net.sourceforge.czt.z.jaxb.gen.Bin"
+"dSelExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010"
+"psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge.czt"
+".zpatt.jaxb.gen.JokerExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018"
+"ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00007ne"
+"t.sourceforge.czt.oz.jaxb.gen.PromotedAttrExprElementq\u0000~\u0000%sq"
+"\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001a"
+"q\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00004net.sourceforge.czt.tcoz.jaxb.gen.Channel"
+"ExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000"
+"~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000)net.sourceforge.czt.z.j"
+"axb.gen.LambdaExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000"
+"~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000%net.sourceforge."
+"czt.z.jaxb.gen.MuExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef"
+"\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sourcefor"
+"ge.czt.z.jaxb.gen.CompExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~"
+"\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sour"
+"ceforge.czt.z.jaxb.gen.RefExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000"
+"\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!"
+"t\u0000%net.sourceforge.czt.z.jaxb.gen.OrExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq"
+"\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000"
+"~\u0000!t\u0000\'net.sourceforge.czt.z.jaxb.gen.ProdExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#"
+"pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~"
+"\u0000 sq\u0000~\u0000!t\u0000&net.sourceforge.czt.z.jaxb.gen.AndExprq\u0000~\u0000%sq\u0000~\u0000\u0000"
+"\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000"
+"\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000(net.sourceforge.czt.z.jaxb.gen.PowerExprq\u0000~\u0000%"
+"sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~"
+"\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000+net.sourceforge.czt.z.jaxb.gen.Expr1Ele"
+"mentq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\n"
+"q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&net.sourceforge.czt.z.jaxb.gen"
+".IffExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017"
+"\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000/net.sourceforge.czt.z.jaxb"
+".gen.ThetaExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef"
+"\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00000net.sourcefor"
+"ge.czt.z.jaxb.gen.RenameExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001"
+"\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000"
+")net.sourceforge.czt.z.jaxb.gen.ExistsExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000"
+"sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 s"
+"q\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb.gen.CondExprElementq\u0000~\u0000%s"
+"q\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000"
+"\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&net.sourceforge.czt.z.jaxb.gen.PreExprq\u0000"
+"~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010p"
+"q\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb.gen.Qnt1E"
+"xprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~"
+"\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000/net.sourceforge.czt.oz.j"
+"axb.gen.ContainmentExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001"
+"\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&net.sourcef"
+"orge.czt.z.jaxb.gen.NegExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000"
+"~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sou"
+"rceforge.czt.z.jaxb.gen.PipeExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018"
+"ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000+ne"
+"t.sourceforge.czt.z.jaxb.gen.Expr2Elementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000s"
+"q\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq"
+"\u0000~\u0000!t\u00002net.sourceforge.czt.z.jaxb.gen.TupleSelExprElementq\u0000~"
+"\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq"
+"\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000(net.sourceforge.czt.z.jaxb.gen.TupleE"
+"xprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq"
+"\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sourceforge.czt.z.jaxb.gen."
+"ProjExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\rq\u0000~\u0000\u0010psq\u0000~\u0000\u0017"
+"\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb"
+".gen.ApplExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\f\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0014\u0001\u00f6\u00ef\r"
+"q\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0001\u00f6\u00ef\nq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforg"
+"e.czt.z.jaxb.gen.QntExprElementq\u0000~\u0000%sq\u0000~\u0000\u0017\u0002\u0095\u001d\u009appsq\u0000~\u0000(\u0001\u0004\u00cadpp"
+"sr\u0000,com.sun.msv.datatype.xsd.PositiveIntegerType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000$com.sun.msv.datatype.xsd.IntegerType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000+com.su"
+"n.msv.datatype.xsd.IntegerDerivedType\u0099\u00f1]\u0090&6k\u00be\u0002\u0000\u0001L\u0000\nbaseFacet"
+"st\u0000)Lcom/sun/msv/datatype/xsd/XSDatatypeImpl;xq\u0000~\u0000-q\u0000~\u00002t\u0000\u000fp"
+"ositiveIntegerq\u0000~\u00006sr\u0000*com.sun.msv.datatype.xsd.MinInclusive"
+"Facet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000#com.sun.msv.datatype.xsd.RangeFacet\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\nlimitValuet\u0000\u0012Ljava/lang/Object;xr\u00009com.sun.msv.data"
+"type.xsd.DataTypeWithValueConstraintFacet\"\u00a7Ro\u00ca\u00c7\u008aT\u0002\u0000\u0000xr\u0000*com."
+"sun.msv.datatype.xsd.DataTypeWithFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0005Z\u0000\fisFacetF"
+"ixedZ\u0000\u0012needValueCheckFlagL\u0000\bbaseTypeq\u0000~\u0001\u0080L\u0000\fconcreteTypet\u0000\'L"
+"com/sun/msv/datatype/xsd/ConcreteType;L\u0000\tfacetNameq\u0000~\u0000\"xq\u0000~\u0000"
+"/ppq\u0000~\u00006\u0000\u0000sr\u0000/com.sun.msv.datatype.xsd.NonNegativeIntegerTyp"
+"e\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0001~q\u0000~\u00002t\u0000\u0012nonNegativeIntegerq\u0000~\u00006sq\u0000~\u0001\u0083ppq\u0000~"
+"\u00006\u0000\u0000sq\u0000~\u0001~q\u0000~\u00002t\u0000\u0007integerq\u0000~\u00006sr\u0000,com.sun.msv.datatype.xsd.F"
+"ractionDigitsFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001I\u0000\u0005scalexr\u0000;com.sun.msv.datatyp"
+"e.xsd.DataTypeWithLexicalConstraintFacetT\u0090\u001c>\u001azb\u00ea\u0002\u0000\u0000xq\u0000~\u0001\u0087ppq"
+"\u0000~\u00006\u0001\u0000sr\u0000#com.sun.msv.datatype.xsd.NumberType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~"
+"\u0000-q\u0000~\u00002t\u0000\u0007decimalq\u0000~\u00006q\u0000~\u0001\u0094t\u0000\u000efractionDigits\u0000\u0000\u0000\u0000q\u0000~\u0001\u008et\u0000\fminI"
+"nclusivesr\u0000)com.sun.msv.datatype.xsd.IntegerValueType\u0000\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0001\u0002\u0000\u0001L\u0000\u0005valueq\u0000~\u0000\"xr\u0000\u0010java.lang.Number\u0086\u00ac\u0095\u001d\u000b\u0094\u00e0\u008b\u0002\u0000\u0000xpt\u0000\u00010q\u0000~\u0001\u008bq"
+"\u0000~\u0001\u0097sq\u0000~\u0001\u0098t\u0000\u00011q\u0000~\u00008sq\u0000~\u00009q\u0000~\u0001\u0082q\u0000~\u00002sq\u0000~\u0000!t\u0000\u0006Selectt\u0000\u0000sq\u0000~\u0000\f\u0001"
+"\u00femvppsq\u0000~\u0000\u0017\u0001\u00femkq\u0000~\u0000\u0010pq\u0000~\u0000+sq\u0000~\u0000!q\u0000~\u0000<q\u0000~\u0000=q\u0000~\u0000 sq\u0000~\u0000!t\u0000\fTupl"
+"eSelExprq\u0000~\u0000@sr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHa"
+"sh;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8"
+"\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0001\u00a8[\u0000\u0005tablet\u0000![Lcom/sun/"
+"msv/grammar/Expression;xp\u0000\u0000\u0000\u008f\u0000\u0000\u0000\u00e6pur\u0000![Lcom.sun.msv.grammar."
+"Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0002\u00ffq\u0000~\u0001\u0004q\u0000~\u0001\u0005q\u0000~\u0000lq\u0000~\u0000\u00feq\u0000~\u0000kq\u0000~\u0000\u00ffq\u0000"
+"~\u0000jq\u0000~\u0000\u00f8q\u0000~\u0000\u00f9q\u0000~\u0000\u00f2q\u0000~\u0000\u00f3q\u0000~\u0000\u00ecq\u0000~\u0000gq\u0000~\u0000\u00edq\u0000~\u0000fq\u0000~\u0000\u00e6q\u0000~\u0000eq\u0000~\u0000\u00e7q\u0000"
+"~\u0000\u00e0q\u0000~\u0000\u00e1q\u0000~\u0000cq\u0000~\u0000\u00daq\u0000~\u0000bq\u0000~\u0000\u00dbq\u0000~\u0000aq\u0000~\u0000\u00aaq\u0000~\u0000`q\u0000~\u0000\u00b1q\u0000~\u0000\u00b0q\u0000~\u0000\u00b7q\u0000"
+"~\u0000^q\u0000~\u0000\u00b6q\u0000~\u0000]q\u0000~\u0000hq\u0000~\u0000\\q\u0000~\u0000\u00bdq\u0000~\u0000[q\u0000~\u0000\u00bcq\u0000~\u0000\u00c3q\u0000~\u0000\u00c2q\u0000~\u0000Yq\u0000~\u0000\u00c9q\u0000"
+"~\u0000Xq\u0000~\u0000\u00c8q\u0000~\u0000Wq\u0000~\u0000\u00cfq\u0000~\u0000Vq\u0000~\u0000\u00ceq\u0000~\u0000Uq\u0000~\u0000\u00d5q\u0000~\u0000Tq\u0000~\u0000\u00d4q\u0000~\u0000Sq\u0000~\u0000\u0016q\u0000"
+"~\u0000Rq\u0000~\u0000\u0013q\u0000~\u0000Qq\u0000~\u0000nq\u0000~\u0000Pq\u0000~\u0000tq\u0000~\u0000Oq\u0000~\u0000zq\u0000~\u0000Nq\u0000~\u0000\u0080q\u0000~\u0000Mq\u0000~\u0000\u0086q\u0000"
+"~\u0000\u008cq\u0000~\u0000\u0092q\u0000~\u0000Kq\u0000~\u0000\u0098q\u0000~\u0000Jq\u0000~\u0000\u009eq\u0000~\u0000\u00a4q\u0000~\u0000oq\u0000~\u0000uq\u0000~\u0000{q\u0000~\u0000\u0081q\u0000~\u0000\u0087q\u0000"
+"~\u0000\u008dq\u0000~\u0000\u0093q\u0000~\u0000\u0099q\u0000~\u0000\u009fq\u0000~\u0000\u00a5q\u0000~\u0000\u00abq\u0000~\u0000Zq\u0000~\u0000_q\u0000~\u0000dq\u0000~\u0000iq\u0000~\u0000Lq\u0000~\u0000Iq\u0000"
+"~\u0001Mq\u0000~\u0001Lq\u0000~\u0000Hq\u0000~\u0001Sq\u0000~\u0001Rq\u0000~\u0000Gq\u0000~\u0001Yq\u0000~\u0001Xq\u0000~\u0000Fq\u0000~\u0001_q\u0000~\u0001^q\u0000~\u0000Eq\u0000"
+"~\u0001eq\u0000~\u0001dq\u0000~\u0000Dq\u0000~\u0001kq\u0000~\u0001jq\u0000~\u0000Cq\u0000~\u0001qq\u0000~\u0001pq\u0000~\u0000Bq\u0000~\u0001wq\u0000~\u0001vq\u0000~\u0000Aq\u0000"
+"~\u0000\u000bq\u0000~\u0000\tpppppppppppppppppppppppppppppppppppppppppppppppppppp"
+"pppppppppppppppppppppppppppppppppppppppppppq\u0000~\u0001\u00a2pppppppppppp"
+"pppppppppppppppppppppppppppppppppppppppppppppppppppppppppppp"
+"pppppppppppppppppppppppppppppppppppppppppppppppppppppppppppp"
+"pppppppppppppppppppppppppppppppppppppppppppppppppppppppppppp"
+"pppppppppppppppppppppppppppppppppppppppppppppppppppppppppppp"
+"pppppppppppppppppppppppppppppppppppppppppppppppppppppppppppp"
+"pppppppppppppppppppppppppppppppppppppppppppppppppppppppppppp"
+"ppppppppppppppppppppppppppppppppppppppppppppppppppq\u0000~\u0000\nppppp"
+"ppppppppppppppppppppppppppppppppppppppppppppppppppppppppppq\u0000"
+"~\u0000&ppppq\u0000~\u0000\u0011pppppppppppppppppppppq\u0000~\u0000\rpppppppppppppppppppq\u0000~"
+"\u0001Gq\u0000~\u0001Aq\u0000~\u0001;q\u0000~\u00015q\u0000~\u0001/q\u0000~\u0001)q\u0000~\u0001#q\u0000~\u0001\u001dq\u0000~\u0001\u0017q\u0000~\u0001\u0011q\u0000~\u0001\u000bq\u0000~\u0001Fq\u0000~"
+"\u0001@q\u0000~\u0001:q\u0000~\u00014q\u0000~\u0001.q\u0000~\u0001(q\u0000~\u0001\"q\u0000~\u0001\u001cq\u0000~\u0001\u0016q\u0000~\u0001\u0010q\u0000~\u0001\n"));
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
            return net.sourceforge.czt.z.jaxb.gen.impl.TupleSelExprElementImpl.this;
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
                        attIdx = context.getAttribute("", "Select");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().enterElement(___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        break;
                    case  0 :
                        if (("TupleSelExpr" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
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
                    case  1 :
                        attIdx = context.getAttribute("", "Select");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveElement(___uri, ___local, ___qname);
                            return ;
                        }
                        break;
                    case  2 :
                        if (("TupleSelExpr" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
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
                    case  1 :
                        if (("Select" == ___local)&&("" == ___uri)) {
                            spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.TupleSelExprImpl)net.sourceforge.czt.z.jaxb.gen.impl.TupleSelExprElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                            return ;
                        }
                        break;
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
                        attIdx = context.getAttribute("", "Select");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveAttribute(___uri, ___local, ___qname);
                            return ;
                        }
                        break;
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
                            attIdx = context.getAttribute("", "Select");
                            if (attIdx >= 0) {
                                context.consumeAttribute(attIdx);
                                context.getCurrentHandler().text(value);
                                return ;
                            }
                            break;
                    }
                } catch (java.lang.RuntimeException e) {
                    handleUnexpectedTextException(value, e);
                }
                break;
            }
        }

    }

}
