//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.tcoz.jaxb.gen.impl;

public class RecProExprElementImpl
    extends net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl
    implements net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.tcoz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/tcoz";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "RecProExpr";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/tcoz", "RecProExpr");
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
        return (net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\f\u00cc\u000f\u00c5p"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\f\u00cc\u000f\u00bappsq\u0000~\u0000\u0007\n&\u001a\u0014ppsq\u0000~\u0000\u0007\u0005\u0090|\u0010ppsr\u0000\u001dcom.sun.msv.grammar.Choi"
+"ceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u00030\u00be|ppsq\u0000~\u0000\u0000\u00030\u00beqsr\u0000\u0011java.lang.Boolean\u00cd"
+" r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u00030\u00befppsq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(pp"
+"sr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.m"
+"sv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0000(x\u001dq\u0000~\u0000\u0010psr\u0000"
+" com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tna"
+"meClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0000(x\u001aq\u0000~\u0000\u0010psr\u00002com.sun.msv.grammar.Expressi"
+"on$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000\u000f\u0001q\u0000~\u0000\u001asr\u0000 c"
+"om.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.gr"
+"ammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expressi"
+"on$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001bq\u0000~\u0000 sr\u0000#com.s"
+"un.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljav"
+"a/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000\"xq\u0000~\u0000\u001dt\u0000-net.sourceforge.c"
+"zt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/"
+"dummy-elementssq\u0000~\u0000\f\u0003\bF.ppsq\u0000~\u0000\u0017\u0003\bF#q\u0000~\u0000\u0010psr\u0000\u001bcom.sun.msv.gr"
+"ammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Dataty"
+"pe;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~"
+"\u0000\u0004\u0001[\u0001,ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000"
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
+"\u0000\u0002_\u00bd\u008fpp\u0000sq\u0000~\u0000\u0007\u0002_\u00bd\u0084ppsq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010"
+"psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&net.sourceforge.czt"
+".z.jaxb.gen.RefNameq\u0000~\u0000%sq\u0000~\u0000\f\u00027ELppsq\u0000~\u0000\u0017\u00027EAq\u0000~\u0000\u0010pq\u0000~\u0000+sq\u0000"
+"~\u0000!q\u0000~\u0000<q\u0000~\u0000=q\u0000~\u0000 sq\u0000~\u0000!t\u0000\u0006OpNamet\u0000\u001fhttp://czt.sourceforge.n"
+"et/tcozsq\u0000~\u0000\f\u0004\u0095\u009d\u00ffppsq\u0000~\u0000\f\u0004m%\u00cappsq\u0000~\u0000\f\u0004D\u00ad\u0095ppsq\u0000~\u0000\f\u0004\u001c5`ppsq\u0000~\u0000"
+"\f\u0003\u00f3\u00bd+ppsq\u0000~\u0000\f\u0003\u00cbD\u00f6ppsq\u0000~\u0000\f\u0003\u00a2\u00cc\u00c1ppsq\u0000~\u0000\f\u0003zT\u008cppsq\u0000~\u0000\f\u0003Q\u00dcWppsq\u0000~\u0000"
+"\f\u0003)d\"ppsq\u0000~\u0000\f\u0003\u0000\u00eb\u00edppsq\u0000~\u0000\f\u0002\u00d8s\u00b8ppsq\u0000~\u0000\f\u0002\u00af\u00fb\u0083ppsq\u0000~\u0000\f\u0002\u0087\u0083Nppsq\u0000~\u0000"
+"\f\u0002_\u000b\u0019ppsq\u0000~\u0000\f\u00026\u0092\u00e4ppsq\u0000~\u0000\f\u0002\u000e\u001a\u00afppsq\u0000~\u0000\f\u0001\u00e5\u00a2zppsq\u0000~\u0000\f\u0001\u00bd*Eppsq\u0000~\u0000"
+"\f\u0001\u0094\u00b2\u0010ppsq\u0000~\u0000\f\u0001l9\u00dbppsq\u0000~\u0000\f\u0001C\u00c1\u00a6ppsq\u0000~\u0000\f\u0001\u001bIqppsq\u0000~\u0000\f\u0000\u00f2\u00d1<ppsq\u0000~\u0000"
+"\f\u0000\u00caY\u0007ppsq\u0000~\u0000\f\u0000\u00a1\u00e0\u00d2ppsq\u0000~\u0000\f\u0000yh\u009dppsq\u0000~\u0000\f\u0000P\u00f0hppsq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~"
+"\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000"
+"!t\u00003net.sourceforge.czt.tcoz.jaxb.gen.TimeoutEndProExprq\u0000~\u0000%"
+"sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~"
+"\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000+net.sourceforge.czt.oz.jaxb.gen.ParenOp"
+"Exprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001a"
+"q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge.czt.oz.jaxb.ge"
+"n.RenameOpExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x"
+"\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00002net.sourcefor"
+"ge.czt.tcoz.jaxb.gen.AtProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000"
+"\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!"
+"t\u00005net.sourceforge.czt.tcoz.jaxb.gen.GuardProExprElementq\u0000~\u0000"
+"%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000"
+"~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00008net.sourceforge.czt.tcoz.jaxb.gen.Dead"
+"lineProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000"
+"~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge."
+"czt.tcoz.jaxb.gen.InterleaveProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000"
+"(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000"
+"*net.sourceforge.czt.oz.jaxb.gen.ConjOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp"
+"\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 "
+"sq\u0000~\u0000!t\u0000.net.sourceforge.czt.oz.jaxb.gen.ParallelOpExprq\u0000~\u0000%"
+"sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~"
+"\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.oz.jaxb.gen.DistCon"
+"jOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000"
+"(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00006net.sourceforge.czt.oz.jaxb"
+".gen.OpPromotionExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000"
+"~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00006net.sou"
+"rceforge.czt.tcoz.jaxb.gen.SynPllProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000("
+"x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq"
+"\u0000~\u0000 sq\u0000~\u0000!t\u00008net.sourceforge.czt.tcoz.jaxb.gen.TopologyProEx"
+"prElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000"
+"\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00002net.sourceforge.czt.tcoz."
+"jaxb.gen.InterruptProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000"
+"\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00009net.sourc"
+"eforge.czt.tcoz.jaxb.gen.WaitUntilProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000"
+"(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001e"
+"q\u0000~\u0000 sq\u0000~\u0000!t\u00000net.sourceforge.czt.oz.jaxb.gen.DistChoiceOpEx"
+"prq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000"
+"~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.czt.tcoz.jaxb.ge"
+"n.SkipProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010ps"
+"q\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.czt.t"
+"coz.jaxb.gen.StopProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014"
+"\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00001net.source"
+"forge.czt.oz.jaxb.gen.HideOpExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000"
+"~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~"
+"\u0000!t\u00001net.sourceforge.czt.oz.jaxb.gen.ScopeEnrichOpExprq\u0000~\u0000%s"
+"q\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000"
+"\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00005net.sourceforge.czt.tcoz.jaxb.gen.Timeou"
+"tStartProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010ps"
+"q\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00004net.sourceforge.czt.t"
+"coz.jaxb.gen.WaitProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(p"
+"psq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00000net"
+".sourceforge.czt.tcoz.jaxb.gen.DivergeProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3"
+"pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~"
+"\u0000 sq\u0000~\u0000!t\u00002net.sourceforge.czt.oz.jaxb.gen.AssoParallelOpExp"
+"rq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~"
+"\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge.czt.tcoz.jaxb.gen"
+".RecProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000"
+"~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge."
+"czt.oz.jaxb.gen.ExChoiceOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000sq\u0000~\u0000\f\u0000(x(pp"
+"sq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net."
+"sourceforge.czt.oz.jaxb.gen.DistSeqOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000(x3pp\u0000s"
+"q\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq"
+"\u0000~\u0000!t\u0000)net.sourceforge.czt.oz.jaxb.gen.SeqOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000"
+"(x3pp\u0000sq\u0000~\u0000\f\u0000(x(ppsq\u0000~\u0000\u0014\u0000(x\u001dq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000(x\u001aq\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001e"
+"q\u0000~\u0000 sq\u0000~\u0000!t\u00002net.sourceforge.czt.oz.jaxb.gen.BasicOpExprEle"
+"mentq\u0000~\u0000%sq\u0000~\u0000\f\u0002\u00a5\u00f5\u00a1ppsq\u0000~\u0000\u0017\u0002\u00a5\u00f5\u0096q\u0000~\u0000\u0010pq\u0000~\u0000+sq\u0000~\u0000!q\u0000~\u0000<q\u0000~\u0000=q\u0000"
+"~\u0000 sq\u0000~\u0000!t\u0000\nRecProExprq\u0000~\u0000Nsr\u0000\"com.sun.msv.grammar.Expressio"
+"nPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/Expressio"
+"nPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$Cl"
+"osedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0001\u001f[\u0000\u0005tabl"
+"et\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000c\u0000\u0000\u0000rpur\u0000![Lcom.su"
+"n.msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0001\u007fpppppppppq\u0000~\u0000fppq\u0000"
+"~\u0000&pppppppq\u0000~\u0000`ppppppppppq\u0000~\u0000Zppppppppppq\u0000~\u0000Tq\u0000~\u0000\npppppppppp"
+"pppppppppppppppppq\u0000~\u0000gq\u0000~\u0001\u0019pppppppppq\u0000~\u0000appppppppppq\u0000~\u0000[pppp"
+"ppppppq\u0000~\u0000Uppppppppppq\u0000~\u0000Oppppq\u0000~\u0000\tppppppppppppq\u0000~\u0000hpppppppp"
+"ppq\u0000~\u0000bppppppppppq\u0000~\u0000\\ppppppppppq\u0000~\u0000Vppppppppppq\u0000~\u0000Ppppppppp"
+"pppppppppq\u0000~\u0000ippppppppppq\u0000~\u0000cppppppppppq\u0000~\u0000]ppppppppppq\u0000~\u0000Wp"
+"pppppppppq\u0000~\u0000Qpppppppppppppppppq\u0000~\u0000jppppppppppq\u0000~\u0000dppppppppp"
+"pq\u0000~\u0000^ppppppppppq\u0000~\u0000Xppppppq\u0000~\u0000\u00c7q\u0000~\u0000\u00c1q\u0000~\u0000\u00bbq\u0000~\u0000\u00b5q\u0000~\u0000\u00afq\u0000~\u0000\u00a9q\u0000~"
+"\u0000\u00a3q\u0000~\u0000\u009dq\u0000~\u0000\u0097q\u0000~\u0000\u0091q\u0000~\u0000\u008bq\u0000~\u0000\u00c0q\u0000~\u0000\u00baq\u0000~\u0000\u00b4q\u0000~\u0000\u00aeq\u0000~\u0000\u00a8q\u0000~\u0000\u00a2q\u0000~\u0000\u009cq\u0000~"
+"\u0000\u0096q\u0000~\u0000\u0090q\u0000~\u0000\u008aq\u0000~\u0000\u0084q\u0000~\u0000~q\u0000~\u0000xq\u0000~\u0000rq\u0000~\u0000lq\u0000~\u0000Dq\u0000~\u0000\u0013q\u0000~\u0000\u0085q\u0000~\u0000\u007fq\u0000~"
+"\u0000yq\u0000~\u0000sq\u0000~\u0000mq\u0000~\u0000Eq\u0000~\u0000\u0016q\u0000~\u0000\u000bq\u0000~\u0000eq\u0000~\u0000Bq\u0000~\u0000\u00c6q\u0000~\u0000\u0011q\u0000~\u0000\u00cdq\u0000~\u0000\u00ccq\u0000~"
+"\u0000\u00d3q\u0000~\u0000\u00d2q\u0000~\u0000_q\u0000~\u0000\u00d9q\u0000~\u0000\u00d8q\u0000~\u0000\u00dfq\u0000~\u0000\u00deq\u0000~\u0000\u00e5q\u0000~\u0000\u00e4q\u0000~\u0000\u00ebq\u0000~\u0000\u00eaq\u0000~\u0000\u00f1q\u0000~"
+"\u0000\u00f0q\u0000~\u0000Yq\u0000~\u0000\u00f7q\u0000~\u0000\u00f6q\u0000~\u0000\u00fdq\u0000~\u0000\u00fcq\u0000~\u0001\u0003q\u0000~\u0000\rq\u0000~\u0001\u0002q\u0000~\u0000Rq\u0000~\u0001\tq\u0000~\u0001\bq\u0000~"
+"\u0000Sq\u0000~\u0001\u000fq\u0000~\u0001\u000eq\u0000~\u0001\u0015q\u0000~\u0001\u0014ppppppq\u0000~\u0000Ipppppppp"));
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
            return net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  0 :
                        if (("RecProExpr" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
                    case  1 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("OpName" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
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
                        if (("RecProExpr" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.RecProExprElementImpl.this).new Unmarshaller(context)), 2, value);
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
