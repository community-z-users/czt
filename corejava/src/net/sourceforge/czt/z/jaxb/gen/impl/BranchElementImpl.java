//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.10 at 09:41:23 NZST 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class BranchElementImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl
    implements net.sourceforge.czt.z.jaxb.gen.BranchElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.BranchElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/zml";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "Branch";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/zml", "Branch");
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
        return (net.sourceforge.czt.z.jaxb.gen.BranchElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\u0017:\u0013\u0084p"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\u0017:\u0013yppsq\u0000~\u0000\u0007\u0014\u00df\u008b\\ppsq\u0000~\u0000\u0007\u0007\u008b\u00b3\u00c3ppsr\u0000\u001dcom.sun.msv.grammar.Choi"
+"ceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0003\u008e\u00d1mppsq\u0000~\u0000\u0000\u0003\u008e\u00d1bsr\u0000\u0011java.lang.Boolean\u00cd"
+" r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0003\u008e\u00d1Wppsq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008app"
+"sr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.m"
+"sv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0000K\u00d1\u007fq\u0000~\u0000\u0010psr\u0000"
+" com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tna"
+"meClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0000K\u00d1|q\u0000~\u0000\u0010psr\u00002com.sun.msv.grammar.Expressi"
+"on$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000\u000f\u0001q\u0000~\u0000\u001asr\u0000 c"
+"om.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.gr"
+"ammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expressi"
+"on$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001bq\u0000~\u0000 sr\u0000#com.s"
+"un.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljav"
+"a/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000\"xq\u0000~\u0000\u001dt\u0000-net.sourceforge.c"
+"zt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/"
+"dummy-elementssq\u0000~\u0000\f\u0003B\u00ff\u00bdppsq\u0000~\u0000\u0017\u0003B\u00ff\u00b2q\u0000~\u0000\u0010psr\u0000\u001bcom.sun.msv.gr"
+"ammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Dataty"
+"pe;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~"
+"\u0000\u0004\u0001\u00c3\t\u00a3ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000"
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
+"\f\u0003\u00fc\u00e2Qppsq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000"
+"~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb.gen.D"
+"eclNameElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0003\u00b1\u0010\u00bapp\u0000sq\u0000~\u0000\u0007\u0003\u00b1\u0010\u00afppsq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000"
+"~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~"
+"\u0000!t\u0000\'net.sourceforge.czt.z.jaxb.gen.DeclNameq\u0000~\u0000%sq\u0000~\u0000\f\u0003e?\u0015p"
+"psq\u0000~\u0000\u0017\u0003e?\nq\u0000~\u0000\u0010pq\u0000~\u0000+sq\u0000~\u0000!q\u0000~\u0000<q\u0000~\u0000=q\u0000~\u0000 sq\u0000~\u0000!t\u0000\bDeclName"
+"q\u0000~\u0000@sq\u0000~\u0000\f\rS\u00d7\u0094ppsq\u0000~\u0000\f\rS\u00d7\u0089q\u0000~\u0000\u0010psq\u0000~\u0000\f\r\b\u0005\u00f2q\u0000~\u0000\u0010psq\u0000~\u0000\f\f\u00bc4[q"
+"\u0000~\u0000\u0010psq\u0000~\u0000\f\fpb\u00c4q\u0000~\u0000\u0010psq\u0000~\u0000\f\f$\u0091-q\u0000~\u0000\u0010psq\u0000~\u0000\f\u000b\u00d8\u00bf\u0096q\u0000~\u0000\u0010psq\u0000~\u0000\f\u000b"
+"\u008c\u00ed\u00ffq\u0000~\u0000\u0010psq\u0000~\u0000\f\u000bA\u001chq\u0000~\u0000\u0010psq\u0000~\u0000\f\n\u00f5J\u00d1q\u0000~\u0000\u0010psq\u0000~\u0000\f\n\u00a9y:q\u0000~\u0000\u0010psq\u0000"
+"~\u0000\f\n]\u00a7\u00a3q\u0000~\u0000\u0010psq\u0000~\u0000\f\n\u0011\u00d6\fq\u0000~\u0000\u0010psq\u0000~\u0000\f\t\u00c6\u0004uq\u0000~\u0000\u0010psq\u0000~\u0000\f\tz2\u00deq\u0000~\u0000\u0010"
+"psq\u0000~\u0000\f\t.aGq\u0000~\u0000\u0010psq\u0000~\u0000\f\b\u00e2\u008f\u00b0q\u0000~\u0000\u0010psq\u0000~\u0000\f\b\u0096\u00be\u0019q\u0000~\u0000\u0010psq\u0000~\u0000\f\bJ\u00ec\u0082q"
+"\u0000~\u0000\u0010psq\u0000~\u0000\f\u0007\u00ff\u001a\u00ebq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0007\u00b3ITq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0007gw\u00bdq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0007"
+"\u001b\u00a6&q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0006\u00cf\u00d4\u008fq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0006\u0084\u0002\u00f8q\u0000~\u0000\u0010psq\u0000~\u0000\f\u000681aq\u0000~\u0000\u0010psq\u0000"
+"~\u0000\f\u0005\u00ec_\u00caq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0005\u00a0\u008e3q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0005T\u00bc\u009cq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0005\b\u00eb\u0005q\u0000~\u0000\u0010"
+"psq\u0000~\u0000\f\u0004\u00bd\u0019nq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0004qG\u00d7q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0004%v@q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0003\u00d9\u00a4\u00a9q"
+"\u0000~\u0000\u0010psq\u0000~\u0000\f\u0003\u008d\u00d3\u0012q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0003B\u0001{q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0002\u00f6/\u00e4q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0002"
+"\u00aa^Mq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0002^\u008c\u00b6q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0002\u0012\u00bb\u001fq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0001\u00c6\u00e9\u0088q\u0000~\u0000\u0010psq\u0000"
+"~\u0000\f\u0001{\u0017\u00f1q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0001/FZq\u0000~\u0000\u0010psq\u0000~\u0000\f\u0000\u00e3t\u00c3q\u0000~\u0000\u0010psq\u0000~\u0000\f\u0000\u0097\u00a3,q\u0000~\u0000\u0010"
+"psq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000"
+"\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb.gen.Sch"
+"Expr2Elementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000"
+"\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.cz"
+"t.z.jaxb.gen.HideExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008a"
+"ppsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.ne"
+"t.sourceforge.czt.z.jaxb.gen.ApplExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q"
+"\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001e"
+"q\u0000~\u0000 sq\u0000~\u0000!t\u0000&net.sourceforge.czt.z.jaxb.gen.SetExprq\u0000~\u0000%sq\u0000"
+"~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000"
+"~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000)net.sourceforge.czt.z.jaxb.gen.ExistsE"
+"xprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000"
+"K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sourceforge.czt.z.jaxb."
+"gen.PipeExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000"
+"\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.cz"
+"t.z.jaxb.gen.RefExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008ap"
+"psq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net"
+".sourceforge.czt.z.jaxb.gen.CondExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000"
+"~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq"
+"\u0000~\u0000 sq\u0000~\u0000!t\u00001net.sourceforge.czt.z.jaxb.gen.BindSelExprEleme"
+"ntq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K"
+"\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000*net.sourceforge.czt.z.jaxb.g"
+"en.Exists1Exprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000"
+"~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000,net.sourceforge."
+"czt.z.jaxb.gen.Expr2NElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008a"
+"ppsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000)ne"
+"t.sourceforge.czt.z.jaxb.gen.ForallExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p"
+"\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 "
+"sq\u0000~\u0000!t\u0000&net.sourceforge.czt.z.jaxb.gen.AndExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K"
+"\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000"
+"~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000%net.sourceforge.czt.z.jaxb.gen.OrExprq\u0000~\u0000%s"
+"q\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010p"
+"q\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000*net.sourceforge.czt.z.jaxb.gen.SetCo"
+"mpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~"
+"\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00002net.sourceforge.czt.z.ja"
+"xb.gen.TupleSelExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008app"
+"sq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net."
+"sourceforge.czt.z.jaxb.gen.NumExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000"
+"\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~"
+"\u0000 sq\u0000~\u0000!t\u0000/net.sourceforge.czt.z.jaxb.gen.ThetaExprElementq\u0000"
+"~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000"
+"~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.czt.z.jaxb.gen.S"
+"chExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~"
+"\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000+net.sourceforge.c"
+"zt.z.jaxb.gen.Expr2Elementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008app"
+"sq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00007net."
+"sourceforge.czt.oz.jaxb.gen.PromotedAttrExprElementq\u0000~\u0000%sq\u0000~"
+"\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~"
+"\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sourceforge.czt.z.jaxb.gen.ProdExpr"
+"q\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|"
+"q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sourceforge.czt.z.jaxb.gen"
+".CompExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010ps"
+"q\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00004net.sourceforge.czt.t"
+"coz.jaxb.gen.ChannelExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000"
+"K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000"
+"(net.sourceforge.czt.z.jaxb.gen.TupleExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000"
+"\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~"
+"\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.z.jaxb.gen.Qnt1ExprElementq\u0000~"
+"\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~"
+"\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&net.sourceforge.czt.z.jaxb.gen.Pr"
+"eExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000"
+"\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000(net.sourceforge.czt.z.jax"
+"b.gen.PowerExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq"
+"\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000+net.sourceforge"
+".czt.z.jaxb.gen.Expr1Elementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008a"
+"ppsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000,ne"
+"t.sourceforge.czt.z.jaxb.gen.Expr0NElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~"
+"\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000"
+"~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge.czt.zpatt.jaxb.gen.JokerExprElem"
+"entq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000"
+"K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000)net.sourceforge.czt.z.jaxb."
+"gen.LambdaExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000"
+"~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&net.sourceforge."
+"czt.z.jaxb.gen.LetExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~"
+"\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000/net.sour"
+"ceforge.czt.z.jaxb.gen.DecorExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p"
+"\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 "
+"sq\u0000~\u0000!t\u0000&net.sourceforge.czt.z.jaxb.gen.NegExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K"
+"\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000"
+"~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000%net.sourceforge.czt.z.jaxb.gen.MuExprq\u0000~\u0000%s"
+"q\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010p"
+"q\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000(net.sourceforge.czt.oz.jaxb.gen.Self"
+"Exprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017"
+"\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sourceforge.czt.z.jaxb"
+".gen.ProjExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~"
+"\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.c"
+"zt.z.jaxb.gen.QntExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008a"
+"ppsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000&ne"
+"t.sourceforge.czt.z.jaxb.gen.IffExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq"
+"\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000"
+"~\u0000!t\u00000net.sourceforge.czt.z.jaxb.gen.RenameExprElementq\u0000~\u0000%s"
+"q\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010p"
+"q\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000/net.sourceforge.czt.oz.jaxb.gen.Cont"
+"ainmentExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010"
+"psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt"
+".z.jaxb.gen.BindExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008ap"
+"psq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000(net"
+".sourceforge.czt.oz.jaxb.gen.PolyExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095q\u0000~\u0000\u0010p\u0000s"
+"q\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq"
+"\u0000~\u0000!t\u0000*net.sourceforge.czt.z.jaxb.gen.ImpliesExprq\u0000~\u0000%q\u0000~\u0000 s"
+"q\u0000~\u0000\f\u0002Z\u0088\u0018ppsq\u0000~\u0000\u0017\u0002Z\u0088\rq\u0000~\u0000\u0010pq\u0000~\u0000+sq\u0000~\u0000!q\u0000~\u0000<q\u0000~\u0000=q\u0000~\u0000 sq\u0000~\u0000!t"
+"\u0000\u0006Branchq\u0000~\u0000@sr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHa"
+"sh;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8"
+"\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0001\u0096[\u0000\u0005tablet\u0000![Lcom/sun/"
+"msv/grammar/Expression;xp\u0000\u0000\u0000\u0097\u0000\u0000\u0000\u00e6pur\u0000![Lcom.sun.msv.grammar."
+"Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0002\u00ffppppppppppppppq\u0000~\u0000Appppppq\u0000~\u0000\tpp"
+"ppppppppppq\u0000~\u0000^ppppppppppq\u0000~\u0000hpppppq\u0000~\u0001\u0090ppppq\u0000~\u0000rppppppppppq"
+"\u0000~\u0000|pppppppppppppppppppppppppppppppppppq\u0000~\u0000Wpppppppq\u0000~\u0000&ppq\u0000"
+"~\u0000appppppppppq\u0000~\u0000kppppppppppq\u0000~\u0000uppppppppppq\u0000~\u0000\u007fpppppppppppp"
+"pppppppppppppppppppppppq\u0000~\u0000Zppppppppppq\u0000~\u0000dppppppppppq\u0000~\u0000nq\u0000"
+"~\u0001Jq\u0000~\u0001Dq\u0000~\u0001>q\u0000~\u00018q\u0000~\u00012q\u0000~\u0001,q\u0000~\u0001&q\u0000~\u0001 q\u0000~\u0001\u001aq\u0000~\u0001\u0014q\u0000~\u0001Iq\u0000~\u0001Cq\u0000"
+"~\u0001=q\u0000~\u00017q\u0000~\u00011q\u0000~\u0001+q\u0000~\u0000xq\u0000~\u0001%q\u0000~\u0001\u001fq\u0000~\u0001\u0019q\u0000~\u0001\u0013q\u0000~\u0001\rq\u0000~\u0001\u000eq\u0000~\u0001\u0007q\u0000"
+"~\u0001\bq\u0000~\u0001\u0001q\u0000~\u0001\u0002q\u0000~\u0000\u00fbq\u0000~\u0000\u00fcq\u0000~\u0000\u00f5q\u0000~\u0000\u00f6q\u0000~\u0000\u00efq\u0000~\u0000\u00f0q\u0000~\u0000\u00e9q\u0000~\u0000\u00eaq\u0000~\u0000\u00e3q\u0000"
+"~\u0000\u00e4q\u0000~\u0000\u00ddq\u0000~\u0000\u00deq\u0000~\u0000\u00d2q\u0000~\u0000\u00d1q\u0000~\u0000\u00d8q\u0000~\u0000\u00d7q\u0000~\u0000\u0016q\u0000~\u0000Dq\u0000~\u0000Lq\u0000~\u0000\u0084q\u0000~\u0000\u008aq\u0000"
+"~\u0000\u0013q\u0000~\u0000Cq\u0000~\u0000Kq\u0000~\u0000\u0083q\u0000~\u0000\u0089q\u0000~\u0000\u008fq\u0000~\u0000\u0095q\u0000~\u0000\u009bq\u0000~\u0000\u00a1q\u0000~\u0000\u00a7q\u0000~\u0000\u00adq\u0000~\u0000\u00b3q\u0000"
+"~\u0000\u00b9q\u0000~\u0000\u00bfq\u0000~\u0000\u00c5q\u0000~\u0000\u00cbq\u0000~\u0000\u0090q\u0000~\u0000\u0096q\u0000~\u0000\u009cq\u0000~\u0000\u00a2q\u0000~\u0000\u00a8q\u0000~\u0000\u00aeq\u0000~\u0000\u00b4q\u0000~\u0000\u00baq\u0000"
+"~\u0000\u00c0q\u0000~\u0000\u00c6q\u0000~\u0000\u00ccq\u0000~\u0000gq\u0000~\u0001Pq\u0000~\u0001Oq\u0000~\u0001Vq\u0000~\u0000qq\u0000~\u0001Uq\u0000~\u0001\\q\u0000~\u0001[q\u0000~\u0001bq\u0000"
+"~\u0001aq\u0000~\u0000]q\u0000~\u0001hq\u0000~\u0001gq\u0000~\u0001nq\u0000~\u0001mq\u0000~\u0000{q\u0000~\u0001tq\u0000~\u0001sq\u0000~\u0001zq\u0000~\u0001yq\u0000~\u0001\u0080q\u0000"
+"~\u0001\u007fq\u0000~\u0001\u0086q\u0000~\u0001\u0085q\u0000~\u0001\u008cq\u0000~\u0001\u008bppq\u0000~\u0000Pppppppppppppppppppppppq\u0000~\u0000Vppp"
+"pppppppq\u0000~\u0000\u0011q\u0000~\u0000`q\u0000~\u0000Uppppppppq\u0000~\u0000jppppppppppq\u0000~\u0000tq\u0000~\u0000\rppppp"
+"ppppq\u0000~\u0000~pppppppq\u0000~\u0000\u000bpppppppppppppppppppppppppppq\u0000~\u0000Yppppppp"
+"pppq\u0000~\u0000cppppppppppq\u0000~\u0000mppppppppppq\u0000~\u0000wppppppppppq\u0000~\u0000\u0081ppppppp"
+"ppppppppppppppppppppppppppppq\u0000~\u0000\\ppppppppppq\u0000~\u0000fppppppppppq\u0000"
+"~\u0000pppppppppppq\u0000~\u0000zpppppppppppppppq\u0000~\u0000Ipppppppppppppppppppppp"
+"ppppppppq\u0000~\u0000_ppppppppppq\u0000~\u0000ippppppppppq\u0000~\u0000sppppppppppq\u0000~\u0000}pp"
+"pppppppppppppppppppppppppppppppppq\u0000~\u0000Xppppppppppq\u0000~\u0000bppppppp"
+"pppq\u0000~\u0000lppppppppppq\u0000~\u0000vppppppppppq\u0000~\u0000\u0080pppppppppppppppppppppp"
+"pppppppppppppq\u0000~\u0000[ppppppppppq\u0000~\u0000eq\u0000~\u0000\npppppppppq\u0000~\u0000opppppppp"
+"ppq\u0000~\u0000ypppppppppppp"));
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
            return net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  1 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("Branch" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
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
                    case  2 :
                        if (("Branch" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.BranchImpl)net.sourceforge.czt.z.jaxb.gen.impl.BranchElementImpl.this).new Unmarshaller(context)), 2, value);
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
