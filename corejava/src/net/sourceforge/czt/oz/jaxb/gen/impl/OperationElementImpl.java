//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.10 at 09:41:23 NZST 
//


package net.sourceforge.czt.oz.jaxb.gen.impl;

public class OperationElementImpl
    extends net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl
    implements net.sourceforge.czt.oz.jaxb.gen.OperationElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.oz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.oz.jaxb.gen.OperationElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/object-z";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "Operation";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/object-z", "Operation");
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
        return (net.sourceforge.czt.oz.jaxb.gen.OperationElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\u0012T\u0014\u00afp"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\u0012T\u0014\u00a4ppsq\u0000~\u0000\u0007\u000fU&\u00dappsq\u0000~\u0000\u0007\u0006&\u00c5\u008eppsr\u0000\u001dcom.sun.msv.grammar.Choi"
+"ceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u00020\u007f\u00adppsq\u0000~\u0000\u0000\u00020\u007f\u00a2sr\u0000\u0011java.lang.Boolean\u00cd"
+" r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u00020\u007f\u0097ppsq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008app"
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
+"dummy-elementssq\u0000~\u0000\f\u0001\u00e4\u00ad\u00fdppsq\u0000~\u0000\u0017\u0001\u00e4\u00ad\u00f2q\u0000~\u0000\u0010psr\u0000\u001bcom.sun.msv.gr"
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
+"\u0000\u0003\u00f6E\u00dcpp\u0000sq\u0000~\u0000\u0007\u0003\u00f6E\u00d1ppsq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010"
+"psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000\'net.sourceforge.czt"
+".z.jaxb.gen.DeclNameq\u0000~\u0000%sq\u0000~\u0000\f\u0003\u00aat7ppsq\u0000~\u0000\u0017\u0003\u00aat,q\u0000~\u0000\u0010pq\u0000~\u0000+sq"
+"\u0000~\u0000!q\u0000~\u0000<q\u0000~\u0000=q\u0000~\u0000 sq\u0000~\u0000!t\u0000\u0004Namet\u0000#http://czt.sourceforge.ne"
+"t/object-zsq\u0000~\u0000\f\t.aGppsq\u0000~\u0000\f\b\u00e2\u008f\u00b0ppsq\u0000~\u0000\f\b\u0096\u00be\u0019ppsq\u0000~\u0000\f\bJ\u00ec\u0082ppsq"
+"\u0000~\u0000\f\u0007\u00ff\u001a\u00ebppsq\u0000~\u0000\f\u0007\u00b3ITppsq\u0000~\u0000\f\u0007gw\u00bdppsq\u0000~\u0000\f\u0007\u001b\u00a6&ppsq\u0000~\u0000\f\u0006\u00cf\u00d4\u008fppsq"
+"\u0000~\u0000\f\u0006\u0084\u0002\u00f8ppsq\u0000~\u0000\f\u000681appsq\u0000~\u0000\f\u0005\u00ec_\u00cappsq\u0000~\u0000\f\u0005\u00a0\u008e3ppsq\u0000~\u0000\f\u0005T\u00bc\u009cppsq"
+"\u0000~\u0000\f\u0005\b\u00eb\u0005ppsq\u0000~\u0000\f\u0004\u00bd\u0019nppsq\u0000~\u0000\f\u0004qG\u00d7ppsq\u0000~\u0000\f\u0004%v@ppsq\u0000~\u0000\f\u0003\u00d9\u00a4\u00a9ppsq"
+"\u0000~\u0000\f\u0003\u008d\u00d3\u0012ppsq\u0000~\u0000\f\u0003B\u0001{ppsq\u0000~\u0000\f\u0002\u00f6/\u00e4ppsq\u0000~\u0000\f\u0002\u00aa^Mppsq\u0000~\u0000\f\u0002^\u008c\u00b6ppsq"
+"\u0000~\u0000\f\u0002\u0012\u00bb\u001fppsq\u0000~\u0000\f\u0001\u00c6\u00e9\u0088ppsq\u0000~\u0000\f\u0001{\u0017\u00f1ppsq\u0000~\u0000\f\u0001/FZppsq\u0000~\u0000\f\u0000\u00e3t\u00c3ppsq"
+"\u0000~\u0000\f\u0000\u0097\u00a3,ppsq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1"
+"|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00004net.sourceforge.czt.oz.jaxb.g"
+"en.OperationExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000"
+"K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00002net.sourcef"
+"orge.czt.tcoz.jaxb.gen.InterruptProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000"
+"~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~"
+"\u0000!t\u00002net.sourceforge.czt.oz.jaxb.gen.AssoParallelOpExprq\u0000~\u0000%"
+"sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~"
+"\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00000net.sourceforge.czt.oz.jaxb.gen.DistCho"
+"iceOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000"
+"\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.oz.ja"
+"xb.gen.ParallelOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1"
+"\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000)net.sourcefor"
+"ge.czt.oz.jaxb.gen.SeqOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq"
+"\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00002net.so"
+"urceforge.czt.oz.jaxb.gen.BasicOpExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095p"
+"p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000"
+" sq\u0000~\u0000!t\u0000.net.sourceforge.czt.oz.jaxb.gen.DistConjOpExprq\u0000~\u0000"
+"%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000"
+"~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-net.sourceforge.czt.oz.jaxb.gen.DistSe"
+"qOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000"
+"K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00008net.sourceforge.czt.tcoz.ja"
+"xb.gen.DeadlineProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008apps"
+"q\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00005net.s"
+"ourceforge.czt.tcoz.jaxb.gen.TimeoutStartProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000"
+"K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001e"
+"q\u0000~\u0000 sq\u0000~\u0000!t\u0000.net.sourceforge.czt.oz.jaxb.gen.ExChoiceOpExpr"
+"q\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000"
+"\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge.czt.oz.jaxb.gen.Re"
+"nameOpExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~"
+"\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00002net.sourceforge.c"
+"zt.tcoz.jaxb.gen.AtProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1"
+"\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000-n"
+"et.sourceforge.czt.tcoz.jaxb.gen.StopProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095p"
+"p\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000"
+" sq\u0000~\u0000!t\u00000net.sourceforge.czt.tcoz.jaxb.gen.DivergeProExprq\u0000"
+"~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010p"
+"q\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00001net.sourceforge.czt.oz.jaxb.gen.Hide"
+"OpExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010ps"
+"q\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00008net.sourceforge.czt.t"
+"coz.jaxb.gen.TopologyProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000"
+"K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000"
+"-net.sourceforge.czt.tcoz.jaxb.gen.SkipProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1"
+"\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000"
+"~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElem"
+"entq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q"
+"\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00006net.sourceforge.czt.oz.jaxb.gen"
+".OpPromotionExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000"
+"K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourcef"
+"orge.czt.tcoz.jaxb.gen.InterleaveProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq"
+"\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000"
+"~\u0000!t\u00009net.sourceforge.czt.tcoz.jaxb.gen.WaitUntilProExprElem"
+"entq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q"
+"\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000+net.sourceforge.czt.oz.jaxb.gen"
+".ParenOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq"
+"\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u0000*net.sourceforge.czt.oz"
+".jaxb.gen.ConjOpExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007f"
+"q\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourceforg"
+"e.czt.oz.jaxb.gen.OperationBoxElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000"
+"\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!"
+"t\u00006net.sourceforge.czt.tcoz.jaxb.gen.SynPllProExprElementq\u0000~"
+"\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq"
+"\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00004net.sourceforge.czt.tcoz.jaxb.gen.Wai"
+"tProExprElementq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010"
+"psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00003net.sourceforge.czt"
+".tcoz.jaxb.gen.TimeoutEndProExprq\u0000~\u0000%sq\u0000~\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008a"
+"ppsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00005ne"
+"t.sourceforge.czt.tcoz.jaxb.gen.GuardProExprElementq\u0000~\u0000%sq\u0000~"
+"\u0000\u0000\u0000K\u00d1\u0095pp\u0000sq\u0000~\u0000\f\u0000K\u00d1\u008appsq\u0000~\u0000\u0014\u0000K\u00d1\u007fq\u0000~\u0000\u0010psq\u0000~\u0000\u0017\u0000K\u00d1|q\u0000~\u0000\u0010pq\u0000~\u0000\u001aq\u0000"
+"~\u0000\u001eq\u0000~\u0000 sq\u0000~\u0000!t\u00001net.sourceforge.czt.oz.jaxb.gen.ScopeEnrich"
+"OpExprq\u0000~\u0000%sq\u0000~\u0000\f\u0002\u00fe\u00ed\u00c5ppsq\u0000~\u0000\u0017\u0002\u00fe\u00ed\u00baq\u0000~\u0000\u0010pq\u0000~\u0000+sq\u0000~\u0000!q\u0000~\u0000<q\u0000~\u0000="
+"q\u0000~\u0000 sq\u0000~\u0000!t\u0000\tOperationq\u0000~\u0000Nsr\u0000\"com.sun.msv.grammar.Expressi"
+"onPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/Expressi"
+"onPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$C"
+"losedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0001-[\u0000\u0005tab"
+"let\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000i\u0000\u0000\u0000rpur\u0000![Lcom.s"
+"un.msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0001\u007fpppppppq\u0000~\u0000lppppp"
+"pppq\u0000~\u0000jppppppppq\u0000~\u0000hppppppppq\u0000~\u0000fppppppppq\u0000~\u0000dppppppppq\u0000~\u0000b"
+"ppppppq\u0000~\u0000\u0011pq\u0000~\u0000`ppppppppq\u0000~\u0000^ppppppppq\u0000~\u0000\\pq\u0000~\u0000\rppppppq\u0000~\u0000Z"
+"ppppppppq\u0000~\u0000Xppppppppq\u0000~\u0000Vppppppppq\u0000~\u0000Tppppppppq\u0000~\u0000Rpppppppp"
+"q\u0000~\u0000Pppppppppppppppppppppppppppppppppppppppq\u0000~\u0000\u00bdq\u0000~\u0000\u00b7q\u0000~\u0000\u00b1q\u0000"
+"~\u0000\u00abq\u0000~\u0000\u00a5q\u0000~\u0000\u009fq\u0000~\u0000\u0099q\u0000~\u0000\u0093q\u0000~\u0000\u008dq\u0000~\u0000\u0087q\u0000~\u0000\u0081q\u0000~\u0000\u00bcq\u0000~\u0000\u00b6q\u0000~\u0000\u00b0q\u0000~\u0000\u00aaq\u0000"
+"~\u0000\u00a4q\u0000~\u0000\u009eq\u0000~\u0000\u0098q\u0000~\u0000\u0092q\u0000~\u0000\u008cq\u0000~\u0000\u0086q\u0000~\u0000\u0080q\u0000~\u0000zq\u0000~\u0000tq\u0000~\u0000nq\u0000~\u0000Dq\u0000~\u0000\u0013q\u0000"
+"~\u0000{q\u0000~\u0000uq\u0000~\u0000oq\u0000~\u0000Eq\u0000~\u0000kq\u0000~\u0000\u0016q\u0000~\u0000Bq\u0000~\u0000\u00c8q\u0000~\u0000\u00c9q\u0000~\u0000\u00c2q\u0000~\u0000\u00c3q\u0000~\u0000\u00cfq\u0000"
+"~\u0000\u00ceq\u0000~\u0000iq\u0000~\u0000\u00d5q\u0000~\u0000\u00d4q\u0000~\u0000\u00dbq\u0000~\u0000\u00daq\u0000~\u0000\u00e1q\u0000~\u0000\u00e0q\u0000~\u0000\u00e7q\u0000~\u0000\u00e6q\u0000~\u0000gq\u0000~\u0000\u00edq\u0000"
+"~\u0000\u00ecq\u0000~\u0000\u00f3q\u0000~\u0000\u00f2q\u0000~\u0000\u00f9q\u0000~\u0000\u00f8q\u0000~\u0000\u00ffq\u0000~\u0000\u00feq\u0000~\u0000eq\u0000~\u0001\u0005q\u0000~\u0001\u0004q\u0000~\u0001\u000bq\u0000~\u0001\nq\u0000"
+"~\u0001\u0011q\u0000~\u0001\u0010q\u0000~\u0001\u0017q\u0000~\u0001\u0016q\u0000~\u0000cq\u0000~\u0001\u001dq\u0000~\u0001\u001cq\u0000~\u0001#q\u0000~\u0000&q\u0000~\u0001\"q\u0000~\u0000\nq\u0000~\u0000\tpq"
+"\u0000~\u0000appppppppq\u0000~\u0000_ppppppppq\u0000~\u0000]ppppppppq\u0000~\u0000[ppppppppq\u0000~\u0000Ypppp"
+"pppq\u0000~\u0000\u000bq\u0000~\u0000Wppppppppq\u0000~\u0000Uppppppppq\u0000~\u0000Sppppppppq\u0000~\u0000Qpppppppp"
+"q\u0000~\u0000Opppppppppppppppppppppppppq\u0000~\u0001\'pppppppppppppppppppppppq\u0000"
+"~\u0000Ippp"));
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
            return net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this;
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
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("Operation" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
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
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("Operation" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.oz.jaxb.gen.impl.OperationImpl)net.sourceforge.czt.oz.jaxb.gen.impl.OperationElementImpl.this).new Unmarshaller(context)), 2, value);
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
