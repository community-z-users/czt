//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.04.21 at 09:33:05 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen.impl;

public class ParallelProcessRIElementImpl
    extends net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl
    implements net.sourceforge.czt.circus.jaxb.gen.ParallelProcessRIElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.circus.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.circus.jaxb.gen.ParallelProcessRIElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/circus";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "ParallelProcessRI";
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/circus", "ParallelProcessRI");
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
        return (net.sourceforge.czt.circus.jaxb.gen.ParallelProcessRIElement.class);
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
+"t\u0000\u001ehttp://czt.sourceforge.net/zmlq\u0000~\u0000!sq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\r"
+"ppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq"
+"\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\r"
+"ppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000<net.sourceforge.czt.circus.ja"
+"xb.gen.ParallelProcessRIElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q"
+"\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00008net.sourceforge.czt"
+".circus.jaxb.gen.RenameProcessElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rpps"
+"q\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00006net.sourcefor"
+"ge.czt.circus.jaxb.gen.ExtChoiceProcessRIq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000"
+"\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00004net.sourc"
+"eforge.czt.circus.jaxb.gen.ActualGenProcessq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000"
+"~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000/net.sou"
+"rceforge.czt.circus.jaxb.gen.SeqProcessRq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\r"
+"ppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000;net.source"
+"forge.czt.circus.jaxb.gen.ParallelProcessRElementq\u0000~\u0000&sq\u0000~\u0000\u0000"
+"pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.n"
+"et.sourceforge.czt.circus.jaxb.gen.SeqProcessq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000s"
+"q\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00006net.s"
+"ourceforge.czt.circus.jaxb.gen.IntChoiceProcessRIq\u0000~\u0000&sq\u0000~\u0000\u0000"
+"pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00000n"
+"et.sourceforge.czt.circus.jaxb.gen.SeqProcessRIq\u0000~\u0000&sq\u0000~\u0000\u0000pp"
+"\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00005net"
+".sourceforge.czt.circus.jaxb.gen.ExtChoiceProcessRq\u0000~\u0000&sq\u0000~\u0000"
+"\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00008"
+"net.sourceforge.czt.circus.jaxb.gen.InstantiationProcessq\u0000~\u0000"
+"&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000"
+"~\u0000\"t\u00007net.sourceforge.czt.circus.jaxb.gen.BasicProcessElemen"
+"tq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~"
+"\u0000!sq\u0000~\u0000\"t\u00006net.sourceforge.czt.circus.jaxb.gen.CallProcessEl"
+"ementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000"
+"\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00004net.sourceforge.czt.circus.jaxb.gen.IntChoice"
+"Processq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000"
+"~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00004net.sourceforge.czt.circus.jaxb.gen.ExtChoi"
+"ceProcessq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001b"
+"q\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00007net.sourceforge.czt.circus.jaxb.gen.Inter"
+"leaveProcessRIq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011p"
+"q\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00006net.sourceforge.czt.circus.jaxb.gen."
+"ActualParamProcessq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000"
+"~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00005net.sourceforge.czt.circus.jaxb."
+"gen.InterleaveProcessq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00006net.sourceforge.czt.circus.ja"
+"xb.gen.HideProcessElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011ps"
+"q\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000:net.sourceforge.czt.circu"
+"s.jaxb.gen.ParallelProcessElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000"
+"\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00006net.sourceforge.c"
+"zt.circus.jaxb.gen.InterleaveProcessRq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rpps"
+"q\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00005net.sourcefor"
+"ge.czt.circus.jaxb.gen.IntChoiceProcessRq\u0000~\u0000&sq\u0000~\u0000\u0015ppsq\u0000~\u0000\rp"
+"psq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000"
+"~\u0000\"t\u0000-net.sourceforge.czt.z.jaxb.gen.VarDeclElementq\u0000~\u0000&sq\u0000~"
+"\u0000\u0000pp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq"
+"\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000&net.sourceforge.czt.z.jaxb.gen.VarDeclq\u0000~\u0000"
+"&sq\u0000~\u0000\rppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000,q\u0000~\u0000<q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0007VarDeclq\u0000~\u0000Asq\u0000"
+"~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\rppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq"
+"\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00008net.sourceforge.czt.circus"
+".jaxb.gen.DifferenceChannelSetq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000"
+"~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00003net.sourceforge.czt."
+"circus.jaxb.gen.UnionChannelSetq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rppsq\u0000~\u0000\u0015q"
+"\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00008net.sourceforge.czt"
+".circus.jaxb.gen.RefChannelSetElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\rpps"
+"q\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000:net.sourcefor"
+"ge.czt.circus.jaxb.gen.BasicChannelSetElementq\u0000~\u0000&sq\u0000~\u0000\u0000pp\u0000s"
+"q\u0000~\u0000\rppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00007net.s"
+"ourceforge.czt.circus.jaxb.gen.IntersectChannelSetq\u0000~\u0000&sq\u0000~\u0000"
+"\rppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000,q\u0000~\u0000<q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0011ParallelProcessRIt\u0000!h"
+"ttp://czt.sourceforge.net/circussr\u0000\"com.sun.msv.grammar.Expr"
+"essionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/Expr"
+"essionPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPo"
+"ol$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006parentt\u0000$"
+"Lcom/sun/msv/grammar/ExpressionPool;xp\u0000\u0000\u0000a\u0001pq\u0000~\u0000Fq\u0000~\u0000Kq\u0000~\u0000\nq"
+"\u0000~\u0000Uq\u0000~\u0000\u00f1q\u0000~\u0000Oq\u0000~\u0000\u0012q\u0000~\u0000\u00e4q\u0000~\u0000Vq\u0000~\u0000\fq\u0000~\u0000\u00f2q\u0000~\u0000\u00dbq\u0000~\u0000Gq\u0000~\u0000\u000eq\u0000~\u0000Lq"
+"\u0000~\u0000Cq\u0000~\u0000\u00bfq\u0000~\u0000\u00b9q\u0000~\u0000\u00b3q\u0000~\u0000\u00adq\u0000~\u0000\u00a7q\u0000~\u0000\u00a1q\u0000~\u0000\u009bq\u0000~\u0000\u0095q\u0000~\u0000\u008fq\u0000~\u0000\u0089q\u0000~\u0000\u0083q"
+"\u0000~\u0000}q\u0000~\u0000\u00beq\u0000~\u0000\u00b8q\u0000~\u0000\u00b2q\u0000~\u0000\u00acq\u0000~\u0000\u00a6q\u0000~\u0000\u00a0q\u0000~\u0000\u009aq\u0000~\u0000\u0094q\u0000~\u0000\u008eq\u0000~\u0000\u0088q\u0000~\u0000\u0082q"
+"\u0000~\u0000|q\u0000~\u0000vq\u0000~\u0000Sq\u0000~\u0000pq\u0000~\u0000jq\u0000~\u0000\'q\u0000~\u0000dq\u0000~\u0000^q\u0000~\u0000Xq\u0000~\u0000\u0014q\u0000~\u0000wq\u0000~\u0000qq"
+"\u0000~\u0000kq\u0000~\u0000eq\u0000~\u0000_q\u0000~\u0000Yq\u0000~\u0000\u0017q\u0000~\u0000\u00c5q\u0000~\u0000Jq\u0000~\u0000\u00c4q\u0000~\u0000Eq\u0000~\u0000\u00cbq\u0000~\u0000\u00caq\u0000~\u0000\u00d1q"
+"\u0000~\u0000\u00d0q\u0000~\u0000\u00d7q\u0000~\u0000\u00d6q\u0000~\u0000\u00dfq\u0000~\u0000\u00deq\u0000~\u0000\u00e7q\u0000~\u0000\u00e6q\u0000~\u0000\u00ebq\u0000~\u0000\u00f5q\u0000~\u0000\u00f4q\u0000~\u0000\u00fbq\u0000~\u0000\u00faq"
+"\u0000~\u0001\u0001q\u0000~\u0001\u0000q\u0000~\u0001\u0007q\u0000~\u0001\u0006q\u0000~\u0001\rq\u0000~\u0001\fq\u0000~\u0000\u00efq\u0000~\u0001\u0011q\u0000~\u0000Pq\u0000~\u0000\tq\u0000~\u0000Qq\u0000~\u0000Tq"
+"\u0000~\u0000\u00f0q\u0000~\u0000Rq\u0000~\u0000Iq\u0000~\u0000Bq\u0000~\u0000Dq\u0000~\u0000\u00dcq\u0000~\u0000Hq\u0000~\u0000Nq\u0000~\u0000\u000bq\u0000~\u0000Mx"));
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
            return net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this;
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
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ParallelProcessRI" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("RenameProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExtChoiceProcessRI" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ActualGenProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SeqProcessR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ParallelProcessR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SeqProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IntChoiceProcessRI" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SeqProcessRI" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExtChoiceProcessR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InstantiationProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("BasicProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("CallProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IntChoiceProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExtChoiceProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InterleaveProcessRI" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ActualParamProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InterleaveProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("HideProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ParallelProcess" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InterleaveProcessR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IntChoiceProcessR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ProcessDef" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ProcessDef" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("ParallelProcessRI" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
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
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("ParallelProcessRI" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ParallelProcessRIElementImpl.this).new Unmarshaller(context)), 2, value);
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
