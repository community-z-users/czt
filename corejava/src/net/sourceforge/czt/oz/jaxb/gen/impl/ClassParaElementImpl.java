//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.13 at 03:14:32 NZST 
//


package net.sourceforge.czt.oz.jaxb.gen.impl;

public class ClassParaElementImpl
    extends net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl
    implements net.sourceforge.czt.oz.jaxb.gen.ClassParaElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.oz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.oz.jaxb.gen.ClassParaElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/object-z";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "ClassPara";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/object-z", "ClassPara");
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
        return (net.sourceforge.czt.oz.jaxb.gen.ClassParaElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp*+\n\u00a6p"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004*+\n\u009bppsq\u0000~\u0000\u0007)\u0011gYppsq\u0000~\u0000\u0007$F]\u00d3ppsq\u0000~\u0000\u0007\u001e\u001c\u0091\u00fbppsq\u0000~\u0000\u0007\u0018\u00d1bnppsq\u0000~"
+"\u0000\u0007\u0013\u0011\u00cb\"ppsq\u0000~\u0000\u0007\r\u00103$ppsq\u0000~\u0000\u0007\n\u00867Xppsq\u0000~\u0000\u0007\u0005FITppsr\u0000\u001dcom.sun.msv."
+"grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0002UB1ppsq\u0000~\u0000\u0000\u0002UB&sr\u0000\u0011java.l"
+"ang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0002UB\u001bppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000"
+"sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0001"
+"\u00f6\u00ef\rq\u0000~\u0000\u0016psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003e"
+"xpq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016psr\u00002com.sun.msv.gram"
+"mar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000"
+"\u0015\u0001q\u0000~\u0000 sr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dco"
+"m.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gram"
+"mar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000!q\u0000"
+"~\u0000&sr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tloca"
+"lNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000(xq\u0000~\u0000#t\u0000-net.s"
+"ourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.c"
+"om/jaxb/xjc/dummy-elementssq\u0000~\u0000\u0012\u0000^R\u00f3ppsq\u0000~\u0000\u001d\u0000^R\u00e8q\u0000~\u0000\u0016psr\u0000\u001bco"
+"m.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/dat"
+"atype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/Str"
+"ingPair;xq\u0000~\u0000\u0004\u0000O;\u00b2ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnames"
+"paceUriq\u0000~\u0000(L\u0000\btypeNameq\u0000~\u0000(L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/dat"
+"atype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3.org/2001/XM"
+"LSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.WhiteSpaceProces"
+"sor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteSpa"
+"ceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$N"
+"ullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\nq\u0000~\u0000\u0016psr\u0000\u001bcom.sun.msv.u"
+"til.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000(L\u0000\fnamespaceURIq\u0000~"
+"\u0000(xpq\u0000~\u00009q\u0000~\u00008sq\u0000~\u0000\'t\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSche"
+"ma-instanceq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/z"
+"mlq\u0000~\u0000&sq\u0000~\u0000\u0000\u0002\u00f1\u0007\u001epp\u0000sq\u0000~\u0000\u0007\u0002\u00f1\u0007\u0013ppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000"
+"~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000\'net.sou"
+"rceforge.czt.z.jaxb.gen.DeclNameq\u0000~\u0000+sq\u0000~\u0000\u0012\u0000\u00fa\u0017\u00ebppsq\u0000~\u0000\u001d\u0000\u00fa\u0017\u00e0q"
+"\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u0004Namet\u0000#http://czt.so"
+"urceforge.net/object-zsq\u0000~\u0000\u0012\u0005?\u00ed\u00ffppsq\u0000~\u0000\u0012\u0005?\u00ed\u00f4q\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001\u00f6\u00ef#"
+"q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000"
+"$q\u0000~\u0000&sq\u0000~\u0000\'t\u00007net.sourceforge.czt.oz.jaxb.gen.FormalParamet"
+"ersElementq\u0000~\u0000+sq\u0000~\u0000\u0000\u0003H\u00fe\u00cfq\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0003H\u00fe\u00c4ppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000"
+"~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~"
+"\u0000\'t\u00000net.sourceforge.czt.oz.jaxb.gen.FormalParametersq\u0000~\u0000+sq"
+"\u0000~\u0000\u0012\u0001R\u000f\u009cppsq\u0000~\u0000\u001d\u0001R\u000f\u0091q\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000"
+"\u0010FormalParametersq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0002\u0089\u00fb\u00c7ppsq\u0000~\u0000\u0000\u0002\u0089\u00fb\u00bcq\u0000~\u0000\u0016p\u0000sq\u0000~"
+"\u0000\u0007\u0002\u0089\u00fb\u00b1ppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq"
+"\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000+net.sourceforge.czt.oz.jaxb.gen"
+".RefNameListq\u0000~\u0000+sq\u0000~\u0000\u0012\u0000\u0093\f\u0089ppsq\u0000~\u0000\u001d\u0000\u0093\f~q\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000"
+"Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u000eVisibilityListq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0006\u0001\u0097\u00f9ppsq\u0000~"
+"\u0000\u001a\u0006\u0001\u0097\u00eeq\u0000~\u0000\u0016psq\u0000~\u0000\u0012\u0006\u0001\u0097\u00ebq\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001\u00f6\u00ef#q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000"
+"~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u00005net.sou"
+"rceforge.czt.oz.jaxb.gen.InheritedClassElementq\u0000~\u0000+sq\u0000~\u0000\u0000\u0004\n\u00a8"
+"\u00c6q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0004\n\u00a8\u00bbppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016"
+"psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000.net.sourceforge.czt"
+".oz.jaxb.gen.InheritedClassq\u0000~\u0000+sq\u0000~\u0000\u0012\u0002\u0013\u00b9\u0093ppsq\u0000~\u0000\u001d\u0002\u0013\u00b9\u0088q\u0000~\u0000\u0016p"
+"q\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u000eInheritedClassq\u0000~\u0000Tq\u0000~\u0000&s"
+"q\u0000~\u0000\u0012\u0005\u00bf\u0097Gppsq\u0000~\u0000\u0012\u0005\u00bf\u0097<q\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001\u00f6\u00ef#q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~"
+"\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000/net.sour"
+"ceforge.czt.oz.jaxb.gen.LocalDefElementq\u0000~\u0000+sq\u0000~\u0000\u0000\u0003\u00c8\u00a8\u0017q\u0000~\u0000\u0016p"
+"\u0000sq\u0000~\u0000\u0007\u0003\u00c8\u00a8\fppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d"
+"\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000(net.sourceforge.czt.oz.jax"
+"b.gen.LocalDefq\u0000~\u0000+sq\u0000~\u0000\u0012\u0001\u00d1\u00b8\u00e4ppsq\u0000~\u0000\u001d\u0001\u00d1\u00b8\u00d9q\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000"
+"~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\bLocalDefq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0005K/\u0088ppsq\u0000~\u0000\u0012\u0005K"
+"/}q\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001\u00f6\u00ef#q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001"
+"\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000,net.sourceforge.czt.oz.jaxb"
+".gen.StateElementq\u0000~\u0000+sq\u0000~\u0000\u0000\u0003T@Xq\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0003T@Mppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef"
+"#pp\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000"
+"~\u0000&sq\u0000~\u0000\'t\u0000%net.sourceforge.czt.oz.jaxb.gen.Stateq\u0000~\u0000+sq\u0000~\u0000\u0012"
+"\u0001]Q%ppsq\u0000~\u0000\u001d\u0001]Q\u001aq\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\u0005Sta"
+"teq\u0000~\u0000Tq\u0000~\u0000&sq\u0000~\u0000\u0012\u0006)\u00cb\u00d3ppsq\u0000~\u0000\u0012\u0006)\u00cb\u00c8q\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001\u00f6\u00ef#q\u0000~\u0000\u0016p\u0000sq\u0000"
+"~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~"
+"\u0000\'t\u00003net.sourceforge.czt.oz.jaxb.gen.InitialStateElementq\u0000~\u0000"
+"+sq\u0000~\u0000\u0000\u00042\u00dc\u00a3q\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u00042\u00dc\u0098ppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000"
+"\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000,net.sourc"
+"eforge.czt.oz.jaxb.gen.InitialStateq\u0000~\u0000+sq\u0000~\u0000\u0012\u0002;\u00edpppsq\u0000~\u0000\u001d\u0002;"
+"\u00edeq\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\fInitialStateq\u0000~\u0000T"
+"q\u0000~\u0000&sq\u0000~\u0000\u0012\u0004\u00cb\t\u0081ppsq\u0000~\u0000\u001a\u0004\u00cb\tvq\u0000~\u0000\u0016psq\u0000~\u0000\u0012\u0004\u00cb\tsq\u0000~\u0000\u0016psq\u0000~\u0000\u0000\u0001\u00f6\u00ef#q"
+"\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$"
+"q\u0000~\u0000&sq\u0000~\u0000\'t\u00000net.sourceforge.czt.oz.jaxb.gen.OperationEleme"
+"ntq\u0000~\u0000+sq\u0000~\u0000\u0000\u0002\u00d4\u001aNq\u0000~\u0000\u0016p\u0000sq\u0000~\u0000\u0007\u0002\u00d4\u001aCppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\u0012\u0001\u00f6\u00ef\u0018p"
+"psq\u0000~\u0000\u001a\u0001\u00f6\u00ef\rq\u0000~\u0000\u0016psq\u0000~\u0000\u001d\u0001\u00f6\u00ef\nq\u0000~\u0000\u0016pq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000)net"
+".sourceforge.czt.oz.jaxb.gen.Operationq\u0000~\u0000+sq\u0000~\u0000\u0012\u0000\u00dd+\u001bppsq\u0000~\u0000"
+"\u001d\u0000\u00dd+\u0010q\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&sq\u0000~\u0000\'t\u0000\tOperationq\u0000~\u0000T"
+"q\u0000~\u0000&sq\u0000~\u0000\u0012\u0001\u0019\u00a3=ppsq\u0000~\u0000\u001d\u0001\u0019\u00a32q\u0000~\u0000\u0016pq\u0000~\u00001sq\u0000~\u0000\'q\u0000~\u0000Bq\u0000~\u0000Cq\u0000~\u0000&s"
+"q\u0000~\u0000\'t\u0000\tClassParaq\u0000~\u0000Tsr\u0000\"com.sun.msv.grammar.ExpressionPool"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool"
+"$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedH"
+"ash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000\u00e9[\u0000\u0005tablet\u0000!["
+"Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000J\u0000\u0000\u0000rpur\u0000![Lcom.sun.msv"
+".grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0001\u007fpq\u0000~\u0000\u0097ppppppppq\u0000~\u0000\u00c1pppp"
+"pppppq\u0000~\u0000\rq\u0000~\u0000Opq\u0000~\u0000\tppppq\u0000~\u0000\u00cfppq\u0000~\u0000\u00cepppppq\u0000~\u0000lppq\u0000~\u0000zpq\u0000~\u0000\u00cd"
+"q\u0000~\u0000yppppppppppq\u0000~\u0000xq\u0000~\u0000\u00bcq\u0000~\u0000\u00afq\u0000~\u0000\u00a7q\u0000~\u0000\u009aq\u0000~\u0000\u0092q\u0000~\u0000\u0085q\u0000~\u0000}q\u0000~\u0000o"
+"q\u0000~\u0000aq\u0000~\u0000Yq\u0000~\u0000Kq\u0000~\u0000\u00bbq\u0000~\u0000\u00aeq\u0000~\u0000\u00a6q\u0000~\u0000\u0099q\u0000~\u0000\u0091q\u0000~\u0000\u0084q\u0000~\u0000|q\u0000~\u0000nq\u0000~\u0000`"
+"q\u0000~\u0000Xq\u0000~\u0000Jq\u0000~\u0000\u0019q\u0000~\u0000\u001cq\u0000~\u0000jq\u0000~\u0000\u00c3q\u0000~\u0000\u0017q\u0000~\u0000\u00c4q\u0000~\u0000\u00d2q\u0000~\u0000\u00d1q\u0000~\u0000\u00daq\u0000~\u0000\u00d9"
+"ppppq\u0000~\u0000\u008fppppppppq\u0000~\u0000\u00b9pq\u0000~\u0000\u008eq\u0000~\u0000\u0013q\u0000~\u0000Hq\u0000~\u0000\u000bpppppq\u0000~\u0000\u00b8ppppppp"
+"pppppppppppppppppppppppppppq\u0000~\u0000eppq\u0000~\u0000\npppppppppppq\u0000~\u0000\u00b3ppppp"
+"ppppppq\u0000~\u0000\u0010ppppppppppppppppppppppppppppppppppppppppppppppppq"
+"\u0000~\u0000\u0011pppppq\u0000~\u0000^ppppppppq\u0000~\u0000\u000fpq\u0000~\u0000\u00depppq\u0000~\u0000\u00acpppppppq\u0000~\u0000\u0089q\u0000~\u0000\u00e3pp"
+"pppppppppppppppppppppppppppppppppppppppppq\u0000~\u0000\u000epppppq\u0000~\u0000\u009epppp"
+"ppppq\u0000~\u0000\u00c8ppppppq\u0000~\u0000Vppq\u0000~\u0000\u00d7pppppppq\u0000~\u0000Upppq\u0000~\u0000\u00a4q\u0000~\u0000\u0082pppq\u0000~\u0000s"
+"pppppq\u0000~\u0000\u00a3ppppppppppppppppppppppppq\u0000~\u0000\fppppppppppppq\u0000~\u0000,"));
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
            return net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this;
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
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("ClassPara" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
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
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("ClassPara" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaImpl)net.sourceforge.czt.oz.jaxb.gen.impl.ClassParaElementImpl.this).new Unmarshaller(context)), 2, value);
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
