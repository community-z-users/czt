//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2003.11.03 at 03:50:09 NZDT 
//


package net.sourceforge.czt.oz.jaxb.gen.impl;

public class InitialStateElementImpl
    extends net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl
    implements net.sourceforge.czt.oz.jaxb.gen.InitialStateElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.oz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.oz.jaxb.gen.InitialStateElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/object-z";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "InitialState";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/object-z", "InitialState");
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
        return (net.sourceforge.czt.oz.jaxb.gen.InitialStateElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\u0007\u009f\u0094\u00d0p"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\u0007\u009f\u0094\u00c5ppsq\u0000~\u0000\u0007\u0007\u0005`[ppsr\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0000\u0083\u001d\u00b5ppsq\u0000~\u0000\u0000\u0000\u0083\u001d\u00aasr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000"
+"\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0000\u0083\u001d\u009fppsq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsr\u0000 com.sun."
+"msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar.U"
+"naryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0000h$\u0012q\u0000~\u0000\u000fpsr\u0000 com.sun.msv"
+".grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001"
+"xq\u0000~\u0000\u0004\u0000h$\u000fq\u0000~\u0000\u000fpsr\u00002com.sun.msv.grammar.Expression$AnyString"
+"Expression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000\u000e\u0001q\u0000~\u0000\u0019sr\u0000 com.sun.msv.g"
+"rammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameCl"
+"ass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$EpsilonEx"
+"pression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001aq\u0000~\u0000\u001fsr\u0000#com.sun.msv.gramm"
+"ar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/Strin"
+"g;L\u0000\fnamespaceURIq\u0000~\u0000!xq\u0000~\u0000\u001ct\u0000-net.sourceforge.czt.z.jaxb.ge"
+"n.TermA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/dummy-elemen"
+"tssq\u0000~\u0000\u000b\u0000\u001a\u00f9rppsq\u0000~\u0000\u0016\u0000\u001a\u00f9gq\u0000~\u0000\u000fpsr\u0000\u001bcom.sun.msv.grammar.DataEx"
+"p\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Datatype;L\u0000\u0006except"
+"q\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~\u0000\u0004\u0000\u0014t\u00fappsr\u0000\""
+"com.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv"
+".datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.da"
+"tatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.x"
+"sd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000!L\u0000\btypeNameq"
+"\u0000~\u0000!L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/datatype/xsd/WhiteSpaceProc"
+"essor;xpt\u0000 http://www.w3.org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.s"
+"un.msv.datatype.xsd.WhiteSpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000,com.sun.msv.datatype.xsd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xp"
+"sr\u00000com.sun.msv.grammar.Expression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001"
+"\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\nq\u0000~\u0000\u000fpsr\u0000\u001bcom.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000"
+"\u0002L\u0000\tlocalNameq\u0000~\u0000!L\u0000\fnamespaceURIq\u0000~\u0000!xpq\u0000~\u00002q\u0000~\u00001sq\u0000~\u0000 t\u0000\u0004t"
+"ypet\u0000)http://www.w3.org/2001/XMLSchema-instanceq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000"
+"\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/zmlq\u0000~\u0000\u001fsq\u0000~\u0000\u0013\u0006\u0082B\u00a1ppsq\u0000~\u0000"
+"\u000b\u0006\u0082B\u009eppsq\u0000~\u0000\u000b\u0006\u001a\u001etppsq\u0000~\u0000\u000b\u0005\u00b1\u00faJppsq\u0000~\u0000\u000b\u0005I\u00d6 ppsq\u0000~\u0000\u000b\u0004\u00e1\u00b1\u00f6ppsq\u0000~\u0000"
+"\u000b\u0004y\u008d\u00ccppsq\u0000~\u0000\u000b\u0004\u0011i\u00a2ppsq\u0000~\u0000\u000b\u0003\u00a9Exppsq\u0000~\u0000\u000b\u0003A!Nppsq\u0000~\u0000\u000b\u0002\u00d8\u00fd$ppsq\u0000~\u0000"
+"\u000b\u0002p\u00d8\u00fappsq\u0000~\u0000\u000b\u0002\b\u00b4\u00d0ppsq\u0000~\u0000\u000b\u0001\u00a0\u0090\u00a6ppsq\u0000~\u0000\u000b\u00018l|ppsq\u0000~\u0000\u000b\u0000\u00d0HRppsq\u0000~\u0000"
+"\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~"
+"\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\'net.sourceforge.czt.z.jaxb.gen.TruePredq\u0000~\u0000$"
+"sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~"
+"\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000)net.sourceforge.czt.z.jaxb.gen.ExistsPr"
+"edq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000"
+"~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000-net.sourceforge.czt.z.jaxb.gen.Q"
+"ntPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fps"
+"q\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u00003net.sourceforge.czt.z"
+"patt.jaxb.gen.JokerPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dpp"
+"sq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000%net."
+"sourceforge.czt.z.jaxb.gen.OrPredq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$"
+"\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000+n"
+"et.sourceforge.czt.z.jaxb.gen.Pred2Elementq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000"
+"sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fs"
+"q\u0000~\u0000 t\u0000)net.sourceforge.czt.z.jaxb.gen.ForallPredq\u0000~\u0000$sq\u0000~\u0000\u0000"
+"\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000"
+"\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000(net.sourceforge.czt.z.jaxb.gen.FalsePredq\u0000~\u0000$"
+"sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~"
+"\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000.net.sourceforge.czt.z.jaxb.gen.ExprPred"
+"Elementq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000"
+"h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000*net.sourceforge.czt.z.jaxb."
+"gen.Exists1Predq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000f"
+"psq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000-net.sourceforge.czt"
+".z.jaxb.gen.NegPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~"
+"\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000-net.sour"
+"ceforge.czt.z.jaxb.gen.AndPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000"
+"\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 "
+"t\u0000&net.sourceforge.czt.z.jaxb.gen.IffPredq\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000s"
+"q\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq"
+"\u0000~\u0000 t\u0000-net.sourceforge.czt.z.jaxb.gen.MemPredElementq\u0000~\u0000$sq\u0000"
+"~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q"
+"\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000*net.sourceforge.czt.z.jaxb.gen.ImpliesPred"
+"q\u0000~\u0000$sq\u0000~\u0000\u0000\u0000h$(pp\u0000sq\u0000~\u0000\u000b\u0000h$\u001dppsq\u0000~\u0000\u0013\u0000h$\u0012q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000h$\u000fq\u0000~\u0000"
+"\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000*net.sourceforge.czt.z.jaxb.gen.Fac"
+"tElementq\u0000~\u0000$sq\u0000~\u0000\u000b\u0000\u009a4eppsq\u0000~\u0000\u0016\u0000\u009a4Zq\u0000~\u0000\u000fpq\u0000~\u0000*sq\u0000~\u0000 q\u0000~\u0000;q\u0000~"
+"\u0000<q\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\fInitialStatet\u0000#http://czt.sourceforge.net/ob"
+"ject-zsr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bex"
+"pTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHash;xpsr"
+"\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000"
+"\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000\u00b7[\u0000\u0005tablet\u0000![Lcom/sun/msv/gra"
+"mmar/Expression;xp\u0000\u0000\u00008\u0000\u0000\u00009pur\u0000![Lcom.sun.msv.grammar.Express"
+"ion;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0000\u00bfq\u0000~\u0000{q\u0000~\u0000Iq\u0000~\u0000\u0081q\u0000~\u0000Hq\u0000~\u0000\u0087q\u0000~\u0000Gq\u0000~\u0000\u008eq\u0000~\u0000"
+"\u008dq\u0000~\u0000Fq\u0000~\u0000\u0094q\u0000~\u0000\u0093q\u0000~\u0000Eq\u0000~\u0000\u009aq\u0000~\u0000\u0099q\u0000~\u0000Dq\u0000~\u0000\u00a0q\u0000~\u0000\u009fq\u0000~\u0000Cq\u0000~\u0000\u00a6q\u0000~\u0000"
+"\u00a5q\u0000~\u0000Bq\u0000~\u0000\u00acq\u0000~\u0000\u00abq\u0000~\u0000Aq\u0000~\u0000@pppppppppppppppppppppppppppppppppp"
+"pppppq\u0000~\u0000\tppppppppppppppppppppppppq\u0000~\u0000%pq\u0000~\u0000\u0010pppppppppppq\u0000~\u0000"
+"\npppppppppq\u0000~\u0000\fpppppppppppppppppppppppppppppppppq\u0000~\u0000\u00b0ppppppp"
+"pppppppppppq\u0000~\u0000\u0015q\u0000~\u0000Rq\u0000~\u0000Xq\u0000~\u0000^q\u0000~\u0000dq\u0000~\u0000jq\u0000~\u0000pq\u0000~\u0000vq\u0000~\u0000|q\u0000~\u0000"
+"\u0082q\u0000~\u0000\u0088q\u0000~\u0000\u0012q\u0000~\u0000Qq\u0000~\u0000Wq\u0000~\u0000]q\u0000~\u0000cq\u0000~\u0000iq\u0000~\u0000oq\u0000~\u0000Lq\u0000~\u0000Mq\u0000~\u0000Nq\u0000~\u0000"
+"Oq\u0000~\u0000Kq\u0000~\u0000uq\u0000~\u0000J"));
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
            return net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this;
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
                        if (("InitialState" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
                    case  1 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("TruePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExistsPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("QntPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("JokerPred" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("OrPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred2" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ForallPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("FalsePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExprPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Exists1Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IffPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("MemPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ImpliesPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Fact" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
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
                        if (("InitialState" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateImpl)net.sourceforge.czt.oz.jaxb.gen.impl.InitialStateElementImpl.this).new Unmarshaller(context)), 2, value);
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
