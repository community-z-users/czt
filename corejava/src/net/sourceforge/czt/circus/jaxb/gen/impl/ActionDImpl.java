//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen.impl;

public class ActionDImpl
    extends net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl
    implements net.sourceforge.czt.circus.jaxb.gen.ActionD, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    protected net.sourceforge.czt.z.jaxb.gen.VarDecl _VarDecl;
    public final static java.lang.Class version = (net.sourceforge.czt.circus.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.circus.jaxb.gen.ActionD.class);
    }

    public net.sourceforge.czt.z.jaxb.gen.VarDecl getVarDecl() {
        return _VarDecl;
    }

    public void setVarDecl(net.sourceforge.czt.z.jaxb.gen.VarDecl value) {
        _VarDecl = value;
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeBody(context);
        if (_VarDecl instanceof javax.xml.bind.Element) {
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _VarDecl), "VarDecl");
        } else {
            context.startElement("http://czt.sourceforge.net/zml", "VarDecl");
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _VarDecl), "VarDecl");
            context.endNamespaceDecls();
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _VarDecl), "VarDecl");
            context.endAttributes();
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _VarDecl), "VarDecl");
            context.endElement();
        }
    }

    public void serializeAttributes(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeAttributes(context);
        if (_VarDecl instanceof javax.xml.bind.Element) {
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _VarDecl), "VarDecl");
        }
    }

    public void serializeURIs(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeURIs(context);
        if (_VarDecl instanceof javax.xml.bind.Element) {
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _VarDecl), "VarDecl");
        }
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.circus.jaxb.gen.ActionD.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.su"
+"n.msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1t\u0000 Lcom/sun/msv/gra"
+"mmar/Expression;L\u0000\u0004exp2q\u0000~\u0000\u0002xr\u0000\u001ecom.sun.msv.grammar.Expressi"
+"on\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0002L\u0000\u0013epsilonReducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000b"
+"expandedExpq\u0000~\u0000\u0002xpppsq\u0000~\u0000\u0000ppsr\u0000\u001dcom.sun.msv.grammar.ChoiceEx"
+"p\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0001ppsr\u0000\'com.sun.msv.grammar.trex.ElementPatt"
+"ern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;"
+"xr\u0000\u001ecom.sun.msv.grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndecl"
+"aredAttributesL\u0000\fcontentModelq\u0000~\u0000\u0002xq\u0000~\u0000\u0003sr\u0000\u0011java.lang.Boolea"
+"n\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0000ppsq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsr\u0000 com.su"
+"n.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar"
+".UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0002xq\u0000~\u0000\u0003q\u0000~\u0000\u000epsr\u0000 com.sun.msv.g"
+"rammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0002L\u0000\tnameClassq\u0000~\u0000\nxq"
+"\u0000~\u0000\u0003q\u0000~\u0000\u000epsr\u00002com.sun.msv.grammar.Expression$AnyStringExpres"
+"sion\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003sq\u0000~\u0000\r\u0001q\u0000~\u0000\u0018sr\u0000 com.sun.msv.grammar.Any"
+"NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$EpsilonExpression\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003q\u0000~\u0000\u0019q\u0000~\u0000\u001esr\u0000#com.sun.msv.grammar.SimpleNameC"
+"lass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespace"
+"URIq\u0000~\u0000 xq\u0000~\u0000\u001bt\u0000-net.sourceforge.czt.z.jaxb.gen.TermA.AnnsTy"
+"pet\u0000+http://java.sun.com/jaxb/xjc/dummy-elementssq\u0000~\u0000\u0007ppsq\u0000~"
+"\u0000\u0015q\u0000~\u0000\u000epsr\u0000\u001bcom.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLo"
+"rg/relaxng/datatype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0002L\u0000\u0004namet\u0000\u001dLcom/su"
+"n/msv/util/StringPair;xq\u0000~\u0000\u0003ppsr\u0000\"com.sun.msv.datatype.xsd.Q"
+"nameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtomi"
+"cType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000 L\u0000\btypeNameq\u0000~\u0000 L\u0000\nwhiteSpacet\u0000.Lcom/s"
+"un/msv/datatype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3.o"
+"rg/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.WhiteS"
+"paceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xs"
+"d.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Ex"
+"pression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003q\u0000~\u0000\u000epsr\u0000\u001bcom.sun"
+".msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000 L\u0000\fnamespace"
+"URIq\u0000~\u0000 xpq\u0000~\u00001q\u0000~\u00000sq\u0000~\u0000\u001ft\u0000\u0004typet\u0000)http://www.w3.org/2001/X"
+"MLSchema-instanceq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge"
+".net/zmlq\u0000~\u0000\u001esq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007p"
+"psq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000"
+"~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007p"
+"psq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015"
+"q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00009net.sourceforge.czt.circus.jax"
+"b.gen.VarDeclCommandElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000e"
+"psq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000<net.sourceforge.czt.cir"
+"cus.jaxb.gen.ActualParamActionElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007pps"
+"q\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00008net.sourcefor"
+"ge.czt.circus.jaxb.gen.SchTextActionElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000"
+"~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00004net.sou"
+"rceforge.czt.circus.jaxb.gen.IntChoiceActionRq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000s"
+"q\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00008net.s"
+"ourceforge.czt.circus.jaxb.gen.GuardedActionElementq\u0000~\u0000#sq\u0000~"
+"\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000"
+":net.sourceforge.czt.circus.jaxb.gen.PrefixingActionElementq"
+"\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001e"
+"sq\u0000~\u0000\u001ft\u00005net.sourceforge.czt.circus.jaxb.gen.CallActionEleme"
+"ntq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000"
+"~\u0000\u001esq\u0000~\u0000\u001ft\u00003net.sourceforge.czt.circus.jaxb.gen.MuActionElem"
+"entq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq"
+"\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000:net.sourceforge.czt.circus.jaxb.gen.ParallelAct"
+"ionRElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~"
+"\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00004net.sourceforge.czt.circus.jaxb.gen.Int"
+"erleaveActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq"
+"\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.circus.jaxb.gen.S"
+"topActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018"
+"q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000:net.sourceforge.czt.circus.jaxb.gen.SpecS"
+"tmtCommandElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~"
+"\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00005net.sourceforge.czt.circus.jaxb.g"
+"en.FormalParamActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015"
+"q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000-net.sourceforge.czt.circus.jax"
+"b.gen.SeqActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000e"
+"pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00004net.sourceforge.czt.circus.jaxb.gen"
+".ExtChoiceActionRq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~"
+"\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000;net.sourceforge.czt.circus.jaxb.g"
+"en.IfGuardedCommandElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000ep"
+"sq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.circ"
+"us.jaxb.gen.SkipActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~"
+"\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00003net.sourceforge.czt.circus.j"
+"axb.gen.ExtChoiceActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000"
+"~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000<net.sourceforge.czt.circus."
+"jaxb.gen.AssignmentCommandElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000"
+"\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00003net.sourceforge.c"
+"zt.circus.jaxb.gen.IntChoiceActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~"
+"\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00009net.sourceforge."
+"czt.circus.jaxb.gen.ParallelActionElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000"
+"\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000/net.sourc"
+"eforge.czt.circus.jaxb.gen.ChaosActionq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007pp"
+"sq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00005net.sourcefo"
+"rge.czt.circus.jaxb.gen.HideActionElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000"
+"\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourc"
+"eforge.czt.circus.jaxb.gen.SeqActionRq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007pps"
+"q\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00005net.sourcefor"
+"ge.czt.circus.jaxb.gen.InterleaveActionRq\u0000~\u0000#sq\u0000~\u0000\u0007ppsq\u0000~\u0000\tp"
+"p\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000-ne"
+"t.sourceforge.czt.z.jaxb.gen.VarDeclElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000"
+"~\u0000\u0000ppsq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000"
+"\u001esq\u0000~\u0000\u001ft\u0000&net.sourceforge.czt.z.jaxb.gen.VarDeclq\u0000~\u0000#sq\u0000~\u0000\u0007p"
+"psq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000)q\u0000~\u00009q\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\u0007VarDeclq\u0000~\u0000>sr\u0000\"com.sun"
+".msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun"
+"/msv/grammar/ExpressionPool$ClosedHash;xpsr\u0000-com.sun.msv.gra"
+"mmar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVe"
+"rsionL\u0000\u0006parentt\u0000$Lcom/sun/msv/grammar/ExpressionPool;xp\u0000\u0000\u0000X\u0001"
+"pq\u0000~\u0000Gq\u0000~\u0000Lq\u0000~\u0000Fq\u0000~\u0000\u00bfq\u0000~\u0000\u00b9q\u0000~\u0000\u00b3q\u0000~\u0000\u00adq\u0000~\u0000\u00a7q\u0000~\u0000\u00a1q\u0000~\u0000\u009bq\u0000~\u0000\u0095q\u0000~\u0000"
+"Rq\u0000~\u0000\u008fq\u0000~\u0000\u0089q\u0000~\u0000\u0083q\u0000~\u0000}q\u0000~\u0000wq\u0000~\u0000qq\u0000~\u0000kq\u0000~\u0000eq\u0000~\u0000_q\u0000~\u0000Yq\u0000~\u0000\u0014q\u0000~\u0000"
+"\u00c5q\u0000~\u0000\u00cbq\u0000~\u0000Eq\u0000~\u0000\u00d1q\u0000~\u0000\u00d7q\u0000~\u0000\u00ddq\u0000~\u0000\u00e3q\u0000~\u0000\u00e9q\u0000~\u0000\u00f0q\u0000~\u0000\u00f8q\u0000~\u0000Oq\u0000~\u0000Dq\u0000~\u0000"
+"Iq\u0000~\u0000@q\u0000~\u0000Cq\u0000~\u0000Uq\u0000~\u0000Pq\u0000~\u0000?q\u0000~\u0000Nq\u0000~\u0000Qq\u0000~\u0000\u00beq\u0000~\u0000\u00b8q\u0000~\u0000\u00b2q\u0000~\u0000\u00acq\u0000~\u0000"
+"\u00a6q\u0000~\u0000\u00a0q\u0000~\u0000\u009aq\u0000~\u0000\bq\u0000~\u0000\u0094q\u0000~\u0000\u008eq\u0000~\u0000\u0088q\u0000~\u0000\u0082q\u0000~\u0000|q\u0000~\u0000vq\u0000~\u0000pq\u0000~\u0000jq\u0000~\u0000"
+"dq\u0000~\u0000^q\u0000~\u0000Xq\u0000~\u0000\u0011q\u0000~\u0000\u00c4q\u0000~\u0000\u00caq\u0000~\u0000\u00d0q\u0000~\u0000\u00d6q\u0000~\u0000\u00dcq\u0000~\u0000\u00e2q\u0000~\u0000\u00e8q\u0000~\u0000\u00efq\u0000~\u0000"
+"\u00f7q\u0000~\u0000Sq\u0000~\u0000Jq\u0000~\u0000\u0005q\u0000~\u0000\u00edq\u0000~\u0000Hq\u0000~\u0000$q\u0000~\u0000\u00fcq\u0000~\u0000\u0006q\u0000~\u0000Mq\u0000~\u0000Tq\u0000~\u0000Vq\u0000~\u0000"
+"Bq\u0000~\u0000\u000fq\u0000~\u0000\u00f5q\u0000~\u0000Aq\u0000~\u0000Kx"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.circus.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "-----");
        }

        protected Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  2 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("JokerName" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  4 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  1 :
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 2;
                            return ;
                        }
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclElementImpl.class), 4, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        break;
                    case  0 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("VarDeclCommand" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ActualParamAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SchTextAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IntChoiceActionR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("GuardedAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("PrefixingAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("CallAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("MuAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ParallelActionR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InterleaveAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("StopAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SpecStmtCommand" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("FormalParamAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SeqAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExtChoiceActionR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IfGuardedCommand" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SkipAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExtChoiceAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("AssignmentCommand" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IntChoiceAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ParallelAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ChaosAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("HideAction" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("SeqActionR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("InterleaveActionR" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Action" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Action" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
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
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  4 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  3 :
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 4;
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
                    case  2 :
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  4 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                    case  2 :
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  4 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                        case  2 :
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 3, value));
                            return ;
                        case  4 :
                            revertToParentFromText(value);
                            return ;
                        case  0 :
                            spawnHandlerFromText((((net.sourceforge.czt.circus.jaxb.gen.impl.Action1Impl)net.sourceforge.czt.circus.jaxb.gen.impl.ActionDImpl.this).new Unmarshaller(context)), 1, value);
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
