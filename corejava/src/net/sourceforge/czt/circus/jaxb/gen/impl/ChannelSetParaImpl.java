//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen.impl;

public class ChannelSetParaImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl
    implements net.sourceforge.czt.circus.jaxb.gen.ChannelSetPara, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    protected net.sourceforge.czt.circus.jaxb.gen.ChannelSet _ChannelSet;
    protected net.sourceforge.czt.z.jaxb.gen.DeclName _DeclName;
    public final static java.lang.Class version = (net.sourceforge.czt.circus.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.circus.jaxb.gen.ChannelSetPara.class);
    }

    public net.sourceforge.czt.circus.jaxb.gen.ChannelSet getChannelSet() {
        return _ChannelSet;
    }

    public void setChannelSet(net.sourceforge.czt.circus.jaxb.gen.ChannelSet value) {
        _ChannelSet = value;
    }

    public net.sourceforge.czt.z.jaxb.gen.DeclName getDeclName() {
        return _DeclName;
    }

    public void setDeclName(net.sourceforge.czt.z.jaxb.gen.DeclName value) {
        _DeclName = value;
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeBody(context);
        if (_DeclName instanceof javax.xml.bind.Element) {
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _DeclName), "DeclName");
        } else {
            context.startElement("http://czt.sourceforge.net/zml", "DeclName");
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _DeclName), "DeclName");
            context.endNamespaceDecls();
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _DeclName), "DeclName");
            context.endAttributes();
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _DeclName), "DeclName");
            context.endElement();
        }
        if (_ChannelSet instanceof javax.xml.bind.Element) {
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _ChannelSet), "ChannelSet");
        } else {
            context.startElement("http://czt.sourceforge.net/circus", "ChannelSet");
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _ChannelSet), "ChannelSet");
            context.endNamespaceDecls();
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _ChannelSet), "ChannelSet");
            context.endAttributes();
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _ChannelSet), "ChannelSet");
            context.endElement();
        }
    }

    public void serializeAttributes(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeAttributes(context);
        if (_DeclName instanceof javax.xml.bind.Element) {
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _DeclName), "DeclName");
        }
        if (_ChannelSet instanceof javax.xml.bind.Element) {
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _ChannelSet), "ChannelSet");
        }
    }

    public void serializeURIs(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeURIs(context);
        if (_DeclName instanceof javax.xml.bind.Element) {
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _DeclName), "DeclName");
        }
        if (_ChannelSet instanceof javax.xml.bind.Element) {
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _ChannelSet), "ChannelSet");
        }
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.circus.jaxb.gen.ChannelSetPara.class);
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
+".net/zmlq\u0000~\u0000\u001esq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq"
+"\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000.net.sourceforge.czt.z.jaxb"
+".gen.DeclNameElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0000ppsq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007pps"
+"q\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\'net.sourcefor"
+"ge.czt.z.jaxb.gen.DeclNameq\u0000~\u0000#sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000)q\u0000~\u0000"
+"9q\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u0000\bDeclNameq\u0000~\u0000>sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000"
+"~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00003net.sourceforge.czt.zpatt.j"
+"axb.gen.JokerNameElementq\u0000~\u0000#sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007p"
+"psq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000"
+"~\u0000\u001ft\u00003net.sourceforge.czt.circus.jaxb.gen.UnionChannelSetq\u0000~"
+"\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq"
+"\u0000~\u0000\u001ft\u00008net.sourceforge.czt.circus.jaxb.gen.RefChannelSetElem"
+"entq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq"
+"\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00008net.sourceforge.czt.circus.jaxb.gen.DifferenceC"
+"hannelSetq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018"
+"q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00008net.sourceforge.czt.circus.jaxb.gen.SetCh"
+"annelSetElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000e"
+"pq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00007net.sourceforge.czt.circus.jaxb.gen"
+".IntersectChannelSetq\u0000~\u0000#sr\u0000\"com.sun.msv.grammar.ExpressionP"
+"ool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionP"
+"ool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$Clos"
+"edHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006parentt\u0000$Lcom/su"
+"n/msv/grammar/ExpressionPool;xp\u0000\u0000\u0000\u001f\u0001pq\u0000~\u0000Bq\u0000~\u0000Jq\u0000~\u0000Tq\u0000~\u0000^q\u0000~"
+"\u0000dq\u0000~\u0000jq\u0000~\u0000pq\u0000~\u0000vq\u0000~\u0000Yq\u0000~\u0000$q\u0000~\u0000Oq\u0000~\u0000\u000fq\u0000~\u0000Hq\u0000~\u0000\u0014q\u0000~\u0000Cq\u0000~\u0000Kq\u0000~"
+"\u0000Uq\u0000~\u0000_q\u0000~\u0000eq\u0000~\u0000kq\u0000~\u0000qq\u0000~\u0000wq\u0000~\u0000\u0005q\u0000~\u0000[q\u0000~\u0000Zq\u0000~\u0000\\q\u0000~\u0000?q\u0000~\u0000@q\u0000~"
+"\u0000\bq\u0000~\u0000\u0006q\u0000~\u0000\u0011x"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.circus.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "--------");
        }

        protected Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  1 :
                        if (("JokerName" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _DeclName = ((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.class), 4, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 2;
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameElementImpl.class), 4, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        break;
                    case  6 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl.class), 7, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl.class), 7, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  5 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  4 :
                        if (("UnionChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.UnionChannelSetImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.UnionChannelSetImpl.class), 5, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("RefChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.RefChannelSetElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.RefChannelSetElementImpl.class), 5, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("DifferenceChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.DifferenceChannelSetImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.DifferenceChannelSetImpl.class), 5, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("SetChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.SetChannelSetElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.SetChannelSetElementImpl.class), 5, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("IntersectChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.IntersectChannelSetImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.IntersectChannelSetImpl.class), 5, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("ChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 6;
                            return ;
                        }
                        if (("ChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetElementImpl.class), 5, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        break;
                    case  2 :
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().enterElement(___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Word" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  0 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
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
                    case  6 :
                        _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl) spawnChildFromLeaveElement((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl.class), 7, ___uri, ___local, ___qname));
                        return ;
                    case  5 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveElement(___uri, ___local, ___qname);
                            return ;
                        }
                        _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  7 :
                        if (("ChannelSet" == ___local)&&("http://czt.sourceforge.net/circus" == ___uri)) {
                            context.popAttributes();
                            state = 5;
                            return ;
                        }
                        break;
                    case  3 :
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 4;
                            return ;
                        }
                        break;
                    case  0 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                    case  6 :
                        _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl.class), 7, ___uri, ___local, ___qname));
                        return ;
                    case  5 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("Id" == ___local)&&("" == ___uri)) {
                            _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
                            return ;
                        }
                        _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  0 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                    case  6 :
                        _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl.class), 7, ___uri, ___local, ___qname));
                        return ;
                    case  5 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveAttribute(___uri, ___local, ___qname);
                            return ;
                        }
                        _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  0 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                        case  6 :
                            _ChannelSet = ((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl) spawnChildFromText((net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetImpl.class), 7, value));
                            return ;
                        case  5 :
                            revertToParentFromText(value);
                            return ;
                        case  2 :
                            attIdx = context.getAttribute("", "Id");
                            if (attIdx >= 0) {
                                context.consumeAttribute(attIdx);
                                context.getCurrentHandler().text(value);
                                return ;
                            }
                            _DeclName = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, value));
                            return ;
                        case  0 :
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelSetParaImpl.this).new Unmarshaller(context)), 1, value);
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
