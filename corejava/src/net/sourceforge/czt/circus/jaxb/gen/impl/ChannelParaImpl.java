//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen.impl;

public class ChannelParaImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl
    implements net.sourceforge.czt.circus.jaxb.gen.ChannelPara, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    protected net.sourceforge.czt.z.jaxb.gen.VarDecl _VarDecl;
    public final static java.lang.Class version = (net.sourceforge.czt.circus.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.circus.jaxb.gen.ChannelPara.class);
    }

    public net.sourceforge.czt.z.jaxb.gen.VarDecl getVarDecl() {
        return _VarDecl;
    }

    public void setVarDecl(net.sourceforge.czt.z.jaxb.gen.VarDecl value) {
        _VarDecl = value;
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.Unmarshaller(context);
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
        return (net.sourceforge.czt.circus.jaxb.gen.ChannelPara.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.su"
+"n.msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1t\u0000 Lcom/sun/msv/gra"
+"mmar/Expression;L\u0000\u0004exp2q\u0000~\u0000\u0002xr\u0000\u001ecom.sun.msv.grammar.Expressi"
+"on\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0002L\u0000\u0013epsilonReducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000b"
+"expandedExpq\u0000~\u0000\u0002xpppsr\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0001ppsr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom."
+"sun.msv.grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttr"
+"ibutesL\u0000\fcontentModelq\u0000~\u0000\u0002xq\u0000~\u0000\u0003sr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa"
+"\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0000ppsq\u0000~\u0000\bpp\u0000sq\u0000~\u0000\u0006ppsr\u0000 com.sun.msv.gr"
+"ammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar.UnaryEx"
+"p\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0002xq\u0000~\u0000\u0003q\u0000~\u0000\rpsr\u0000 com.sun.msv.grammar.A"
+"ttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0002L\u0000\tnameClassq\u0000~\u0000\txq\u0000~\u0000\u0003q\u0000~\u0000"
+"\rpsr\u00002com.sun.msv.grammar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003sq\u0000~\u0000\f\u0001q\u0000~\u0000\u0017sr\u0000 com.sun.msv.grammar.AnyNameClas"
+"s\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr"
+"\u00000com.sun.msv.grammar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000"
+"\u0000xq\u0000~\u0000\u0003q\u0000~\u0000\u0018q\u0000~\u0000\u001dsr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000\u001f"
+"xq\u0000~\u0000\u001at\u0000-net.sourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+htt"
+"p://java.sun.com/jaxb/xjc/dummy-elementssq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0014q\u0000~\u0000\rp"
+"sr\u0000\u001bcom.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relax"
+"ng/datatype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0002L\u0000\u0004namet\u0000\u001dLcom/sun/msv/ut"
+"il/StringPair;xq\u0000~\u0000\u0003ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000"
+"xr\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnam"
+"espaceUriq\u0000~\u0000\u001fL\u0000\btypeNameq\u0000~\u0000\u001fL\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/d"
+"atatype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3.org/2001/"
+"XMLSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.WhiteSpaceProc"
+"essor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteS"
+"paceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression"
+"$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003q\u0000~\u0000\rpsr\u0000\u001bcom.sun.msv.uti"
+"l.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000\u001fL\u0000\fnamespaceURIq\u0000~\u0000\u001f"
+"xpq\u0000~\u00000q\u0000~\u0000/sq\u0000~\u0000\u001et\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSchema"
+"-instanceq\u0000~\u0000\u001dsq\u0000~\u0000\u001et\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/zml"
+"q\u0000~\u0000\u001dsq\u0000~\u0000\u0006ppsq\u0000~\u0000\bpp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0011q\u0000~\u0000\rpsq\u0000~\u0000\u0014q\u0000~\u0000\rpq\u0000~\u0000\u0017q"
+"\u0000~\u0000\u001bq\u0000~\u0000\u001dsq\u0000~\u0000\u001et\u0000-net.sourceforge.czt.z.jaxb.gen.VarDeclElem"
+"entq\u0000~\u0000\"sq\u0000~\u0000\bpp\u0000sq\u0000~\u0000\u0000ppsq\u0000~\u0000\bpp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0011q\u0000~\u0000\rpsq\u0000~\u0000\u0014"
+"q\u0000~\u0000\rpq\u0000~\u0000\u0017q\u0000~\u0000\u001bq\u0000~\u0000\u001dsq\u0000~\u0000\u001et\u0000&net.sourceforge.czt.z.jaxb.gen"
+".VarDeclq\u0000~\u0000\"sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0014q\u0000~\u0000\rpq\u0000~\u0000(q\u0000~\u00008q\u0000~\u0000\u001dsq\u0000~\u0000\u001et\u0000\u0007Var"
+"Declq\u0000~\u0000=sr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHash;x"
+"psr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000"
+"\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006parentt\u0000$Lcom/sun/msv/grammar/Ex"
+"pressionPool;xp\u0000\u0000\u0000\r\u0001pq\u0000~\u0000@q\u0000~\u0000Hq\u0000~\u0000#q\u0000~\u0000Mq\u0000~\u0000\u000eq\u0000~\u0000Fq\u0000~\u0000\u0013q\u0000~\u0000"
+"Aq\u0000~\u0000Iq\u0000~\u0000\u0005q\u0000~\u0000>q\u0000~\u0000\u0007q\u0000~\u0000\u0010x"));
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
            return net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  3 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("JokerName" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("DeclName" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  1 :
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 3;
                            return ;
                        }
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclElementImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        break;
                    case  2 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
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
                    case  4 :
                        if (("VarDecl" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 2;
                            return ;
                        }
                        break;
                    case  3 :
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname));
                        return ;
                    case  2 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname));
                        return ;
                    case  2 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                        _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, ___uri, ___local, ___qname));
                        return ;
                    case  2 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
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
                            _VarDecl = ((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.VarDeclImpl.class), 4, value));
                            return ;
                        case  2 :
                            revertToParentFromText(value);
                            return ;
                        case  0 :
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.circus.jaxb.gen.impl.ChannelParaImpl.this).new Unmarshaller(context)), 1, value);
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
