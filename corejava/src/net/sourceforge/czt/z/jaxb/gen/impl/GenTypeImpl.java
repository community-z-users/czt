//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class GenTypeImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.TypeImpl
    implements net.sourceforge.czt.z.jaxb.gen.GenType, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    protected net.sourceforge.czt.z.jaxb.gen.DeclName _Name;
    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.GenType.class);
    }

    public net.sourceforge.czt.z.jaxb.gen.DeclName getName() {
        return _Name;
    }

    public void setName(net.sourceforge.czt.z.jaxb.gen.DeclName value) {
        _Name = value;
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeBody(context);
        context.startElement("http://czt.sourceforge.net/zml", "Name");
        context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Name), "Name");
        context.endNamespaceDecls();
        context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Name), "Name");
        context.endAttributes();
        context.childAsBody(((com.sun.xml.bind.JAXBObject) _Name), "Name");
        context.endElement();
    }

    public void serializeAttributes(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeAttributes(context);
    }

    public void serializeURIs(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeURIs(context);
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.z.jaxb.gen.GenType.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.su"
+"n.msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1t\u0000 Lcom/sun/msv/gra"
+"mmar/Expression;L\u0000\u0004exp2q\u0000~\u0000\u0002xr\u0000\u001ecom.sun.msv.grammar.Expressi"
+"on\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilonReducibilityt\u0000\u0013Ljava"
+"/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0002xp\u0004)*\u00d5ppsr\u0000\u001dcom.sun.msv.gra"
+"mmar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0001\u0002\u000b\u008b\u00feppsr\u0000\'com.sun.msv.grammar"
+".trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\tnameClasst\u0000\u001fLcom/sun/msv/g"
+"rammar/NameClass;xr\u0000\u001ecom.sun.msv.grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000\fcontentModelq\u0000~\u0000\u0002xq\u0000~\u0000\u0003\u0002\u000b\u008b"
+"\u00f3sr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0000\u0002\u000b\u008b\u00e8ppsq"
+"\u0000~\u0000\b\u0000(x3pp\u0000sq\u0000~\u0000\u0006\u0000(x(ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq"
+"\u0000~\u0000\u0002xq\u0000~\u0000\u0003\u0000(x\u001dq\u0000~\u0000\rpsr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0002L\u0000\tnameClassq\u0000~\u0000\txq\u0000~\u0000\u0003\u0000(x\u001aq\u0000~\u0000\rpsr\u00002com.s"
+"un.msv.grammar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~"
+"\u0000\u0003\u0000\u0000\u0000\bsq\u0000~\u0000\f\u0001q\u0000~\u0000\u0017sr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.s"
+"un.msv.grammar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003"
+"\u0000\u0000\u0000\tq\u0000~\u0000\u0018q\u0000~\u0000\u001dsr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000\u001fxq\u0000"
+"~\u0000\u001at\u0000-net.sourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http:/"
+"/java.sun.com/jaxb/xjc/dummy-elementssq\u0000~\u0000\u0006\u0001\u00e3\u0013\u00b0ppsq\u0000~\u0000\u0014\u0001\u00e3\u0013\u00a5q"
+"\u0000~\u0000\rpsr\u0000\u001bcom.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/"
+"relaxng/datatype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0002L\u0000\u0004namet\u0000\u001dLcom/sun/m"
+"sv/util/StringPair;xq\u0000~\u0000\u0003\u0001[\u0001,ppsr\u0000\"com.sun.msv.datatype.xsd."
+"QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtom"
+"icType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001"
+"\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000\u001fL\u0000\btypeNameq\u0000~\u0000\u001fL\u0000\nwhiteSpacet\u0000.Lcom/"
+"sun/msv/datatype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3."
+"org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.White"
+"SpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.x"
+"sd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.E"
+"xpression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003\u0000\u0000\u0000\nq\u0000~\u0000\rpsr\u0000\u001bco"
+"m.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000\u001fL\u0000\fname"
+"spaceURIq\u0000~\u0000\u001fxpq\u0000~\u00000q\u0000~\u0000/sq\u0000~\u0000\u001et\u0000\u0004typet\u0000)http://www.w3.org/2"
+"001/XMLSchema-instanceq\u0000~\u0000\u001dsq\u0000~\u0000\u001et\u0000\u0004Annst\u0000\u001ehttp://czt.source"
+"forge.net/zmlq\u0000~\u0000\u001dsq\u0000~\u0000\b\u0002\u001d\u009e\u00d2pp\u0000sq\u0000~\u0000\u0000\u0002\u001d\u009e\u00c7ppsq\u0000~\u0000\b\u0000(x3pp\u0000sq\u0000~"
+"\u0000\u0006\u0000(x(ppsq\u0000~\u0000\u0011\u0000(x\u001dq\u0000~\u0000\rpsq\u0000~\u0000\u0014\u0000(x\u001aq\u0000~\u0000\rpq\u0000~\u0000\u0017q\u0000~\u0000\u001bq\u0000~\u0000\u001dsq\u0000~\u0000"
+"\u001et\u0000\'net.sourceforge.czt.z.jaxb.gen.DeclNameq\u0000~\u0000\"sq\u0000~\u0000\u0006\u0001\u00f5&\u008fpp"
+"sq\u0000~\u0000\u0014\u0001\u00f5&\u0084q\u0000~\u0000\rpq\u0000~\u0000(sq\u0000~\u0000\u001eq\u0000~\u00009q\u0000~\u0000:q\u0000~\u0000\u001dsq\u0000~\u0000\u001et\u0000\u0004Nameq\u0000~\u0000="
+"sr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTable"
+"t\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHash;xpsr\u0000-com."
+"sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005count"
+"I\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000L[\u0000\u0005tablet\u0000![Lcom/sun/msv/grammar/E"
+"xpression;xp\u0000\u0000\u0000\n\u0000\u0000\u00009pur\u0000![Lcom.sun.msv.grammar.Expression;\u00d68"
+"D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0000\u00bfppq\u0000~\u0000Fpppppppppppppppppppppppppppppppppppppp"
+"ppppppppppppppppppppppppppppppppppppppppppppppppppppppq\u0000~\u0000\u000ep"
+"ppppppppq\u0000~\u0000#pppppppppppq\u0000~\u0000\u0007pppppppq\u0000~\u0000\u0005ppppppppppppppppppp"
+"pppppppppq\u0000~\u0000\u0013q\u0000~\u0000Bpppppppppq\u0000~\u0000\u0010q\u0000~\u0000Appppppppppppppppq\u0000~\u0000?p"
+"pppppp"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.oz.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "-----");
        }

        protected Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  4 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.TypeImpl)net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.TypeImpl)net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  2 :
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().enterElement(___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Word" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  1 :
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 2;
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
                    case  4 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  3 :
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 4;
                            return ;
                        }
                        break;
                    case  0 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.TypeImpl)net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveElement(___uri, ___local, ___qname);
                            return ;
                        }
                        _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
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
                    case  4 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.TypeImpl)net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("Id" == ___local)&&("" == ___uri)) {
                            _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
                            return ;
                        }
                        _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
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
                    case  4 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.TypeImpl)net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveAttribute(___uri, ___local, ___qname);
                            return ;
                        }
                        _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, ___uri, ___local, ___qname));
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
                        case  4 :
                            revertToParentFromText(value);
                            return ;
                        case  0 :
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.TypeImpl)net.sourceforge.czt.z.jaxb.gen.impl.GenTypeImpl.this).new Unmarshaller(context)), 1, value);
                            return ;
                        case  2 :
                            attIdx = context.getAttribute("", "Id");
                            if (attIdx >= 0) {
                                context.consumeAttribute(attIdx);
                                context.getCurrentHandler().text(value);
                                return ;
                            }
                            _Name = ((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.DeclNameImpl.class), 3, value));
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
