//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.13 at 03:14:32 NZST 
//


package net.sourceforge.czt.tcoz.jaxb.gen.impl;

public class ConnectionElementImpl
    extends net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl
    implements net.sourceforge.czt.tcoz.jaxb.gen.ConnectionElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.tcoz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.tcoz.jaxb.gen.ConnectionElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/tcoz";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "Connection";
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/tcoz", "Connection");
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
        return (net.sourceforge.czt.tcoz.jaxb.gen.ConnectionElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilon"
+"Reducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xp\u000ef|Hp"
+"p\u0000sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun."
+"msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~"
+"\u0000\u0004\u000ef|=ppsq\u0000~\u0000\u0007\f\u0083\u00e2\u000bppsq\u0000~\u0000\u0007\n\"\u00a13ppsq\u0000~\u0000\u0007\u0006\u00a3R\u00e7ppsr\u0000\u001dcom.sun.msv."
+"grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\b\u0003\u00a9\u00db\u00feppsq\u0000~\u0000\u0000\u0003\u00a9\u00db\u00f3sr\u0000\u0011java.l"
+"ang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007\u0003\u00a9\u00db\u00e8ppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000"
+"sq\u0000~\u0000\r\u0001\u00f6\u00ef\u0018ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"r\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004\u0001"
+"\u00f6\u00ef\rq\u0000~\u0000\u0011psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003e"
+"xpq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004\u0001\u00f6\u00ef\nq\u0000~\u0000\u0011psr\u00002com.sun.msv.gram"
+"mar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\bsq\u0000~\u0000"
+"\u0010\u0001q\u0000~\u0000\u001bsr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dco"
+"m.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gram"
+"mar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\tq\u0000~\u0000\u001cq\u0000"
+"~\u0000!sr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tloca"
+"lNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000#xq\u0000~\u0000\u001et\u0000-net.s"
+"ourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.c"
+"om/jaxb/xjc/dummy-elementssq\u0000~\u0000\r\u0001\u00b2\u00ec\u00c0ppsq\u0000~\u0000\u0018\u0001\u00b2\u00ec\u00b5q\u0000~\u0000\u0011psr\u0000\u001bco"
+"m.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/dat"
+"atype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/Str"
+"ingPair;xq\u0000~\u0000\u0004\u0000O;\u00b2ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnames"
+"paceUriq\u0000~\u0000#L\u0000\btypeNameq\u0000~\u0000#L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/dat"
+"atype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3.org/2001/XM"
+"LSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.WhiteSpaceProces"
+"sor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteSpa"
+"ceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$N"
+"ullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004\u0000\u0000\u0000\nq\u0000~\u0000\u0011psr\u0000\u001bcom.sun.msv.u"
+"til.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000#L\u0000\fnamespaceURIq\u0000~"
+"\u0000#xpq\u0000~\u00004q\u0000~\u00003sq\u0000~\u0000\"t\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSche"
+"ma-instanceq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/z"
+"mlq\u0000~\u0000!sq\u0000~\u0000\u0000\u0002\u00f9v\u00e4pp\u0000sq\u0000~\u0000\u0007\u0002\u00f9v\u00d9ppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\r\u0001\u00f6\u00ef\u0018ppsq\u0000"
+"~\u0000\u0015\u0001\u00f6\u00ef\rq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0001\u00f6\u00ef\nq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000+net.sou"
+"rceforge.czt.oz.jaxb.gen.RefNameListq\u0000~\u0000&sq\u0000~\u0000\r\u0001\u0002\u0087\u00b1ppsq\u0000~\u0000\u0018\u0001"
+"\u0002\u0087\u00a6q\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\"q\u0000~\u0000=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u000bLeftProcesst\u0000\u001fht"
+"tp://czt.sourceforge.net/tcozsq\u0000~\u0000\u0000\u0003\u007fNGpp\u0000sq\u0000~\u0000\u0007\u0003\u007fN<ppsq\u0000~\u0000\u0000"
+"\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\r\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0015\u0001\u00f6\u00ef\rq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0001\u00f6\u00ef\nq\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000"
+"\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000Iq\u0000~\u0000&sq\u0000~\u0000\r\u0001\u0088_\u0014ppsq\u0000~\u0000\u0018\u0001\u0088_\tq\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000"
+"\"q\u0000~\u0000=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\fRightProcessq\u0000~\u0000Osq\u0000~\u0000\u0000\u0002a@\u00d3pp\u0000sq\u0000~\u0000"
+"\u0007\u0002a@\u00c8ppsq\u0000~\u0000\u0000\u0001\u00f6\u00ef#pp\u0000sq\u0000~\u0000\r\u0001\u00f6\u00ef\u0018ppsq\u0000~\u0000\u0015\u0001\u00f6\u00ef\rq\u0000~\u0000\u0011psq\u0000~\u0000\u0018\u0001\u00f6\u00ef\nq\u0000"
+"~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"q\u0000~\u0000Iq\u0000~\u0000&sq\u0000~\u0000\r\u0000jQ\u00a0ppsq\u0000~\u0000\u0018\u0000jQ\u0095q\u0000~"
+"\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\"q\u0000~\u0000=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\bChannelsq\u0000~\u0000Osq\u0000~\u0000\r\u0001\u00e2\u009a"
+"-ppsq\u0000~\u0000\u0018\u0001\u00e2\u009a\"q\u0000~\u0000\u0011pq\u0000~\u0000,sq\u0000~\u0000\"q\u0000~\u0000=q\u0000~\u0000>q\u0000~\u0000!sq\u0000~\u0000\"t\u0000\nConnec"
+"tionq\u0000~\u0000Osr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHash;x"
+"psr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000"
+"\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000n[\u0000\u0005tablet\u0000![Lcom/sun/msv/"
+"grammar/Expression;xp\u0000\u0000\u0000\u0016\u0000\u0000\u00009pur\u0000![Lcom.sun.msv.grammar.Expr"
+"ession;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0000\u00bfpppppppppppppppppppppppppppppppq\u0000~\u0000]"
+"q\u0000~\u0000cppppppppppppppppppppppppppppppppppppppppq\u0000~\u0000\tpppppppq\u0000~"
+"\u0000\u000bppppppppppppppppppppppppppppq\u0000~\u0000\u0012q\u0000~\u0000\'pppppppppq\u0000~\u0000Qq\u0000~\u0000Wp"
+"ppppq\u0000~\u0000\nppq\u0000~\u0000hq\u0000~\u0000\u000eppq\u0000~\u0000\fpppppppppppppppppppppppppppq\u0000~\u0000\u0017"
+"q\u0000~\u0000Fq\u0000~\u0000Tq\u0000~\u0000`pppppppq\u0000~\u0000\u0014q\u0000~\u0000Eq\u0000~\u0000Sq\u0000~\u0000_q\u0000~\u0000Cq\u0000~\u0000Jpppppppp"
+"ppp"));
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
            return net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this;
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
                        if (("Connection" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
                    case  1 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("LeftProcess" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
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
                        if (("Connection" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionElementImpl.this).new Unmarshaller(context)), 2, value);
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
