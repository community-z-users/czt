//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.04.21 at 09:33:05 GMT 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class SpecImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl
    implements net.sourceforge.czt.z.jaxb.gen.Spec, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    protected java.util.Calendar _Modified;
    protected java.lang.String _Version;
    protected java.lang.String _Author;
    protected java.lang.String _Source;
    protected com.sun.xml.bind.util.ListImpl _Sect;
    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.Spec.class);
    }

    public java.util.Calendar getModified() {
        return _Modified;
    }

    public void setModified(java.util.Calendar value) {
        _Modified = value;
    }

    public java.lang.String getVersion() {
        if (_Version == null) {
            return "1.0";
        } else {
            return _Version;
        }
    }

    public void setVersion(java.lang.String value) {
        _Version = value;
    }

    public java.lang.String getAuthor() {
        return _Author;
    }

    public void setAuthor(java.lang.String value) {
        _Author = value;
    }

    public java.lang.String getSource() {
        return _Source;
    }

    public void setSource(java.lang.String value) {
        _Source = value;
    }

    protected com.sun.xml.bind.util.ListImpl _getSect() {
        if (_Sect == null) {
            _Sect = new com.sun.xml.bind.util.ListImpl(new java.util.ArrayList());
        }
        return _Sect;
    }

    public java.util.List getSect() {
        return _getSect();
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx5 = 0;
        final int len5 = ((_Sect == null)? 0 :_Sect.size());
        super.serializeBody(context);
        while (idx5 != len5) {
            if (_Sect.get(idx5) instanceof javax.xml.bind.Element) {
                context.childAsBody(((com.sun.xml.bind.JAXBObject) _Sect.get(idx5 ++)), "Sect");
            } else {
                context.startElement("http://czt.sourceforge.net/zml", "Sect");
                int idx_0 = idx5;
                context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Sect.get(idx_0 ++)), "Sect");
                context.endNamespaceDecls();
                int idx_1 = idx5;
                context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Sect.get(idx_1 ++)), "Sect");
                context.endAttributes();
                context.childAsBody(((com.sun.xml.bind.JAXBObject) _Sect.get(idx5 ++)), "Sect");
                context.endElement();
            }
        }
    }

    public void serializeAttributes(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx5 = 0;
        final int len5 = ((_Sect == null)? 0 :_Sect.size());
        if (_Author!= null) {
            context.startAttribute("", "Author");
            try {
                context.text(((java.lang.String) _Author), "Author");
            } catch (java.lang.Exception e) {
                net.sourceforge.czt.circus.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
            }
            context.endAttribute();
        }
        if (_Modified!= null) {
            context.startAttribute("", "Modified");
            try {
                context.text(com.sun.msv.datatype.xsd.DateTimeType.theInstance.serializeJavaObject(((java.util.Calendar) _Modified), null), "Modified");
            } catch (java.lang.Exception e) {
                net.sourceforge.czt.circus.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
            }
            context.endAttribute();
        }
        if (_Source!= null) {
            context.startAttribute("", "Source");
            try {
                context.text(((java.lang.String) _Source), "Source");
            } catch (java.lang.Exception e) {
                net.sourceforge.czt.circus.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
            }
            context.endAttribute();
        }
        if (_Version!= null) {
            context.startAttribute("", "Version");
            try {
                context.text(((java.lang.String) _Version), "Version");
            } catch (java.lang.Exception e) {
                net.sourceforge.czt.circus.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
            }
            context.endAttribute();
        }
        super.serializeAttributes(context);
        while (idx5 != len5) {
            if (_Sect.get(idx5) instanceof javax.xml.bind.Element) {
                context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Sect.get(idx5 ++)), "Sect");
            } else {
                idx5 += 1;
            }
        }
    }

    public void serializeURIs(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx5 = 0;
        final int len5 = ((_Sect == null)? 0 :_Sect.size());
        super.serializeURIs(context);
        while (idx5 != len5) {
            if (_Sect.get(idx5) instanceof javax.xml.bind.Element) {
                context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Sect.get(idx5 ++)), "Sect");
            } else {
                idx5 += 1;
            }
        }
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.z.jaxb.gen.Spec.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.su"
+"n.msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1t\u0000 Lcom/sun/msv/gra"
+"mmar/Expression;L\u0000\u0004exp2q\u0000~\u0000\u0002xr\u0000\u001ecom.sun.msv.grammar.Expressi"
+"on\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0002L\u0000\u0013epsilonReducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000b"
+"expandedExpq\u0000~\u0000\u0002xpppsq\u0000~\u0000\u0000ppsq\u0000~\u0000\u0000ppsq\u0000~\u0000\u0000ppsq\u0000~\u0000\u0000ppsr\u0000\u001dcom."
+"sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0001ppsr\u0000\'com.sun.msv."
+"grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\tnameClasst\u0000\u001fLcom/su"
+"n/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv.grammar.ElementExp\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000\fcontentModelq\u0000~\u0000\u0002xq"
+"\u0000~\u0000\u0003sr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0000ppsq\u0000"
+"~\u0000\fpp\u0000sq\u0000~\u0000\nppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000"
+"\u0000xr\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0002xq\u0000~\u0000"
+"\u0003q\u0000~\u0000\u0011psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003exp"
+"q\u0000~\u0000\u0002L\u0000\tnameClassq\u0000~\u0000\rxq\u0000~\u0000\u0003q\u0000~\u0000\u0011psr\u00002com.sun.msv.grammar.Ex"
+"pression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003sq\u0000~\u0000\u0010\u0001q\u0000~\u0000\u001bsr\u0000"
+" com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv."
+"grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expres"
+"sion$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003q\u0000~\u0000\u001cq\u0000~\u0000!sr\u0000#com.sun"
+".msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/"
+"lang/String;L\u0000\fnamespaceURIq\u0000~\u0000#xq\u0000~\u0000\u001et\u0000-net.sourceforge.czt"
+".z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/du"
+"mmy-elementssq\u0000~\u0000\nppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011psr\u0000\u001bcom.sun.msv.grammar.Data"
+"Exp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Datatype;L\u0000\u0006exce"
+"ptq\u0000~\u0000\u0002L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~\u0000\u0003ppsr\u0000\"co"
+"m.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.d"
+"atatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.data"
+"type.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xsd"
+".XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000#L\u0000\btypeNameq\u0000~"
+"\u0000#L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/datatype/xsd/WhiteSpaceProces"
+"sor;xpt\u0000 http://www.w3.org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.sun"
+".msv.datatype.xsd.WhiteSpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000"
+",com.sun.msv.datatype.xsd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr"
+"\u00000com.sun.msv.grammar.Expression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000"
+"\u0000xq\u0000~\u0000\u0003q\u0000~\u0000\u0011psr\u0000\u001bcom.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlo"
+"calNameq\u0000~\u0000#L\u0000\fnamespaceURIq\u0000~\u0000#xpq\u0000~\u00004q\u0000~\u00003sq\u0000~\u0000\"t\u0000\u0004typet\u0000)"
+"http://www.w3.org/2001/XMLSchema-instanceq\u0000~\u0000!sq\u0000~\u0000\"t\u0000\u0004Annst"
+"\u0000\u001ehttp://czt.sourceforge.net/zmlq\u0000~\u0000!sq\u0000~\u0000\nppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000"
+"~\u0000\nq\u0000~\u0000\u0011psq\u0000~\u0000\nq\u0000~\u0000\u0011psq\u0000~\u0000\fq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\nppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~\u0000\u0018"
+"q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u00003net.sourceforge.czt.z.jaxb.gen"
+".UnparsedZSectElementq\u0000~\u0000&sq\u0000~\u0000\fq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\nppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011ps"
+"q\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000+net.sourceforge.czt.z.jax"
+"b.gen.ZSectElementq\u0000~\u0000&sq\u0000~\u0000\fq\u0000~\u0000\u0011p\u0000sq\u0000~\u0000\nppsq\u0000~\u0000\u0015q\u0000~\u0000\u0011psq\u0000~"
+"\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000\u001bq\u0000~\u0000\u001fq\u0000~\u0000!sq\u0000~\u0000\"t\u0000.net.sourceforge.czt.z.jaxb.g"
+"en.NarrSectElementq\u0000~\u0000&q\u0000~\u0000!sq\u0000~\u0000\nppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011psq\u0000~\u0000)q\u0000~\u0000\u0011p"
+"sr\u0000#com.sun.msv.datatype.xsd.StringType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001Z\u0000\risAlway"
+"sValidxq\u0000~\u0000.q\u0000~\u00003t\u0000\u0006stringsr\u00005com.sun.msv.datatype.xsd.White"
+"SpaceProcessor$Preserve\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u00006\u0001q\u0000~\u00009sq\u0000~\u0000:q\u0000~\u0000]q\u0000~"
+"\u00003sq\u0000~\u0000\"t\u0000\u0006Authort\u0000\u0000q\u0000~\u0000!sq\u0000~\u0000\nppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011psq\u0000~\u0000)ppsr\u0000%com"
+".sun.msv.datatype.xsd.DateTimeType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000)com.sun.msv"
+".datatype.xsd.DateTimeBaseType\u0014W\u001a@3\u00a5\u00b4\u00e5\u0002\u0000\u0000xq\u0000~\u0000.q\u0000~\u00003t\u0000\bdateT"
+"imeq\u0000~\u00007q\u0000~\u00009sq\u0000~\u0000:q\u0000~\u0000jq\u0000~\u00003sq\u0000~\u0000\"t\u0000\bModifiedq\u0000~\u0000cq\u0000~\u0000!sq\u0000~"
+"\u0000\nppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011psq\u0000~\u0000)ppsr\u0000#com.sun.msv.datatype.xsd.AnyURIT"
+"ype\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000.q\u0000~\u00003t\u0000\u0006anyURIq\u0000~\u00007q\u0000~\u00009sq\u0000~\u0000:q\u0000~\u0000sq\u0000~\u00003"
+"sq\u0000~\u0000\"t\u0000\u0006Sourceq\u0000~\u0000cq\u0000~\u0000!sq\u0000~\u0000\nppsq\u0000~\u0000\u0018q\u0000~\u0000\u0011pq\u0000~\u0000Zsq\u0000~\u0000\"t\u0000\u0007V"
+"ersionq\u0000~\u0000cq\u0000~\u0000!sr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$Close"
+"dHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0"
+"N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006parentt\u0000$Lcom/sun/msv/gra"
+"mmar/ExpressionPool;xp\u0000\u0000\u0000\u0018\u0001pq\u0000~\u0000\bq\u0000~\u0000\u0012q\u0000~\u0000\u0007q\u0000~\u0000\u0006q\u0000~\u0000\tq\u0000~\u0000dq\u0000"
+"~\u0000Cq\u0000~\u0000\u0005q\u0000~\u0000\u0017q\u0000~\u0000Hq\u0000~\u0000Nq\u0000~\u0000Tq\u0000~\u0000wq\u0000~\u0000\u0014q\u0000~\u0000Gq\u0000~\u0000Mq\u0000~\u0000Sq\u0000~\u0000Bq\u0000"
+"~\u0000Dq\u0000~\u0000Xq\u0000~\u0000\u000bq\u0000~\u0000nq\u0000~\u0000\'q\u0000~\u0000Ex"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.circus.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "-----------------");
        }

        protected Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  12 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.this).new Unmarshaller(context)), 13, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.this).new Unmarshaller(context)), 13, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  13 :
                        if (("UnparsedZSect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.UnparsedZSectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.UnparsedZSectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("ZSect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.ZSectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ZSectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("NarrSect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.NarrSectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.NarrSectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Sect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 15;
                            return ;
                        }
                        if (("Sect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.SectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        state = 14;
                        continue outer;
                    case  9 :
                        attIdx = context.getAttribute("", "Version");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 12;
                            continue outer;
                        }
                        state = 12;
                        continue outer;
                    case  14 :
                        if (("UnparsedZSect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.UnparsedZSectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.UnparsedZSectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("ZSect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.ZSectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ZSectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("NarrSect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.NarrSectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.NarrSectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Sect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 15;
                            return ;
                        }
                        if (("Sect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.SectElementImpl.class), 14, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        attIdx = context.getAttribute("", "Author");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText2(v);
                            state = 3;
                            continue outer;
                        }
                        state = 3;
                        continue outer;
                    case  6 :
                        attIdx = context.getAttribute("", "Source");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText3(v);
                            state = 9;
                            continue outer;
                        }
                        state = 9;
                        continue outer;
                    case  15 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl.class), 16, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl.class), 16, ___uri, ___local, ___qname, __atts)));
                        return ;
                    case  3 :
                        attIdx = context.getAttribute("", "Modified");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText4(v);
                            state = 6;
                            continue outer;
                        }
                        state = 6;
                        continue outer;
                }
                super.enterElement(___uri, ___local, ___qname, __atts);
                break;
            }
        }

        private void eatText1(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            try {
                _Version = value;
            } catch (java.lang.Exception e) {
                handleParseConversionException(e);
            }
        }

        private void eatText2(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            try {
                _Author = value;
            } catch (java.lang.Exception e) {
                handleParseConversionException(e);
            }
        }

        private void eatText3(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            try {
                _Source = com.sun.xml.bind.WhiteSpaceProcessor.collapse(value);
            } catch (java.lang.Exception e) {
                handleParseConversionException(e);
            }
        }

        private void eatText4(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            try {
                _Modified = ((java.util.Calendar) com.sun.msv.datatype.xsd.DateTimeType.theInstance.createJavaObject(com.sun.xml.bind.WhiteSpaceProcessor.collapse(value), null));
            } catch (java.lang.Exception e) {
                handleParseConversionException(e);
            }
        }

        public void leaveElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  12 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.this).new Unmarshaller(context)), 13, ___uri, ___local, ___qname);
                        return ;
                    case  13 :
                        state = 14;
                        continue outer;
                    case  9 :
                        attIdx = context.getAttribute("", "Version");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 12;
                            continue outer;
                        }
                        state = 12;
                        continue outer;
                    case  14 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  16 :
                        if (("Sect" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 14;
                            return ;
                        }
                        break;
                    case  0 :
                        attIdx = context.getAttribute("", "Author");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText2(v);
                            state = 3;
                            continue outer;
                        }
                        state = 3;
                        continue outer;
                    case  6 :
                        attIdx = context.getAttribute("", "Source");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText3(v);
                            state = 9;
                            continue outer;
                        }
                        state = 9;
                        continue outer;
                    case  15 :
                        _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl.class), 16, ___uri, ___local, ___qname)));
                        return ;
                    case  3 :
                        attIdx = context.getAttribute("", "Modified");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText4(v);
                            state = 6;
                            continue outer;
                        }
                        state = 6;
                        continue outer;
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
                    case  12 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.this).new Unmarshaller(context)), 13, ___uri, ___local, ___qname);
                        return ;
                    case  13 :
                        state = 14;
                        continue outer;
                    case  9 :
                        if (("Version" == ___local)&&("" == ___uri)) {
                            state = 10;
                            return ;
                        }
                        state = 12;
                        continue outer;
                    case  14 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        if (("Author" == ___local)&&("" == ___uri)) {
                            state = 1;
                            return ;
                        }
                        state = 3;
                        continue outer;
                    case  6 :
                        if (("Source" == ___local)&&("" == ___uri)) {
                            state = 7;
                            return ;
                        }
                        state = 9;
                        continue outer;
                    case  15 :
                        _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl.class), 16, ___uri, ___local, ___qname)));
                        return ;
                    case  3 :
                        if (("Modified" == ___local)&&("" == ___uri)) {
                            state = 4;
                            return ;
                        }
                        state = 6;
                        continue outer;
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
                    case  12 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.this).new Unmarshaller(context)), 13, ___uri, ___local, ___qname);
                        return ;
                    case  13 :
                        state = 14;
                        continue outer;
                    case  9 :
                        attIdx = context.getAttribute("", "Version");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 12;
                            continue outer;
                        }
                        state = 12;
                        continue outer;
                    case  11 :
                        if (("Version" == ___local)&&("" == ___uri)) {
                            state = 12;
                            return ;
                        }
                        break;
                    case  5 :
                        if (("Modified" == ___local)&&("" == ___uri)) {
                            state = 6;
                            return ;
                        }
                        break;
                    case  14 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        attIdx = context.getAttribute("", "Author");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText2(v);
                            state = 3;
                            continue outer;
                        }
                        state = 3;
                        continue outer;
                    case  6 :
                        attIdx = context.getAttribute("", "Source");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText3(v);
                            state = 9;
                            continue outer;
                        }
                        state = 9;
                        continue outer;
                    case  2 :
                        if (("Author" == ___local)&&("" == ___uri)) {
                            state = 3;
                            return ;
                        }
                        break;
                    case  15 :
                        _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl.class), 16, ___uri, ___local, ___qname)));
                        return ;
                    case  3 :
                        attIdx = context.getAttribute("", "Modified");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText4(v);
                            state = 6;
                            continue outer;
                        }
                        state = 6;
                        continue outer;
                    case  8 :
                        if (("Source" == ___local)&&("" == ___uri)) {
                            state = 9;
                            return ;
                        }
                        break;
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
                        case  12 :
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.z.jaxb.gen.impl.SpecImpl.this).new Unmarshaller(context)), 13, value);
                            return ;
                        case  13 :
                            state = 14;
                            continue outer;
                        case  9 :
                            attIdx = context.getAttribute("", "Version");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText1(v);
                                state = 12;
                                continue outer;
                            }
                            state = 12;
                            continue outer;
                        case  1 :
                            eatText2(value);
                            state = 2;
                            return ;
                        case  14 :
                            revertToParentFromText(value);
                            return ;
                        case  10 :
                            eatText1(value);
                            state = 11;
                            return ;
                        case  0 :
                            attIdx = context.getAttribute("", "Author");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText2(v);
                                state = 3;
                                continue outer;
                            }
                            state = 3;
                            continue outer;
                        case  4 :
                            eatText4(value);
                            state = 5;
                            return ;
                        case  6 :
                            attIdx = context.getAttribute("", "Source");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText3(v);
                                state = 9;
                                continue outer;
                            }
                            state = 9;
                            continue outer;
                        case  7 :
                            eatText3(value);
                            state = 8;
                            return ;
                        case  15 :
                            _getSect().add(((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.SectImpl.class), 16, value)));
                            return ;
                        case  3 :
                            attIdx = context.getAttribute("", "Modified");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText4(v);
                                state = 6;
                                continue outer;
                            }
                            state = 6;
                            continue outer;
                    }
                } catch (java.lang.RuntimeException e) {
                    handleUnexpectedTextException(value, e);
                }
                break;
            }
        }

    }

}
