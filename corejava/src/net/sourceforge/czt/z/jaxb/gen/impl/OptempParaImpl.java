//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class OptempParaImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl
    implements net.sourceforge.czt.z.jaxb.gen.OptempPara, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    protected java.lang.String _Cat;
    protected com.sun.xml.bind.util.ListImpl _Oper = new com.sun.xml.bind.util.ListImpl(new java.util.ArrayList());
    protected java.lang.String _Assoc;
    protected java.lang.Integer _Prec;
    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.OptempPara.class);
    }

    public java.lang.String getCat() {
        return _Cat;
    }

    public void setCat(java.lang.String value) {
        _Cat = value;
    }

    public java.util.List getOper() {
        return _Oper;
    }

    public java.lang.String getAssoc() {
        if (_Assoc == null) {
            return "Left";
        } else {
            return _Assoc;
        }
    }

    public void setAssoc(java.lang.String value) {
        _Assoc = value;
    }

    public java.lang.Integer getPrec() {
        return _Prec;
    }

    public void setPrec(java.lang.Integer value) {
        _Prec = value;
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx2 = 0;
        final int len2 = _Oper.size();
        super.serializeBody(context);
        while (idx2 != len2) {
            if (_Oper.get(idx2) instanceof javax.xml.bind.Element) {
                context.childAsBody(((com.sun.xml.bind.JAXBObject) _Oper.get(idx2 ++)), "Oper");
            } else {
                context.startElement("http://czt.sourceforge.net/zml", "Oper");
                int idx_0 = idx2;
                context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Oper.get(idx_0 ++)), "Oper");
                context.endNamespaceDecls();
                int idx_1 = idx2;
                context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Oper.get(idx_1 ++)), "Oper");
                context.endAttributes();
                context.childAsBody(((com.sun.xml.bind.JAXBObject) _Oper.get(idx2 ++)), "Oper");
                context.endElement();
            }
        }
    }

    public void serializeAttributes(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx2 = 0;
        final int len2 = _Oper.size();
        context.startAttribute("", "Cat");
        try {
            context.text(((java.lang.String) _Cat), "Cat");
        } catch (java.lang.Exception e) {
            net.sourceforge.czt.oz.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
        }
        context.endAttribute();
        if (_Assoc!= null) {
            context.startAttribute("", "Assoc");
            try {
                context.text(((java.lang.String) _Assoc), "Assoc");
            } catch (java.lang.Exception e) {
                net.sourceforge.czt.oz.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
            }
            context.endAttribute();
        }
        context.startAttribute("", "Prec");
        try {
            context.text(net.sourceforge.czt.base.util.CztDatatypeConverter.printInteger(((java.lang.Integer) _Prec)), "Prec");
        } catch (java.lang.Exception e) {
            net.sourceforge.czt.oz.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
        }
        context.endAttribute();
        super.serializeAttributes(context);
        while (idx2 != len2) {
            if (_Oper.get(idx2) instanceof javax.xml.bind.Element) {
                context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Oper.get(idx2 ++)), "Oper");
            } else {
                idx2 += 1;
            }
        }
    }

    public void serializeURIs(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx2 = 0;
        final int len2 = _Oper.size();
        super.serializeURIs(context);
        while (idx2 != len2) {
            if (_Oper.get(idx2) instanceof javax.xml.bind.Element) {
                context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Oper.get(idx2 ++)), "Oper");
            } else {
                idx2 += 1;
            }
        }
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.z.jaxb.gen.OptempPara.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.su"
+"n.msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1t\u0000 Lcom/sun/msv/gra"
+"mmar/Expression;L\u0000\u0004exp2q\u0000~\u0000\u0002xr\u0000\u001ecom.sun.msv.grammar.Expressi"
+"on\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilonReducibilityt\u0000\u0013Ljava"
+"/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0002xp\u0013\u001f\u0089Pppsq\u0000~\u0000\u0000\u0011\u00d3\u00a0rppsq\u0000~\u0000\u0000\u000e"
+"\u00f0\u00b9\u00a2ppsq\u0000~\u0000\u0000\rD\u00ea\u00aappsq\u0000~\u0000\u0000\t\u0088X\u00e6ppsq\u0000~\u0000\u0000\u0005\u00cb\u00c70ppsr\u0000\u001dcom.sun.msv.gra"
+"mmar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0001\u0002\u000f5zppsr\u0000\'com.sun.msv.grammar"
+".trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\tnameClasst\u0000\u001fLcom/sun/msv/g"
+"rammar/NameClass;xr\u0000\u001ecom.sun.msv.grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000\fcontentModelq\u0000~\u0000\u0002xq\u0000~\u0000\u0003\u0002\u000f5"
+"osr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0000\u0002\u000f5dppsq"
+"\u0000~\u0000\r\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000(x(ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq"
+"\u0000~\u0000\u0002xq\u0000~\u0000\u0003\u0000(x\u001dq\u0000~\u0000\u0012psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0002L\u0000\tnameClassq\u0000~\u0000\u000exq\u0000~\u0000\u0003\u0000(x\u001aq\u0000~\u0000\u0012psr\u00002com.s"
+"un.msv.grammar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~"
+"\u0000\u0003\u0000\u0000\u0000\bsq\u0000~\u0000\u0011\u0001q\u0000~\u0000\u001csr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.s"
+"un.msv.grammar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003"
+"\u0000\u0000\u0000\tq\u0000~\u0000\u001dq\u0000~\u0000\"sr\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000$xq\u0000"
+"~\u0000\u001ft\u0000-net.sourceforge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http:/"
+"/java.sun.com/jaxb/xjc/dummy-elementssq\u0000~\u0000\u000b\u0001\u00e6\u00bd,ppsq\u0000~\u0000\u0019\u0001\u00e6\u00bd!q"
+"\u0000~\u0000\u0012psr\u0000\u001bcom.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/"
+"relaxng/datatype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0002L\u0000\u0004namet\u0000\u001dLcom/sun/m"
+"sv/util/StringPair;xq\u0000~\u0000\u0003\u0001[\u0001,ppsr\u0000\"com.sun.msv.datatype.xsd."
+"QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.BuiltinAtom"
+"icType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.ConcreteType\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001"
+"\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000$L\u0000\btypeNameq\u0000~\u0000$L\u0000\nwhiteSpacet\u0000.Lcom/"
+"sun/msv/datatype/xsd/WhiteSpaceProcessor;xpt\u0000 http://www.w3."
+"org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.xsd.White"
+"SpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.x"
+"sd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.E"
+"xpression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003\u0000\u0000\u0000\nq\u0000~\u0000\u0012psr\u0000\u001bco"
+"m.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000$L\u0000\fname"
+"spaceURIq\u0000~\u0000$xpq\u0000~\u00005q\u0000~\u00004sq\u0000~\u0000#t\u0000\u0004typet\u0000)http://www.w3.org/2"
+"001/XMLSchema-instanceq\u0000~\u0000\"sq\u0000~\u0000#t\u0000\u0004Annst\u0000\u001ehttp://czt.source"
+"forge.net/zmlq\u0000~\u0000\"sq\u0000~\u0000\u000b\u0003\u00bc\u0091\u00b1ppsq\u0000~\u0000\u000b\u0003\u0094\u0019|ppsq\u0000~\u0000\u000b\u0003k\u00a1Gppsq\u0000~\u0000\r"
+"\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000"
+" q\u0000~\u0000\"sq\u0000~\u0000#t\u0000*net.sourceforge.czt.z.jaxb.gen.OperElementq\u0000~"
+"\u0000\'sq\u0000~\u0000\r\u0003C)\u0012pp\u0000sq\u0000~\u0000\u0000\u0003C)\u0007ppsq\u0000~\u0000\r\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000("
+"x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#t\u0000#net.sourcefo"
+"rge.czt.z.jaxb.gen.Operq\u0000~\u0000\'sq\u0000~\u0000\u000b\u0003\u001a\u00b0\u00cfppsq\u0000~\u0000\u0019\u0003\u001a\u00b0\u00c4q\u0000~\u0000\u0012pq\u0000~\u0000"
+"-sq\u0000~\u0000#q\u0000~\u0000>q\u0000~\u0000?q\u0000~\u0000\"sq\u0000~\u0000#t\u0000\u0004Operq\u0000~\u0000Bsq\u0000~\u0000\r\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000"
+"(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#t\u0000"
+"-net.sourceforge.czt.z.jaxb.gen.OperandElementq\u0000~\u0000\'sq\u0000~\u0000\r\u0000(x"
+"3pp\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000"
+"~\u0000\"sq\u0000~\u0000#t\u0000.net.sourceforge.czt.z.jaxb.gen.OperatorElementq\u0000"
+"~\u0000\'sq\u0000~\u0000\u000b\u0003\u00bc\u0091\u00b1ppsq\u0000~\u0000\u000b\u0003\u0094\u0019|ppsq\u0000~\u0000\u000b\u0003k\u00a1Gppsq\u0000~\u0000\r\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000("
+"x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#q\u0000~"
+"\u0000Kq\u0000~\u0000\'sq\u0000~\u0000\r\u0003C)\u0012pp\u0000sq\u0000~\u0000\u0000\u0003C)\u0007ppsq\u0000~\u0000\r\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000"
+"~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#q\u0000~\u0000Sq\u0000~\u0000\'"
+"sq\u0000~\u0000\u000b\u0003\u001a\u00b0\u00cfppsq\u0000~\u0000\u0019\u0003\u001a\u00b0\u00c4q\u0000~\u0000\u0012pq\u0000~\u0000-q\u0000~\u0000Vq\u0000~\u0000\"q\u0000~\u0000Wsq\u0000~\u0000\r\u0000(x3pp"
+"\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\""
+"sq\u0000~\u0000#q\u0000~\u0000^q\u0000~\u0000\'sq\u0000~\u0000\r\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000"
+"~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#q\u0000~\u0000dq\u0000~\u0000\'sq\u0000~\u0000\u000b\u0003\u00bc\u0091\u00bfppsq\u0000~"
+"\u0000\u0016\u0003\u00bc\u0091\u00b4q\u0000~\u0000\u0012psq\u0000~\u0000\u000b\u0003\u00bc\u0091\u00b1q\u0000~\u0000\u0012psq\u0000~\u0000\u000b\u0003\u0094\u0019|q\u0000~\u0000\u0012psq\u0000~\u0000\u000b\u0003k\u00a1Gq\u0000~\u0000\u0012p"
+"sq\u0000~\u0000\r\u0000(x3q\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012"
+"pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#q\u0000~\u0000Kq\u0000~\u0000\'sq\u0000~\u0000\r\u0003C)\u0012q\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u0000\u0003C)\u0007p"
+"psq\u0000~\u0000\r\u0000(x3pp\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000"
+"~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#q\u0000~\u0000Sq\u0000~\u0000\'sq\u0000~\u0000\u000b\u0003\u001a\u00b0\u00cfppsq\u0000~\u0000\u0019\u0003\u001a\u00b0\u00c4q\u0000~\u0000\u0012pq\u0000~"
+"\u0000-q\u0000~\u0000Vq\u0000~\u0000\"q\u0000~\u0000Wsq\u0000~\u0000\r\u0000(x3q\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000"
+"\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~\u0000#q\u0000~\u0000^q\u0000~\u0000\'sq\u0000~\u0000\r\u0000(x3q"
+"\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u000b\u0000(x(ppsq\u0000~\u0000\u0016\u0000(x\u001dq\u0000~\u0000\u0012psq\u0000~\u0000\u0019\u0000(x\u001aq\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 "
+"q\u0000~\u0000\"sq\u0000~\u0000#q\u0000~\u0000dq\u0000~\u0000\'q\u0000~\u0000\"sq\u0000~\u0000\u0019\u0001\u00ab\u00ce\u00f3ppsq\u0000~\u0000*\u0000\u00f7\u00d5\u00b6ppsr\u0000)com.su"
+"n.msv.datatype.xsd.EnumerationFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0006valuest\u0000\u000fLj"
+"ava/util/Set;xr\u00009com.sun.msv.datatype.xsd.DataTypeWithValueC"
+"onstraintFacet\"\u00a7Ro\u00ca\u00c7\u008aT\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.DataTy"
+"peWithFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0005Z\u0000\fisFacetFixedZ\u0000\u0012needValueCheckFlagL\u0000"
+"\bbaseTypet\u0000)Lcom/sun/msv/datatype/xsd/XSDatatypeImpl;L\u0000\fconc"
+"reteTypet\u0000\'Lcom/sun/msv/datatype/xsd/ConcreteType;L\u0000\tfacetNa"
+"meq\u0000~\u0000$xq\u0000~\u00001q\u0000~\u0000Bt\u0000\u0003Catsr\u00005com.sun.msv.datatype.xsd.WhiteSp"
+"aceProcessor$Preserve\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u00007\u0000\u0000sr\u0000#com.sun.msv.data"
+"type.xsd.StringType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001Z\u0000\risAlwaysValidxq\u0000~\u0000/q\u0000~\u00004t\u0000\u0006"
+"stringq\u0000~\u0000\u00a8\u0001q\u0000~\u0000\u00aat\u0000\u000benumerationsr\u0000\u0011java.util.HashSet\u00baD\u0085\u0095\u0096\u00b8\u00b74"
+"\u0003\u0000\u0000xpw\f\u0000\u0000\u0000\u0010?@\u0000\u0000\u0000\u0000\u0000\u0003t\u0000\u0007Generict\u0000\bRelationt\u0000\bFunctionxq\u0000~\u0000:sq\u0000"
+"~\u0000;q\u0000~\u0000\u00a6q\u0000~\u0000Bsq\u0000~\u0000#t\u0000\u0003Catt\u0000\u0000sq\u0000~\u0000\u000b\u0002\u00e2\u00e6\u00cbppsq\u0000~\u0000\u0019\u0002\u00e2\u00e6\u00c0q\u0000~\u0000\u0012psq\u0000~"
+"\u0000*\u00013\u000b\u0004ppsq\u0000~\u0000\u009fq\u0000~\u0000Bt\u0000\u0005Assocq\u0000~\u0000\u00a8\u0000\u0000q\u0000~\u0000\u00aaq\u0000~\u0000\u00aaq\u0000~\u0000\u00acsq\u0000~\u0000\u00adw\f\u0000\u0000\u0000"
+"\u0010?@\u0000\u0000\u0000\u0000\u0000\u0002t\u0000\u0005Rightt\u0000\u0004Leftxq\u0000~\u0000:sq\u0000~\u0000;q\u0000~\u0000\u00baq\u0000~\u0000Bsq\u0000~\u0000#t\u0000\u0005Assoc"
+"q\u0000~\u0000\u00b5q\u0000~\u0000\"sq\u0000~\u0000\u0019\u0001K\u00e8\u00d9ppsq\u0000~\u0000*\u0000\u00c8\u00e2\u00b4ppsr\u0000/com.sun.msv.datatype.x"
+"sd.NonNegativeIntegerType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000$com.sun.msv.datatype"
+".xsd.IntegerType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000+com.sun.msv.datatype.xsd.Inte"
+"gerDerivedType\u0099\u00f1]\u0090&6k\u00be\u0002\u0000\u0001L\u0000\nbaseFacetsq\u0000~\u0000\u00a3xq\u0000~\u0000/q\u0000~\u00004t\u0000\u0012non"
+"NegativeIntegerq\u0000~\u00008sr\u0000*com.sun.msv.datatype.xsd.MinInclusiv"
+"eFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000#com.sun.msv.datatype.xsd.RangeFacet\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\nlimitValuet\u0000\u0012Ljava/lang/Object;xq\u0000~\u0000\u00a1ppq\u0000~\u00008\u0000\u0000sq\u0000~"
+"\u0000\u00c4q\u0000~\u00004t\u0000\u0007integerq\u0000~\u00008sr\u0000,com.sun.msv.datatype.xsd.FractionD"
+"igitsFacet\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001I\u0000\u0005scalexr\u0000;com.sun.msv.datatype.xsd.Da"
+"taTypeWithLexicalConstraintFacetT\u0090\u001c>\u001azb\u00ea\u0002\u0000\u0000xq\u0000~\u0000\u00a2ppq\u0000~\u00008\u0001\u0000sr"
+"\u0000#com.sun.msv.datatype.xsd.NumberType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000/q\u0000~\u00004t"
+"\u0000\u0007decimalq\u0000~\u00008q\u0000~\u0000\u00d2t\u0000\u000efractionDigits\u0000\u0000\u0000\u0000q\u0000~\u0000\u00cct\u0000\fminInclusive"
+"sr\u0000)com.sun.msv.datatype.xsd.IntegerValueType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0005v"
+"alueq\u0000~\u0000$xr\u0000\u0010java.lang.Number\u0086\u00ac\u0095\u001d\u000b\u0094\u00e0\u008b\u0002\u0000\u0000xpt\u0000\u00010q\u0000~\u0000:sq\u0000~\u0000;q\u0000~"
+"\u0000\u00c7q\u0000~\u00004sq\u0000~\u0000#t\u0000\u0004Precq\u0000~\u0000\u00b5sr\u0000\"com.sun.msv.grammar.ExpressionP"
+"ool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionP"
+"ool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$Clos"
+"edHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000\u00de[\u0000\u0005tablet"
+"\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u00005\u0000\u0000\u00009pur\u0000![Lcom.sun."
+"msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0000\u00bfppppq\u0000~\u0000\u0013pppppppppq\u0000"
+"~\u0000(pppppppppppq\u0000~\u0000\fppppppppppppq\u0000~\u0000\u00b6pppppppppppppppq\u0000~\u0000\u0007pppp"
+"pppppppppppppppq\u0000~\u0000Cq\u0000~\u0000eq\u0000~\u0000\u0082q\u0000~\u0000\u0081pppppppppq\u0000~\u0000Dq\u0000~\u0000fq\u0000~\u0000\u0083q"
+"\u0000~\u0000\u0080q\u0000~\u0000\bpq\u0000~\u0000\u0005ppppq\u0000~\u0000\u0006pq\u0000~\u0000Eq\u0000~\u0000gq\u0000~\u0000Mq\u0000~\u0000nq\u0000~\u0000\u008bq\u0000~\u0000\nq\u0000~\u0000\u0084"
+"pppppq\u0000~\u0000Tq\u0000~\u0000tq\u0000~\u0000\u0091ppppppppppppppppppppppppppppppppppppppq\u0000"
+"~\u0000\u0018q\u0000~\u0000Hq\u0000~\u0000Pq\u0000~\u0000[q\u0000~\u0000aq\u0000~\u0000jq\u0000~\u0000qq\u0000~\u0000xq\u0000~\u0000}q\u0000~\u0000\u0087q\u0000~\u0000\u008eq\u0000~\u0000\u0015q\u0000"
+"~\u0000Gq\u0000~\u0000Oq\u0000~\u0000Zq\u0000~\u0000`q\u0000~\u0000iq\u0000~\u0000pq\u0000~\u0000wq\u0000~\u0000|q\u0000~\u0000\u0086q\u0000~\u0000\u008dq\u0000~\u0000\u0095q\u0000~\u0000\u0094q\u0000"
+"~\u0000\u009aq\u0000~\u0000\u0099ppppppq\u0000~\u0000\tpppp"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.oz.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "--------------");
        }

        protected Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  10 :
                        if (("Operand" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperandElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OperandElementImpl.class), 11, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Operator" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperatorElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OperatorElementImpl.class), 11, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Oper" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 12;
                            return ;
                        }
                        if (("Oper" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OperElementImpl.class), 11, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        break;
                    case  9 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.this).new Unmarshaller(context)), 10, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.this).new Unmarshaller(context)), 10, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  12 :
                        _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl.class), 13, ___uri, ___local, ___qname, __atts)));
                        return ;
                    case  11 :
                        if (("Operand" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperandElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OperandElementImpl.class), 11, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Operator" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperatorElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OperatorElementImpl.class), 11, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Oper" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 12;
                            return ;
                        }
                        if (("Oper" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OperElementImpl.class), 11, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  6 :
                        attIdx = context.getAttribute("", "Prec");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 9;
                            continue outer;
                        }
                        break;
                    case  0 :
                        attIdx = context.getAttribute("", "Cat");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText2(v);
                            state = 3;
                            continue outer;
                        }
                        break;
                    case  3 :
                        attIdx = context.getAttribute("", "Assoc");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText3(v);
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
                _Prec = net.sourceforge.czt.base.util.CztDatatypeConverter.parseInteger(com.sun.xml.bind.WhiteSpaceProcessor.collapse(value));
            } catch (java.lang.Exception e) {
                handleParseConversionException(e);
            }
        }

        private void eatText2(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            try {
                _Cat = value;
            } catch (java.lang.Exception e) {
                handleParseConversionException(e);
            }
        }

        private void eatText3(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            try {
                _Assoc = value;
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
                    case  9 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.this).new Unmarshaller(context)), 10, ___uri, ___local, ___qname);
                        return ;
                    case  12 :
                        _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl.class), 13, ___uri, ___local, ___qname)));
                        return ;
                    case  11 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  6 :
                        attIdx = context.getAttribute("", "Prec");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 9;
                            continue outer;
                        }
                        break;
                    case  13 :
                        if (("Oper" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 11;
                            return ;
                        }
                        break;
                    case  0 :
                        attIdx = context.getAttribute("", "Cat");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText2(v);
                            state = 3;
                            continue outer;
                        }
                        break;
                    case  3 :
                        attIdx = context.getAttribute("", "Assoc");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText3(v);
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
                    case  9 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.this).new Unmarshaller(context)), 10, ___uri, ___local, ___qname);
                        return ;
                    case  12 :
                        _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl.class), 13, ___uri, ___local, ___qname)));
                        return ;
                    case  11 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  6 :
                        if (("Prec" == ___local)&&("" == ___uri)) {
                            state = 7;
                            return ;
                        }
                        break;
                    case  0 :
                        if (("Cat" == ___local)&&("" == ___uri)) {
                            state = 1;
                            return ;
                        }
                        break;
                    case  3 :
                        if (("Assoc" == ___local)&&("" == ___uri)) {
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
                    case  9 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.this).new Unmarshaller(context)), 10, ___uri, ___local, ___qname);
                        return ;
                    case  12 :
                        _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl.class), 13, ___uri, ___local, ___qname)));
                        return ;
                    case  11 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  6 :
                        attIdx = context.getAttribute("", "Prec");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 9;
                            continue outer;
                        }
                        break;
                    case  2 :
                        if (("Cat" == ___local)&&("" == ___uri)) {
                            state = 3;
                            return ;
                        }
                        break;
                    case  0 :
                        attIdx = context.getAttribute("", "Cat");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText2(v);
                            state = 3;
                            continue outer;
                        }
                        break;
                    case  5 :
                        if (("Assoc" == ___local)&&("" == ___uri)) {
                            state = 6;
                            return ;
                        }
                        break;
                    case  3 :
                        attIdx = context.getAttribute("", "Assoc");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText3(v);
                            state = 6;
                            continue outer;
                        }
                        state = 6;
                        continue outer;
                    case  8 :
                        if (("Prec" == ___local)&&("" == ___uri)) {
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
                        case  7 :
                            eatText1(value);
                            state = 8;
                            return ;
                        case  4 :
                            eatText3(value);
                            state = 5;
                            return ;
                        case  9 :
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.z.jaxb.gen.impl.OptempParaImpl.this).new Unmarshaller(context)), 10, value);
                            return ;
                        case  12 :
                            _Oper.add(((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.OperImpl.class), 13, value)));
                            return ;
                        case  11 :
                            revertToParentFromText(value);
                            return ;
                        case  6 :
                            attIdx = context.getAttribute("", "Prec");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText1(v);
                                state = 9;
                                continue outer;
                            }
                            break;
                        case  1 :
                            eatText2(value);
                            state = 2;
                            return ;
                        case  0 :
                            attIdx = context.getAttribute("", "Cat");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText2(v);
                                state = 3;
                                continue outer;
                            }
                            break;
                        case  3 :
                            attIdx = context.getAttribute("", "Assoc");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText3(v);
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
