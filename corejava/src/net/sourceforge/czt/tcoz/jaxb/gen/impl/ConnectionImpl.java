//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.tcoz.jaxb.gen.impl;

public class ConnectionImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl
    implements net.sourceforge.czt.tcoz.jaxb.gen.Connection, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    protected net.sourceforge.czt.oz.jaxb.gen.RefNameList _Channels;
    protected net.sourceforge.czt.oz.jaxb.gen.RefNameList _RightProcess;
    protected net.sourceforge.czt.oz.jaxb.gen.RefNameList _LeftProcess;
    public final static java.lang.Class version = (net.sourceforge.czt.tcoz.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.tcoz.jaxb.gen.Connection.class);
    }

    public net.sourceforge.czt.oz.jaxb.gen.RefNameList getChannels() {
        return _Channels;
    }

    public void setChannels(net.sourceforge.czt.oz.jaxb.gen.RefNameList value) {
        _Channels = value;
    }

    public net.sourceforge.czt.oz.jaxb.gen.RefNameList getRightProcess() {
        return _RightProcess;
    }

    public void setRightProcess(net.sourceforge.czt.oz.jaxb.gen.RefNameList value) {
        _RightProcess = value;
    }

    public net.sourceforge.czt.oz.jaxb.gen.RefNameList getLeftProcess() {
        return _LeftProcess;
    }

    public void setLeftProcess(net.sourceforge.czt.oz.jaxb.gen.RefNameList value) {
        _LeftProcess = value;
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeBody(context);
        context.startElement("http://czt.sourceforge.net/tcoz", "LeftProcess");
        context.childAsURIs(((com.sun.xml.bind.JAXBObject) _LeftProcess), "LeftProcess");
        context.endNamespaceDecls();
        context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _LeftProcess), "LeftProcess");
        context.endAttributes();
        context.childAsBody(((com.sun.xml.bind.JAXBObject) _LeftProcess), "LeftProcess");
        context.endElement();
        context.startElement("http://czt.sourceforge.net/tcoz", "RightProcess");
        context.childAsURIs(((com.sun.xml.bind.JAXBObject) _RightProcess), "RightProcess");
        context.endNamespaceDecls();
        context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _RightProcess), "RightProcess");
        context.endAttributes();
        context.childAsBody(((com.sun.xml.bind.JAXBObject) _RightProcess), "RightProcess");
        context.endElement();
        context.startElement("http://czt.sourceforge.net/tcoz", "Channels");
        context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Channels), "Channels");
        context.endNamespaceDecls();
        context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Channels), "Channels");
        context.endAttributes();
        context.childAsBody(((com.sun.xml.bind.JAXBObject) _Channels), "Channels");
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
        return (net.sourceforge.czt.tcoz.jaxb.gen.Connection.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.su"
+"n.msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1t\u0000 Lcom/sun/msv/gra"
+"mmar/Expression;L\u0000\u0004exp2q\u0000~\u0000\u0002xr\u0000\u001ecom.sun.msv.grammar.Expressi"
+"on\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0003I\u0000\u000ecachedHashCodeL\u0000\u0013epsilonReducibilityt\u0000\u0013Ljava"
+"/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0002xp\f\u0092\u00f4\u00b2ppsq\u0000~\u0000\u0000\tH\u00d36ppsq\u0000~\u0000\u0000\u0005"
+"\u00fc}Xppsr\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0001\u00034*&p"
+"psr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\tna"
+"meClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv.gra"
+"mmar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000\fco"
+"ntentModelq\u0000~\u0000\u0002xq\u0000~\u0000\u0003\u00034*\u001bsr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005"
+"valuexp\u0000p\u0000sq\u0000~\u0000\u0000\u00034*\u0010ppsq\u0000~\u0000\n\u0000(x3pp\u0000sq\u0000~\u0000\b\u0000(x(ppsr\u0000 com.sun.m"
+"sv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar.Un"
+"aryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0002xq\u0000~\u0000\u0003\u0000(x\u001dq\u0000~\u0000\u000fpsr\u0000 com.sun.msv."
+"grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0002L\u0000\tnameClassq\u0000~\u0000\u000bx"
+"q\u0000~\u0000\u0003\u0000(x\u001aq\u0000~\u0000\u000fpsr\u00002com.sun.msv.grammar.Expression$AnyStringE"
+"xpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003\u0000\u0000\u0000\bsq\u0000~\u0000\u000e\u0001q\u0000~\u0000\u0019sr\u0000 com.sun.msv.gr"
+"ammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameCla"
+"ss\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$EpsilonExp"
+"ression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003\u0000\u0000\u0000\tq\u0000~\u0000\u001aq\u0000~\u0000\u001fsr\u0000#com.sun.msv.gramma"
+"r.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String"
+";L\u0000\fnamespaceURIq\u0000~\u0000!xq\u0000~\u0000\u001ct\u0000-net.sourceforge.czt.z.jaxb.gen"
+".TermA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/dummy-element"
+"ssq\u0000~\u0000\b\u0003\u000b\u00b1\u00d8ppsq\u0000~\u0000\u0016\u0003\u000b\u00b1\u00cdq\u0000~\u0000\u000fpsr\u0000\u001bcom.sun.msv.grammar.DataExp"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Datatype;L\u0000\u0006exceptq"
+"\u0000~\u0000\u0002L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~\u0000\u0003\u0001[\u0001,ppsr\u0000\"c"
+"om.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv."
+"datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.dat"
+"atype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xs"
+"d.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000!L\u0000\btypeNameq\u0000"
+"~\u0000!L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/datatype/xsd/WhiteSpaceProce"
+"ssor;xpt\u0000 http://www.w3.org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.su"
+"n.msv.datatype.xsd.WhiteSpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000,com.sun.msv.datatype.xsd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xps"
+"r\u00000com.sun.msv.grammar.Expression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002"
+"\u0000\u0000xq\u0000~\u0000\u0003\u0000\u0000\u0000\nq\u0000~\u0000\u000fpsr\u0000\u001bcom.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002"
+"L\u0000\tlocalNameq\u0000~\u0000!L\u0000\fnamespaceURIq\u0000~\u0000!xpq\u0000~\u00002q\u0000~\u00001sq\u0000~\u0000 t\u0000\u0004ty"
+"pet\u0000)http://www.w3.org/2001/XMLSchema-instanceq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\u0004"
+"Annst\u0000\u001ehttp://czt.sourceforge.net/zmlq\u0000~\u0000\u001fsq\u0000~\u0000\n\u0002\u00c8S-pp\u0000sq\u0000~\u0000"
+"\u0000\u0002\u00c8S\"ppsq\u0000~\u0000\n\u0000(x3pp\u0000sq\u0000~\u0000\b\u0000(x(ppsq\u0000~\u0000\u0013\u0000(x\u001dq\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000(x\u001aq\u0000"
+"~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000+net.sourceforge.czt.oz.jaxb.gen."
+"RefNameListq\u0000~\u0000$sq\u0000~\u0000\b\u0002\u009f\u00da\u00eappsq\u0000~\u0000\u0016\u0002\u009f\u00da\u00dfq\u0000~\u0000\u000fpq\u0000~\u0000*sq\u0000~\u0000 q\u0000~\u0000;"
+"q\u0000~\u0000<q\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\u000bLeftProcesst\u0000\u001fhttp://czt.sourceforge.net/"
+"tcozsq\u0000~\u0000\n\u0003LU\u00d9pp\u0000sq\u0000~\u0000\u0000\u0003LU\u00ceppsq\u0000~\u0000\n\u0000(x3pp\u0000sq\u0000~\u0000\b\u0000(x(ppsq\u0000~\u0000\u0013"
+"\u0000(x\u001dq\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000(x\u001aq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 q\u0000~\u0000Gq\u0000~\u0000$sq\u0000"
+"~\u0000\b\u0003#\u00dd\u0096ppsq\u0000~\u0000\u0016\u0003#\u00dd\u008bq\u0000~\u0000\u000fpq\u0000~\u0000*sq\u0000~\u0000 q\u0000~\u0000;q\u0000~\u0000<q\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\f"
+"RightProcessq\u0000~\u0000Msq\u0000~\u0000\n\u0003J!wpp\u0000sq\u0000~\u0000\u0000\u0003J!lppsq\u0000~\u0000\n\u0000(x3pp\u0000sq\u0000~\u0000"
+"\b\u0000(x(ppsq\u0000~\u0000\u0013\u0000(x\u001dq\u0000~\u0000\u000fpsq\u0000~\u0000\u0016\u0000(x\u001aq\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 "
+"q\u0000~\u0000Gq\u0000~\u0000$sq\u0000~\u0000\b\u0003!\u00a94ppsq\u0000~\u0000\u0016\u0003!\u00a9)q\u0000~\u0000\u000fpq\u0000~\u0000*sq\u0000~\u0000 q\u0000~\u0000;q\u0000~\u0000<q"
+"\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\bChannelsq\u0000~\u0000Msr\u0000\"com.sun.msv.grammar.Expression"
+"Pool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/Expression"
+"Pool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$Clo"
+"sedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0002\u0000\u0004I\u0000\u0005countI\u0000\tthresholdL\u0000\u0006parentq\u0000~\u0000g[\u0000\u0005table"
+"t\u0000![Lcom/sun/msv/grammar/Expression;xp\u0000\u0000\u0000\u0014\u0000\u0000\u00009pur\u0000![Lcom.sun"
+".msv.grammar.Expression;\u00d68D\u00c3]\u00ad\u00a7\n\u0002\u0000\u0000xp\u0000\u0000\u0000\u00bfppppppppppppppppppp"
+"ppppq\u0000~\u0000\u0010pppppppq\u0000~\u0000Apq\u0000~\u0000%ppq\u0000~\u0000[ppq\u0000~\u0000\u0006pq\u0000~\u0000Hpppq\u0000~\u0000\tq\u0000~\u0000a"
+"ppppppppppppppppppppppppppppppppppppppppppppq\u0000~\u0000\u0005q\u0000~\u0000\u0007pppppp"
+"pppppppppppppppppppppppq\u0000~\u0000Opppppppppq\u0000~\u0000Upppppppppppppppppp"
+"pppq\u0000~\u0000\u0015q\u0000~\u0000Dq\u0000~\u0000Rq\u0000~\u0000^pppppppq\u0000~\u0000\u0012q\u0000~\u0000Cq\u0000~\u0000Qq\u0000~\u0000]pppppppppp"
+"pppppppppppp"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.oz.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "-----------");
        }

        protected Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  1 :
                        if (("LeftProcess" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 2;
                            return ;
                        }
                        break;
                    case  0 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  4 :
                        if (("RightProcess" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 5;
                            return ;
                        }
                        break;
                    case  2 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            _LeftProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _LeftProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 3, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  10 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  8 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _Channels = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 9, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            _Channels = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 9, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _Channels = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 9, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  5 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 6, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Name" == ___local)&&("http://czt.sourceforge.net/object-z" == ___uri)) {
                            _RightProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 6, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _RightProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 6, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  7 :
                        if (("Channels" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 8;
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
                    case  0 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  9 :
                        if (("Channels" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.popAttributes();
                            state = 10;
                            return ;
                        }
                        break;
                    case  2 :
                        _LeftProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromLeaveElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  6 :
                        if (("RightProcess" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
                            context.popAttributes();
                            state = 7;
                            return ;
                        }
                        break;
                    case  10 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  8 :
                        _Channels = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromLeaveElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 9, ___uri, ___local, ___qname));
                        return ;
                    case  5 :
                        _RightProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromLeaveElement((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 6, ___uri, ___local, ___qname));
                        return ;
                    case  3 :
                        if (("LeftProcess" == ___local)&&("http://czt.sourceforge.net/tcoz" == ___uri)) {
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
                    case  0 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        _LeftProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  10 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  8 :
                        _Channels = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 9, ___uri, ___local, ___qname));
                        return ;
                    case  5 :
                        _RightProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 6, ___uri, ___local, ___qname));
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
                    case  0 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        _LeftProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 3, ___uri, ___local, ___qname));
                        return ;
                    case  10 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  8 :
                        _Channels = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 9, ___uri, ___local, ___qname));
                        return ;
                    case  5 :
                        _RightProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 6, ___uri, ___local, ___qname));
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
                        case  0 :
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.TermAImpl)net.sourceforge.czt.tcoz.jaxb.gen.impl.ConnectionImpl.this).new Unmarshaller(context)), 1, value);
                            return ;
                        case  2 :
                            _LeftProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromText((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 3, value));
                            return ;
                        case  10 :
                            revertToParentFromText(value);
                            return ;
                        case  8 :
                            _Channels = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromText((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 9, value));
                            return ;
                        case  5 :
                            _RightProcess = ((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl) spawnChildFromText((net.sourceforge.czt.oz.jaxb.gen.impl.RefNameListImpl.class), 6, value));
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
