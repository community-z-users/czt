//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.zpatt.jaxb.gen.impl;

public class RuleImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl
    implements net.sourceforge.czt.zpatt.jaxb.gen.Rule, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    protected com.sun.xml.bind.util.ListImpl _Sequent;
    protected java.lang.String _Name;
    public final static java.lang.Class version = (net.sourceforge.czt.zpatt.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.Rule.class);
    }

    protected com.sun.xml.bind.util.ListImpl _getSequent() {
        if (_Sequent == null) {
            _Sequent = new com.sun.xml.bind.util.ListImpl(new java.util.ArrayList());
        }
        return _Sequent;
    }

    public java.util.List getSequent() {
        return _getSequent();
    }

    public java.lang.String getName() {
        return _Name;
    }

    public void setName(java.lang.String value) {
        _Name = value;
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx1 = 0;
        final int len1 = ((_Sequent == null)? 0 :_Sequent.size());
        super.serializeBody(context);
        while (idx1 != len1) {
            if (_Sequent.get(idx1) instanceof javax.xml.bind.Element) {
                context.childAsBody(((com.sun.xml.bind.JAXBObject) _Sequent.get(idx1 ++)), "Sequent");
            } else {
                context.startElement("http://czt.sourceforge.net/zpatt", "Sequent");
                int idx_0 = idx1;
                context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Sequent.get(idx_0 ++)), "Sequent");
                context.endNamespaceDecls();
                int idx_1 = idx1;
                context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Sequent.get(idx_1 ++)), "Sequent");
                context.endAttributes();
                context.childAsBody(((com.sun.xml.bind.JAXBObject) _Sequent.get(idx1 ++)), "Sequent");
                context.endElement();
            }
        }
    }

    public void serializeAttributes(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx1 = 0;
        final int len1 = ((_Sequent == null)? 0 :_Sequent.size());
        if (_Name!= null) {
            context.startAttribute("", "Name");
            try {
                context.text(((java.lang.String) _Name), "Name");
            } catch (java.lang.Exception e) {
                net.sourceforge.czt.circus.jaxb.gen.impl.runtime.Util.handlePrintConversionException(this, e, context);
            }
            context.endAttribute();
        }
        super.serializeAttributes(context);
        while (idx1 != len1) {
            if (_Sequent.get(idx1) instanceof javax.xml.bind.Element) {
                context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _Sequent.get(idx1 ++)), "Sequent");
            } else {
                idx1 += 1;
            }
        }
    }

    public void serializeURIs(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        int idx1 = 0;
        final int len1 = ((_Sequent == null)? 0 :_Sequent.size());
        super.serializeURIs(context);
        while (idx1 != len1) {
            if (_Sequent.get(idx1) instanceof javax.xml.bind.Element) {
                context.childAsURIs(((com.sun.xml.bind.JAXBObject) _Sequent.get(idx1 ++)), "Sequent");
            } else {
                idx1 += 1;
            }
        }
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.Rule.class);
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
+".net/zmlq\u0000~\u0000\u001esq\u0000~\u0000\u0012ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0012"
+"q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00005net.sourceforge.cz"
+"t.zpatt.jaxb.gen.DefnSequentElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007ppsq\u0000"
+"~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00005net.sourceforge"
+".czt.zpatt.jaxb.gen.PredSequentElementq\u0000~\u0000#sq\u0000~\u0000\tpp\u0000sq\u0000~\u0000\u0007pp"
+"sq\u0000~\u0000\u0012q\u0000~\u0000\u000epsq\u0000~\u0000\u0015q\u0000~\u0000\u000epq\u0000~\u0000\u0018q\u0000~\u0000\u001cq\u0000~\u0000\u001esq\u0000~\u0000\u001ft\u00005net.sourcefo"
+"rge.czt.zpatt.jaxb.gen.TypeSequentElementq\u0000~\u0000#sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0015"
+"q\u0000~\u0000\u000epsq\u0000~\u0000&q\u0000~\u0000\u000epsr\u0000#com.sun.msv.datatype.xsd.StringType\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001Z\u0000\risAlwaysValidxq\u0000~\u0000+q\u0000~\u00000t\u0000\u0006stringsr\u00005com.sun.msv."
+"datatype.xsd.WhiteSpaceProcessor$Preserve\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u00003\u0001q"
+"\u0000~\u00006sq\u0000~\u00007q\u0000~\u0000Yq\u0000~\u00000sq\u0000~\u0000\u001ft\u0000\u0004Namet\u0000\u0000q\u0000~\u0000\u001esr\u0000\"com.sun.msv.gra"
+"mmar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/gra"
+"mmar/ExpressionPool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.Exp"
+"ressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006"
+"parentt\u0000$Lcom/sun/msv/grammar/ExpressionPool;xp\u0000\u0000\u0000\u0011\u0001pq\u0000~\u0000\u0014q\u0000"
+"~\u0000Dq\u0000~\u0000Jq\u0000~\u0000Pq\u0000~\u0000\u0005q\u0000~\u0000?q\u0000~\u0000\u0011q\u0000~\u0000Cq\u0000~\u0000Iq\u0000~\u0000Oq\u0000~\u0000Aq\u0000~\u0000\bq\u0000~\u0000$q\u0000"
+"~\u0000Tq\u0000~\u0000\u000fq\u0000~\u0000\u0006q\u0000~\u0000@x"));
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
            return net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  6 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("SequentContext" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("SequentContext" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, ___uri, ___local, ___qname, __atts)));
                        return ;
                    case  5 :
                        if (("DefnSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("PredSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.PredSequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.PredSequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("TypeSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.TypeSequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.TypeSequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Sequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 6;
                            return ;
                        }
                        if (("Sequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        attIdx = context.getAttribute("", "Name");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 3;
                            continue outer;
                        }
                        state = 3;
                        continue outer;
                    case  3 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.this).new Unmarshaller(context)), 4, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.this).new Unmarshaller(context)), 4, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  4 :
                        if (("DefnSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.DefnSequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("PredSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.PredSequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.PredSequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("TypeSequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.TypeSequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.TypeSequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        if (("Sequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 6;
                            return ;
                        }
                        if (("Sequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentElementImpl.class), 5, ___uri, ___local, ___qname, __atts)));
                            return ;
                        }
                        break;
                }
                super.enterElement(___uri, ___local, ___qname, __atts);
                break;
            }
        }

        private void eatText1(final java.lang.String value)
            throws org.xml.sax.SAXException
        {
            try {
                _Name = value;
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
                    case  6 :
                        _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromLeaveElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, ___uri, ___local, ___qname)));
                        return ;
                    case  7 :
                        if (("Sequent" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            context.popAttributes();
                            state = 5;
                            return ;
                        }
                        break;
                    case  5 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        attIdx = context.getAttribute("", "Name");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 3;
                            continue outer;
                        }
                        state = 3;
                        continue outer;
                    case  3 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.this).new Unmarshaller(context)), 4, ___uri, ___local, ___qname);
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
                        _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, ___uri, ___local, ___qname)));
                        return ;
                    case  5 :
                        revertToParentFromEnterAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        if (("Name" == ___local)&&("" == ___uri)) {
                            state = 1;
                            return ;
                        }
                        state = 3;
                        continue outer;
                    case  3 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.this).new Unmarshaller(context)), 4, ___uri, ___local, ___qname);
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
                        _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, ___uri, ___local, ___qname)));
                        return ;
                    case  5 :
                        revertToParentFromLeaveAttribute(___uri, ___local, ___qname);
                        return ;
                    case  0 :
                        attIdx = context.getAttribute("", "Name");
                        if (attIdx >= 0) {
                            final java.lang.String v = context.eatAttribute(attIdx);
                            eatText1(v);
                            state = 3;
                            continue outer;
                        }
                        state = 3;
                        continue outer;
                    case  3 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.this).new Unmarshaller(context)), 4, ___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("Name" == ___local)&&("" == ___uri)) {
                            state = 3;
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
                        case  6 :
                            _getSequent().add(((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl) spawnChildFromText((net.sourceforge.czt.zpatt.jaxb.gen.impl.SequentImpl.class), 7, value)));
                            return ;
                        case  5 :
                            revertToParentFromText(value);
                            return ;
                        case  1 :
                            eatText1(value);
                            state = 2;
                            return ;
                        case  0 :
                            attIdx = context.getAttribute("", "Name");
                            if (attIdx >= 0) {
                                final java.lang.String v = context.eatAttribute(attIdx);
                                eatText1(v);
                                state = 3;
                                continue outer;
                            }
                            state = 3;
                            continue outer;
                        case  3 :
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.ParaImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.RuleImpl.this).new Unmarshaller(context)), 4, value);
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
