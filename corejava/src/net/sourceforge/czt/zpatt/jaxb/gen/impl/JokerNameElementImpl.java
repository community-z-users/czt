//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.zpatt.jaxb.gen.impl;

public class JokerNameElementImpl
    extends net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl
    implements net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.zpatt.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/zpatt";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "JokerName";
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/zpatt", "JokerName");
        super.serializeURIs(context);
        context.endNamespaceDecls();
        super.serializeAttributes(context);
        context.endAttributes();
        super.serializeBody(context);
        context.endElement();
    }

    public void serializeAttributes(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
    }

    public void serializeURIs(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElement.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\'com.sun.msv.grammar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000"
+"\tnameClasst\u0000\u001fLcom/sun/msv/grammar/NameClass;xr\u0000\u001ecom.sun.msv."
+"grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000"
+"\fcontentModelt\u0000 Lcom/sun/msv/grammar/Expression;xr\u0000\u001ecom.sun."
+"msv.grammar.Expression\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0002L\u0000\u0013epsilonReducibilityt\u0000\u0013Lj"
+"ava/lang/Boolean;L\u0000\u000bexpandedExpq\u0000~\u0000\u0003xppp\u0000sr\u0000\u001fcom.sun.msv.gra"
+"mmar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.BinaryExp"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~\u0000\u0004ppsq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007pps"
+"q\u0000~\u0000\u0007ppsq\u0000~\u0000\u0007ppsr\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000x"
+"q\u0000~\u0000\bppsq\u0000~\u0000\u0000sr\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq"
+"\u0000~\u0000\u0007ppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000eppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq"
+"\u0000~\u0000\u0003xq\u0000~\u0000\u0004q\u0000~\u0000\u0012psr\u0000 com.sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001"
+"\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tnameClassq\u0000~\u0000\u0001xq\u0000~\u0000\u0004q\u0000~\u0000\u0012psr\u00002com.sun.msv.g"
+"rammar.Expression$AnyStringExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004sq\u0000~\u0000\u0011"
+"\u0001q\u0000~\u0000\u001csr\u0000 com.sun.msv.grammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom"
+".sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.gramm"
+"ar.Expression$EpsilonExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u001dq\u0000~\u0000\"sr"
+"\u0000#com.sun.msv.grammar.SimpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalName"
+"t\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceURIq\u0000~\u0000$xq\u0000~\u0000\u001ft\u0000-net.source"
+"forge.czt.z.jaxb.gen.TermA.AnnsTypet\u0000+http://java.sun.com/ja"
+"xb/xjc/dummy-elementssq\u0000~\u0000\u000eppsq\u0000~\u0000\u0019q\u0000~\u0000\u0012psr\u0000\u001bcom.sun.msv.gra"
+"mmar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Datatyp"
+"e;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~\u0000"
+"\u0004ppsr\u0000\"com.sun.msv.datatype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com."
+"sun.msv.datatype.xsd.BuiltinAtomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun"
+".msv.datatype.xsd.ConcreteType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.dat"
+"atype.xsd.XSDatatypeImpl\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000$L\u0000\bty"
+"peNameq\u0000~\u0000$L\u0000\nwhiteSpacet\u0000.Lcom/sun/msv/datatype/xsd/WhiteSp"
+"aceProcessor;xpt\u0000 http://www.w3.org/2001/XMLSchemat\u0000\u0005QNamesr"
+"\u00005com.sun.msv.datatype.xsd.WhiteSpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.datatype.xsd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$NullSetExpression\u0000"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u0012psr\u0000\u001bcom.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d"
+"\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000$L\u0000\fnamespaceURIq\u0000~\u0000$xpq\u0000~\u00005q\u0000~\u00004sq\u0000~\u0000#t"
+"\u0000\u0004typet\u0000)http://www.w3.org/2001/XMLSchema-instanceq\u0000~\u0000\"sq\u0000~\u0000"
+"#t\u0000\u0004Annst\u0000\u001ehttp://czt.sourceforge.net/zmlq\u0000~\u0000\"sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000"
+"\u0007ppsq\u0000~\u0000*q\u0000~\u0000\u0012psr\u0000#com.sun.msv.datatype.xsd.StringType\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0001Z\u0000\risAlwaysValidxq\u0000~\u0000/q\u0000~\u00004t\u0000\u0006stringsr\u00005com.sun.msv.dat"
+"atype.xsd.WhiteSpaceProcessor$Preserve\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u00007\u0001q\u0000~\u0000"
+":sq\u0000~\u0000;q\u0000~\u0000Hq\u0000~\u00004sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0019q\u0000~\u0000\u0012pq\u0000~\u0000-q\u0000~\u0000=q\u0000~\u0000\"sq\u0000~\u0000#t\u0000"
+"\u0004Wordq\u0000~\u0000Bsq\u0000~\u0000\u000eppsq\u0000~\u0000\u0016q\u0000~\u0000\u0012psq\u0000~\u0000\u000eq\u0000~\u0000\u0012psq\u0000~\u0000\u000eq\u0000~\u0000\u0012psq\u0000~\u0000\u000e"
+"q\u0000~\u0000\u0012psq\u0000~\u0000\u0000q\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0016q\u0000~\u0000\u0012psq\u0000~\u0000\u0019q\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000"
+" q\u0000~\u0000\"sq\u0000~\u0000#t\u0000)net.sourceforge.czt.z.jaxb.gen.NextStrokeq\u0000~\u0000"
+"\'sq\u0000~\u0000\u0000q\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0016q\u0000~\u0000\u0012psq\u0000~\u0000\u0019q\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000"
+"\"sq\u0000~\u0000#t\u0000/net.sourceforge.czt.z.jaxb.gen.NumStrokeElementq\u0000~"
+"\u0000\'sq\u0000~\u0000\u0000q\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0016q\u0000~\u0000\u0012psq\u0000~\u0000\u0019q\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~"
+"\u0000\"sq\u0000~\u0000#t\u0000(net.sourceforge.czt.z.jaxb.gen.OutStrokeq\u0000~\u0000\'sq\u0000~"
+"\u0000\u0000q\u0000~\u0000\u0012p\u0000sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0016q\u0000~\u0000\u0012psq\u0000~\u0000\u0019q\u0000~\u0000\u0012pq\u0000~\u0000\u001cq\u0000~\u0000 q\u0000~\u0000\"sq\u0000~"
+"\u0000#t\u0000\'net.sourceforge.czt.z.jaxb.gen.InStrokeq\u0000~\u0000\'q\u0000~\u0000\"sq\u0000~\u0000\u000e"
+"ppsq\u0000~\u0000\u0019q\u0000~\u0000\u0012psq\u0000~\u0000*ppsr\u0000\u001fcom.sun.msv.datatype.xsd.IDType\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000#com.sun.msv.datatype.xsd.NcnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000\"com.sun.msv.datatype.xsd.TokenType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000Fq\u0000~\u00004t\u0000"
+"\u0002IDq\u0000~\u00008\u0000q\u0000~\u0000:sq\u0000~\u0000;q\u0000~\u0000tq\u0000~\u00004sq\u0000~\u0000#t\u0000\u0002Idt\u0000\u0000q\u0000~\u0000\"sq\u0000~\u0000\u000eppsq\u0000"
+"~\u0000\u0019q\u0000~\u0000\u0012pq\u0000~\u0000Esq\u0000~\u0000#t\u0000\u0004Nameq\u0000~\u0000xq\u0000~\u0000\"sq\u0000~\u0000\u000eppsq\u0000~\u0000\u0019q\u0000~\u0000\u0012pq\u0000~"
+"\u0000-q\u0000~\u0000=q\u0000~\u0000\"sq\u0000~\u0000#t\u0000\tJokerNamet\u0000 http://czt.sourceforge.net/"
+"zpattsr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexp"
+"Tablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$ClosedHash;xpsr\u0000"
+"-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005"
+"countB\u0000\rstreamVersionL\u0000\u0006parentt\u0000$Lcom/sun/msv/grammar/Expres"
+"sionPool;xp\u0000\u0000\u0000\u001c\u0001pq\u0000~\u0000Vq\u0000~\u0000\\q\u0000~\u0000bq\u0000~\u0000hq\u0000~\u0000Qq\u0000~\u0000Pq\u0000~\u0000\tq\u0000~\u0000(q\u0000~"
+"\u0000Lq\u0000~\u0000yq\u0000~\u0000}q\u0000~\u0000\nq\u0000~\u0000\rq\u0000~\u0000\u0013q\u0000~\u0000\u0018q\u0000~\u0000Wq\u0000~\u0000]q\u0000~\u0000cq\u0000~\u0000iq\u0000~\u0000Dq\u0000~"
+"\u0000Sq\u0000~\u0000Rq\u0000~\u0000\u000bq\u0000~\u0000Tq\u0000~\u0000\fq\u0000~\u0000mq\u0000~\u0000\u000fq\u0000~\u0000\u0015x"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.circus.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "----");
        }

        protected Unmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this;
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
                    case  1 :
                        attIdx = context.getAttribute("", "Name");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().enterElement(___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().enterElement(___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Word" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  0 :
                        if (("JokerName" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
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
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("JokerName" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  1 :
                        attIdx = context.getAttribute("", "Name");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveElement(___uri, ___local, ___qname);
                            return ;
                        }
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveElement(___uri, ___local, ___qname);
                            return ;
                        }
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        if (("Name" == ___local)&&("" == ___uri)) {
                            spawnHandlerFromEnterAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                            return ;
                        }
                        if (("Id" == ___local)&&("" == ___uri)) {
                            spawnHandlerFromEnterAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
                            return ;
                        }
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        attIdx = context.getAttribute("", "Name");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveAttribute(___uri, ___local, ___qname);
                            return ;
                        }
                        attIdx = context.getAttribute("", "Id");
                        if (attIdx >= 0) {
                            context.consumeAttribute(attIdx);
                            context.getCurrentHandler().leaveAttribute(___uri, ___local, ___qname);
                            return ;
                        }
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            attIdx = context.getAttribute("", "Name");
                            if (attIdx >= 0) {
                                context.consumeAttribute(attIdx);
                                context.getCurrentHandler().text(value);
                                return ;
                            }
                            attIdx = context.getAttribute("", "Id");
                            if (attIdx >= 0) {
                                context.consumeAttribute(attIdx);
                                context.getCurrentHandler().text(value);
                                return ;
                            }
                            spawnHandlerFromText((((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerNameElementImpl.this).new Unmarshaller(context)), 2, value);
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
