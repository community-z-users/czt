//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.04.21 at 09:33:05 GMT 
//


package net.sourceforge.czt.z.jaxb.gen.impl;

public class NegPredElementImpl
    extends net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl
    implements net.sourceforge.czt.z.jaxb.gen.NegPredElement, com.sun.xml.bind.RIElement, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.circus.jaxb.gen.impl.runtime.ValidatableObject
{

    public final static java.lang.Class version = (net.sourceforge.czt.z.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.z.jaxb.gen.NegPredElement.class);
    }

    public java.lang.String ____jaxb_ri____getNamespaceURI() {
        return "http://czt.sourceforge.net/zml";
    }

    public java.lang.String ____jaxb_ri____getLocalName() {
        return "NegPred";
    }

    public net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.circus.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        context.startElement("http://czt.sourceforge.net/zml", "NegPred");
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
        return (net.sourceforge.czt.z.jaxb.gen.NegPredElement.class);
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
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1q\u0000~\u0000\u0003L\u0000\u0004exp2q\u0000~\u0000\u0003xq\u0000~\u0000\u0004ppsq\u0000~\u0000\u0007ppsr\u0000\u001dcom.s"
+"un.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\bppsq\u0000~\u0000\u0000sr\u0000\u0011java.la"
+"ng.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000p\u0000sq\u0000~\u0000\u0007ppsq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bpps"
+"r\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001ccom.sun.ms"
+"v.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0003xq\u0000~\u0000\u0004q\u0000~\u0000\u000fpsr\u0000 com."
+"sun.msv.grammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0003L\u0000\tnameCla"
+"ssq\u0000~\u0000\u0001xq\u0000~\u0000\u0004q\u0000~\u0000\u000fpsr\u00002com.sun.msv.grammar.Expression$AnyStr"
+"ingExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004sq\u0000~\u0000\u000e\u0001q\u0000~\u0000\u0019sr\u0000 com.sun.msv.gr"
+"ammar.AnyNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameCla"
+"ss\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$EpsilonExp"
+"ression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u001aq\u0000~\u0000\u001fsr\u0000#com.sun.msv.grammar.Si"
+"mpleNameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\f"
+"namespaceURIq\u0000~\u0000!xq\u0000~\u0000\u001ct\u0000-net.sourceforge.czt.z.jaxb.gen.Ter"
+"mA.AnnsTypet\u0000+http://java.sun.com/jaxb/xjc/dummy-elementssq\u0000"
+"~\u0000\u000bppsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpsr\u0000\u001bcom.sun.msv.grammar.DataExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L"
+"\u0000\u0002dtt\u0000\u001fLorg/relaxng/datatype/Datatype;L\u0000\u0006exceptq\u0000~\u0000\u0003L\u0000\u0004namet"
+"\u0000\u001dLcom/sun/msv/util/StringPair;xq\u0000~\u0000\u0004ppsr\u0000\"com.sun.msv.datat"
+"ype.xsd.QnameType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000*com.sun.msv.datatype.xsd.Bui"
+"ltinAtomicType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000%com.sun.msv.datatype.xsd.Concre"
+"teType\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\'com.sun.msv.datatype.xsd.XSDatatypeImpl"
+"\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0003L\u0000\fnamespaceUriq\u0000~\u0000!L\u0000\btypeNameq\u0000~\u0000!L\u0000\nwhiteSpace"
+"t\u0000.Lcom/sun/msv/datatype/xsd/WhiteSpaceProcessor;xpt\u0000 http:/"
+"/www.w3.org/2001/XMLSchemat\u0000\u0005QNamesr\u00005com.sun.msv.datatype.x"
+"sd.WhiteSpaceProcessor$Collapse\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000,com.sun.msv.da"
+"tatype.xsd.WhiteSpaceProcessor\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xpsr\u00000com.sun.msv.g"
+"rammar.Expression$NullSetExpression\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0004q\u0000~\u0000\u000fpsr"
+"\u0000\u001bcom.sun.msv.util.StringPair\u00d0t\u001ejB\u008f\u008d\u00a0\u0002\u0000\u0002L\u0000\tlocalNameq\u0000~\u0000!L\u0000\f"
+"namespaceURIq\u0000~\u0000!xpq\u0000~\u00002q\u0000~\u00001sq\u0000~\u0000 t\u0000\u0004typet\u0000)http://www.w3.o"
+"rg/2001/XMLSchema-instanceq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\u0004Annst\u0000\u001ehttp://czt.so"
+"urceforge.net/zmlq\u0000~\u0000\u001fsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000b"
+"ppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq\u0000~\u0000\u000bppsq"
+"\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 "
+"t\u00003net.sourceforge.czt.zpatt.jaxb.gen.JokerPredElementq\u0000~\u0000$s"
+"q\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000"
+" t\u0000)net.sourceforge.czt.z.jaxb.gen.ExistsPredq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000s"
+"q\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000*net.s"
+"ourceforge.czt.z.jaxb.gen.ImpliesPredq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bpps"
+"q\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000*net.sourcefor"
+"ge.czt.z.jaxb.gen.Exists1Predq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~"
+"\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000.net.sourceforge.czt.z"
+".jaxb.gen.ExprPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fps"
+"q\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000-net.sourceforge.czt.z.jax"
+"b.gen.NegPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016"
+"q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000-net.sourceforge.czt.z.jaxb.gen"
+".MemPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000f"
+"pq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000\'net.sourceforge.czt.z.jaxb.gen.True"
+"Predq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001d"
+"q\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000(net.sourceforge.czt.z.jaxb.gen.FalsePredq\u0000~\u0000$s"
+"q\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000"
+" t\u0000%net.sourceforge.czt.z.jaxb.gen.OrPredq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000"
+"\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000&net.sourc"
+"eforge.czt.z.jaxb.gen.IffPredq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~"
+"\u0000\u000fpsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000-net.sourceforge.czt.z"
+".jaxb.gen.AndPredElementq\u0000~\u0000$sq\u0000~\u0000\u0000pp\u0000sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0013q\u0000~\u0000\u000fpsq"
+"\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000\u0019q\u0000~\u0000\u001dq\u0000~\u0000\u001fsq\u0000~\u0000 t\u0000)net.sourceforge.czt.z.jaxb"
+".gen.ForallPredq\u0000~\u0000$sq\u0000~\u0000\u000bppsq\u0000~\u0000\u0016q\u0000~\u0000\u000fpq\u0000~\u0000*q\u0000~\u0000:q\u0000~\u0000\u001fsq\u0000~\u0000"
+" t\u0000\u0007NegPredq\u0000~\u0000?sr\u0000\"com.sun.msv.grammar.ExpressionPool\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/ExpressionPool$Close"
+"dHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$ClosedHash\u00d7j\u00d0"
+"N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006parentt\u0000$Lcom/sun/msv/gra"
+"mmar/ExpressionPool;xp\u0000\u0000\u0000.\u0001pq\u0000~\u0000Cq\u0000~\u0000\u0010q\u0000~\u0000\u0015q\u0000~\u0000Nq\u0000~\u0000Tq\u0000~\u0000Zq\u0000"
+"~\u0000`q\u0000~\u0000fq\u0000~\u0000lq\u0000~\u0000rq\u0000~\u0000xq\u0000~\u0000~q\u0000~\u0000Dq\u0000~\u0000\u0084q\u0000~\u0000\u008aq\u0000~\u0000\u0090q\u0000~\u0000Iq\u0000~\u0000\u0096q\u0000"
+"~\u0000\u0012q\u0000~\u0000Mq\u0000~\u0000Sq\u0000~\u0000Yq\u0000~\u0000_q\u0000~\u0000eq\u0000~\u0000kq\u0000~\u0000qq\u0000~\u0000wq\u0000~\u0000}q\u0000~\u0000\u0083q\u0000~\u0000\u0089q\u0000"
+"~\u0000Fq\u0000~\u0000Gq\u0000~\u0000\u008fq\u0000~\u0000\u0095q\u0000~\u0000\nq\u0000~\u0000Hq\u0000~\u0000Eq\u0000~\u0000Jq\u0000~\u0000\fq\u0000~\u0000Aq\u0000~\u0000%q\u0000~\u0000\u009aq\u0000"
+"~\u0000Kq\u0000~\u0000Bq\u0000~\u0000@q\u0000~\u0000\tx"));
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
            return net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this;
        }

        public void enterElement(java.lang.String ___uri, java.lang.String ___local, java.lang.String ___qname, org.xml.sax.Attributes __atts)
            throws org.xml.sax.SAXException
        {
            int attIdx;
            outer:
            while (true) {
                switch (state) {
                    case  0 :
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 1;
                            return ;
                        }
                        break;
                    case  3 :
                        revertToParentFromEnterElement(___uri, ___local, ___qname, __atts);
                        return ;
                    case  1 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("JokerPred" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExistsPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ImpliesPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Exists1Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ExprPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("MemPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("TruePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("FalsePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("OrPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("IffPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("ForallPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
                            return ;
                        }
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname, __atts);
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
                    case  3 :
                        revertToParentFromLeaveElement(___uri, ___local, ___qname);
                        return ;
                    case  2 :
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  1 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, ___uri, ___local, ___qname);
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
                            spawnHandlerFromText((((net.sourceforge.czt.z.jaxb.gen.impl.NegPredImpl)net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.this).new Unmarshaller(context)), 2, value);
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
