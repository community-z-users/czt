//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.02.13 at 10:27:41 GMT 
//


package net.sourceforge.czt.zpatt.jaxb.gen.impl;

public class PredTransformImpl
    extends net.sourceforge.czt.zpatt.jaxb.gen.impl.TransformImpl
    implements net.sourceforge.czt.zpatt.jaxb.gen.PredTransform, com.sun.xml.bind.JAXBObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallableObject, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializable, net.sourceforge.czt.oz.jaxb.gen.impl.runtime.ValidatableObject
{

    protected net.sourceforge.czt.z.jaxb.gen.Pred _RightPred;
    protected net.sourceforge.czt.z.jaxb.gen.Pred _LeftPred;
    public final static java.lang.Class version = (net.sourceforge.czt.zpatt.jaxb.gen.impl.JAXBVersion.class);
    private static com.sun.msv.grammar.Grammar schemaFragment;

    private final static java.lang.Class PRIMARY_INTERFACE_CLASS() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.PredTransform.class);
    }

    public net.sourceforge.czt.z.jaxb.gen.Pred getRightPred() {
        return _RightPred;
    }

    public void setRightPred(net.sourceforge.czt.z.jaxb.gen.Pred value) {
        _RightPred = value;
    }

    public net.sourceforge.czt.z.jaxb.gen.Pred getLeftPred() {
        return _LeftPred;
    }

    public void setLeftPred(net.sourceforge.czt.z.jaxb.gen.Pred value) {
        _LeftPred = value;
    }

    public net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingEventHandler createUnmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
        return new net.sourceforge.czt.zpatt.jaxb.gen.impl.PredTransformImpl.Unmarshaller(context);
    }

    public void serializeBody(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeBody(context);
        if (_LeftPred instanceof javax.xml.bind.Element) {
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _LeftPred), "LeftPred");
        } else {
            context.startElement("http://czt.sourceforge.net/zml", "Pred");
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _LeftPred), "LeftPred");
            context.endNamespaceDecls();
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _LeftPred), "LeftPred");
            context.endAttributes();
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _LeftPred), "LeftPred");
            context.endElement();
        }
        if (_RightPred instanceof javax.xml.bind.Element) {
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _RightPred), "RightPred");
        } else {
            context.startElement("http://czt.sourceforge.net/zml", "Pred");
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _RightPred), "RightPred");
            context.endNamespaceDecls();
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _RightPred), "RightPred");
            context.endAttributes();
            context.childAsBody(((com.sun.xml.bind.JAXBObject) _RightPred), "RightPred");
            context.endElement();
        }
    }

    public void serializeAttributes(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeAttributes(context);
        if (_LeftPred instanceof javax.xml.bind.Element) {
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _LeftPred), "LeftPred");
        }
        if (_RightPred instanceof javax.xml.bind.Element) {
            context.childAsAttributes(((com.sun.xml.bind.JAXBObject) _RightPred), "RightPred");
        }
    }

    public void serializeURIs(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.XMLSerializer context)
        throws org.xml.sax.SAXException
    {
        super.serializeURIs(context);
        if (_LeftPred instanceof javax.xml.bind.Element) {
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _LeftPred), "LeftPred");
        }
        if (_RightPred instanceof javax.xml.bind.Element) {
            context.childAsURIs(((com.sun.xml.bind.JAXBObject) _RightPred), "RightPred");
        }
    }

    public java.lang.Class getPrimaryInterface() {
        return (net.sourceforge.czt.zpatt.jaxb.gen.PredTransform.class);
    }

    public com.sun.msv.verifier.DocumentDeclaration createRawValidator() {
        if (schemaFragment == null) {
            schemaFragment = com.sun.xml.bind.validator.SchemaDeserializer.deserialize((
 "\u00ac\u00ed\u0000\u0005sr\u0000\u001fcom.sun.msv.grammar.SequenceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.su"
+"n.msv.grammar.BinaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0004exp1t\u0000 Lcom/sun/msv/gra"
+"mmar/Expression;L\u0000\u0004exp2q\u0000~\u0000\u0002xr\u0000\u001ecom.sun.msv.grammar.Expressi"
+"on\u00f8\u0018\u0082\u00e8N5~O\u0002\u0000\u0002L\u0000\u0013epsilonReducibilityt\u0000\u0013Ljava/lang/Boolean;L\u0000\u000b"
+"expandedExpq\u0000~\u0000\u0002xpppsr\u0000\u001dcom.sun.msv.grammar.ChoiceExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0001ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006pp"
+"sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsr\u0000\'com.sun.msv.gram"
+"mar.trex.ElementPattern\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\tnameClasst\u0000\u001fLcom/sun/ms"
+"v/grammar/NameClass;xr\u0000\u001ecom.sun.msv.grammar.ElementExp\u0000\u0000\u0000\u0000\u0000\u0000"
+"\u0000\u0001\u0002\u0000\u0002Z\u0000\u001aignoreUndeclaredAttributesL\u0000\fcontentModelq\u0000~\u0000\u0002xq\u0000~\u0000\u0003"
+"pp\u0000sq\u0000~\u0000\u0006ppsr\u0000 com.sun.msv.grammar.OneOrMoreExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr"
+"\u0000\u001ccom.sun.msv.grammar.UnaryExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\u0003expq\u0000~\u0000\u0002xq\u0000~\u0000\u0003sr"
+"\u0000\u0011java.lang.Boolean\u00cd r\u0080\u00d5\u009c\u00fa\u00ee\u0002\u0000\u0001Z\u0000\u0005valuexp\u0000psr\u0000 com.sun.msv.gr"
+"ammar.AttributeExp\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\u0003expq\u0000~\u0000\u0002L\u0000\tnameClassq\u0000~\u0000\u0014xq\u0000"
+"~\u0000\u0003q\u0000~\u0000\u001cpsr\u00002com.sun.msv.grammar.Expression$AnyStringExpress"
+"ion\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003sq\u0000~\u0000\u001b\u0001q\u0000~\u0000 sr\u0000 com.sun.msv.grammar.AnyN"
+"ameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xr\u0000\u001dcom.sun.msv.grammar.NameClass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001"
+"\u0002\u0000\u0000xpsr\u00000com.sun.msv.grammar.Expression$EpsilonExpression\u0000\u0000\u0000"
+"\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0000xq\u0000~\u0000\u0003q\u0000~\u0000!q\u0000~\u0000&sr\u0000#com.sun.msv.grammar.SimpleNameCl"
+"ass\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0002L\u0000\tlocalNamet\u0000\u0012Ljava/lang/String;L\u0000\fnamespaceU"
+"RIq\u0000~\u0000(xq\u0000~\u0000#t\u0000)net.sourceforge.czt.z.jaxb.gen.ForallPredt\u0000+"
+"http://java.sun.com/jaxb/xjc/dummy-elementssq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006pp"
+"sq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000&net.sourcefo"
+"rge.czt.z.jaxb.gen.IffPredq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cp"
+"sq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000(net.sourceforge.czt.z.ja"
+"xb.gen.FalsePredq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000"
+"\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u00003net.sourceforge.czt.zpatt.jaxb.gen"
+".JokerPredElementq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~"
+"\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000\'net.sourceforge.czt.z.jaxb.gen.Tr"
+"uePredq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~"
+"\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000*net.sourceforge.czt.z.jaxb.gen.Exists1Predq\u0000"
+"~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&s"
+"q\u0000~\u0000\'t\u0000.net.sourceforge.czt.z.jaxb.gen.ExprPredElementq\u0000~\u0000+s"
+"q\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000"
+"\'t\u0000%net.sourceforge.czt.z.jaxb.gen.OrPredq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000"
+"\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000*net.sourc"
+"eforge.czt.z.jaxb.gen.ImpliesPredq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000-net.sourceforge.c"
+"zt.z.jaxb.gen.NegPredElementq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000"
+"\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000-net.sourceforge.czt.z."
+"jaxb.gen.AndPredElementq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000"
+"~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000-net.sourceforge.czt.z.jaxb."
+"gen.MemPredElementq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000"
+"~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'t\u0000)net.sourceforge.czt.z.jaxb.gen.E"
+"xistsPredq\u0000~\u0000+sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006"
+"ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0013pp\u0000s"
+"q\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000*q\u0000~"
+"\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq"
+"\u0000~\u0000\'q\u0000~\u00001q\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 "
+"q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u00007q\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000"
+"\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000=q\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000Cq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000s"
+"q\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000Iq\u0000~"
+"\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq"
+"\u0000~\u0000\'q\u0000~\u0000Oq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 "
+"q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000Uq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000"
+"\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000[q\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000"
+"\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000aq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000s"
+"q\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000gq\u0000~"
+"\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 q\u0000~\u0000$q\u0000~\u0000&sq"
+"\u0000~\u0000\'q\u0000~\u0000mq\u0000~\u0000+sq\u0000~\u0000\u0013pp\u0000sq\u0000~\u0000\u0006ppsq\u0000~\u0000\u0018q\u0000~\u0000\u001cpsq\u0000~\u0000\u001dq\u0000~\u0000\u001cpq\u0000~\u0000 "
+"q\u0000~\u0000$q\u0000~\u0000&sq\u0000~\u0000\'q\u0000~\u0000sq\u0000~\u0000+sr\u0000\"com.sun.msv.grammar.Expression"
+"Pool\u0000\u0000\u0000\u0000\u0000\u0000\u0000\u0001\u0002\u0000\u0001L\u0000\bexpTablet\u0000/Lcom/sun/msv/grammar/Expression"
+"Pool$ClosedHash;xpsr\u0000-com.sun.msv.grammar.ExpressionPool$Clo"
+"sedHash\u00d7j\u00d0N\u00ef\u00e8\u00ed\u001c\u0003\u0000\u0003I\u0000\u0005countB\u0000\rstreamVersionL\u0000\u0006parentt\u0000$Lcom/s"
+"un/msv/grammar/ExpressionPool;xp\u0000\u0000\u0000M\u0001pq\u0000~\u0000\u009fq\u0000~\u0000\u009aq\u0000~\u0000\u0095q\u0000~\u0000\u0090q\u0000"
+"~\u0000\u008bq\u0000~\u0000\u0086q\u0000~\u0000\u0081q\u0000~\u0000oq\u0000~\u0000iq\u0000~\u0000cq\u0000~\u0000]q\u0000~\u0000Wq\u0000~\u0000Qq\u0000~\u0000Kq\u0000~\u0000Eq\u0000~\u0000?q\u0000"
+"~\u00009q\u0000~\u00003q\u0000~\u0000-q\u0000~\u0000\u0017q\u0000~\u0000\u00a4q\u0000~\u0000\u00a9q\u0000~\u0000\u00aeq\u0000~\u0000\u00b3q\u0000~\u0000\u00b8q\u0000~\u0000\u00bdq\u0000~\u0000\bq\u0000~\u0000uq\u0000"
+"~\u0000\fq\u0000~\u0000yq\u0000~\u0000\u0005q\u0000~\u0000\u007fq\u0000~\u0000\u0012q\u0000~\u0000\rq\u0000~\u0000zq\u0000~\u0000~q\u0000~\u0000\u0011q\u0000~\u0000}q\u0000~\u0000\u0010q\u0000~\u0000\u0007q\u0000"
+"~\u0000tq\u0000~\u0000\u00a0q\u0000~\u0000\u000bq\u0000~\u0000\u009bq\u0000~\u0000\u0096q\u0000~\u0000|q\u0000~\u0000\u000fq\u0000~\u0000\u0091q\u0000~\u0000\u008cq\u0000~\u0000\u0087q\u0000~\u0000\u0082q\u0000~\u0000pq\u0000"
+"~\u0000jq\u0000~\u0000dq\u0000~\u0000^q\u0000~\u0000Xq\u0000~\u0000Rq\u0000~\u0000Lq\u0000~\u0000Fq\u0000~\u0000@q\u0000~\u0000:q\u0000~\u00004q\u0000~\u0000.q\u0000~\u0000\u001aq\u0000"
+"~\u0000\u00a5q\u0000~\u0000\u00aaq\u0000~\u0000xq\u0000~\u0000\u00afq\u0000~\u0000\u00b4q\u0000~\u0000\u00b9q\u0000~\u0000\u00beq\u0000~\u0000\nq\u0000~\u0000wq\u0000~\u0000{q\u0000~\u0000\u000eq\u0000~\u0000\tq\u0000"
+"~\u0000vx"));
        }
        return new com.sun.msv.verifier.regexp.REDocumentDeclaration(schemaFragment);
    }

    public class Unmarshaller
        extends net.sourceforge.czt.oz.jaxb.gen.impl.runtime.AbstractUnmarshallingEventHandlerImpl
    {


        public Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context) {
            super(context, "--------");
        }

        protected Unmarshaller(net.sourceforge.czt.oz.jaxb.gen.impl.runtime.UnmarshallingContext context, int startState) {
            this(context);
            state = startState;
        }

        public java.lang.Object owner() {
            return net.sourceforge.czt.zpatt.jaxb.gen.impl.PredTransformImpl.this;
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
                        if (("ForallPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ForallPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ForallPredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("IffPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.IffPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.IffPredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("FalsePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.FalsePredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.FalsePredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("JokerPred" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerPredElementImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("TruePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.TruePredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.TruePredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Exists1Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.Exists1PredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.Exists1PredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("ExprPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ExprPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ExprPredElementImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("OrPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.OrPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OrPredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("ImpliesPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ImpliesPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ImpliesPredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("MemPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.MemPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.MemPredElementImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("ExistsPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ExistsPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ExistsPredImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 6;
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.PredElementImpl.class), 2, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        break;
                    case  0 :
                        spawnHandlerFromEnterElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.TransformImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.PredTransformImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname, __atts);
                        return ;
                    case  6 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 7, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 7, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  4 :
                        if (("Anns" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 5, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 5, ___uri, ___local, ___qname, __atts));
                        return ;
                    case  2 :
                        if (("ForallPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ForallPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ForallPredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("IffPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.IffPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.IffPredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("FalsePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.FalsePredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.FalsePredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("JokerPred" == ___local)&&("http://czt.sourceforge.net/zpatt" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.zpatt.jaxb.gen.impl.JokerPredElementImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("TruePred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.TruePredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.TruePredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Exists1Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.Exists1PredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.Exists1PredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("ExprPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ExprPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ExprPredElementImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("OrPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.OrPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.OrPredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("ImpliesPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ImpliesPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ImpliesPredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("NegPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.NegPredElementImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("AndPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.AndPredElementImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("MemPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.MemPredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.MemPredElementImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("ExistsPred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.ExistsPredImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.ExistsPredImpl.class), 3, ___uri, ___local, ___qname, __atts));
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.pushAttributes(__atts, false);
                            state = 4;
                            return ;
                        }
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredElementImpl) spawnChildFromEnterElement((net.sourceforge.czt.z.jaxb.gen.impl.PredElementImpl.class), 3, ___uri, ___local, ___qname, __atts));
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
                    case  5 :
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 3;
                            return ;
                        }
                        break;
                    case  0 :
                        spawnHandlerFromLeaveElement((((net.sourceforge.czt.zpatt.jaxb.gen.impl.TransformImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.PredTransformImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  7 :
                        if (("Pred" == ___local)&&("http://czt.sourceforge.net/zml" == ___uri)) {
                            context.popAttributes();
                            state = 2;
                            return ;
                        }
                        break;
                    case  6 :
                        _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 7, ___uri, ___local, ___qname));
                        return ;
                    case  4 :
                        _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromLeaveElement((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 5, ___uri, ___local, ___qname));
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
                    case  0 :
                        spawnHandlerFromEnterAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.TransformImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.PredTransformImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  6 :
                        _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 7, ___uri, ___local, ___qname));
                        return ;
                    case  4 :
                        _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromEnterAttribute((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 5, ___uri, ___local, ___qname));
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
                    case  0 :
                        spawnHandlerFromLeaveAttribute((((net.sourceforge.czt.zpatt.jaxb.gen.impl.TransformImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.PredTransformImpl.this).new Unmarshaller(context)), 1, ___uri, ___local, ___qname);
                        return ;
                    case  6 :
                        _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 7, ___uri, ___local, ___qname));
                        return ;
                    case  4 :
                        _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromLeaveAttribute((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 5, ___uri, ___local, ___qname));
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
                        case  0 :
                            spawnHandlerFromText((((net.sourceforge.czt.zpatt.jaxb.gen.impl.TransformImpl)net.sourceforge.czt.zpatt.jaxb.gen.impl.PredTransformImpl.this).new Unmarshaller(context)), 1, value);
                            return ;
                        case  6 :
                            _LeftPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 7, value));
                            return ;
                        case  4 :
                            _RightPred = ((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl) spawnChildFromText((net.sourceforge.czt.z.jaxb.gen.impl.PredImpl.class), 5, value));
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
