//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.07.01 at 10:48:15 NZST 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for NegPred complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Z.xsd line 1582)
 * <p>
 * <pre>
 * &lt;complexType name="NegPred">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Pred">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Pred"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface NegPred
    extends net.sourceforge.czt.z.jaxb.gen.Pred
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.ExistsPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.TruePred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Pred2Element}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ForallPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.QntPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.AndPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.MemPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Exists1Pred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ExprPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ImpliesPred}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.PromotedInitPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.PredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.FactElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.OrPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.FalsePred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Pred}
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.IffPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.NegPredElement}
     */
    net.sourceforge.czt.z.jaxb.gen.Pred getPred();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.ExistsPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.TruePred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Pred2Element}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ForallPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.QntPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.AndPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.MemPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Exists1Pred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ExprPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ImpliesPred}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.PromotedInitPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.PredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.FactElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.OrPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.FalsePred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Pred}
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerPredElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.IffPred}
     *     {@link net.sourceforge.czt.z.jaxb.gen.NegPredElement}
     */
    void setPred(net.sourceforge.czt.z.jaxb.gen.Pred value);

}
