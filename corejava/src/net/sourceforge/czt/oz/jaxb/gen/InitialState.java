//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.13 at 03:14:32 NZST 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for InitialState complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Object-Z.xsd line 356)
 * <p>
 * <pre>
 * &lt;complexType name="InitialState">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Pred" maxOccurs="unbounded"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface InitialState
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the Pred property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Pred property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getPred().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.Exists1Pred}
     * {@link net.sourceforge.czt.z.jaxb.gen.ExistsPred}
     * {@link net.sourceforge.czt.z.jaxb.gen.Pred}
     * {@link net.sourceforge.czt.z.jaxb.gen.TruePred}
     * {@link net.sourceforge.czt.z.jaxb.gen.Pred2Element}
     * {@link net.sourceforge.czt.z.jaxb.gen.NegPredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.FalsePred}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerPredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.FactElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.PredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.OrPred}
     * {@link net.sourceforge.czt.z.jaxb.gen.MemPredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.QntPredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.ExprPredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.IffPred}
     * {@link net.sourceforge.czt.z.jaxb.gen.ForallPred}
     * {@link net.sourceforge.czt.oz.jaxb.gen.PromotedInitPredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.AndPredElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.ImpliesPred}
     * 
     */
    java.util.List getPred();

}
