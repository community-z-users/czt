//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for DistOpExpr complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Object-Z.xsd line 286)
 * <p>
 * <pre>
 * &lt;complexType name="DistOpExpr">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/object-z}OpExpr">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}SchText"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}OpExpr"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface DistOpExpr
    extends net.sourceforge.czt.oz.jaxb.gen.OpExpr
{


    /**
     * Gets the value of the schText property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchText}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchTextElement}
     */
    net.sourceforge.czt.z.jaxb.gen.SchText getSchText();

    /**
     * Sets the value of the schText property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchText}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchTextElement}
     */
    void setSchText(net.sourceforge.czt.z.jaxb.gen.SchText value);

    /**
     * Gets the value of the opExpr property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.HideOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.AtProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.AssoParallelOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TopologyProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SkipProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ScopeEnrichOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DistInterleaveProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterleaveProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpPromotionExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.AnonOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitUntilProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ConjOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ParallelOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SynPllProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DeadlineProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistSeqOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutStartProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DistInChoiceProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterruptProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DivergeProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistConjOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistChoiceOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ExChoiceOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InChoiceProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.SeqOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutEndProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.StopProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.GuardProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterruptTimeOpExprElement}
     */
    net.sourceforge.czt.oz.jaxb.gen.OpExpr getOpExpr();

    /**
     * Sets the value of the opExpr property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.HideOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.AtProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.AssoParallelOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TopologyProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SkipProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ScopeEnrichOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DistInterleaveProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterleaveProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpPromotionExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.AnonOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitUntilProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ConjOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ParallelOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SynPllProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DeadlineProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistSeqOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutStartProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DistInChoiceProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterruptProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DivergeProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistConjOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistChoiceOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ExChoiceOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InChoiceProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.SeqOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutEndProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.StopProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.GuardProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterruptTimeOpExprElement}
     */
    void setOpExpr(net.sourceforge.czt.oz.jaxb.gen.OpExpr value);

}
