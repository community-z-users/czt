//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for MainOpExpr complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Object-Z.xsd line 392)
 * <p>
 * <pre>
 * &lt;complexType name="MainOpExpr">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/object-z}OperationExpr">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}SchText"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}OperationExpr"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface MainOpExpr
    extends net.sourceforge.czt.oz.jaxb.gen.OperationExpr
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchText}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchTextElement}
     */
    net.sourceforge.czt.z.jaxb.gen.SchText getSchText();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchText}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchTextElement}
     */
    void setSchText(net.sourceforge.czt.z.jaxb.gen.SchText value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.BasicOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.AtProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OperationExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpPromotionExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SkipProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DeadlineProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.StopProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ExChoiceOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.GuardProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistChoiceOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.HideOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterleaveProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TopologyProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ConjOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitUntilProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutStartProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OperationExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterruptProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ParallelOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DivergeProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.SeqOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistConjOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.AssoParallelOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ScopeEnrichOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutEndProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SynPllProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ParenOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameOpExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistSeqOpExpr}
     */
    net.sourceforge.czt.oz.jaxb.gen.OperationExpr getOperationExpr();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.BasicOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.AtProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OperationExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpPromotionExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SkipProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DeadlineProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.StopProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ExChoiceOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.GuardProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistChoiceOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.HideOpExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterleaveProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TopologyProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ConjOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.WaitUntilProExprElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutStartProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OperationExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.InterruptProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ParallelOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.DivergeProExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.SeqOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistConjOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.AssoParallelOpExpr}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ScopeEnrichOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.TimeoutEndProExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.SynPllProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ParenOpExpr}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.RecProExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameOpExprElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.DistSeqOpExpr}
     */
    void setOperationExpr(net.sourceforge.czt.oz.jaxb.gen.OperationExpr value);

}
