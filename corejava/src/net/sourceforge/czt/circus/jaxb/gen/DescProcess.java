//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen;


/**
 * Java content class for DescProcess complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Circus.xsd line 1084)
 * <p>
 * <pre>
 * &lt;complexType name="DescProcess">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/circus}ProcessDef">
 *       &lt;sequence>
 *         &lt;element name="StateSchemaRefName" type="{http://czt.sourceforge.net/zml}RefName"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Para" maxOccurs="unbounded" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/circus}Action"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface DescProcess
    extends net.sourceforge.czt.circus.jaxb.gen.ProcessDef
{


    /**
     * Gets the value of the stateSchemaRefName property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    net.sourceforge.czt.z.jaxb.gen.RefName getStateSchemaRefName();

    /**
     * Sets the value of the stateSchemaRefName property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    void setStateSchemaRefName(net.sourceforge.czt.z.jaxb.gen.RefName value);

    /**
     * Gets the value of the mainAction property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SpecStmtCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ParallelActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.HideActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SeqActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ParallelActionRElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.Action}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.GuardedActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IfGuardedCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ExtChoiceAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.VarDeclCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.PrefixingActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.AssignmentCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ChaosAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.CallActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.MuActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SeqAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntChoiceActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.FormalParamAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.InterleaveAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ExtChoiceActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SkipAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.InterleaveActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SchTextActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ActualParamActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.StopAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntChoiceAction}
     */
    net.sourceforge.czt.circus.jaxb.gen.Action getMainAction();

    /**
     * Sets the value of the mainAction property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SpecStmtCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ParallelActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.HideActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SeqActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ParallelActionRElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.Action}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.GuardedActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IfGuardedCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ExtChoiceAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.VarDeclCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.PrefixingActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.AssignmentCommandElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ChaosAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.CallActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.MuActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SeqAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntChoiceActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.FormalParamAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.InterleaveAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ExtChoiceActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SkipAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.InterleaveActionR}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SchTextActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.ActualParamActionElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.StopAction}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntChoiceAction}
     */
    void setMainAction(net.sourceforge.czt.circus.jaxb.gen.Action value);

    /**
     * Gets the value of the Para property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Para property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getPara().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.GivenParaElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.NameSetParaElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.ChannelSetParaElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.RuleElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.ChannelParaElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.SchChannelParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.UnparsedParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.FreeParaElement}
     * {@link net.sourceforge.czt.oz.jaxb.gen.ClassParaElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.JokersElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.ParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Para}
     * {@link net.sourceforge.czt.circus.jaxb.gen.ProcessParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.LatexMarkupParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.OptempParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.ConjParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.AxParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.NarrParaElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.ActionParaElement}
     * 
     */
    java.util.List getPara();

}
