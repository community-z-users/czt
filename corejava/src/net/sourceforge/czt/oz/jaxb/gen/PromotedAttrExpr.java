//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for PromotedAttrExpr complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Object-Z.xsd line 488)
 * <p>
 * <pre>
 * &lt;complexType name="PromotedAttrExpr">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Expr1">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}RefName"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface PromotedAttrExpr
    extends net.sourceforge.czt.z.jaxb.gen.Expr1
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefNameElement}
     */
    net.sourceforge.czt.z.jaxb.gen.RefName getRefName();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefNameElement}
     */
    void setRefName(net.sourceforge.czt.z.jaxb.gen.RefName value);

}
