//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.10 at 09:41:23 NZST 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for ThetaExpr complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/tmp/czt/gnast/src/xsd/Z.xsd line 1472)
 * <p>
 * <pre>
 * &lt;complexType name="ThetaExpr">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Expr1">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Stroke" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface ThetaExpr
    extends net.sourceforge.czt.z.jaxb.gen.Expr1
{


    /**
     * Gets the value of the Stroke property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Stroke property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getStroke().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.Stroke}
     * {@link net.sourceforge.czt.z.jaxb.gen.NextStroke}
     * {@link net.sourceforge.czt.z.jaxb.gen.OutStroke}
     * {@link net.sourceforge.czt.z.jaxb.gen.InStroke}
     * {@link net.sourceforge.czt.z.jaxb.gen.StrokeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.NumStrokeElement}
     * 
     */
    java.util.List getStroke();

}
