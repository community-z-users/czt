//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen;


/**
 * Java content class for NameSet2 complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Circus.xsd line 1276)
 * <p>
 * <pre>
 * &lt;complexType name="NameSet2">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/circus}NameSet">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/circus}NameSet"/>
 *         &lt;element ref="{http://czt.sourceforge.net/circus}NameSet"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface NameSet2
    extends net.sourceforge.czt.circus.jaxb.gen.NameSet
{


    /**
     * Gets the value of the rightOperand property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntersectionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SetNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.DifferenceNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.RefNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.UnionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSet}
     */
    net.sourceforge.czt.circus.jaxb.gen.NameSet getRightOperand();

    /**
     * Sets the value of the rightOperand property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntersectionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SetNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.DifferenceNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.RefNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.UnionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSet}
     */
    void setRightOperand(net.sourceforge.czt.circus.jaxb.gen.NameSet value);

    /**
     * Gets the value of the leftOperand property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntersectionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SetNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.DifferenceNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.RefNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.UnionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSet}
     */
    net.sourceforge.czt.circus.jaxb.gen.NameSet getLeftOperand();

    /**
     * Sets the value of the leftOperand property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.circus.jaxb.gen.IntersectionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.SetNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.DifferenceNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.RefNameSetElement}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.UnionNameSet}
     *     {@link net.sourceforge.czt.circus.jaxb.gen.NameSet}
     */
    void setLeftOperand(net.sourceforge.czt.circus.jaxb.gen.NameSet value);

}
