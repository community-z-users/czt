//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.10 at 09:41:23 NZST 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for Operand complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/tmp/czt/gnast/src/xsd/Z.xsd line 1740)
 * <p>
 * <pre>
 * &lt;complexType name="Operand">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Oper">
 *       &lt;attribute name="List" type="{http://www.w3.org/2001/XMLSchema}boolean" default="false" />
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface Operand
    extends net.sourceforge.czt.z.jaxb.gen.Oper
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link java.lang.Boolean}
     */
    java.lang.Boolean getList();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.Boolean}
     */
    void setList(java.lang.Boolean value);

}
