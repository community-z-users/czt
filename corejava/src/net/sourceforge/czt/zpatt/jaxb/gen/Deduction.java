//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.zpatt.jaxb.gen;


/**
 * Java content class for Deduction complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/ZPattern.xsd line 300)
 * <p>
 * <pre>
 * &lt;complexType name="Deduction">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zpatt}Binding" maxOccurs="unbounded" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zpatt}Sequent" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *       &lt;attribute name="Name" type="{http://www.w3.org/2001/XMLSchema}string" />
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface Deduction
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the Binding property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Binding property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getBinding().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerNameBindingElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.BindingElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerPredBindingElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerDeclListBindingElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.Binding}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerExprBindingElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerExprListBindingElement}
     * 
     */
    java.util.List getBinding();

    /**
     * Gets the value of the Sequent property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Sequent property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getSequent().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.SequentElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.Sequent}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.DefnSequentElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.TypeSequentElement}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.PredSequentElement}
     * 
     */
    java.util.List getSequent();

    /**
     * Gets the value of the name property.
     * 
     * @return
     *     possible object is
     *     {@link java.lang.String}
     */
    java.lang.String getName();

    /**
     * Sets the value of the name property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.String}
     */
    void setName(java.lang.String value);

}
