//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for Name complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Z.xsd line 1326)
 * <p>
 * <pre>
 * &lt;complexType name="Name">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element name="Word" type="{http://www.w3.org/2001/XMLSchema}string"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Stroke" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface Name
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the word property.
     * 
     * @return
     *     possible object is
     *     {@link java.lang.String}
     */
    java.lang.String getWord();

    /**
     * Sets the value of the word property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.String}
     */
    void setWord(java.lang.String value);

    /**
     * Gets the value of the Stroke property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Stroke property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getStroke().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.Stroke}
     * {@link net.sourceforge.czt.z.jaxb.gen.StrokeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.InStroke}
     * {@link net.sourceforge.czt.z.jaxb.gen.NextStroke}
     * {@link net.sourceforge.czt.z.jaxb.gen.NumStrokeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.OutStroke}
     * 
     */
    java.util.List getStroke();

}
