//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen;


/**
 * Java content class for Communication complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Circus.xsd line 1493)
 * <p>
 * <pre>
 * &lt;complexType name="Communication">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element name="ChanName" type="{http://czt.sourceforge.net/zml}RefName"/>
 *         &lt;element ref="{http://czt.sourceforge.net/circus}Field" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *       &lt;attribute name="CommType" type="{http://czt.sourceforge.net/circus}CommType" default="Synch" />
 *       &lt;attribute name="MultiSych" type="{http://www.w3.org/2001/XMLSchema}nonNegativeInteger" default="0" />
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface Communication
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the ChanFields property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the ChanFields property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getChanFields().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.circus.jaxb.gen.Field}
     * {@link net.sourceforge.czt.circus.jaxb.gen.InputFieldElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.FieldElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.MixedFieldElement}
     * {@link net.sourceforge.czt.circus.jaxb.gen.OutputFieldElement}
     * 
     */
    java.util.List getChanFields();

    /**
     * Gets the value of the multiSych property.
     * 
     * @return
     *     possible object is
     *     {@link java.lang.Integer}
     */
    java.lang.Integer getMultiSych();

    /**
     * Sets the value of the multiSych property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.Integer}
     */
    void setMultiSych(java.lang.Integer value);

    /**
     * Gets the value of the commType property.
     * 
     * @return
     *     possible object is
     *     {@link java.lang.String}
     */
    java.lang.String getCommType();

    /**
     * Sets the value of the commType property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.String}
     */
    void setCommType(java.lang.String value);

    /**
     * Gets the value of the chanName property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    net.sourceforge.czt.z.jaxb.gen.RefName getChanName();

    /**
     * Sets the value of the chanName property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    void setChanName(net.sourceforge.czt.z.jaxb.gen.RefName value);

}
