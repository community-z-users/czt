//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for Spec complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Z.xsd line 1123)
 * <p>
 * <pre>
 * &lt;complexType name="Spec">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Sect" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *       &lt;attribute name="Author" type="{http://www.w3.org/2001/XMLSchema}string" />
 *       &lt;attribute name="Modified" type="{http://www.w3.org/2001/XMLSchema}dateTime" />
 *       &lt;attribute name="Source" type="{http://www.w3.org/2001/XMLSchema}anyURI" />
 *       &lt;attribute name="Version" type="{http://www.w3.org/2001/XMLSchema}string" default="1.0" />
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface Spec
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the modified property.
     * 
     * @return
     *     possible object is
     *     {@link java.util.Calendar}
     */
    java.util.Calendar getModified();

    /**
     * Sets the value of the modified property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.util.Calendar}
     */
    void setModified(java.util.Calendar value);

    /**
     * Gets the value of the version property.
     * 
     * @return
     *     possible object is
     *     {@link java.lang.String}
     */
    java.lang.String getVersion();

    /**
     * Sets the value of the version property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.String}
     */
    void setVersion(java.lang.String value);

    /**
     * Gets the value of the author property.
     * 
     * @return
     *     possible object is
     *     {@link java.lang.String}
     */
    java.lang.String getAuthor();

    /**
     * Sets the value of the author property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.String}
     */
    void setAuthor(java.lang.String value);

    /**
     * Gets the value of the source property.
     * 
     * @return
     *     possible object is
     *     {@link java.lang.String}
     */
    java.lang.String getSource();

    /**
     * Sets the value of the source property.
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.String}
     */
    void setSource(java.lang.String value);

    /**
     * Gets the value of the Sect property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Sect property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getSect().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.ZSectElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.NarrSectElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.SectElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Sect}
     * {@link net.sourceforge.czt.z.jaxb.gen.UnparsedZSectElement}
     * 
     */
    java.util.List getSect();

}
