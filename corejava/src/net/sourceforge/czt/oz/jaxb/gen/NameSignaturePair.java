//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for NameSignaturePair complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Object-Z.xsd line 506)
 * <p>
 * <pre>
 * &lt;complexType name="NameSignaturePair">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="Name" type="{http://czt.sourceforge.net/zml}DeclName" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Signature"/>
 *       &lt;/sequence>
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface NameSignaturePair {


    /**
     * Gets the value of the signature property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.Signature}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SignatureElement}
     */
    net.sourceforge.czt.z.jaxb.gen.Signature getSignature();

    /**
     * Sets the value of the signature property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.Signature}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SignatureElement}
     */
    void setSignature(net.sourceforge.czt.z.jaxb.gen.Signature value);

    /**
     * Gets the value of the name property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     */
    net.sourceforge.czt.z.jaxb.gen.DeclName getName();

    /**
     * Sets the value of the name property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     */
    void setName(net.sourceforge.czt.z.jaxb.gen.DeclName value);

}
