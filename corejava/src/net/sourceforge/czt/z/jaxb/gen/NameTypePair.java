//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for NameTypePair complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Z.xsd line 1853)
 * <p>
 * <pre>
 * &lt;complexType name="NameTypePair">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="Name" type="{http://czt.sourceforge.net/zml}DeclName"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Type"/>
 *       &lt;/sequence>
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface NameTypePair {


    /**
     * Gets the value of the type property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.GivenTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenParamTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.TypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenericTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Type}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchemaTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.PowerTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ProdTypeElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassTypeElement}
     */
    net.sourceforge.czt.z.jaxb.gen.Type getType();

    /**
     * Sets the value of the type property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.GivenTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenParamTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.TypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenericTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Type}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchemaTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.PowerTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ProdTypeElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassTypeElement}
     */
    void setType(net.sourceforge.czt.z.jaxb.gen.Type value);

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
