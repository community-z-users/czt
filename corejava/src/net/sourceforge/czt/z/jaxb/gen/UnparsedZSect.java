//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.10 at 09:41:23 NZST 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for UnparsedZSect complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/tmp/czt/gnast/src/xsd/Z.xsd line 1103)
 * <p>
 * <pre>
 * &lt;complexType name="UnparsedZSect">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Sect">
 *       &lt;sequence>
 *         &lt;element name="Content" type="{http://www.w3.org/2001/XMLSchema}anyType"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface UnparsedZSect
    extends net.sourceforge.czt.z.jaxb.gen.Sect
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link org.w3._2001.xmlschema.AnyType}
     */
    org.w3._2001.xmlschema.AnyType getContent();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link org.w3._2001.xmlschema.AnyType}
     */
    void setContent(org.w3._2001.xmlschema.AnyType value);

}
