//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.04.21 at 09:33:05 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen;


/**
 * Java content class for CallAction complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Circus.xsd line 1471)
 * <p>
 * <pre>
 * &lt;complexType name="CallAction">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/circus}Action">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}RefName"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface CallAction
    extends net.sourceforge.czt.circus.jaxb.gen.Action
{


    /**
     * Gets the value of the refName property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefNameElement}
     */
    net.sourceforge.czt.z.jaxb.gen.RefName getRefName();

    /**
     * Sets the value of the refName property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefNameElement}
     */
    void setRefName(net.sourceforge.czt.z.jaxb.gen.RefName value);

}
