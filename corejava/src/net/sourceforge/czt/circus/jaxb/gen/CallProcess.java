//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen;


/**
 * Java content class for CallProcess complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Circus.xsd line 1075)
 * <p>
 * <pre>
 * &lt;complexType name="CallProcess">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/circus}ProcessDef">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}RefName"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface CallProcess
    extends net.sourceforge.czt.circus.jaxb.gen.ProcessDef
{


    /**
     * Gets the value of the refName property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    net.sourceforge.czt.z.jaxb.gen.RefName getRefName();

    /**
     * Sets the value of the refName property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    void setRefName(net.sourceforge.czt.z.jaxb.gen.RefName value);

}
