//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.circus.jaxb.gen;


/**
 * Java content class for MuAction complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Circus.xsd line 1388)
 * <p>
 * <pre>
 * &lt;complexType name="MuAction">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/circus}Action1">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}DeclName"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface MuAction
    extends net.sourceforge.czt.circus.jaxb.gen.Action1
{


    /**
     * Gets the value of the declName property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclNameElement}
     */
    net.sourceforge.czt.z.jaxb.gen.DeclName getDeclName();

    /**
     * Sets the value of the declName property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclNameElement}
     */
    void setDeclName(net.sourceforge.czt.z.jaxb.gen.DeclName value);

}
