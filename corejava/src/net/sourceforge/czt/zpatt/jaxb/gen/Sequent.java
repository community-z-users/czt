//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.zpatt.jaxb.gen;


/**
 * Java content class for Sequent complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/ZPattern.xsd line 315)
 * <p>
 * <pre>
 * &lt;complexType name="Sequent">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zpatt}SequentContext"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface Sequent
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the sequentContext property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.SequentContextElement}
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.SequentContext}
     */
    net.sourceforge.czt.zpatt.jaxb.gen.SequentContext getSequentContext();

    /**
     * Sets the value of the sequentContext property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.SequentContextElement}
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.SequentContext}
     */
    void setSequentContext(net.sourceforge.czt.zpatt.jaxb.gen.SequentContext value);

}
