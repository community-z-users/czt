//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for TypeAnn complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Z.xsd line 1717)
 * <p>
 * <pre>
 * &lt;complexType name="TypeAnn">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Ann">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Type"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface TypeAnn
    extends net.sourceforge.czt.z.jaxb.gen.Ann
{


    /**
     * Gets the value of the type property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassUnionTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchemaTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenericTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ProdTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenParamTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GivenTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Type}
     *     {@link net.sourceforge.czt.z.jaxb.gen.PowerTypeElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassRefTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.TypeElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassPolyTypeElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.ChannelTypeElement}
     */
    net.sourceforge.czt.z.jaxb.gen.Type getType();

    /**
     * Sets the value of the type property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassUnionTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchemaTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenericTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.ProdTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GenParamTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.GivenTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.Type}
     *     {@link net.sourceforge.czt.z.jaxb.gen.PowerTypeElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassRefTypeElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.TypeElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ClassPolyTypeElement}
     *     {@link net.sourceforge.czt.tcoz.jaxb.gen.ChannelTypeElement}
     */
    void setType(net.sourceforge.czt.z.jaxb.gen.Type value);

}
