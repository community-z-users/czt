//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.23 at 11:46:17 GMT 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for ClassRef complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Object-Z.xsd line 495)
 * <p>
 * <pre>
 * &lt;complexType name="ClassRef">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}RefName"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Type2" maxOccurs="unbounded" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}NameNamePair" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface ClassRef
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the Type2 property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Type2 property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getType2().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.oz.jaxb.gen.ClassUnionTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.SchemaTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Type2Element}
     * {@link net.sourceforge.czt.z.jaxb.gen.ProdTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.GivenTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.GenParamTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.PowerTypeElement}
     * {@link net.sourceforge.czt.oz.jaxb.gen.ClassRefTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Type2}
     * {@link net.sourceforge.czt.oz.jaxb.gen.ClassPolyTypeElement}
     * {@link net.sourceforge.czt.tcoz.jaxb.gen.ChannelTypeElement}
     * 
     */
    java.util.List getType2();

    /**
     * Gets the value of the NameNamePair property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the NameNamePair property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getNameNamePair().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.NameNamePair}
     * {@link net.sourceforge.czt.z.jaxb.gen.NameNamePairElement}
     * 
     */
    java.util.List getNameNamePair();

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
