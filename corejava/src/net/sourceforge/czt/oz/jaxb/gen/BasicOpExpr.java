//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2003.11.03 at 03:50:09 NZDT 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for BasicOpExpr complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Object-Z.xsd line 345)
 * <p>
 * <pre>
 * &lt;complexType name="BasicOpExpr">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/object-z}OperationExpr">
 *       &lt;sequence>
 *         &lt;element name="DeltaList" type="{http://czt.sourceforge.net/object-z}StringListType" minOccurs="0"/>
 *         &lt;element name="SchText" type="{http://czt.sourceforge.net/zml}SchText" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface BasicOpExpr
    extends net.sourceforge.czt.oz.jaxb.gen.OperationExpr
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchText}
     */
    net.sourceforge.czt.z.jaxb.gen.SchText getSchText();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.SchText}
     */
    void setSchText(net.sourceforge.czt.z.jaxb.gen.SchText value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.StringListType}
     */
    net.sourceforge.czt.oz.jaxb.gen.StringListType getDeltaList();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.StringListType}
     */
    void setDeltaList(net.sourceforge.czt.oz.jaxb.gen.StringListType value);

}
