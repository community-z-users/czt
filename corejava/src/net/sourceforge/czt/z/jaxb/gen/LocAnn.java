//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.10 at 09:41:23 NZST 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for LocAnn complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/tmp/czt/gnast/src/xsd/Z.xsd line 1633)
 * <p>
 * <pre>
 * &lt;complexType name="LocAnn">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Ann">
 *       &lt;attribute name="Line" type="{http://www.w3.org/2001/XMLSchema}nonNegativeInteger" />
 *       &lt;attribute name="Col" type="{http://www.w3.org/2001/XMLSchema}nonNegativeInteger" />
 *       &lt;attribute name="Loc" use="required" type="{http://www.w3.org/2001/XMLSchema}anyURI" />
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface LocAnn
    extends net.sourceforge.czt.z.jaxb.gen.Ann
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link java.lang.Integer}
     */
    java.lang.Integer getCol();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.Integer}
     */
    void setCol(java.lang.Integer value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link java.lang.String}
     */
    java.lang.String getLoc();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.String}
     */
    void setLoc(java.lang.String value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link java.lang.Integer}
     */
    java.lang.Integer getLine();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link java.lang.Integer}
     */
    void setLine(java.lang.Integer value);

}
