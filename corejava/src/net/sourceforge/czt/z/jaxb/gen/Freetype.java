//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.04.21 at 09:33:05 GMT 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for Freetype complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Z.xsd line 1676)
 * <p>
 * <pre>
 * &lt;complexType name="Freetype">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}DeclName"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Branch" maxOccurs="unbounded"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface Freetype
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the Branch property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Branch property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getBranch().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.BranchElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Branch}
     * 
     */
    java.util.List getBranch();

    /**
     * Gets the value of the declName property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     */
    net.sourceforge.czt.z.jaxb.gen.DeclName getDeclName();

    /**
     * Sets the value of the declName property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.zpatt.jaxb.gen.JokerNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclNameElement}
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     */
    void setDeclName(net.sourceforge.czt.z.jaxb.gen.DeclName value);

}
