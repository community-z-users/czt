//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.03.08 at 10:18:03 GMT 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for ProdType complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Z.xsd line 1801)
 * <p>
 * <pre>
 * &lt;complexType name="ProdType">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Type2">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Type2" maxOccurs="unbounded" minOccurs="2"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface ProdType
    extends net.sourceforge.czt.z.jaxb.gen.Type2
{


    /**
     * Gets the value of the Type property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Type property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getType().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.GivenTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Type2}
     * {@link net.sourceforge.czt.z.jaxb.gen.GenParamTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Type2Element}
     * {@link net.sourceforge.czt.z.jaxb.gen.SchemaTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.PowerTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.ProdTypeElement}
     * {@link net.sourceforge.czt.oz.jaxb.gen.ClassTypeElement}
     * 
     */
    java.util.List getType();

}
