//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.07.01 at 10:48:15 NZST 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * Java content class for ProdType complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Z.xsd line 1714)
 * <p>
 * <pre>
 * &lt;complexType name="ProdType">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Type">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}Type" maxOccurs="unbounded" minOccurs="2"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface ProdType
    extends net.sourceforge.czt.z.jaxb.gen.Type
{


    /**
     * Gets the value of the Type property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Type property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getType().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.PowerTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.TypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.GenTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.ProdTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.SchemaTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.GivenTypeElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.Type}
     * 
     */
    java.util.List getType();

}
