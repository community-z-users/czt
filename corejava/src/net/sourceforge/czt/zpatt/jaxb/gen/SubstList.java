//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.13 at 03:14:32 NZST 
//


package net.sourceforge.czt.zpatt.jaxb.gen;


/**
 * Java content class for SubstList complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/ZPattern.xsd line 93)
 * <p>
 * <pre>
 * &lt;complexType name="SubstList">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zpatt}Substitute" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface SubstList {


    /**
     * Gets the value of the Substitute property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Substitute property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getSubstitute().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.Substitute}
     * {@link net.sourceforge.czt.zpatt.jaxb.gen.SubstituteElement}
     * 
     */
    java.util.List getSubstitute();

}
