//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.13 at 03:14:32 NZST 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for InheritedClass complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Object-Z.xsd line 300)
 * <p>
 * <pre>
 * &lt;complexType name="InheritedClass">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element name="Name" type="{http://czt.sourceforge.net/zml}RefName"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}ActualParameters" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}RenameList" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface InheritedClass
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameListElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameList}
     */
    net.sourceforge.czt.oz.jaxb.gen.RenameList getRenameList();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameListElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RenameList}
     */
    void setRenameList(net.sourceforge.czt.oz.jaxb.gen.RenameList value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ActualParameters}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ActualParametersElement}
     */
    net.sourceforge.czt.oz.jaxb.gen.ActualParameters getActualParameters();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ActualParameters}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.ActualParametersElement}
     */
    void setActualParameters(net.sourceforge.czt.oz.jaxb.gen.ActualParameters value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    net.sourceforge.czt.z.jaxb.gen.RefName getName();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.RefName}
     */
    void setName(net.sourceforge.czt.z.jaxb.gen.RefName value);

}
