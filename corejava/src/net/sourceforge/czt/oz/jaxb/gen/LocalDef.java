//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.03.15 at 11:59:27 NZDT 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * Java content class for LocalDef complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Object-Z.xsd line 315)
 * <p>
 * <pre>
 * &lt;complexType name="LocalDef">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}TermA">
 *       &lt;sequence>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}GivenPara" maxOccurs="unbounded" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}AxPara" maxOccurs="unbounded" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/zml}FreePara" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface LocalDef
    extends net.sourceforge.czt.z.jaxb.gen.TermA
{


    /**
     * Gets the value of the FreePara property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the FreePara property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getFreePara().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.FreeParaElement}
     * {@link net.sourceforge.czt.z.jaxb.gen.FreePara}
     * 
     */
    java.util.List getFreePara();

    /**
     * Gets the value of the AxPara property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the AxPara property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getAxPara().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.AxPara}
     * {@link net.sourceforge.czt.z.jaxb.gen.AxParaElement}
     * 
     */
    java.util.List getAxPara();

    /**
     * Gets the value of the GivenPara property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the GivenPara property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getGivenPara().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.z.jaxb.gen.GivenPara}
     * {@link net.sourceforge.czt.z.jaxb.gen.GivenParaElement}
     * 
     */
    java.util.List getGivenPara();

}
