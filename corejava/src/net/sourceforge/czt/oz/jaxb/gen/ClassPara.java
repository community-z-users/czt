//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.2-b15-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2004.05.13 at 03:14:32 NZST 
//


package net.sourceforge.czt.oz.jaxb.gen;


/**
 * New addition of Object-Z construct:
 * class definition added by Li Yuanfang.
 * 
 * Java content class for ClassPara complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/projects/gnast/src/xsd/Object-Z.xsd line 260)
 * <p>
 * <pre>
 * &lt;complexType name="ClassPara">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/zml}Para">
 *       &lt;sequence>
 *         &lt;element name="Name" type="{http://czt.sourceforge.net/zml}DeclName"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}FormalParameters" minOccurs="0"/>
 *         &lt;element name="VisibilityList" type="{http://czt.sourceforge.net/object-z}RefNameList" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}InheritedClass" maxOccurs="unbounded" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}LocalDef" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}State" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}InitialState" minOccurs="0"/>
 *         &lt;element ref="{http://czt.sourceforge.net/object-z}Operation" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface ClassPara
    extends net.sourceforge.czt.z.jaxb.gen.Para
{


    /**
     * Gets the value of the Operation property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the Operation property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getOperation().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.oz.jaxb.gen.OperationElement}
     * {@link net.sourceforge.czt.oz.jaxb.gen.Operation}
     * 
     */
    java.util.List getOperation();

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.LocalDefElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.LocalDef}
     */
    net.sourceforge.czt.oz.jaxb.gen.LocalDef getLocalDef();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.LocalDefElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.LocalDef}
     */
    void setLocalDef(net.sourceforge.czt.oz.jaxb.gen.LocalDef value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.InitialState}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.InitialStateElement}
     */
    net.sourceforge.czt.oz.jaxb.gen.InitialState getInitialState();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.InitialState}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.InitialStateElement}
     */
    void setInitialState(net.sourceforge.czt.oz.jaxb.gen.InitialState value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.State}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.StateElement}
     */
    net.sourceforge.czt.oz.jaxb.gen.State getState();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.State}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.StateElement}
     */
    void setState(net.sourceforge.czt.oz.jaxb.gen.State value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RefNameList}
     */
    net.sourceforge.czt.oz.jaxb.gen.RefNameList getVisibilityList();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.RefNameList}
     */
    void setVisibilityList(net.sourceforge.czt.oz.jaxb.gen.RefNameList value);

    /**
     * Gets the value of the InheritedClass property.
     * 
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the InheritedClass property.
     * 
     * For example, to add a new item, do as follows:
     * <pre>
     *    getInheritedClass().add(newItem);
     * </pre>
     * 
     * 
     * Objects of the following type(s) are allowed in the list
     * {@link net.sourceforge.czt.oz.jaxb.gen.InheritedClass}
     * {@link net.sourceforge.czt.oz.jaxb.gen.InheritedClassElement}
     * 
     */
    java.util.List getInheritedClass();

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.FormalParametersElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.FormalParameters}
     */
    net.sourceforge.czt.oz.jaxb.gen.FormalParameters getFormalParameters();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.FormalParametersElement}
     *     {@link net.sourceforge.czt.oz.jaxb.gen.FormalParameters}
     */
    void setFormalParameters(net.sourceforge.czt.oz.jaxb.gen.FormalParameters value);

    /**
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     */
    net.sourceforge.czt.z.jaxb.gen.DeclName getName();

    /**
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.DeclName}
     */
    void setName(net.sourceforge.czt.z.jaxb.gen.DeclName value);

}
