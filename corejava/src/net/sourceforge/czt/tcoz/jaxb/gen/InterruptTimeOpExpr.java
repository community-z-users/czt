//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.02.13 at 10:27:41 GMT 
//


package net.sourceforge.czt.tcoz.jaxb.gen;


/**
 * Java content class for InterruptTimeOpExpr complex type.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/TCOZ.xsd line 274)
 * <p>
 * <pre>
 * &lt;complexType name="InterruptTimeOpExpr">
 *   &lt;complexContent>
 *     &lt;extension base="{http://czt.sourceforge.net/object-z}OpExpr">
 *       &lt;sequence>
 *         &lt;element name="NormalOp" type="{http://czt.sourceforge.net/object-z}OpExpr"/>
 *         &lt;element name="IntOrTimeout" type="{http://czt.sourceforge.net/zml}Expr1"/>
 *         &lt;element name="HandlerOp" type="{http://czt.sourceforge.net/object-z}OpExpr"/>
 *       &lt;/sequence>
 *     &lt;/extension>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 */
public interface InterruptTimeOpExpr
    extends net.sourceforge.czt.oz.jaxb.gen.OpExpr
{


    /**
     * Gets the value of the normalOp property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExpr}
     */
    net.sourceforge.czt.oz.jaxb.gen.OpExpr getNormalOp();

    /**
     * Sets the value of the normalOp property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExpr}
     */
    void setNormalOp(net.sourceforge.czt.oz.jaxb.gen.OpExpr value);

    /**
     * Gets the value of the intOrTimeout property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.Expr1}
     */
    net.sourceforge.czt.z.jaxb.gen.Expr1 getIntOrTimeout();

    /**
     * Sets the value of the intOrTimeout property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.z.jaxb.gen.Expr1}
     */
    void setIntOrTimeout(net.sourceforge.czt.z.jaxb.gen.Expr1 value);

    /**
     * Gets the value of the handlerOp property.
     * 
     * @return
     *     possible object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExpr}
     */
    net.sourceforge.czt.oz.jaxb.gen.OpExpr getHandlerOp();

    /**
     * Sets the value of the handlerOp property.
     * 
     * @param value
     *     allowed object is
     *     {@link net.sourceforge.czt.oz.jaxb.gen.OpExpr}
     */
    void setHandlerOp(net.sourceforge.czt.oz.jaxb.gen.OpExpr value);

}
