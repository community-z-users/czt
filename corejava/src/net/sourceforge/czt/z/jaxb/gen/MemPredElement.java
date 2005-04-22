//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v1.0.4-b18-fcs 
// See <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Any modifications to this file will be lost upon recompilation of the source schema. 
// Generated on: 2005.04.21 at 09:33:05 GMT 
//


package net.sourceforge.czt.z.jaxb.gen;


/**
 * A relation operator application (C.5.12).
 * The mixfix attribute is false iff the input has the form
 * Expr1 \in Expr2.
 * When mixfix=true, the second (right) Expr must be either a
 * relational operator and the first (left) Expr must be a tuple
 * containing the corresponding number of arguments (unless the
 * operator has one argument, then no tuple is required) or an
 * equality and the the second (right) Expr must be a set expression
 * containing exactly one expression.
 * For example, the input "m < n" generates a MemPred element with
 * mixfix=true, left=(m,n) and right=" _ < _ ", whereas
 * "(m,n) \in (_ < _)" has the same left and right expressions,
 * but mixfix=false.
 * 
 * Java content class for MemPred element declaration.
 * <p>The following schema fragment specifies the expected content contained within this java content object. (defined at file:/research/czt/gnast/src/xsd/Z.xsd line 739)
 * <p>
 * <pre>
 * &lt;element name="MemPred" type="{http://czt.sourceforge.net/zml}MemPred"/>
 * </pre>
 * 
 */
public interface MemPredElement
    extends javax.xml.bind.Element, net.sourceforge.czt.z.jaxb.gen.MemPred
{


}
