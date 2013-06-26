/*
 * CircusConcreteSyntaxSymbol.java
 *
 * Created on 14 April 2013, 16:56
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.ohcircus.util;

/**
 * An enumeration of concrete syntax symbols.
 * These are based on the concrete syntax productions in
 * Circus,
 * <p>
 * The {@link OhCircusConcreteSyntaxSymbolVisitor} in this package can be
 * used to classify most kinds of AST nodes as one of these
 * symbols.
 * </p>
 * @author leo
 */
public enum OhCircusConcreteSyntaxSymbol
{
  /* Support for OhCircus*/
  EXTEND_KEYWORD("Extendes Class Para"),
  THIS_KEYWORD("this keyword"),
  NULL_KEYWORD("null keyword"),
  NEW_KEYWORD("new keyword"),
  SUPER_CLASS("super keyword"),
  PUBLIC_QUALIFIER("public qualifier"),
  PROTECTED_QUALIFIER("protected qualifier"),
  PRIVATE_QUALIFIER("private qualifier"),
  LOGICAL_QUALIFIER("logical qualifier"),
  INITIAL_STATE("initila keyword"),

  /* Class level paragraph */
  OHCIRCUS_CLASS_PARA("OhCircus Class paragraph"),

  /* Method level paragraph */
  METHOD_PARA("Method paragraph"),

  /* (Abstract) Method definitions */
  OHCIRCUS_METHOD("Method definition"),                     // Method
  UNARY_METHOD("Unary method definition"),                // Method1
  BINARY_METHOD("Binary method definition"),              // Method2
  CALL_METHOD("Method call"),
  PARAM_METHOD("Parameterised method"),                   
  GUARDED_METHOD("Guarded method"),
  LETVAR_METHOD("Local environment for variable declaration"),
  LETMU_METHOD("Local environment for recursive method"),
  SEQ_METHOD("Sequential composition method"),
  MU_METHOD("Recursive Method"),

  /* Commands */
  OHCIRCUS_COMMAND("OhCircus Command"),
  OHCIRCUS_IF_CMD("Guarded alternation - OhCircus if statement"),
  OHCIRCUS_DO_CMD("Guarded loop - OhCircus do statement"),
  OHCIRCUS_VAR_CMD("Variable block"),
  OHCIRCUS_DOT("OhCircus expression"),
  
  QUALIFIED_CLASS_PRIVATE("Qualified class or variables declaration - by private"),
  QUALIFIED_CLASS_PUBLIC("Qualified  class or variables declaration - by public"),
  QUALIFIED_CLASS_PROTECTED("Qualified class or variables  declaration - by protected"),
  QUALIFIED_CLASS_LOGICAL("Qualified  class or variables declaration - by logical"),
  
  //New added 
  OHCIRCUS_VISIBILITY("OhCircus Visibility"),
  METHOD_SIGNATURE_LIST("Method signature list"),
  OHCIRCUS_CLASS_REF_LIST("OhCircus Class Ref. List"),
  OHCIRCUS_CLASS_TYPE("Ohcircus Class type"),
  METHOD_LIST("OhCircus method list"),  
  OHCIRCUS_CALSS_SIGNATURE("OhCircus Class signature"),
  METHOD_SIGNATURE("Method signature"),
  METHOD_TYPE("Method type"),
  OHCIRCUS_PRED("OhCircus Predicate"),
  OHCIRCUS_STATE("OhCircus State"),
  SCH_EXPR_METHOD("Schema Expression Method"),
  OHCIRCUS_CLASS_SIGNATURE_LIST("OhCircus Class Signature List"),
  OHCIRCUS_CLASS_REF_TYPE("OhCircus Class Ref. Type"),
  OHCIRCUS_CLASS_REF("OhCircus Class Reference")
  
;

  private final String description_;
  
  OhCircusConcreteSyntaxSymbol(String description)
  {
    description_ = description;
  }
  
  public String getDescription()
  {
    return description_;
  }
}
