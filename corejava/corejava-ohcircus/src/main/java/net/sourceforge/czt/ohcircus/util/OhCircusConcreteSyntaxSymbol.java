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

CLASS_OHCIRCUS("Class Paragraph"),
EXTEND_KEYWORD("Extendes Class Para"),
THIS_KEYWORD("this keyword"),
NULL_KEYWORD("null keyword"),
NEW_KEYWORD("new keyword"),
SUPER_CLASS("super keyword"),
PUBLIC_QUALIFIER("public qualifier"),
PROTECTED_QUALIFIER("protected qualifier"),
PRIVATE_QUALIFIER("private qualifier"),
LOGICAL_QUALIFIER("logical qualifier"),
INITIAL_QUALIFIER("initila keyword")
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
