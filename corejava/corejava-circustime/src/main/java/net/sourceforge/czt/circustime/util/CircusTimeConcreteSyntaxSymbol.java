/*
 * CircusConcreteSyntaxSymbol.java
 *
 * Created on 08 June 2006, 15:56
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circustime.util;

/**
 * An enumeration of concrete syntax symbols.
 * These are based on the concrete syntax productions in
 * Circus,
 * <p>
 * The {@link CircusConcreteSyntaxSymbolVisitor} in this package can be
 * used to classify most kinds of AST nodes as one of these
 * symbols.
 * </p>
 * @author leo
 */
public enum CircusTimeConcreteSyntaxSymbol
{
  /* Support for Circus Time */
  TIMEOUT_ACTION("Timeout Action"),
  WAIT_ACTION("Wait Action"),
  DEADLINE_ACTION("Wait Action")
  ;
  
  private final String description_;
  
  CircusTimeConcreteSyntaxSymbol(String description)
  {
    description_ = description;
  }
  
  public String getDescription()
  {
    return description_;
  }
}
