/*
 * CircusConcreteSyntaxSymbol.java
 *
 * Created on 08 June 2006, 15:56
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circusconf.util;

import net.sourceforge.czt.circus.util.CircusConcreteSyntaxSymbolVisitor;

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
public enum CircusConfConcreteSyntaxSymbol
{
  /* Support for Circus Time */
 
CONFIDENTIALITY_ACTION("Confidentiality action"),
CONFIDENTIALITY_PROCESS("Confidentiality process")

;

  private final String description_;
  
  CircusConfConcreteSyntaxSymbol(String description)
  {
    description_ = description;
  }
  
  public String getDescription()
  {
    return description_;
  }
}
