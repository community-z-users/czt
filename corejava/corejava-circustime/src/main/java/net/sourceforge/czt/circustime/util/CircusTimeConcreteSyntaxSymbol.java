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
 
  
 /* Support for Circus Time: Process */
DEADLINE_END_PROCESS("Deadline End Process"),
DEADLINE_START_PROCESS("Deadline Start Process"),
TIMEOUT_PROCESS("Timeout Process"),
TIMEDINTERRUPT_PROCESS("Timedinterrupt Process"),


/* Support for Circus Time: Action */
DEADLINE_END_ACTION("Deadline End Action"),
DEADLINE_START_ACTION("Deadline Start Action"),
TIMEOUT_ACTION("Timeout Action"),
TIMEDINTERRUPT_ACTION("Timedinterrupt Action"),

WAIT_BASIC_ACTION("Wait Basic Action"),
WAIT_EXPR_ACTION("Wait Expr Action"),

PREFIX_EXPR_ACTION("Prefixing Expression Action"),
AT_PREFIX_ACTION("At Prefixing Action"),
AT_PREFIX_EXPR_ACTION("At Prefixing Expression Action")

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
