/*
 * CircusUtils.java
 *
 * Created on 15 June 2006, 09:04
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.circusconf.util;


/**
 *
 * @author leo
 */
public final class CircusConfUtils
{

  /**
   * Do not create instances of this class.
   */
  private CircusConfUtils()
  {
  }
  public static final Factory FACTORY = new Factory();
  /** The name of the basic Circus toolkit. */
  public static final String CIRCUSCONF_TOOLKIT = "circusconf_toolkit";
  /** The name of the Circus prelude. */
  public static final String CIRCUSCONF_PRELUDE = "circusconf_prelude";
  
  /**
   * Concrete syntax symbol visitor that can be used everywhere.
   */
  public static final CircusConfConcreteSyntaxSymbolVisitor 
    CIRCUSCONF_CONCRETE_SYNTAXSYMBOL_VISITOR = new CircusConfConcreteSyntaxSymbolVisitor();
  
}
