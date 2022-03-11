/*
 * CircusUtils.java
 *
 * Created on 15 June 2006, 09:04
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.circustime.util;


/**
 *
 * @author leo
 */
public final class CircusTimeUtils
{

  /**
   * Do not create instances of this class.
   */
  private CircusTimeUtils()
  {
  }
  public static final Factory FACTORY = new Factory();
  /** The name of the basic Circus toolkit. */
  public static final String CIRCUSTIME_TOOLKIT = "circustime_toolkit";
  /** The name of the Circus prelude. */
  public static final String CIRCUSTIME_PRELUDE = "circustime_prelude";
  
  /**
   * Concrete syntax symbol visitor that can be used everywhere.
   */
  public static final CircusTimeConcreteSyntaxSymbolVisitor 
    CIRCUSTIME_CONCRETE_SYNTAXSYMBOL_VISITOR = new CircusTimeConcreteSyntaxSymbolVisitor();
  
}
