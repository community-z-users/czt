/*
 * CircusTimeConcreteSyntaxSymbolVisitor.java
 *
 * Created on 08 June 2006, 15:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.ohcircus.util;


import net.sourceforge.czt.ohcircus.ast.*;
import net.sourceforge.czt.ohcircus.visitor.*;

import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.util.IsEmptyNameList;
import net.sourceforge.czt.z.util.StandardZ;

/**
 * This visitor classifies a given AST node as a concrete syntax
 * symbol {@link CircusConcreteSyntaxSymbol}.  This can be used by the JEdit and
 * Eclipse plugins to produce an outline view (or structure tree) of
 * the source.
 *
 * @author leo
 */
public class OhCircusConcreteSyntaxSymbolVisitor
  implements OhCircusVisitor<OhCircusConcreteSyntaxSymbol>
{

  private Utils utils_;

  public OhCircusConcreteSyntaxSymbolVisitor()
  {
    utils_ = new UtilsImpl();
  }

  public OhCircusConcreteSyntaxSymbolVisitor(Utils utils)
  {
    utils_ = utils;
  }


/* Support for OhCircus */
  
// Add here AST for new sysmbols for OhCircus


  public interface Utils
    extends IsEmptyNameList
  {
  }

  public static class UtilsImpl
    extends StandardZ
    implements Utils
  {
  }
}
