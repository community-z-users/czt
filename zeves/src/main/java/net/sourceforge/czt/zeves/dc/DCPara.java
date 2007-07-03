/*
 * DCPara.java
 *
 * Created on 03 July 2007, 03:24
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.zeves.dc;

import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;

/**
 *
 * @author leo
 */
public class DCPara extends AbstractDC implements 
   GivenParaVisitor<Pred>,
   FreeParaVisitor<Pred>,
   AxParaVisitor<Pred>,
   ConjParaVisitor<Pred>,
   NarrParaVisitor<Pred>,
   OptempParaVisitor<Pred>,
   LatexMarkupParaVisitor<Pred>, 
   UnparsedParaVisitor<Pred>, 
   ZParaListVisitor<Pred>
{
  
  /** Creates a new instance of DCPara */
  public DCPara()
  {
  }

  public Pred visitUnparsedPara(UnparsedPara term)
  {
    return null;
  }

  public Pred visitOptempPara(OptempPara term)
  {
    return null;
  }

  public Pred visitConjPara(ConjPara term)
  {
    return null;
  }

  public Pred visitZParaList(ZParaList term)
  {
    return null;
  }

  public Pred visitNarrPara(NarrPara term)
  {
    return null;
  }

  public Pred visitLatexMarkupPara(LatexMarkupPara term)
  {
    return null;
  }

  public Pred visitFreePara(FreePara term)
  {
    return null;
  }

  public Pred visitAxPara(AxPara term)
  {
    return null;
  }

  public Pred visitGivenPara(GivenPara term)
  {
    return null;
  }
  
}
