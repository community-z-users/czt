/**
 * 
 */
package net.sourceforge.czt.eclipse.outline;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.eclipse.CZTPluginImages;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

import org.eclipse.swt.graphics.Image;

/**
 * @author Chengdong Xu
 */
public class NodeIconVisitor
    implements
      TermVisitor<Image>,
      ZSectVisitor<Image>,
      GivenParaVisitor<Image>,
      AxParaVisitor<Image>,
      ConjParaVisitor<Image>,
      FreeParaVisitor<Image>,
      OptempParaVisitor<Image>,
      ConstDeclVisitor<Image>,
      VarDeclVisitor<Image>
{

  /*
   * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
   */
  public Image visitTerm(Term term)
  {
    return null;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZSectVisitor#visitZSect(net.sourceforge.czt.z.ast.ZSect)
   */
  public Image visitZSect(ZSect zSect)
  {
    return CZTPluginImages.get(CZTPluginImages.IMG_ZSECTION);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.GivenParaVisitor#visitGivenPara(net.sourceforge.czt.z.ast.GivenPara)
   */
  public Image visitGivenPara(GivenPara givenPara)
  {
    return CZTPluginImages.get(CZTPluginImages.IMG_GIVENPARA);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.AxParaVisitor#visitAxPara(net.sourceforge.czt.z.ast.AxPara)
   */
  public Image visitAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    if ((box == null) || Box.AxBox.equals(box))
      return CZTPluginImages.get(CZTPluginImages.IMG_AXPARA_AXBOX);
    else if (Box.OmitBox.equals(box))
      return CZTPluginImages.get(CZTPluginImages.IMG_AXPARA_OMITBOX);
    else if (Box.SchBox.equals(box))
      return CZTPluginImages.get(CZTPluginImages.IMG_AXPARA_SCHBOX);
    return null;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConjParaVisitor#visitConjPara(net.sourceforge.czt.z.ast.ConjPara)
   */
  public Image visitConjPara(ConjPara conjPara)
  {
    return CZTPluginImages.get(CZTPluginImages.IMG_CONJPARA);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreeParaVisitor#visitFreePara(net.sourceforge.czt.z.ast.FreePara)
   */
  public Image visitFreePara(FreePara freePara)
  {
    return CZTPluginImages.get(CZTPluginImages.IMG_FREEPARA);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OptempParaVisitor#visitOptempPara(net.sourceforge.czt.z.ast.OptempPara)
   */
  public Image visitOptempPara(OptempPara optempPara)
  {
    return CZTPluginImages.get(CZTPluginImages.IMG_OPTEMPPARA);
  }

  /*
   * @see net.sourceforge.czt.z.visitor.ConstDeclVisitor#visitConstDecl(net.sourceforge.czt.z.ast.ConstDecl)
   */
  public Image visitConstDecl(ConstDecl constDecl)
  {
    // TODO Auto-generated method stub
    return null;
  }

  /*
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor#visitVarDecl(net.sourceforge.czt.z.ast.VarDecl)
   */
  public Image visitVarDecl(VarDecl varDecl)
  {
    // TODO Auto-generated method stub
    return null;
  }

}
