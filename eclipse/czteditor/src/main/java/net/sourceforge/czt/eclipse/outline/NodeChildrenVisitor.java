
package net.sourceforge.czt.eclipse.outline;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.oz.ast.ClassPara;
import net.sourceforge.czt.oz.visitor.ClassParaVisitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * 
 * @author Chengdong Xu
 *
 */
public class NodeChildrenVisitor
    implements
      TermVisitor<Term[]>,
      SpecVisitor<Term[]>,
      ZSectVisitor<Term[]>,
      ZParaListVisitor<Term[]>,
      AxParaVisitor<Term[]>,
      SchExprVisitor<Term[]>,
      ClassParaVisitor<Term[]>   // for Object-Z
{
  public Term[] visitTerm(Term term)
  {
    /*
    List<Term> children = new ArrayList<Term>();
    for (Object child : term.getChildren()) {
      if (child != null)
        if (child instanceof Term)
          children.add((Term) child);
    }

    return children.toArray(new Term[0]);
    */
    return new Term[0];
  }

  public Term[] visitSpec(Spec spec)
  {
    List<Sect> children = spec.getSect();
    for (Iterator<Sect> iter = children.iterator(); iter.hasNext();) {
      Sect sect = iter.next();
      if (sect instanceof NarrSect) {
        iter.remove();
      }
    }
    return children.toArray(new Term[0]);
  }
  
  public Term[] visitZSect(ZSect zSect)
  {
    return zSect.getParaList().accept(this);
  }

  public Term[] visitZParaList(ZParaList zParaList)
  {
    List<Para> result = new ArrayList<Para>();
    for (Para para : zParaList) {
      if (! (para instanceof LatexMarkupPara) &&
          ! (para instanceof NarrPara)) {
        result.add(para);
      }
    }
    return result.toArray(new Term[0]);
  }
  
  public Term[] visitAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    
    if (box == null || Box.AxBox.equals(box)) {
      ZDeclList declList = axPara.getZSchText().getZDeclList();
      if (declList.size() > 1)
        return declList.toArray(new Term[0]);
    }
    
    return new Term[0];
  }

  public Term[] visitSchExpr(SchExpr schExpr)
  {
    return schExpr.getZSchText().getZDeclList().toArray(new Term[0]);
  }
  
  public Term[] visitClassPara(ClassPara para)
  {
    return new Term[] {}; // para.getName()  //getZSchText().getZDeclList().toArray(new Term[0]);
  }
}
