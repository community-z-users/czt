
package net.sourceforge.czt.eclipse.ui.internal.outline;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
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
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.visitor.ProofScriptVisitor;

/**
 * Just for declarations within CztTreeNoteFactory created elements.
 * @author Chengdong Xu
 * @author Andrius Velykis
 * @author Leo Freitas
 *
 */
public class NodeChildrenVisitor
    implements
      TermVisitor<List<? extends Term>>,
      SpecVisitor<List<? extends Term>>,
      ZSectVisitor<List<? extends Term>>,
      ZParaListVisitor<List<? extends Term>>,
      AxParaVisitor<List<? extends Term>>,
      SchExprVisitor<List<? extends Term>>,
      ClassParaVisitor<List<? extends Term>>,   // for Object-Z
      ProofScriptVisitor<List<? extends Term>>, // for Z/EVES
	// Circus
	ChannelParaVisitor<List<? extends Term>>
{
  public List<? extends Term> visitTerm(Term term)
  {
    /*
    List<? extends Term> children = new ArrayList<Term>();
    for (Object child : term.getChildren()) {
      if (child != null)
        if (child instanceof Term)
          children.add((Term) child);
    }

    return children.toArray(new Term[0]);
    */
    return Collections.emptyList();
  }

  public List<? extends Term> visitSpec(Spec spec)
  {
    List<Sect> children = new ArrayList<Sect>();
    for (Sect sect : spec.getSect()) {
      if (sect instanceof NarrSect) {
        continue;
      }
      
      children.add(sect);
    }
    return children;
  }
  
  public List<? extends Term> visitZSect(ZSect zSect)
  {
    return zSect.getParaList().accept(this);
  }

  public List<? extends Term> visitZParaList(ZParaList zParaList)
  {
    List<Para> result = new ArrayList<Para>();
    for (Para para : zParaList) {
      if (! (para instanceof LatexMarkupPara) &&
          ! (para instanceof NarrPara)) {
        result.add(para);
      }
    }
    return result;
  }
  
  public List<? extends Term> visitAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    
    if (box == null || Box.AxBox.equals(box)) {
      return axPara.getZSchText().getZDeclList();
    }
    
    return Collections.emptyList();
  }
  
  public List<? extends Term> visitSchExpr(SchExpr schExpr)
  {
    return schExpr.getZSchText().getZDeclList();
  }
  
  public List<? extends Term> visitClassPara(ClassPara para)
  {
    return Collections.emptyList(); // para.getName()  //getZSchText().getZDeclList().toArray(new Term[0]);
  }

  // Z/EVES 
  @Override
  public List<? extends Term> visitProofScript(ProofScript term)
  { 
    return term.getProofCommandList();
  }

  // Circus: nothing with declaration except Channel?

	@Override
	public List<? extends Term> visitChannelPara(ChannelPara term) {
		return term.getZDeclList(); 
	}
}
