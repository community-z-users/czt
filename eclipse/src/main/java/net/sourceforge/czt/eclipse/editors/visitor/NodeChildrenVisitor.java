package net.sourceforge.czt.eclipse.editors.visitor;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * 
 * @author Chengdong Xu
 *
 */
public class NodeChildrenVisitor implements TermVisitor<Term[]>,
		SpecVisitor<Term[]>, ZSectVisitor<Term[]>,
		AxParaVisitor<Term[]>, SchExprVisitor<Term[]> {
	public Term[] visitTerm(Term term) {
		List<Term> children = new ArrayList<Term>();
		for (Object child : term.getChildren()) {
			if (child != null)
				if (child instanceof Term)
					children.add((Term)child);
		}
		
		return children.toArray(new Term[0]);
	}
	
	public Term[] visitSpec(Spec spec) {
		List<Sect> children = spec.getSect();
		for (Iterator<Sect> iter = children.iterator(); iter.hasNext();) {
			Sect sect = iter.next();
			if (sect instanceof NarrSect) {
				iter.remove();
			}
		}	
		return children.toArray(new Term[0]);
	}
	
	public Term[] visitZSect(ZSect zSect) {
		List<Para> children = zSect.getPara();
		for (Iterator<Para> iter = children.iterator(); iter.hasNext();) {
			Para para = iter.next();
			if (para instanceof LatexMarkupPara) {
				iter.remove();
			}
		}
		return children.toArray(new Term[0]);
	}

	public Term[] visitAxPara(AxPara axPara) {
		return axPara.getZSchText().getZDeclList().toArray(new Term[0]);
	}

	public Term[] visitSchExpr(SchExpr schExpr) {
		return schExpr.getZSchText().getZDeclList().toArray(new Term[0]);
	}
}
