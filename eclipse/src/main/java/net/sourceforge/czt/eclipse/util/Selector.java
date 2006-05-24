package net.sourceforge.czt.eclipse.util;

import java.util.Stack;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.ZRefName;

import org.eclipse.jface.text.Position;

/**
 * @author Chengdong Xu
 */
public class Selector {
	private Term fAST = null;
	private Stack<Term> fTermStack = new Stack<Term>();
	private int fSelection = -1;
	
	public Selector(Term ast) {
		this.fAST = ast;
	}
	
	public Term getTerm(Position position) {
		init();
		fillTermStack(fAST, position);
		
		if (fTermStack.isEmpty())
			return null;
		
		fSelection = fTermStack.size() - 1;
		return fTermStack.get(fSelection);
	}
	
	public Term previous() {
		if (fTermStack.isEmpty())
			return null;
		fSelection++;
		if (fSelection > fTermStack.size())
			fSelection--;
		if (fSelection == fTermStack.size())
			return null;
		return fTermStack.get(fSelection);
	}
	
	public Term current() {
		if (fSelection < 0)
			return null;
		return fTermStack.get(fSelection);
	}
	
	public Term next() {
		if (fTermStack.isEmpty())
			return null;
		fSelection--;
		if (fSelection == -1)
			return null;
		if (fSelection < -1)
			fSelection = fTermStack.size() - 1;
		return fTermStack.get(fSelection);
	}
	
	private void init() {
		this.fTermStack.clear();
		this.fSelection = -1;
	}
	
	private boolean fillTermStack(Object object, Position position) {
		if (object == null)
			return false;
		if (!(object instanceof Term))
			return false;
		
		boolean success = false;
		Term term = (Term)object;
		LocAnn locAnn = (LocAnn)term.getAnn(LocAnn.class);
		if (locAnn != null) {
			Integer start = locAnn.getStart();
			Integer length = locAnn.getLength();
			if ((start != null) && (length != null)) {
				if ((start <= position.getOffset())
						&& (start + length >= position.getOffset()
								+ position.getLength())) {
					this.fTermStack.push(term);		
					success = true;
				}
			}
		}
		
		if (term instanceof ZRefName)
			return success;
		
		for (Object child : term.getChildren()) {
			if (fillTermStack(child, position))
				return true;
		}
		
		return success;
	}	
}
