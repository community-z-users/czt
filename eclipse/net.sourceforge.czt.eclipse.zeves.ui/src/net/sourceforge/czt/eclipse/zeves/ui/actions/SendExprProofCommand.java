package net.sourceforge.czt.eclipse.zeves.ui.actions;

import org.eclipse.swt.widgets.Shell;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Expr;


public class SendExprProofCommand extends SendSelectionProofCommand {

	@Override
	protected Expr parseSelection(Shell shell, String selectedText, SectionManager sectInfo,
			String sectName) {
		
		Term term = super.parseSelection(shell, selectedText, sectInfo, sectName);
		if (term instanceof Expr) {
			return (Expr) term;
		}
		
		return null;
	}

}
