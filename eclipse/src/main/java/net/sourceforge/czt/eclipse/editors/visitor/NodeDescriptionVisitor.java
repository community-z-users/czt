package net.sourceforge.czt.eclipse.editors.visitor;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NarrSectVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclNameVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * @author Chengdong Xu
 */
public class NodeDescriptionVisitor implements TermVisitor<String>,
		AxParaVisitor<String>, ConjParaVisitor<String>,
		FreeParaVisitor<String>, NarrParaVisitor<String>,
		NarrSectVisitor<String>, OptempParaVisitor<String>,
		UnparsedParaVisitor<String>, ZSectVisitor<String>,
		VarDeclVisitor<String>, ZDeclNameVisitor<String> {
	
	public String visitTerm(Term term) {
		return term.getClass().getName();
	}
	
	public String visitAxPara(AxPara axPara) {
		return "Z paragraph - " + axPara.getDeclName().toString();
	}
	
	public String visitConjPara(ConjPara conjPara) {
		return "Conjecture paragraph - " + conjPara.getDeclName().toString();
	}
	
	public String visitFreePara(FreePara freePara) {
		return "Free types paragraph";
	}
	
	public String visitNarrPara(NarrPara narrPara) {
		return "Narrative paragraph";
	}
	
	public String visitNarrSect(NarrSect narrSect) {
		return "Narrative section";
	}
	
	public String visitOptempPara(OptempPara optempPara) {
		return "Operator template parargraph";
	}
	
	public String visitUnparsedPara(UnparsedPara unparsedPara) {
		return "Unparsed paragraph";
	}
	
	public String visitZSect(ZSect zSect) {
		return "Z section '" + zSect.getName() + "'";
	}
	
	public String visitVarDecl(VarDecl varDecl) {
		return varDecl.getDeclName().toString();
	}
	
	public String visitZDeclName(ZDeclName zDeclName) {
		return zDeclName.getWord();
	}
}
