package net.sourceforge.czt.eclipse.editors.visitor;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZDeclNameList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NarrSectVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.OrExprVisitor;
import net.sourceforge.czt.z.visitor.PowerExprVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.TupleExprVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclNameVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
/**
 * @author Chengdong Xu
 */
public class NodeNameVisitor implements
		TermVisitor<String>, GivenParaVisitor<String>,
		AxParaVisitor<String>, ConjParaVisitor<String>,
		FreeParaVisitor<String>, NarrParaVisitor<String>,
		NarrSectVisitor<String>, OptempParaVisitor<String>,
		UnparsedParaVisitor<String>, ZSectVisitor<String>,
		ConstDeclVisitor<String>, VarDeclVisitor<String>,
		ZDeclNameVisitor<String>, RefExprVisitor<String>,
		PowerExprVisitor<String>, DecorExprVisitor<String>,
		SchExprVisitor<String>, SetExprVisitor<String>,
		TupleExprVisitor<String>, ApplExprVisitor<String>,
		AndExprVisitor<String>, OrExprVisitor<String> {

	public String visitTerm(Term term) {
		return String.valueOf(term);
	}
	
	public String visitGivenPara(GivenPara givenPara) {
		return "GivenPara: " + getNames(givenPara.getDeclName());
	}

	public String visitAxPara(AxPara axPara) {
		return "AxPara: " + getNames(axPara.getDeclName());
	}

	public String visitConjPara(ConjPara conjPara) {
		return "ConjPara" + getNames((ZDeclNameList)conjPara.getDeclNameList());
	}

	public String visitFreePara(FreePara freePara) {
		return "FreePara" + freePara.getFreetype().toString();
	}

	public String visitNarrPara(NarrPara narrPara) {
		return "Narrative";
	}

	public String visitNarrSect(NarrSect narrSect) {
		return "Narrative";
	}

	public String visitOptempPara(OptempPara optempPara) {
		return "OptempPara";
	}

	public String visitUnparsedPara(UnparsedPara unparsedPara) {
		return "UnparsedPara";
	}

	public String visitZSect(ZSect zSect) {
		return zSect.getName();
	}
	
	public String visitConstDecl(ConstDecl constDecl) {
		return constDecl.getZDeclName().accept(this);
	}
	
	public String visitVarDecl(VarDecl varDecl) {
		ZDeclNameList declNameList = varDecl.getDeclName();
		if (declNameList.size() == 0)
			return null;
		String name;
		if (declNameList.size() == 1)
			name = declNameList.get(0).toString();
		else
			name = declNameList.toString();

		String type = varDecl.getExpr().accept(this);
		return name + " : " + type;
	}

	public String visitZDeclName(ZDeclName zDeclName) {
		return zDeclName.toString();
	}
	
	public String visitRefExpr(RefExpr refExpr) {
		return refExpr.getZRefName().getWord();
	}
	
	public String visitPowerExpr(PowerExpr powerExpr) {
		return powerExpr.getExpr().accept(this);
	}

	public String visitDecorExpr(DecorExpr decorExpr) {
		return decorExpr.getExpr().accept(this);
	}
	
	public String visitSchExpr(SchExpr schExpr) {
		return schExpr.getZSchText().getPred().accept(this);
	}
	
	public String visitSetExpr(SetExpr setExpr) {
		return String.valueOf(setExpr);
	}
	
	public String visitTupleExpr(TupleExpr tupleExpr) {
		return String.valueOf(tupleExpr);
	}
	
	public String visitApplExpr(ApplExpr applExpr) {
		return String.valueOf(applExpr);
	}
	
	public String visitAndExpr(AndExpr andExpr) {
		return String.valueOf(andExpr);
	}
	
	public String visitOrExpr(OrExpr orExpr) {
		return String.valueOf(orExpr);
	}
	
	private String getNames(ZDeclNameList declNames) {
		if (declNames.size() == 0)
			return "";
		if (declNames.size() == 1)
			return declNames.get(0).accept(this);
		String result = "[" + declNames.get(0).accept(this);
		for (int i = 1; i < declNames.size(); i++)
			result = result + ", " + declNames.get(i).accept(this);
		result = result + "]";

		return result;
	}
}
