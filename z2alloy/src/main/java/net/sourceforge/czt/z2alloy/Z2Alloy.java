/**
Copyright (C) 2008 Petra Malik, Clare Lenihan
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z2alloy;

import java.io.StringWriter;
import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.parser.zpatt.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.visitor.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

public class Z2Alloy
  implements TermVisitor<Term>,
	     AndPredVisitor<Term>,
	     ApplExprVisitor<Term>,
	     AxParaVisitor<Term>,
	     ConjParaVisitor<Term>,
	     //	     ConstDeclVisitor<Term>,
	     DecorExprVisitor<Term>,
	     ExistsPredVisitor<Term>,
	     ExprPredVisitor<Term>,
	     ForallPredVisitor<Term>,
	     FreeParaVisitor<Term>,
	     FreetypeVisitor<Term>,
	     GivenParaVisitor<Term>,
	     ImpliesPredVisitor<Term>,
	     InclDeclVisitor<Term>,
	     LatexMarkupParaVisitor<Term>,
	     MemPredVisitor<Term>,
	     NarrParaVisitor<Term>,
	     OrPredVisitor<Term>,
	     PowerExprVisitor<Term>,
	     ProdExprVisitor<Term>,
             RefExprVisitor<Term>,
	     RuleVisitor<Term>,
	     SchExprVisitor<Term>,
	     SetCompExprVisitor<Term>,
	     SetExprVisitor<Term>,
	     TruePredVisitor<Term>,
	     VarDeclVisitor<Term>,
	     ZDeclListVisitor<Term>,
	     ZFreetypeListVisitor<Term>,
	     ZSchTextVisitor<Term>,
             ZSectVisitor<Term>
{
  private SectionManager manager_;
  private AlloyPrintVisitor printVisitor = new AlloyPrintVisitor();
  private String section_ = "z2alloy";
  private Map<String,String> binOpTable_;

  public Z2Alloy(SectionManager manager)
    throws Exception
  {
    manager_ = manager;
    binOpTable_ = buildBinOpTable();
  }

  private Map<String,String> buildBinOpTable()
  {
    Map result = new HashMap<String,String>();
    result.put(ZString.CUP, "+");
    result.put(ZString.MAPSTO, "->");
    result.put(ZString.OPLUS, "++");
    return result;
  }

  //==================== Visitor Methods ==================

  public Term visitTerm(Term term)
  {
    System.err.println(term.getClass() + " not yet implemented");
    return null;
  }

  public Term visitAndPred(AndPred andPred)
  {
    visit(andPred.getLeftPred());
    System.out.println(" and ");
    visit(andPred.getRightPred());
    return null;
  }

  public Term visitApplExpr(ApplExpr applExpr)
  {
    if (applExpr.getRightExpr() instanceof TupleExpr &&
	applExpr.getLeftExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
      String binOp = isInfixOperator(refExpr.getZName());
      if (binOpTable_.containsKey(binOp)) {
	ZExprList exprs = ((TupleExpr) applExpr.getRightExpr()).getZExprList();
	visit(exprs.get(0));
	System.out.print(" " + binOpTable_.get(binOp) + " ");
	visit(exprs.get(1));
	return null;
      }
      if (isInfixOperator(refExpr.getZName(), ZString.NDRES)) { // ndres
	ZExprList exprs = ((TupleExpr) applExpr.getRightExpr()).getZExprList();
	System.out.print("ndres[");
	visit(exprs.get(0));
	System.out.print(", ");
	visit(exprs.get(1));
	System.out.print("]");
	return null;
      }
      if ((refExpr.getZName().getZStrokeList() == null ||
	   refExpr.getZName().getZStrokeList().size() == 0) &&
	  ZString.ARITHMOS.equals(refExpr.getZName().getWord())) {
	System.out.print(" Int ");
	return null;
      }
    }
    visit(applExpr.getLeftExpr());
    System.out.print("[");
    visit(applExpr.getRightExpr());
    System.out.print("]");
    return null;
  }

  public Term visitAxPara(AxPara para)
  {
    if (para.getName().size() > 0) {
      System.err.println("Generic definitions not handled yet.");
      return null;
    }
    ZSchText schText = para.getZSchText();
    for (Decl decl : schText.getZDeclList()) {
      if (decl instanceof ConstDecl) {
	ConstDecl cDecl = (ConstDecl) decl;
	try {
	  String sigName = print(cDecl.getName());
	  Source exprSource =
	    new StringSource("normalize~" +
			     cDecl.getName().accept(new PrintVisitor()));
	  exprSource.setMarkup(Markup.LATEX);
	  Expr toBeNormalized =
	    ParseUtils.parseExpr(exprSource, section_, manager_);
	  Expr result = (Expr) preprocess(toBeNormalized);
	  if (! (result instanceof SchExpr)) {
	    System.out.println("one sig " + print(cDecl.getName()) + " {");
	    System.out.print("  data: ");
	    visit(cDecl.getExpr());
	    System.out.println("\n}");
	    return null;
	  }
	  System.out.println("sig " + sigName + " { ");
	  visit(((SchExpr)result).getZSchText().getDeclList());
	  System.out.println("}{");
	  visit(((SchExpr)result).getZSchText().getPred());
	  System.out.println("\n}\nrun { one " + sigName + " }\n");
	}
	catch (Exception e) {
	  throw new RuntimeException(e);
	}
      }
      else if (decl instanceof VarDecl) {
	VarDecl vDecl = (VarDecl) decl;
	if (vDecl.getExpr() instanceof RefExpr) {
	  System.out.print("one sig " + print(vDecl.getName()) + " in ");
	  visit(vDecl.getExpr());
	  System.out.println(" {}");
	  return null;
	}
	else {
	  System.out.println("one sig " + print(vDecl.getName()) + " {");
	  System.out.print("  data: ");
	  visit(vDecl.getExpr());
	  System.out.println("\n}");
	}
      }
      else {
	System.err.println(decl.getClass() + " in AxPara not yet supported");
      }
    }
    if (schText.getPred() != null) {
      System.out.println("fact {");
      visit(schText.getPred());
      System.out.println("}");
    }
    return null;
  }

  public Term visitConjPara(ConjPara cPara)
  {
    debug(preprocess(cPara.getPred()));
    System.out.println("pred " + cPara.getName() + " {");
    visit(preprocess(cPara.getPred()));
    System.out.println("\n}");
    return null;
  }

  public Term visitDecorExpr(DecorExpr decorExpr)
  {
    System.out.print(" a': ");
    visit(decorExpr.getExpr());
    return null;
  }

  public Term visitExistsPred(ExistsPred existsPred)
  {
    System.out.print(" some ");
    visit(existsPred.getZSchText().getDeclList());
    System.out.print(" | ");
    visit(existsPred.getZSchText().getPred());
    if (existsPred.getZSchText().getPred() != null)
      System.out.print(" and ");
    visit(existsPred.getPred());
    return null;
  }

  public Term visitExprPred(ExprPred exprPred)
  {
    visit(exprPred.getExpr());
    return null;
  }

  public Term visitForallPred(ForallPred allPred)
  {
    System.out.print(" all ");
    visit(allPred.getZSchText().getDeclList());
    System.out.print(" | ");
    visit(allPred.getZSchText().getPred());
    if (allPred.getZSchText().getPred() != null)
      System.out.print(" implies ");
    visit(allPred.getPred());
    return null;
  }

  public Term visitFreePara(FreePara para)
  {
    visit(para.getFreetypeList());
    return null;
  }

  public Term visitFreetype(Freetype freetype)
  {
    System.out.print("enum " + print(freetype.getName()) + " { ");
    Iterator<Branch> i = assertZBranchList(freetype.getBranchList()).iterator();
    while (i.hasNext()) {
      Branch branch = (Branch) i.next();
      if (branch.getExpr() != null)
        System.err.println("free types must be simple enumerations, but "
			   +branch.getName()+" branch has expression "
			   +branch.getExpr());
      System.out.print(print(branch.getName()));
      System.out.print(i.hasNext() ? ", " : " ");
    }
    System.out.println("}");
    return null;
  }

  public Term visitGivenPara(GivenPara para)
  {
    for (Name name : para.getNames()) {
      System.out.println("sig " + print(name) + " {}");
    }
    return null;
  }

  public Term visitImpliesPred(ImpliesPred impl)
  {
    System.out.print("(");
    visit(impl.getLeftPred());
    System.out.print(" implies ");
    visit(impl.getRightPred());
    System.out.print(")");
    return null;
  }

  public Term visitInclDecl(InclDecl inclDecl)
  {
    visit(inclDecl.getExpr());
    System.out.println(",");
    return null;
  }

  /** Ignore Latex markup paragraphs. */
  public Term visitLatexMarkupPara(LatexMarkupPara para)
  {
    return null;
  }

  public Term visitMemPred(MemPred memPred)
  {
    if (memPred.getRightExpr() instanceof SetExpr &&
	((SetExpr) memPred.getRightExpr()).getZExprList().size() == 1) {
      // equality
      visit(memPred.getLeftExpr());
      System.out.print(" = ");
      visit(((SetExpr) memPred.getRightExpr()).getZExprList().get(0));
      return null;
    }
    if (memPred.getLeftExpr() instanceof TupleExpr &&
	memPred.getRightExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) memPred.getRightExpr();
      if (isInfixOperator(refExpr.getZName(), ZString.NOTMEM)) {
	ZExprList exprs = ((TupleExpr) memPred.getLeftExpr()).getZExprList();
	visit(exprs.get(0));
	System.out.print(" not in ");
	visit(exprs.get(1));
	return null;
      }
    }
    visit(memPred.getLeftExpr());
    System.out.print(" in ");
    visit(memPred.getRightExpr());
    return null;
  }

  /** Ignore narrative paragraphs. */
  public Term visitNarrPara(NarrPara para)
  {
    return null;
  }

  public Term visitOrPred(OrPred orPred)
  {
    System.out.print("(");
    visit(orPred.getLeftPred());
    System.out.print(" or ");
    visit(orPred.getRightPred());
    System.out.print(")");
    return null;
  }

  public Term visitPowerExpr(PowerExpr powerExpr)
  {
    System.out.print(" set (");
    visit(powerExpr.getExpr());
    System.out.print(")");
    return null;
  }

  public Term visitProdExpr(ProdExpr prodExpr)
  {
    for (Iterator<Expr> iter = prodExpr.getZExprList().iterator();
	 iter.hasNext();) {
      visit(iter.next());
      if (iter.hasNext()) System.out.print(" -> ");
    }
    return null;
  }

  public Term visitRefExpr(RefExpr refExpr)
  {
    if (isInfixOperator(refExpr.getZName(), ZString.PFUN)) { // pfun
      visit(refExpr.getZExprList().get(0));
      System.out.print(" -> lone ");
      visit(refExpr.getZExprList().get(1));
      return null;
    }
    if (isPostfixOperator(refExpr.getZName(), "seq")) { // seq
      System.out.print(" seq ");
      visit(refExpr.getZExprList().get(0));
      return null;
    }
    System.out.print(print(refExpr.getName()));
    return null;
  }

  public Term visitRule(Rule r)
  {
    return null;
  }

  public Term visitSchExpr(SchExpr schExpr)
  {
    visit(schExpr.getZSchText());
    return null;
  }

  public Term visitSetCompExpr(SetCompExpr setCompExpr)
  {
    ZSchText zSchText = setCompExpr.getZSchText();
    System.out.print("{");
    visit(zSchText.getDeclList());
    System.out.println(" | ");
    visit(zSchText.getPred());
    System.out.print("}");
    return null;
  }

  public Term visitSetExpr(SetExpr setExpr)
  {
    if (setExpr.getExprList() == null) {
      System.out.print(" none ");
      return null;
    }
    ZExprList exprs = setExpr.getZExprList();
    if (exprs.size() == 0) {
      System.out.print(" none ");
      return null;
    }
    else if (exprs.size() == 1) {
      visit(exprs.get(0));
    }
    else {
      System.out.println(setExpr.getClass() + " not supported");
    }
    return null;
  }

  public Term visitTruePred(TruePred truePred)
  {
    System.out.print(" 1 = 1 ");
    return null;
  }

  public Term visitVarDecl(VarDecl vDecl)
  {
    System.out.print(print(vDecl.getName()) + ": ");
    visit(vDecl.getExpr());
    System.out.println(",");
    return null;
  }

  public Term visitZDeclList(ZDeclList zDeclList)
  {
    for (Decl decl : zDeclList) visit(decl);
    return null;
  }

  public Term visitZFreetypeList(ZFreetypeList list)
  {
    for (Freetype freetype : list)
    {
      visit(freetype);
    }
    return null;
  }

  public Term visitZSchText(ZSchText zSchText)
  {
    visit(zSchText.getDeclList());
    visit(zSchText.getPred());
    return null;
  }

  public Term visitZSect(ZSect zSect)
  {
    Source specSource = new StringSource("\\begin{zsection} "
					 + "\\SECTION " + section_ + " "
					 + "\\parents "
					 + zSect.getName() + ", "
					 + "expansion\\_rules, "
					 + "simplification\\_rules"
					 + "\\end{zsection}",
					 section_);
    specSource.setMarkup(Markup.LATEX);
    manager_.put(new Key<Source>(section_ ,Source.class), specSource);

    if (zSect.getName() != "Specification") {
      System.out.println("module " + zSect.getName());
    }
    System.out.println("open functions");
    for (Para para : zSect.getZParaList()) {
      visit(para);
    }
    return null;
  }

  private boolean isPostfixOperator(ZName name, String op)
  {
    try {
      OperatorName opName = new OperatorName(name);
      String[] opWords = opName.getWords();
      return opWords.length > 0 && op.equals(opWords[0]);
    }
    catch (OperatorName.OperatorNameException e) {
      return false;
    }
  }

  private String isInfixOperator(ZName name)
  {
    try {
      OperatorName opName = new OperatorName(name);
      if (! opName.isInfix()) return null;
      return opName.getWords()[1];
    }
    catch (OperatorName.OperatorNameException e) {
      return null;
    }
  }

  private boolean isInfixOperator(ZName name, String op)
  {
    try {
      OperatorName opName = new OperatorName(name);
      String[] opWords = opName.getWords();
      return opWords.length > 0 && op.equals(opWords[1]);
    }
    catch (OperatorName.OperatorNameException e) {
      return false;
    }
  }

  private String print(Term t)
  {
    if (t != null) return t.accept(printVisitor);
    else return "";
  }

  private void visit(Term t)
  {
    if (t != null) t.accept(this);
  }

  private Term preprocess(Term term)
  {
    try {
      RuleTable rules = 
	manager_.get(new Key<RuleTable>(section_, RuleTable.class));
      RewriteVisitor rewriter =
	new RewriteVisitor(rules, manager_, section_);
      return Strategies.innermost(term, rewriter);
    }
    catch(Exception e) {
      throw new RuntimeException(e);
    }
  }

  private void debug(Term t)
  {
    StringWriter foo = new StringWriter();
    PrintUtils.print(t, foo, manager_, section_, Markup.UNICODE);
    System.out.println("Debug: " + foo);
  }
}

class AlloyPrintVisitor extends PrintVisitor
{
  public String visitZName(ZName zName)
  {
    String word = zName.getWord();
    word = word.replaceAll(ZString.DELTA, "Delta");
    word = word.replaceAll(ZString.XI, "Xi");
    word = word.replaceAll("\u03A8", "Psi");
    return word + visit(zName.getStrokeList());
  }

  public String visitInStroke(InStroke inStroke)
  {
    return "_in";
  }

  public String visitNextStroke(NextStroke nextStroke)
  {
    return "'";
  }

  public String visitOutStroke(OutStroke outStroke)
  {
    return "_out";
  }
}
