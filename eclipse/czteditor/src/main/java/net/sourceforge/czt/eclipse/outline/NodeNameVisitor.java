
package net.sourceforge.czt.eclipse.outline;

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
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Operator;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZDeclNameList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.DeclNameVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NarrSectVisitor;
import net.sourceforge.czt.z.visitor.OperVisitor;
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
public class NodeNameVisitor
    implements
      TermVisitor<String>,
      ZSectVisitor<String>,
      GivenParaVisitor<String>,
      AxParaVisitor<String>,
      ConjParaVisitor<String>,
      FreeParaVisitor<String>,
      NarrParaVisitor<String>,
      NarrSectVisitor<String>,
      OptempParaVisitor<String>,
      UnparsedParaVisitor<String>,
      ConstDeclVisitor<String>,
      VarDeclVisitor<String>,
      ZDeclNameVisitor<String>,
      DeclNameVisitor<String>,
      RefExprVisitor<String>,
      PowerExprVisitor<String>,
      DecorExprVisitor<String>,
      SchExprVisitor<String>,
      SetExprVisitor<String>,
      TupleExprVisitor<String>,
      ApplExprVisitor<String>,
      AndExprVisitor<String>,
      OrExprVisitor<String>,
      OperVisitor<String>
{

  public String visitTerm(Term term)
  {
    return String.valueOf(term);
  }
  
  public String visitZSect(ZSect zSect)
  {
    return zSect.getName();
  }

  public String visitGivenPara(GivenPara givenPara)
  {
    return getNames(givenPara.getDeclNames());
  }

  public String visitAxPara(AxPara axPara)
  {
    return getNames(axPara.getZSchText().getZDeclList());
  }

  public String visitConjPara(ConjPara conjPara)
  {
    return getNames((ZDeclNameList) conjPara.getDeclNameList());
  }

  public String visitFreePara(FreePara freePara)
  {
    ZFreetypeList list = (ZFreetypeList) freePara.getFreetypeList();
    return list.get(0).getDeclName().accept(new PrintVisitor());
  }

  public String visitNarrPara(NarrPara narrPara)
  {
    return "Narrative Para";
  }

  public String visitNarrSect(NarrSect narrSect)
  {
    return "Narrative Sect";
  }

  public String visitOptempPara(OptempPara optempPara)
  {
    /*
    ListTerm<Oper> operList = optempPara.getOper();
    
    if (operList.size() == 0)
      return "";
    
    if (operList.size() == 1)
      return operList.get(0).accept(this);
    
    String result = "[" + operList.get(0).accept(this);
    
    for (int i=1; i<operList.size(); i++)
      result = result + ", " + operList.get(i).accept(this);
    
    result = result + "]";
    
    return result;
    */
    return "Optemp Para";
  }

  public String visitUnparsedPara(UnparsedPara unparsedPara)
  {
    return "UnparsedPara";
  }

  public String visitConstDecl(ConstDecl constDecl)
  {
    return constDecl.getZDeclName().accept(this);
  }

  public String visitVarDecl(VarDecl varDecl)
  {
    ZDeclNameList declNameList = varDecl.getDeclName();
    if (declNameList.size() == 0)
      return null;
    String name = getNames(declNameList);
    //String type = varDecl.getExpr().accept(this);
    //return name + " : " + type;
    return name;
  }

  public String visitZDeclName(ZDeclName zDeclName)
  {
    return zDeclName.accept(new PrintVisitor());
  }
  
  public String visitDeclName(DeclName declName)
  {
    return declName.accept(new PrintVisitor());
  }

  public String visitRefExpr(RefExpr refExpr)
  {
    return refExpr.getZRefName().getWord();
  }

  public String visitPowerExpr(PowerExpr powerExpr)
  {
    return powerExpr.getExpr().accept(this);
  }

  public String visitDecorExpr(DecorExpr decorExpr)
  {
    return decorExpr.getExpr().accept(this);
  }

  public String visitSchExpr(SchExpr schExpr)
  {
    return schExpr.getZSchText().getPred().accept(this);
  }

  public String visitSetExpr(SetExpr setExpr)
  {
    return setExpr.accept(new PrintVisitor());
  }

  public String visitTupleExpr(TupleExpr tupleExpr)
  {
    return tupleExpr.accept(new PrintVisitor());
  }

  public String visitApplExpr(ApplExpr applExpr)
  {
    return applExpr.accept(new PrintVisitor());
  }

  public String visitAndExpr(AndExpr andExpr)
  {
    return andExpr.accept(new PrintVisitor());
  }

  public String visitOrExpr(OrExpr orExpr)
  {
    return orExpr.accept(new PrintVisitor());
  }
  
  public String visitOper(Oper oper)
  {
    return oper.toString();
  }

  private String getNames(ZDeclNameList declNames)
  {
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
  
  private String getNames(ZDeclList declList) {
    if (declList.size() == 0)
      return "";
    
    if (declList.size() == 1)
      return declList.get(0).accept(this);
    
    String result = "[" + declList.get(0).accept(this);
    for (int i=1; i<declList.size(); i++)
      result = result + ", " + declList.get(i).accept(this);
    result = result + "]";
    
    return result;
  }
}
