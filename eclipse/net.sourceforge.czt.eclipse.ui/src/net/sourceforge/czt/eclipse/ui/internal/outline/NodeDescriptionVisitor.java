
package net.sourceforge.czt.eclipse.ui.internal.outline;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.eclipse.ui.internal.outline.NodeNameVisitor.PrintVisitor;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Operand;
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
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
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
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z.visitor.ZNameListVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * @author Chengdong Xu
 */
public class NodeDescriptionVisitor
    implements
      TermVisitor<String>,
      ZSectVisitor<String>,
      NarrSectVisitor<String>,
      GivenParaVisitor<String>,
      AxParaVisitor<String>,
      ConjParaVisitor<String>,
      FreeParaVisitor<String>,
      OptempParaVisitor<String>,
      NarrParaVisitor<String>,
      UnparsedParaVisitor<String>,
      ConstDeclVisitor<String>,
      VarDeclVisitor<String>,
      ZDeclListVisitor<String>,
      ZNameVisitor<String>,
      ZNameListVisitor<String>,
      RefExprVisitor<String>,
      PowerExprVisitor<String>,
      DecorExprVisitor<String>,
      SchExprVisitor<String>,
      SetExprVisitor<String>,
      TupleExprVisitor<String>,
      ApplExprVisitor<String>,
      AndExprVisitor<String>,
      OrExprVisitor<String>,
      OperVisitor<String>,
      GivenTypeVisitor<String>,
      ZFreetypeListVisitor<String>,
      FreetypeVisitor<String>
{

  /**
   * @see net.sourceforge.czt.z.visitor.TermVisitor#visitTerm(net.sourceforge.czt.z.ast.Term)
   */
  public String visitTerm(Term term)
  {
    String result = term.accept(new PrintVisitor());
    if (result != null)
      return result;

//    String classname = term.getClass().getSimpleName();
//    if (classname.endsWith("Impl"))
//      classname = classname.substring(0, classname.lastIndexOf("Impl"));
//    return classname;
    return null;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZSectVisitor#visitZSect(net.sourceforge.czt.z.ast.ZSect)
   */
  public String visitZSect(ZSect zSect)
  {
    return "Z Section - " + zSect.getName();
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrSectVisitor#visitNarrSect(net.sourceforge.czt.z.ast.NarrSect)
   */
  public String visitNarrSect(NarrSect narrSect)
  {
    return "Narrative Section";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.GivenParaVisitor#visitGivenPara(net.sourceforge.czt.z.ast.GivenPara)
   */
  public String visitGivenPara(GivenPara givenPara)
  {
    return "Given Paragraph - " + givenPara.getNames().accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.AxParaVisitor#visitAxPara(net.sourceforge.czt.z.ast.AxPara)
   */
  public String visitAxPara(AxPara axPara)
  {
    return "Axiomatic Paragraph - "
        + axPara.getZSchText().getZDeclList().accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConjParaVisitor#visitConjPara(net.sourceforge.czt.z.ast.ConjPara)
   */
  public String visitConjPara(ConjPara conjPara)
  {
    return "Conjecture Paragraph - " + (conjPara.getZNameList()).accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreeParaVisitor#visitFreePara(net.sourceforge.czt.z.ast.FreePara)
   */
  public String visitFreePara(FreePara freePara)
  {
    ZFreetypeList list = (ZFreetypeList) freePara.getFreetypeList();
    return "Free Types Paragraph - " + list.accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OptempParaVisitor#visitOptempPara(net.sourceforge.czt.z.ast.OptempPara)
   */
  public String visitOptempPara(OptempPara optempPara)
  {
    return "Operator Template Parargraph - "
        + OpTable.getOpNameWithoutStrokes(optempPara.getOper());
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrParaVisitor#visitNarrPara(net.sourceforge.czt.z.ast.NarrPara)
   */
  public String visitNarrPara(NarrPara narrPara)
  {
    return "Narrative Paragraph";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.UnparsedParaVisitor#visitUnparsedPara(net.sourceforge.czt.z.ast.UnparsedPara)
   */
  public String visitUnparsedPara(UnparsedPara unparsedPara)
  {
    return "Unparsed Paragraph";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConstDeclVisitor#visitConstDecl(net.sourceforge.czt.z.ast.ConstDecl)
   */
  public String visitConstDecl(ConstDecl constDecl)
  {
    return constDecl.getZName().accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor#visitVarDecl(net.sourceforge.czt.z.ast.VarDecl)
   */
  public String visitVarDecl(VarDecl varDecl)
  {
    ZNameList declNameList = varDecl.getName();
    if (declNameList.size() == 0)
      return null;
    String name = declNameList.accept(this);
    String type = varDecl.getExpr().accept(this);
    return name + " : " + type;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZDeclListVisitor#visitZDeclList(net.sourceforge.czt.z.ast.ZDeclList)
   */
  public String visitZDeclList(ZDeclList zDeclList)
  {
    if (zDeclList.size() == 0)
      return "";

    if (zDeclList.size() == 1)
      return zDeclList.get(0).accept(this);

    String result = "[" + zDeclList.get(0).accept(this);
    for (int i = 1; i < zDeclList.size(); i++)
      result = result + ", " + zDeclList.get(i).accept(this);
    result = result + "]";

    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZNameVisitor#visitZName(net.sourceforge.czt.z.ast.ZName)
   */
  public String visitZName(ZName zName)
  {
    return zName.accept(new PrintVisitor());
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZNameListVisitor#visitZNameList(net.sourceforge.czt.z.ast.ZNameList)
   */
  public String visitZNameList(ZNameList zNameList)
  {
    if (zNameList.size() == 0)
      return "";

    if (zNameList.size() == 1)
      return zNameList.get(0).accept(this);

    String result = "[" + zNameList.get(0).accept(this);
    for (int i = 1; i < zNameList.size(); i++)
      result = result + ", " + zNameList.get(i).accept(this);
    result = result + "]";

    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.RefExprVisitor#visitRefExpr(net.sourceforge.czt.z.ast.RefExpr)
   */
  public String visitRefExpr(RefExpr refExpr)
  {
    return refExpr.getZName().getWord();
  }

  /**
   * @see net.sourceforge.czt.z.visitor.PowerExprVisitor#visitPowerExpr(net.sourceforge.czt.z.ast.PowerExpr)
   */
  public String visitPowerExpr(PowerExpr powerExpr)
  {
    return powerExpr.getExpr().accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.DecorExprVisitor#visitDecorExpr(net.sourceforge.czt.z.ast.DecorExpr)
   */
  public String visitDecorExpr(DecorExpr decorExpr)
  {
    return decorExpr.getExpr().accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.SchExprVisitor#visitSchExpr(net.sourceforge.czt.z.ast.SchExpr)
   */
  public String visitSchExpr(SchExpr schExpr)
  {
    return schExpr.getZSchText().getPred().accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.SetExprVisitor#visitSetExpr(net.sourceforge.czt.z.ast.SetExpr)
   */
  public String visitSetExpr(SetExpr setExpr)
  {
    return setExpr.accept(new PrintVisitor());
  }

  /**
   * @see net.sourceforge.czt.z.visitor.TupleExprVisitor#visitTupleExpr(net.sourceforge.czt.z.ast.TupleExpr)
   */
  public String visitTupleExpr(TupleExpr tupleExpr)
  {
    return tupleExpr.accept(new PrintVisitor());
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ApplExprVisitor#visitApplExpr(net.sourceforge.czt.z.ast.ApplExpr)
   */
  public String visitApplExpr(ApplExpr applExpr)
  {
    return applExpr.accept(new PrintVisitor());
  }

  /**
   * @see net.sourceforge.czt.z.visitor.AndExprVisitor#visitAndExpr(net.sourceforge.czt.z.ast.AndExpr)
   */
  public String visitAndExpr(AndExpr andExpr)
  {
    return andExpr.accept(new PrintVisitor());
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OrExprVisitor#visitOrExpr(net.sourceforge.czt.z.ast.OrExpr)
   */
  public String visitOrExpr(OrExpr orExpr)
  {
    return orExpr.accept(new PrintVisitor());
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OperVisitor#visitOper(net.sourceforge.czt.z.ast.Oper)
   */
  public String visitOper(Oper oper)
  {
    if (oper instanceof Operator)
      return "OPERATOR - " + ((Operator) oper).getWord();
    else if (oper instanceof Operand)
      return "OPERAND";

    return "OPER";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.GivenTypeVisitor#visitGivenType(net.sourceforge.czt.z.ast.GivenType)
   */
  public String visitGivenType(GivenType givenType)
  {
    return givenType.getName().accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZFreetypeListVisitor#visitZFreetypeList(net.sourceforge.czt.z.ast.ZFreetypeList)
   */
  public String visitZFreetypeList(ZFreetypeList zFreetypeList)
  {
    return zFreetypeList.get(0).accept(this);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreetypeVisitor#visitFreetype(net.sourceforge.czt.z.ast.Freetype)
   */
  public String visitFreetype(Freetype freetype)
  {
    return freetype.getZName().accept(new PrintVisitor());
  }
}
