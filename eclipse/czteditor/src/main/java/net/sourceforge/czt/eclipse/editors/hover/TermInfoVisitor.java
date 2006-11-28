/**
 * 
 */

package net.sourceforge.czt.eclipse.editors.hover;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.eclipse.editors.parser.NameInfo;
import net.sourceforge.czt.eclipse.editors.parser.NameInfoResolver;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.outline.NodeNameVisitor;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Operand;
import net.sourceforge.czt.z.ast.Operator;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.TupleSelExpr;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
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
import net.sourceforge.czt.z.visitor.TupleSelExprVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z.visitor.ZNameListVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class TermInfoVisitor
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
      ExprVisitor<String>,
      OperVisitor<String>,
      GivenTypeVisitor<String>,
      ZFreetypeListVisitor<String>,
      FreetypeVisitor<String>
{

  ITextEditor fEditor = null;

  private static NodeNameVisitor getTermNameVisitor_ = new NodeNameVisitor();

  public TermInfoVisitor(ITextEditor textEditor)
  {
    fEditor = textEditor;
  }

  /**
   * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
   */
  public String visitTerm(Term term)
  {
    return "The highlighted term is a " + term.accept(getTermNameVisitor_);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZSectVisitor#visitZSect(net.sourceforge.czt.z.ast.ZSect)
   */
  public String visitZSect(ZSect zSect)
  {
    return "The highlighted term is a Z section paragraph." + "\nIts name is "
        + zSect.getName() + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrSectVisitor#visitNarrSect(net.sourceforge.czt.z.ast.NarrSect)
   */
  public String visitNarrSect(NarrSect narrPara)
  {
    return "The highlighted term is a narrative section.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.GivenParaVisitor#visitGivenPara(net.sourceforge.czt.z.ast.GivenPara)
   */
  public String visitGivenPara(GivenPara givenPara)
  {
    String result = "The highlighted term is a given Paragraph.";
    String name = givenPara.getNames().accept(getTermNameVisitor_);
    return result + "\nIts name is " + name + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.AxParaVisitor#visitAxPara(net.sourceforge.czt.z.ast.AxPara)
   */
  public String visitAxPara(AxPara axPara)
  {
    String result = "The highlighted term is an axiomatic paragraph.";
    String name = axPara.getZSchText().getZDeclList().accept(
        getTermNameVisitor_);
    return result + "\nIts name is " + name + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConjParaVisitor#visitConjPara(net.sourceforge.czt.z.ast.ConjPara)
   */
  public String visitConjPara(ConjPara conjPara)
  {
    String result = "The highlighted term is a conjecture paragraph.";
    String name = conjPara.getZNameList().accept(getTermNameVisitor_);
    return result + "\nIts name is " + name + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreeParaVisitor#visitFreePara(net.sourceforge.czt.z.ast.FreePara)
   */
  public String visitFreePara(FreePara freePara)
  {
    String result = "The highlighted term is a free types paragraph.";
    String name = ((ZFreetypeList) freePara.getFreetypeList())
        .accept(getTermNameVisitor_);
    return result + "\nIts name is " + name + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OptempParaVisitor#visitOptempPara(net.sourceforge.czt.z.ast.OptempPara)
   */
  public String visitOptempPara(OptempPara optempPara)
  {
    String result = "The highlighted term is an operator template parargraph.";
    String name = OpTable.getOpNameWithoutStrokes(optempPara.getOper());
    return result + "\nOperators: " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrParaVisitor#visitNarrPara(net.sourceforge.czt.z.ast.NarrPara)
   */
  public String visitNarrPara(NarrPara narrPara)
  {
    return "The highlighted term is a narrative paragraph.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.UnparsedParaVisitor#visitUnparsedPara(net.sourceforge.czt.z.ast.UnparsedPara)
   */
  public String visitUnparsedPara(UnparsedPara unparsedPara)
  {
    return "The highlighted paragraph is not parsed";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConstDeclVisitor#visitConstDecl(net.sourceforge.czt.z.ast.ConstDecl)
   */
  public String visitConstDecl(ConstDecl constDecl)
  {
    String result = "The highlighted term is a ConstDecl";
    String type = constDecl.getExpr().accept(getTermNameVisitor_);
    return result + "\nIts type is " + type + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor#visitVarDecl(net.sourceforge.czt.z.ast.VarDecl)
   */
  public String visitVarDecl(VarDecl varDecl)
  {
    String result = "The highlighted term is a variable declaration.";
    String type = varDecl.getExpr().accept(getTermNameVisitor_);
    return result + "\nThe type of the variable(s) is " + type + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor#visitZDeclList(net.sourceforge.czt.z.ast.ZDeclList)
   */
  public String visitZDeclList(ZDeclList zDeclList)
  {
    return "This highlighted term is a declaration list.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZNameVisitor#visitZName(net.sourceforge.czt.z.ast.ZName)
   */
  public String visitZName(ZName zName)
  {
    String result = "The highlighted term is a Z name.";
    String type = getTypeOfZName(zName);
    if (type != null)
      result = result.concat("\nIts type is " + type + ".");

    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZNameListVisitor#visitZNameList(net.sourceforge.czt.z.ast.ZNameList)
   */
  public String visitZNameList(ZNameList zNameList)
  {
    if (zNameList.size() == 0)
      return null;

    String result = "The highlighted term is a Z name list";
    String type = getTypeOfZName((ZName) zNameList.get(0));
    if (type != null)
      result = result.concat("\nThe type of the name(s) is " + type + ".");

    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.RefExprVisitor#visitRefExpr(net.sourceforge.czt.z.ast.RefExpr)
   */
  public String visitExpr(Expr expr)
  {
    String result = "The highlighted term is an expression - "
        + expr.accept(getTermNameVisitor_) + ".";
    TypeAnn typeann = expr.getAnn(TypeAnn.class);
    String type = null;
    if (typeann != null)
      type = typeann.getType().accept(new PrintVisitor());
    if (type != null)
      result = result.concat("\nIts type is " + type);

    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OperVisitor#visitOper(net.sourceforge.czt.z.ast.Oper)
   */
  public String visitOper(Oper oper)
  {
    if (oper instanceof Operator)
      return "The highlighted term is an operator.";
    else if (oper instanceof Operand)
      return "The highlighted term is an operand.";

    return null;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.GivenTypeVisitor#visitGivenType(net.sourceforge.czt.z.ast.GivenType)
   */
  public String visitGivenType(GivenType givenType)
  {
    return "The highlighted term is a given type.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreetypeListVisitor#visitFreetypeList(net.sourceforge.czt.z.ast.FreetypeList)
   */
  public String visitZFreetypeList(ZFreetypeList zFreetypeList)
  {
    return "The highlighted term is a Z free types list.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreetypeVisitor#visitFreetype(net.sourceforge.czt.z.ast.Freetype)
   */
  public String visitFreetype(Freetype freetype)
  {
    return "The highlighted term is a Z free type.";
  }

  private String getTypeOfZName(ZName zName)
  {
    if (fEditor == null || !(fEditor instanceof ZEditor))
      return null;

    List<NameInfo> nameInfoList = ((ZEditor) fEditor).getParsedData()
        .getNameInfoList();
    NameInfo info = NameInfoResolver.findInfo(nameInfoList, zName);
    if (info != null)
      return info.getType();

    return null;
  }
}
