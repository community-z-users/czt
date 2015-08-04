/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.hover;

import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.NameInfo;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.NameInfoResolver;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.outline.TermLabelVisitorFactory;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
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
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NarrSectVisitor;
import net.sourceforge.czt.z.visitor.OperVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
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
public class TermHighlightInfoVisitor
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

  public TermHighlightInfoVisitor(ITextEditor textEditor)
  {
    fEditor = textEditor;
  }

  /**
   * @see net.sourceforge.czt.base.visitor.TermVisitor
   *    #visitTerm(net.sourceforge.czt.base.ast.Term)
   */
  public String visitTerm(Term term)
  {
    return "The highlighted term is a " + getClassName(term);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZSectVisitor
   *    #visitZSect(net.sourceforge.czt.z.ast.ZSect)
   */
  public String visitZSect(ZSect zSect)
  {
    return "The highlighted term is a Z section paragraph - " + zSect.getName()
        + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrSectVisitor
   *    #visitNarrSect(net.sourceforge.czt.z.ast.NarrSect)
   */
  public String visitNarrSect(NarrSect narrPara)
  {
    return "The highlighted term is a narrative section.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.GivenParaVisitor
   *    #visitGivenPara(net.sourceforge.czt.z.ast.GivenPara)
   */
  public String visitGivenPara(GivenPara givenPara)
  {
    return "The highlighted term is a given Paragraph - "
        + givenPara.getNames().accept(getTermNameVisitor()) + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.AxParaVisitor
   *    #visitAxPara(net.sourceforge.czt.z.ast.AxPara)
   */
  public String visitAxPara(AxPara axPara)
  {
    return "The highlighted term is an axiomatic paragraph - "
        + axPara.getZSchText().getZDeclList().accept(getTermNameVisitor()) + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConjParaVisitor
   *    #visitConjPara(net.sourceforge.czt.z.ast.ConjPara)
   */
  public String visitConjPara(ConjPara conjPara)
  {
    String result = "The highlighted term is a conjecture paragraph.";
    String name = conjPara.getZNameList().accept(getTermNameVisitor());
    return result + "\nIts name is " + name + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreeParaVisitor
   *    #visitFreePara(net.sourceforge.czt.z.ast.FreePara)
   */
  public String visitFreePara(FreePara freePara)
  {
    String result = "The highlighted term is a free types paragraph.";
    String name = ((ZFreetypeList) freePara.getFreetypeList())
        .accept(getTermNameVisitor());
    return result + "\nIts name is " + name + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OptempParaVisitor
   *    #visitOptempPara(net.sourceforge.czt.z.ast.OptempPara)
   */
  public String visitOptempPara(OptempPara optempPara)
  {
    String result = "The highlighted term is an operator template parargraph.";
    String name = OpTable.getOpNameWithoutStrokes(optempPara.getOper());
    return result + "\nOperators: " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrParaVisitor
   *    #visitNarrPara(net.sourceforge.czt.z.ast.NarrPara)
   */
  public String visitNarrPara(NarrPara narrPara)
  {
    return "The highlighted term is a narrative paragraph.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.UnparsedParaVisitor
   *    #visitUnparsedPara(net.sourceforge.czt.z.ast.UnparsedPara)
   */
  public String visitUnparsedPara(UnparsedPara unparsedPara)
  {
    return "The highlighted paragraph is not parsed";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConstDeclVisitor
   *    #visitConstDecl(net.sourceforge.czt.z.ast.ConstDecl)
   */
  public String visitConstDecl(ConstDecl constDecl)
  {
    String result = "The highlighted term is a ConstDecl";
    String type = constDecl.getExpr().accept(getTermNameVisitor());
    return result + "\nIts type is " + type + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor
   *    #visitVarDecl(net.sourceforge.czt.z.ast.VarDecl)
   */
  public String visitVarDecl(VarDecl varDecl)
  {
    String result = "The highlighted term is a variable declaration.";
    String type = varDecl.getExpr().accept(getTermNameVisitor());
    return result + "\nThe type of the variable(s) is " + type + ".";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor
   *    #visitZDeclList(net.sourceforge.czt.z.ast.ZDeclList)
   */
  public String visitZDeclList(ZDeclList zDeclList)
  {
    return "This highlighted term is a declaration list.";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZNameVisitor
   *    #visitZName(net.sourceforge.czt.z.ast.ZName)
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
   * @see net.sourceforge.czt.z.visitor.ZNameListVisitor
   *    #visitZNameList(net.sourceforge.czt.z.ast.ZNameList)
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

  private static final class LazyPVLoader {
	  private static final PrintVisitor INSTANCE = new PrintVisitor();
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ExprVisitor
   *    #visitExpr(net.sourceforge.czt.z.ast.Expr)
   */
  public String visitExpr(Expr expr)
  {
    String result = "The highlighted term is an expression - "
        + getClassName(expr) + ".";
    TypeAnn typeann = expr.getAnn(TypeAnn.class);
    String type = null;
    if (typeann != null)
      type = typeann.getType().accept(LazyPVLoader.INSTANCE);
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

  /*
   * Return the type of the specified name
   */
  private String getTypeOfZName(ZName zName)
  {
    if (fEditor == null || !(fEditor instanceof ZEditor))
      return null;

    Map<ZName, NameInfo> nameInfoMap = ((ZEditor) fEditor).getParsedData()
        .getNameInfoMap();
    NameInfo info = NameInfoResolver.findInfo(nameInfoMap, zName);
    if (info != null)
      return info.getType();

    return null;
  }

  /*
   * Return the class name of the term
   */
  private String getClassName(Term term)
  {
    if (term == null)
      return null;

    String classname = term.getClass().getSimpleName();

    // Remove the surfix "Impl" from the class name
    if (classname.endsWith("Impl"))
      classname = classname.substring(0, classname.lastIndexOf("Impl"));

    return classname;
  }

  private static TermVisitor<String> getTermNameVisitor()
  {
    return TermLabelVisitorFactory.getTermLabelVisitor();
  }
}
