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
import net.sourceforge.czt.z.ast.TupleSelExpr;
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
      RefExprVisitor<String>,
      PowerExprVisitor<String>,
      DecorExprVisitor<String>,
      SchExprVisitor<String>,
      SetExprVisitor<String>,
      TupleExprVisitor<String>,
      TupleSelExprVisitor<String>,
      ApplExprVisitor<String>,
      AndExprVisitor<String>,
      OrExprVisitor<String>,
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
    return "Highlight - " + term.accept(getTermNameVisitor_);
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZSectVisitor#visitZSect(net.sourceforge.czt.z.ast.ZSect)
   */
  public String visitZSect(ZSect zSect)
  {
    return "Highlight - Z Section" + "\nNAME ---> " + zSect.getName();
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrSectVisitor#visitNarrSect(net.sourceforge.czt.z.ast.NarrSect)
   */
  public String visitNarrSect(NarrSect narrPara)
  {
    return "Highlight - Narrative Section";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.GivenParaVisitor#visitGivenPara(net.sourceforge.czt.z.ast.GivenPara)
   */
  public String visitGivenPara(GivenPara givenPara)
  {
    String result = "Highlight - Given Paragraph";
    String name = givenPara.getNames().accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.AxParaVisitor#visitAxPara(net.sourceforge.czt.z.ast.AxPara)
   */
  public String visitAxPara(AxPara axPara)
  {
    String result = "Highlight - Axiomatic Paragraph";
    String name = axPara.getZSchText().getZDeclList().accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConjParaVisitor#visitConjPara(net.sourceforge.czt.z.ast.ConjPara)
   */
  public String visitConjPara(ConjPara conjPara)
  {
    String result = "Highlight - Conjecture Paragraph";
    String name = conjPara.getZNameList().accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreeParaVisitor#visitFreePara(net.sourceforge.czt.z.ast.FreePara)
   */
  public String visitFreePara(FreePara freePara)
  {
    String result = "Highlight - Free Types Paragraph";
    String name = ((ZFreetypeList)freePara.getFreetypeList()).accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OptempParaVisitor#visitOptempPara(net.sourceforge.czt.z.ast.OptempPara)
   */
  public String visitOptempPara(OptempPara optempPara)
  {
    String result = "Highlight - Operator Template Parargraph";
    String name = OpTable.getOpNameWithoutStrokes(optempPara.getOper());
    return result + "\nOP ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.NarrParaVisitor#visitNarrPara(net.sourceforge.czt.z.ast.NarrPara)
   */
  public String visitNarrPara(NarrPara narrPara)
  {
    return "Highlight - Narrative Paragraph";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.UnparsedParaVisitor#visitUnparsedPara(net.sourceforge.czt.z.ast.UnparsedPara)
   */
  public String visitUnparsedPara(UnparsedPara unparsedPara)
  {
    return "Highlight - Unparsed Paragraph";
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ConstDeclVisitor#visitConstDecl(net.sourceforge.czt.z.ast.ConstDecl)
   */
  public String visitConstDecl(ConstDecl constDecl)
  {
    String result = "Highlight - ConstDecl";
    String name = constDecl.getZName().accept(getTermNameVisitor_);
    String type = constDecl.getExpr().accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name + "\nTYPE ---> " + type;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor#visitVarDecl(net.sourceforge.czt.z.ast.VarDecl)
   */
  public String visitVarDecl(VarDecl varDecl)
  {
    String result = "Highlight - VarDecl";
    ZNameList declNameList = varDecl.getName();
    String name = declNameList.accept(getTermNameVisitor_);
    String type = varDecl.getExpr().accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name + "\nTYPE ---> " + type;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.VarDeclVisitor#visitZDeclList(net.sourceforge.czt.z.ast.ZDeclList)
   */
  public String visitZDeclList(ZDeclList zDeclList)
  {
    String result = "Highlight - ZDeclList";
    String name = zDeclList.accept(getTermNameVisitor_);

    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZNameVisitor#visitZName(net.sourceforge.czt.z.ast.ZName)
   */
  public String visitZName(ZName zName)
  {
    String result = "Highlight - ZName";
    result = result.concat("\nNAME ---> " + zName.accept(new PrintVisitor()));
    String type = getTypeOfZName(zName);
    if(type != null)
      result = result.concat("\nTYPE ---> " + type);
    
    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ZNameListVisitor#visitZNameList(net.sourceforge.czt.z.ast.ZNameList)
   */
  public String visitZNameList(ZNameList zNameList)
  {
    if (zNameList.size() == 0)
      return null;
    
    String result = "Highlight - ZNameList";
    String name = zNameList.get(0).accept(new PrintVisitor());
    
    if (zNameList.size() > 1) {
      for (int i = 1; i < zNameList.size(); i++)
        name = name.concat(", " + zNameList.get(i).accept(new PrintVisitor()));
      name = "[" + name + "]";
    }
    result = result.concat("\nNAME ---> " + name);
    
    String type = getTypeOfZName((ZName)zNameList.get(0));
    if (type != null)
      result = result.concat("\nTYPE ---> " + type);
    
    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.RefExprVisitor#visitRefExpr(net.sourceforge.czt.z.ast.RefExpr)
   */
  public String visitRefExpr(RefExpr refExpr)
  {
    String result = "Highlight - RefExpr";
    ZName name = refExpr.getZName();
    result = result.concat("\nNAME ---> " + name.accept(new PrintVisitor()));
    String type = getTypeOfZName(name);
    if(type != null)
      result = result.concat("\nTYPE ---> " + type);
    
    return result;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.PowerExprVisitor#visitPowerExpr(net.sourceforge.czt.z.ast.PowerExpr)
   */
  public String visitPowerExpr(PowerExpr powerExpr)
  {
    String result = "Highlight - PowerExpr";
    String name = powerExpr.getExpr().accept(getTermNameVisitor_);
    return result + "\nExpr ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.DecorExprVisitor#visitDecorExpr(net.sourceforge.czt.z.ast.DecorExpr)
   */
  public String visitDecorExpr(DecorExpr decorExpr)
  {
    String result = "Highlight - DecorExpr";
    String name = decorExpr.getExpr().accept(getTermNameVisitor_);
    return result + "\nExpr ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.SchExprVisitor#visitSchExpr(net.sourceforge.czt.z.ast.SchExpr)
   */
  public String visitSchExpr(SchExpr schExpr)
  {
    String result = "Highlight - SchExpr";
    String name = schExpr.getZSchText().getPred().accept(getTermNameVisitor_);
    return result + "\nPredicate ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.SetExprVisitor#visitSetExpr(net.sourceforge.czt.z.ast.SetExpr)
   */
  public String visitSetExpr(SetExpr setExpr)
  {
    String result = "Highlight - SetExpr";
    String name = setExpr.accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.TupleExprVisitor#visitTupleExpr(net.sourceforge.czt.z.ast.TupleExpr)
   */
  public String visitTupleExpr(TupleExpr tupleExpr)
  {
    String result = "Highlight - TupleExpr";
    String name = tupleExpr.accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.TupleSelExprVisitor#visitTupleSelExpr(net.sourceforge.czt.z.ast.TupleSelExpr)
   */
  public String visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    String result = "Highlight - TupleSelExpr";
    String name = tupleSelExpr.getExpr().accept(getTermNameVisitor_);
    return result + "\nExpr ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.ApplExprVisitor#visitApplExpr(net.sourceforge.czt.z.ast.ApplExpr)
   */
  public String visitApplExpr(ApplExpr applExpr)
  {
    String result = "Highlight - ApplExpr";
    String name = applExpr.accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.AndExprVisitor#visitAndExpr(net.sourceforge.czt.z.ast.AndExpr)
   */
  public String visitAndExpr(AndExpr andExpr)
  {
    String result = "Highlight - AndExpr";
    String name = andExpr.accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.OrExprVisitor#visitOrExpr(net.sourceforge.czt.z.ast.OrExpr)
   */
  public String visitOrExpr(OrExpr orExpr)
  {
    String result = "Highlight - OrExpr";
    String name = orExpr.accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
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
    String result = "Highlight - GivenType";
    String name = givenType.accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreetypeListVisitor#visitFreetypeList(net.sourceforge.czt.z.ast.FreetypeList)
   */
  public String visitZFreetypeList(ZFreetypeList zFreetypeList)
  {
    String result = "Highlight - ZFreetypeList";
    String name = zFreetypeList.accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }

  /**
   * @see net.sourceforge.czt.z.visitor.FreetypeVisitor#visitFreetype(net.sourceforge.czt.z.ast.Freetype)
   */
  public String visitFreetype(Freetype freetype)
  {
    String result = "Highlight - Freetype";
    String name = freetype.getZName().accept(getTermNameVisitor_);
    return result + "\nNAME ---> " + name;
  }
  
  private String getTypeOfZName(ZName zName) {
    if (fEditor == null || !(fEditor instanceof ZEditor))
      return null;
    
    List<NameInfo> nameInfoList = ((ZEditor) fEditor).getParsedData().getNameInfoList();
    NameInfo info = NameInfoResolver.findInfo(nameInfoList, zName);
    if (info != null)
      return info.getType();
    
    return null;
  }
}
