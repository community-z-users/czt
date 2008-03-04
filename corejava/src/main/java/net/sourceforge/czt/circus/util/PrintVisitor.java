/*
Copyright (C) 2006 Mark Utting
This file is part of the czt project.
The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.
The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.circus.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.circus.ast.BasicChannelSetExpr;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusChannelSet;
import net.sourceforge.czt.circus.ast.CommUsage;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.ast.OutputFieldAnn;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.BasicProcessSignature;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.ProcessUsage;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.ChannelDeclVisitor;

import net.sourceforge.czt.circus.visitor.ChannelSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ChannelTypeVisitor;
import net.sourceforge.czt.circus.visitor.CommunicationTypeVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus.visitor.ProcessTypeVisitor;
import net.sourceforge.czt.circus.visitor.ActionTypeVisitor;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ProcessSignatureVisitor;
import net.sourceforge.czt.circus.visitor.BasicProcessSignatureVisitor;
import net.sourceforge.czt.circus.visitor.ActionSignatureVisitor;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetParaVisitor;
import net.sourceforge.czt.circus.visitor.CircusChannelSetVisitor;
import net.sourceforge.czt.circus.visitor.BasicChannelSetExprVisitor;
import net.sourceforge.czt.circus.visitor.CircusCommunicationListVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus.visitor.CommunicationVisitor;
import net.sourceforge.czt.circus.visitor.InputFieldVisitor;
import net.sourceforge.czt.circus.visitor.DotFieldVisitor;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.DirectiveType;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.DirectiveVisitor;
import net.sourceforge.czt.z.visitor.FalsePredVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NarrSectVisitor;
import net.sourceforge.czt.z.visitor.ParentVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;
import net.sourceforge.czt.z.visitor.TupleExprVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZNameListVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * @author Leo Freitas
 */
public class PrintVisitor
  extends net.sourceforge.czt.z.util.PrintVisitor
  implements
  ChannelTypeVisitor<String>,
  CommunicationTypeVisitor<String>,
  ChannelSetTypeVisitor<String>,
  ProcessTypeVisitor<String>,
  ActionTypeVisitor<String>,
  NameSetTypeVisitor<String>,
  ProcessSignatureVisitor<String>,
  BasicProcessSignatureVisitor<String>,
  ActionSignatureVisitor<String>,
  BasicProcessVisitor<String>,
  ProcessParaVisitor<String>,
  ActionParaVisitor<String>,
  ZParaListVisitor<String>,
  ZSectVisitor<String>,
  ParentVisitor<String>,
  AxParaVisitor<String>,
  VarDeclVisitor<String>,
  TruePredVisitor<String>,
  FalsePredVisitor<String>,
  RefExprVisitor<String>,
  TupleExprVisitor<String>,
  ApplExprVisitor<String>,
  SetExprVisitor<String>,
  MemPredVisitor<String>,
  AndPredVisitor<String>,
  LatexMarkupParaVisitor<String>,
  NarrParaVisitor<String>,
  NarrSectVisitor<String>,
  DirectiveVisitor<String>,
  ChannelParaVisitor<String>,
  ZDeclListVisitor<String>,
  ChannelSetParaVisitor<String>,
  CircusChannelSetVisitor<String>,
  BasicChannelSetExprVisitor<String>,
  CommunicationVisitor<String>,
  InputFieldVisitor<String>,
  DotFieldVisitor<String>,
  ChannelDeclVisitor<String>,
  ZNameListVisitor<String>,
  SchExprActionVisitor<String>,
  SpecVisitor<String>,
  CallActionVisitor<String>,
  CircusCommunicationListVisitor<String>
{

  private int tabCount = 0;

  public String stringOfChar(char c, int count)
  {
    StringBuilder sb = new StringBuilder("");
    while (count > 0)
    {
      sb.append(c);
      count--;
    }
    return sb.toString();
  }

  private String NLAndTabs()
  {
    return "\n" + stringOfChar('\t', tabCount);
  }

  private void addNLAndTabs(StringBuilder builder)
  {
    builder.append(NLAndTabs());
  }

  private void openTabScope(StringBuilder builder)
  {
    tabCount++;
    addNLAndTabs(builder);
  }

  private void closeTabScope(StringBuilder builder)
  {
    tabCount--;
    addNLAndTabs(builder);
  }

  public String visitSpec(Spec term)
  {
    StringBuilder result = new StringBuilder("SPEC-" + term.getVersion());
    result.append("{#");
    openTabScope(result);
    int i = term.getSect().size() - 1;
    for (Sect s : term.getSect())
    {
      result.append(visit(s));
      if (i > 0)
      {
        addNLAndTabs(result);
      }
      i--;
    }
    closeTabScope(result);
    result.append("#}");
    addNLAndTabs(result);
    return result.toString();
  }

  public String visitZSect(ZSect term)
  {
    StringBuilder result = new StringBuilder("SECTION[" + term.getName());
    result.append(visitList(term.getParent(), " parents ", ", ", ""));
    result.append("]{");
    openTabScope(result);
    result.append(visit(term.getZParaList()));
    closeTabScope(result);
    result.append("}");
    addNLAndTabs(result);
    return result.toString();
  }

  protected String visitNarrText(String header, List text)
  {
    int size = text.size();
    StringBuilder result = new StringBuilder(header + "(" + size + ")={");
    if (size > 0)
    {
      String s = text.get(0).toString();
      s = s.replaceAll("\n", "NL");
      result.append(s.substring(0, Math.min(50, s.length())));
    }
    result.append("...}");
    return result.toString();
  }

  public String visitNarrPara(NarrPara term)
  {
    return visitNarrText("NarrPara", term.getContent());
  }

  public String visitNarrSect(NarrSect term)
  {
    return visitNarrText("NarrSect", term.getContent());
  }

  public String visitLatexMarkupPara(LatexMarkupPara term)
  {
    StringBuilder result = new StringBuilder("LaTeXMarkUpPara(");
    result.append(term.getDirective().size());
    result.append(")[");
    for (Directive directive : term.getDirective())
    {
      result.append(visit(directive));
    }
    result.append("]");
    return result.toString();
  }

  public String visitDirective(Directive term)
  {
    StringBuffer result = new StringBuffer("%%Z");
    if (!term.getType().equals(DirectiveType.NONE))
    {
      result.append(term.getType().toString().toLowerCase());
    }
    result.append(term.getUnicode().length() == 1 || term.getUnicode().
      startsWith("U+") ? "char" : "word");
    result.append(" ");
    result.append(term.getCommand());
    result.append(" ");
    ZUtils.unicodeToAscii(term.getUnicode(), result);
    return result.toString();
  }

  public String visitZParaList(ZParaList term)
  {
    // Avoided visitList as this list may contain lists, and
    // visitList for this case seems to not behave alright,
    // despite it seems to consider lists within lists.
    StringBuilder result = new StringBuilder("ZParaList(");
    result.append(term.size());
    result.append(")[");
    openTabScope(result);
    int i = term.size() - 1;
    int j = 1;
    for (Para p : term)
    {
      if (p == null)
      {
        result.append("FOUND NULL @ " + j + "  ");
      }
      result.append(j);
      result.append("::");
      result.append(visit(p));
      if (i > 0)
      {
        addNLAndTabs(result);
      }
      i--;
      j++;
    }
    closeTabScope(result);
    result.append("]");
    addNLAndTabs(result);
    return result.toString();
//    int j = 0;
//    for(Para p: term) {
//      System.out.println("j = " + j + " ; " + p != null ? p.getClass().getName() : "null");
//      j++;
//    }
//    return "";
  }

  public String visitZDeclList(ZDeclList term)
  {
    StringBuilder result = new StringBuilder("ZDeclList(");
    result.append(term.size());
    result.append(")[");
    openTabScope(result);
    int i = term.size() - 1;
    int j = 0;
    for (Decl d : term)
    {
      if (d == null)
      {
        result.append("FOUND NULL @ " + j + "  ");
      }
      result.append(visit(d));
      if (i > 0)
      {
        addNLAndTabs(result);
      }
      i--;
      j++;
    }
    closeTabScope(result);
    result.append("]");
    addNLAndTabs(result);
    return result.toString();
  }

  public String visitZNameList(ZNameList term)
  {
    return super.visitZNameList(term);
  /*
  StringBuilder result = new StringBuilder("ZNameList(");
  result.append(term.size());
  result.append(")[");
  openTabScope(result);
  int i = term.size() - 1; int j = 0;
  for(Name n : term) {
  if (n == null) result.append("FOUND NULL @ " + j + "  ");
  result.append(visit(n));
  if (i > 0) {        
  addNLAndTabs(result);
  }
  i--; j++;
  }
  closeTabScope(result);
  result.append("]");
  addNLAndTabs(result);
  return result.toString();          
   */
  }

  public String visitChannelDecl(ChannelDecl term)
  {
    StringBuilder result = new StringBuilder("ChannelDecl[");
    result.append(visitList(term.getZGenFormals(), "[", ", ", "]"));
    openTabScope(result);
    result.append(visitList(term.getZChannelNameList(), ", "));
    result.append(" : ");
    result.append(visit(term.getExpr()));
    closeTabScope(result);
    result.append("]");
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitChannelPara(ChannelPara term)
  {
    StringBuilder result = new StringBuilder("ChannelPara[");
    openTabScope(result);
    result.append(visit(term.getZDeclList()));
    closeTabScope(result);
    result.append("]");
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitChannelSetPara(ChannelSetPara term)
  {
    StringBuilder result = new StringBuilder("ChannelSetPara[");
    openTabScope(result);
    result.append(visit(term.getZName()));
    result.append(visit(term.getZGenFormals()));
    result.append(" == ");
    result.append(visit(term.getChannelSet()));
    closeTabScope(result);
    result.append("]");
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitCircusChannelSet(CircusChannelSet term)
  {
    return visit(term.getExpr());
  }

  public String visitBasicChannelSetExpr(BasicChannelSetExpr term)
  {
    return visitList(term.getCircusCommunicationList(), "{ ", ", ", " }");
  }

  public String visitVarDecl(VarDecl term)
  {
    StringBuilder result = new StringBuilder("VarDecl[");
    result.append(visitList(term.getZNameList(), "", ", ", ": "));
    result.append(visit(term.getExpr()));
    result.append("]");
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitRefExpr(RefExpr term)
  {
    boolean hasMixfix = term.getMixfix();
    StringBuilder result = new StringBuilder(hasMixfix ? "RefExpr(" : "");      
    result.append(visit(term.getName()));
    result.append(visitList(term.getZExprList(), "[", ", ", "]"));    
    result.append(term.getExplicit() ? "_E_" : "");
    result.append(hasMixfix ? ")" : "");
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitTupleExpr(TupleExpr term)
  {
    return visitList(term.getZExprList(), "TupleExpr(", ", ", ")");
  }

  public String visitApplExpr(ApplExpr term)
  {
    StringBuilder result = new StringBuilder("ApplExpr{LHS=");
    result.append(visit(term.getLeftExpr()));
    result.append(",\n RHS=");
    result.append(visit(term.getRightExpr()));
    result.append(",\n MF=" + term.getMixfix());
    result.append("}");
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitSetExpr(SetExpr term)
  {
    return visitList(term.getZExprList(), "SetExpr(", ", ", ")");
  }

  public String visitAndPred(AndPred term)
  {
    StringBuilder result = new StringBuilder("AndPred{LHS=");
    result.append(visit(term.getLeftPred()));
    result.append(",");
    addNLAndTabs(result);
    result.append("RHS=");
    result.append(visit(term.getRightPred()));
    result.append(",");
    addNLAndTabs(result);
    result.append("AND=" + term.getAnd());
    result.append("}");
    addNLAndTabs(result);
    return result.toString();
  }

  public String visitMemPred(MemPred term)
  {
    StringBuilder result = new StringBuilder("MemPred{LHS=");
    result.append(visit(term.getLeftExpr()));
    result.append(",");
    addNLAndTabs(result);
    result.append("RHS=");
    result.append(visit(term.getRightExpr()));
    result.append(",");
    addNLAndTabs(result);
    result.append("MF=" + term.getMixfix());
    result.append("}");
    addNLAndTabs(result);
    return result.toString();
  }

  public String visitTruePred(TruePred term)
  {
    return "true";
  }

  public String visitFalsePred(FalsePred term)
  {
    return "false";
  }

  public String visitParent(Parent term)
  {
    return term.getWord();
  }

  /** Schema or generic schema definition (vertical).
   *      AxPara.Box          = SchBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = ConstDecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = SchemaName
   *      ConstDecl.expr      = SchExpr
   *
   * Axiomatic or generic definitions
   *      AxPara.Box          = AxBox
   *      AxPara.decl         = generics
   *
   *      AxPara.SchText.decl = declared variables
   *      AxPara.SchText.pred = axiomatic predicate
   *
   * Horizontal definition
   *      AxPara.Box          = OmitBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = Constdecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = HorizDefName (either SchName or AbbrvName)
   *      ConstDecl.expr      = HorizDefExpr (either SchExpr or Other)
   */
  public String visitAxPara(AxPara term)
  {
    StringBuilder result = new StringBuilder();
    if (ZUtils.isSchema(term))
    {
      result.append("Schema");
      result.append(visitList(ZUtils.getAxParaZGenFormals(term), "[", ", ", "]"));
      result.append("{");
      result.append(visit(ZUtils.getSchemaName(term)));
      result.append("}=");
      result.append(visit(ZUtils.getSchemaDefExpr(term)));
    }
    else if (ZUtils.isHorizontalDef(term))
    {
      result.append("Abbreviation");
      result.append(visitList(ZUtils.getAxParaZGenFormals(term), "[", ", ", "]"));
      result.append("{");
      result.append(visit(ZUtils.getAbbreviationName(term)));
      result.append(" == ");
      result.append(visit(ZUtils.getAbbreviationExpr(term)));
      result.append("}");
    }
    else
    {
      result.append("AxBox");
      result.append(visitList(ZUtils.getAxParaZGenFormals(term), "[", ", ", "]"));
      result.append("{");
      result.append(visitList(ZUtils.getAxBoxDecls(term), ";"));
      result.append(" | ");
      result.append(visit(ZUtils.getAxBoxPred(term)));
      result.append("}");
    }
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitChannelType(ChannelType term)
  {
    return "CHANNEL_TYPE " + visit(term.getType());
  }

  public String visitCommunicationType(CommunicationType term)
  {
    return "COMM_TYPE " + visit(term.getSignature());
  }

  public String visitChannelSetType(ChannelSetType term)
  {
    return "CHANSET_TYPE " + visit(term.getSignature());
  }

  public String visitProcessType(ProcessType term)
  {
    return "PROCESS_TYPE [" + NLAndTabs() + visit(term.getProcessSignature()) + NLAndTabs() + "]";
  }

  public String visitActionType(ActionType term)
  {
    return "ACTION_TYPE [" + NLAndTabs() + visit(term.getActionSignature()) + NLAndTabs() + "]";
  }

  public String visitNameSetType(NameSetType term)
  {
    return "NAMESET_TYPE " + visit(term.getSignature());
  }

  public String visitProcessSignature(ProcessSignature term)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(term.getProcessName()));
    result.append(visitList(ZUtils.assertZNameList(term.getGenFormals()), "[",
      ",", "]"));

    // Print parameters or indexes signature if they exist
    if (term.getFormalParamsOrIndexes() != null && !term.getFormalParamsOrIndexes().
      getNameTypePair().isEmpty())
    {
      result.append(term.getUsage().equals(ProcessUsage.Parameterised) ? "_P(" : "_I(");
      result.append(visit(term.getFormalParamsOrIndexes()));
      result.append(")");
    }

    openTabScope(result);
    result.append("Used channels: ");
    openTabScope(result);    
    result.append(visitListNL(term.getUsedCommunications(), ","));
    closeTabScope(result);
    closeTabScope(result);

    return result.toString();
  }

  public String visitBasicProcessSignature(BasicProcessSignature term)
  {
    StringBuilder result = new StringBuilder();

    String baseClass = visitProcessSignature(term);
    result.append(baseClass);

    openTabScope(result);
    result.append("State signature...:");
    addNLAndTabs(result);
    result.append(visit(term.getStateSignature()));
    addNLAndTabs(result);

    result.append("Used name sets....:");
    addNLAndTabs(result);
    result.append(visit(term.getUsedNameSets()));
    addNLAndTabs(result);

    result.append("Decl. Transformers:");
    result.append(visitList(term.getTransformerParaName(), ","));
    addNLAndTabs(result);

    result.append("Local Z signatures:");
    openTabScope(result);
    result.append(visitListNL(term.getLocalZSignatures(), ","));
    closeTabScope(result);

    result.append("Action signatures:");
    openTabScope(result);
    result.append(visitListNL(term.getActionSignatures(), ","));
    closeTabScope(result);
    closeTabScope(result);

    return result.toString();
  }

  public String visitActionSignature(ActionSignature term)
  {
    StringBuilder result = new StringBuilder("{ ");
    result.append(term.getActionName());
    if (term.getFormalParams() != null)
    {
      result.append("P(");
      result.append(visit(term.getFormalParams()));//Signature
      result.append(")");
    }
    if (term.getLocalVars() != null)
    {
      result.append(" | V[");
      result.append(visit(term.getLocalVars()));//Signature
      result.append("]");
    }
    if (term.getUsedCommunications() != null)
    {
      result.append(" @ C[");
      result.append(visit(term.getUsedCommunications()));
      result.append("]");
    }
    result.append(" }");
    return result.toString();
  }

  public String visitProcessPara(ProcessPara term)
  {
    StringBuilder result = new StringBuilder("ProcessPara(" + visit(term.getName()) + ")");
    result.append(visitList(ZUtils.assertZNameList(term.getGenFormals()), "[",
      ",", "]"));
    result.append(" == ");
    result.append(visit(term.getCircusProcess()));
    return result.toString();
  }

  public String visitActionPara(ActionPara term)
  {
    StringBuilder result = new StringBuilder("ActionPara(" + visit(term.getName()) + ")");
    result.append(" == ");
    result.append(visit(term.getCircusAction()));
    return result.toString();
  }

  public String visitSchExprAction(SchExprAction term)
  {
    return visit(term.getExpr());
  }

  public String visitBasicProcess(BasicProcess term)
  {
    StringBuilder result = new StringBuilder("BasicProcess(hC=");
    result.append(term.hashCode());
    result.append(")[");
    openTabScope(result);
    /*
    result.append("StatePara=");
    result.append(visit(term.getStatePara()));
    int paraCnt = term.getLocalPara().size();
    addNLAndTabs(result);
    result.append("LocalPara(" + paraCnt + ")");
    result.append(visitList(term.getLocalPara(), "\n"));
    int ontheflyCnt = term.getOnTheFlyPara().size();
    addNLAndTabs(result);
    result.append("OnTheFlyPara(" + ontheflyCnt + ")");
    result.append(visitList(term.getOnTheFlyPara(), "\n"));
    addNLAndTabs(result);
    result.append("MainAction=");
    result.append(visit(term.getMainAction()));
    addNLAndTabs(result);
    result.append("\tTotal paras=" + (paraCnt+ontheflyCnt));
     */
    result.append(visit(term.getZParaList()));
    addNLAndTabs(result);
    result.append("\tTotal paras=" + (term.getZParaList().size()));
    closeTabScope(result);
    result.append("]");
    //addNLAndTabs(result);
    return result.toString();
  }

  public String visitCircusCommunicationList(CircusCommunicationList term)
  {
    return visitList(term, ", ");
  }

  public String visitCommunication(Communication term)
  {
    StringBuilder result = new StringBuilder();
    
    Boolean explicit = term.getChannelExpr().getExplicit();
    if (term.getCommUsage().equals(CommUsage.Generic) && 
        explicit != null && !explicit)
    {
      result.append("G_");
    }
    if (term.getIndexed())
    {
      result.append("I_");
    }
    result.append(visit(term.getChannelExpr()));
    result.append(visitList(term.getCircusFieldList(), ""));    
    return result.toString();
  }

  public String visitInputField(InputField term)
  {
    return "?" + term.getVariableZName() +
      (term.getRestriction() instanceof TruePred ? "" : " : " +
      visit(term.getRestriction()));
  }

  public String visitDotField(DotField term)
  {
    boolean isOutputField = term.getAnn(OutputFieldAnn.class) != null;
    return (isOutputField ? "!" : ".") + visit(term.getExpr());
  }

  public String visitCallAction(CallAction term)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(term.getName()));
    result.append(visitList(term.getZExprList(), "(", ", ", ")"));
    return result.toString();
  }
  private static FindProcessPara findPP_ = new FindProcessPara();

  public String printProcessPara(Term term)
  {
    StringBuilder result = new StringBuilder();
    List<ProcessPara> pps = findPP_.collectProcessParaFrom(term);
    result.append("----------------------------------------\n");
    result.append("Found " + pps.size() + " process paras  \n");
    result.append("----------------------------------------");
    for (ProcessPara pp : pps)
    {
      result.append("\n");
      result.append(visit(pp));

    }
    result.append("\n----------------------------------------\n");
    return result.toString();
  }

  static class FindProcessPara implements
    TermVisitor<Object>,
    ProcessParaVisitor<Object>
  {

    List<ProcessPara> processPara_ = new ArrayList<ProcessPara>();

    public Object visitProcessPara(ProcessPara term)
    {
      processPara_.add(term);
      return term;
    }

    public Object visitTerm(Term term)
    {
      VisitorUtils.visitTerm(this, term);
      return term;
    }

    List<ProcessPara> collectProcessParaFrom(Term term)
    {
      assert term != null : "Invalid (null) term";
      processPara_.clear();
      term.accept(this);
      return Collections.unmodifiableList(processPara_);
    }
  }

  protected String visitListNL(List<? extends Term> list, String separator)
  {
    final StringBuilder result = new StringBuilder();
    String sep = "";
    for (Term term : list)
    {
      String string = visit(term);
      if (string != null)
      {
        result.append(sep + string);
        sep = separator;
        addNLAndTabs(result);
      }
    }
    return result.toString();
  }
}
