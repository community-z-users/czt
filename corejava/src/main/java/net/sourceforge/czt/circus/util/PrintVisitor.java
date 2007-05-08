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
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessKind;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.BasicProcessSignature;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.ChannelDeclVisitor;

import net.sourceforge.czt.circus.visitor.ChannelTypeVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetTypeVisitor;
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
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.DirectiveType;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.RefExpr;
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
    implements ChannelTypeVisitor<String>,
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
    DirectiveVisitor<String>,
    ChannelParaVisitor<String>,
    ZDeclListVisitor<String>,
    ChannelSetParaVisitor<String>,
    ChannelDeclVisitor<String>,
    ZNameListVisitor<String>,
    SchExprActionVisitor<String>,
    SpecVisitor<String>
{
    
    public String visitSpec(Spec term) {
        StringBuilder result = new StringBuilder("SPEC-" + term.getVersion());
        result.append("{#\n");
        result.append(visitList(term.getSect(), "\n"));
        result.append("#}\n");
        return result.toString();
    }
        
    public String visitZSect(ZSect term) {
        StringBuilder result = new StringBuilder("SECTION[" + term.getName());
        result.append(visitList(term.getParent(), " parents ", ", ", ""));
        result.append(")]{\n");
        result.append(visit(term.getZParaList()));
        result.append("\n}\n");
        return result.toString();
    }    
    
    public String visitNarrPara(NarrPara term) {
        return "NarrPara(" + term.getContent().size() + " in size)";
    }
    
    public String visitLatexMarkupPara(LatexMarkupPara term) {
        return visitList(term.getDirective(), "LatexMarkupPara[", ",\n", "]");
    }
    
    public String visitDirective(Directive term) {
        StringBuffer result = new StringBuffer("%%Z");
        if (!term.getType().equals(DirectiveType.NONE)) {
            result.append(term.getType().toString().toLowerCase());
        }        
        result.append(term.getUnicode().length() == 1 || term.getUnicode().startsWith("U+") ? "char" : "word");
        result.append(" ");
        result.append(term.getCommand());
        result.append(" ");
        unicodeToAscii(term.getUnicode(), result);
        return result.toString();
    }
    
    public String visitZParaList(ZParaList term) {
        return visitList(term, "ZParaList[\n", ",\n"  , "\n]");
    }    
    
    public String visitZDeclList(ZDeclList term) {
        return visitList(term, "ZDeclList[", ",\n" , "\n]");
    }
    
    public String visitZNameList(ZNameList term) {
        return visitList(term, "ZNameList[", ", " , "]");
    }
    
    
    public String visitChannelDecl(ChannelDecl term) {
        StringBuffer result = new StringBuffer("ChannelDecl[\n");
        result.append(visitList(term.getZGenFormals(), "[" , ", ", "]"));        
        result.append(visitList(term.getZNameList(), ", "));
        result.append(" : ");
        result.append(visit(term.getExpr()));
        return result.toString();            
    }
    
    public String visitChannelPara(ChannelPara term) {
        return visitList(term.getZDeclList(), "ChannelPara[\n", ";\n", "]");
    }
    
    public String visitChannelSetPara(ChannelSetPara term) {
        StringBuffer result = new StringBuffer("ChannelSetPara[\n");
        result.append(visit(term.getZName()));        
        result.append(visit(term.getZGenFormals()));
        result.append(" == ");
        result.append(visit(term.getChannelSet()));
        return result.toString();        
    }
    
    public String visitVarDecl(VarDecl term) {
        StringBuffer result = new StringBuffer("VarDecl[");
        result.append(visitList(term.getZNameList(), "", ", ", ": "));
        result.append(visit(term.getExpr()));
        result.append("]\n");
        return result.toString();
    }
    
    public String visitRefExpr(RefExpr term) {
        StringBuffer result = new StringBuffer("RefExpr{");
        result.append(visit(term.getName()));
        result.append(visitList(term.getZExprList(), "[", ", ", "]"));
        result.append(", MF=" +term.getMixfix());
        result.append(", EX=" +term.getExplicit());
        result.append("}\n");
        return result.toString();
    }
    
    public String visitTupleExpr(TupleExpr term) {
        return visitList(term.getZExprList(), "TupleExpr(", ", ", ")\n");
    }
    
    public String visitApplExpr(ApplExpr term) {
        StringBuffer result = new StringBuffer("ApplExpr{LHS=");
        result.append(visit(term.getLeftExpr()));
        result.append(",\n RHS=");
        result.append(visit(term.getRightExpr()));
        result.append(",\n MF=" +term.getMixfix());
        result.append("}\n");
        return result.toString();
    }
    
    public String visitSetExpr(SetExpr term) {
        return visitList(term.getZExprList(), "SetExpr(", ", ", ")");
    }
    
    public String visitAndPred(AndPred term) {
        StringBuffer result = new StringBuffer("AndPred{LHS=");
        result.append(visit(term.getLeftPred()));
        result.append(",\n RHS=");
        result.append(visit(term.getRightPred()));
        result.append(",\n AND=" +term.getAnd());
        result.append("}\n");
        return result.toString();        
    }
    
    public String visitMemPred(MemPred term) {
        StringBuffer result = new StringBuffer("MemPred{LHS=");
        result.append(visit(term.getLeftExpr()));
        result.append(",\n RHS=");
        result.append(visit(term.getRightExpr()));
        result.append(",\n MF=" +term.getMixfix());
        result.append("}\n");
        return result.toString();
    }
    
    public String visitTruePred(TruePred term) {
        return "true";
    }
    
    public String visitFalsePred(FalsePred term) {
        return "false";
    }
    
    public String visitParent(Parent term) {
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
    public String visitAxPara(AxPara term) {
       StringBuffer result = new StringBuffer(); 
       if (ZUtils.isSchema(term)) {
           result.append("Schema");
           result.append(visitList(ZUtils.getAxParaZGenFormals(term), "[", ", ", "]"));
           result.append("{\n");
           result.append(visit(ZUtils.getSchemaName(term)));
           result.append("}=");
           result.append(visit(ZUtils.getSchemaDefExpr(term)));
       } else if (ZUtils.isHorizontalDef(term)) {           
           result.append("Abbreviation");
           result.append(visitList(ZUtils.getAxParaZGenFormals(term), "[", ", ", "]"));
           result.append("{");
           result.append(visit(ZUtils.getAbbreviationName(term)));
           result.append(" == ");
           result.append(visit(ZUtils.getAbbreviationExpr(term)));
           result.append("\n}");
       } else {
           result.append("AxBox");
           result.append(visitList(ZUtils.getAxParaZGenFormals(term), "[", ", ", "]"));
           result.append("{");
           result.append(visitList(ZUtils.getAxBoxDecls(term), ";\n "));
           result.append(" | ");
           result.append(visit(ZUtils.getAxBoxPred(term)));
           result.append("\n}");
       }
       result.append("\n");
       return result.toString();
    }
    
    public String visitChannelType(ChannelType term) {
        StringBuffer result =  new StringBuffer("CHANNEL_TYPE ");
        result.append(visitList(ZUtils.assertZNameList(term.getGenFormals()), "[", ", ", "]"));
        if (term.getResolvedType() != null)
            result.append(visit(term.getResolvedType()));
        else if (term.getDeclaredType() != null)
            result.append(visit(term.getDeclaredType()));
        else
            result.append(" SYNCH");//TODO:Check this
        return result.toString();
    }
    
    public String visitChannelSetType(ChannelSetType term) {
        return "CHANSET_TYPE [" + visit(term.getSignature()) + "]";
    }
    
    public String visitProcessType(ProcessType term) {
        return "PROCESS_TYPE [" + visit(term.getProcessSignature()) + "]";
    }
    
    public String visitActionType(ActionType term) {
        return "ACTION_TYPE [" + visit(term.getActionSignature()) + "]";
    }
    
    public String visitNameSetType(NameSetType term) {
        return "NAMESET_TYPE [" + visit(term.getSignature()) + "]";
    }
    
    public String visitProcessSignature(ProcessSignature term) {
        return visitProcess(term);
    }
    
    public String visitBasicProcessSignature(BasicProcessSignature term) {
        StringBuffer result = new StringBuffer(visitProcess(term));
        if (term.getStateType() != null) {
            result.append(visit(term.getStateType()));//SchemaType
        }
        final String sep = "\n\t";
        result.append(visitList(term.getZSignature(), "ZDeclSig : ["+ sep, sep, "]\n"));//List<Signature>
        result.append(visitList(term.getActionSignature(), "ActionSig: ["+ sep, sep, "]\n"));//List<Signature>
        result.append(visitList(term.getNameSet(), "NameSet  : [", ", ", "]\n"));//ZNameList
        return result.toString();
    }
    
    public String visitActionSignature(ActionSignature term) {
        StringBuffer result = new StringBuffer("{ ");
        result.append(term.getActionName());
        if (term.getFormalParams() != null) {
            result.append("P(");
            result.append(visit(term.getFormalParams()));//Signature
            result.append(")");
        }
        if (term.getLocalVars() != null) {
            result.append(" | V[");
            result.append(visit(term.getLocalVars()));//Signature
            result.append("]");
        }
        if (!term.getUsedChannels().getNameTypePair().isEmpty()) {
            result.append(" @ C[");
            result.append(visit(term.getUsedChannels()));
            result.append("]");
        }
        result.append(" }");
        return result.toString();
    }
    
    protected String visitProcess(ProcessSignature term) {
        StringBuffer result = new StringBuffer("Process: ");
        result.append(visit(term.getProcessName()));
        result.append(visitList(ZUtils.assertZNameList(term.getGenFormals()), "[", ",", "]"));
        // Print parameters or indexes signature if they exist
        if (term.getParamOrIndexes() != null && !term.getParamOrIndexes().getNameTypePair().isEmpty()) {
            result.append(term.getKind().equals(ProcessKind.Parameterised) ? "P [" : "I [");
            result.append(visit(term.getParamOrIndexes()));
            result.append("]");
        }
        return result.toString();
    }
    
    public String visitProcessPara(ProcessPara term) {
        StringBuffer result = new StringBuffer("ProcessPara(" + visit(term.getName()) + ")");
        result.append(visitList(ZUtils.assertZNameList(term.getGenFormals()), "[", ",", "]"));
        result.append(" == ");
        result.append(visit(term.getCircusProcess()));
        return result.toString();
    }
    
    public String visitActionPara(ActionPara term) {
        StringBuffer result = new StringBuffer("ActionPara(" + visit(term.getName()) + ")");
        result.append(" == ");
        result.append(visit(term.getCircusAction()));
        return result.toString();
    }    
    
    public String visitSchExprAction(SchExprAction term) {        
        return visit(term.getExpr());
    }
    
    public String visitBasicProcess(BasicProcess term) {
        StringBuffer result = new StringBuffer("BasicProcess(hC=");        
        result.append(term.hashCode());
        result.append(")[");
        result.append("\nStatePara=");
        result.append(visit(term.getStatePara()));
        int paraCnt = term.getZLocalPara().size();
        result.append("\nLocalPara(" + paraCnt + ")");
        result.append(visitList(term.getZLocalPara(), "[\n", "\n", "]"));
        int ontheflyCnt = term.getZOnTheFlyPara().size();
        result.append("\nOnTheFlyPara(" + ontheflyCnt + ")");        
        result.append(visitList(term.getZOnTheFlyPara(), "[\n", "\n", "]"));
        result.append("\nMainAction=");
        result.append(visit(term.getMainAction()));
        result.append("\nTotal paras=" + (paraCnt+ontheflyCnt));
        result.append("\n]\n");
        return result.toString();
    }
    
    private static FindProcessPara findPP_ = new FindProcessPara();
    
    public String printProcessPara(Term term) {
        StringBuffer result = new StringBuffer();
        List<ProcessPara> pps = findPP_.collectProcessParaFrom(term);
        result.append("----------------------------------------\n");
        result.append("Found " + pps.size() + " process paras  \n");
        result.append("----------------------------------------");
        for(ProcessPara pp : pps) {
            result.append("\n");
            result.append(visit(pp));
            
        }
        result.append("\n----------------------------------------\n");
        return result.toString();
    }
    
    static class FindProcessPara implements
        TermVisitor<Object>,
        ProcessParaVisitor<Object> {
        
        List<ProcessPara> processPara_ = new ArrayList<ProcessPara>();
        
        public Object visitProcessPara(ProcessPara term) {
            processPara_.add(term);
            return term;
        }
        
        public Object visitTerm(Term term) {
            VisitorUtils.visitTerm(this, term);
            return term;
        }
        
        List<ProcessPara> collectProcessParaFrom(Term term) {
            assert term != null : "Invalid (null) term";
            processPara_.clear();
            term.accept(this);
            return Collections.unmodifiableList(processPara_);
        }
    }
}
