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
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessKind;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.BasicProcessSignature;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;

import net.sourceforge.czt.circus.visitor.ChannelTypeVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus.visitor.ProcessTypeVisitor;
import net.sourceforge.czt.circus.visitor.ActionTypeVisitor;
import net.sourceforge.czt.circus.visitor.NameSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ProcessSignatureVisitor;
import net.sourceforge.czt.circus.visitor.BasicProcessSignatureVisitor;
import net.sourceforge.czt.circus.visitor.ActionSignatureVisitor;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
        
/**
 * @author Petra Malik
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
             ZParaListVisitor<String>
{
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
        StringBuffer result = new StringBuffer("Name: ");
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
        StringBuffer result = new StringBuffer(term.getProcessName().accept(this));        
        result.append(visitList(ZUtils.assertZNameList(term.getGenFormals()), "[", ",", "]"));        
        result.append(" == ");
        result.append(term.getCircusProcess().accept(this));
        return result.toString();
    }
    
    public String visitZParaList(ZParaList term) {
        return visitList(term, "ZParaList[", ","  , "]");
    }
    
    public String visitBasicProcess(BasicProcess term) {
        StringBuffer result = new StringBuffer("StatePara=");
        result.append(term.getStatePara().accept(this));
        result.append("\nLocalPara");
        result.append(visitList(term.getZLocalPara(), "[", "\n", "]"));
        result.append("\nOnTheFlyPara");
        result.append(visitList(term.getZOnTheFlyPara(), "[", "\n", "]"));
        result.append("\nMainAction=");
        result.append(term.getMainAction().accept(this));
        return result.toString();
    }
    
    private static FindBasicProcesses findBP_ = new FindBasicProcesses();
        
    public String printBasicProcesses(Term term) {
        StringBuffer result = new StringBuffer();
        List<BasicProcess> bps = findBP_.collectBasicProcessesFrom(term);
        result.append("----------------------------------------\n");
        result.append("Found " + bps.size() + " basic processes");
        for(BasicProcess bp : bps) {
            result.append("\nBasicProcess[\n");
            result.append(bp.accept(this));
            result.append("\n]");
        }
        result.append("\n----------------------------------------\n");
        return result.toString();
    }
        
    static class FindBasicProcesses implements TermVisitor<Object>, BasicProcessVisitor<Object> {
        
        List<BasicProcess> basicProcesses_ = new ArrayList<BasicProcess>();
        
        public Object visitBasicProcess(BasicProcess term) {
            basicProcesses_.add(term);
            return term;
        }
        
        public Object visitTerm(Term term) {
            VisitorUtils.visitTerm(this, term);
            return term;
        }
        
        List<BasicProcess> collectBasicProcessesFrom(Term term) {
            basicProcesses_.clear();
            term.accept(this);
            return Collections.unmodifiableList(basicProcesses_);
        }
    }
}
