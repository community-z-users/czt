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

import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessKind;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.BasicProcessSignature;
import net.sourceforge.czt.circus.ast.ActionSignature;

import net.sourceforge.czt.circus.visitor.ChannelTypeVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ProcessTypeVisitor;
import net.sourceforge.czt.circus.visitor.ActionTypeVisitor;
import net.sourceforge.czt.circus.visitor.NameSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ProcessSignatureVisitor;
import net.sourceforge.czt.circus.visitor.BasicProcessSignatureVisitor;
import net.sourceforge.czt.circus.visitor.ActionSignatureVisitor;
import net.sourceforge.czt.z.util.ZUtils;
        
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
             ActionSignatureVisitor<String>                    
{
    public String visitChannelType(ChannelType term) {
        StringBuffer result =  new StringBuffer("CHANNEL_TYPE ");        
        result.append(visitList(ZUtils.assertZDeclNameList(term.getGenFormals()), "[", ", ", "]"));
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
        result.append(visitList(term.getZDeclSignature(), "ZDeclSig : ["+ sep, sep, "]\n"));//List<Signature>
        result.append(visitList(term.getActionSignature(), "ActionSig: ["+ sep, sep, "]\n"));//List<Signature>
        result.append(visitList(term.getNameSet(), "NameSet  : [", ", ", "]\n"));//ZRefNameList          
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
        result.append(visitList(term.getUsedChannels(), " @ C[", ", ", "]"));        
        result.append(" }");
        return result.toString();
    }    
    
    protected String visitProcess(ProcessSignature term) {
        StringBuffer result = new StringBuffer("Name: ");
        result.append(visit(term.getProcessName()));
        result.append(visitList(ZUtils.assertZDeclNameList(term.getGenFormals()), "[", ",", "]"));        
        // Print parameters or indexes signature if they exist
        if (term.getParamsOrIndexes() != null && !term.getParamsOrIndexes().getNameTypePair().isEmpty()) {
            result.append(term.getKind().equals(ProcessKind.Parameterised) ? "P [" : "I [");
            result.append(visit(term.getParamsOrIndexes()));
            result.append("]");
        }         
        // Print used channels signature if not empty
        if (term.getUsedChannels() != null && !term.getUsedChannels().isEmpty()) {            
            result.append(visitList(ZUtils.assertZRefNameList(term.getUsedChannels()), " @\n USED_CHAN [", ", ", "]\n"));//zrefnamelist        
        }
        return result.toString();
    }
}
