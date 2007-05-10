/*
 * ProofUtils.java
 *
 * Created on 29 November 2005, 17:41
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.zeves.proof;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.ast.TermA;
import net.sourceforge.czt.zeves.util.ZEvesUtils;
import net.sourceforge.czt.zeves.util.ZEvesXMLPatterns;

/**
 *
 * @author leo
 */
public class ProofUtils extends ZEvesUtils implements ZEvesXMLPatterns {
    
    /** Creates a new instance of ProofUtils */
    protected ProofUtils() {        
    }
    
    public static List<String> queryIfIsProved(String goalName) {
        List<String> result = new ArrayList<String>();
        result.add(MessageFormat.format(ZEVES_COMMAND, "set-current-goal-name", goalName));
        result.add(MessageFormat.format(ZEVES_COMMAND, "get-goal-proved-state", goalName));
        return result;
    }
    
    public static ProofScript getProofScriptAnn(TermA term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves proof script is allowed only for ConjPara and Pred terms");
        ProofScript ps = (ProofScript)term.getAnn(ProofScript.class);
        return ps;
    }
    
    public static void addProofScriptAnn(TermA term, ProofScript ann) {
        if (getProofScriptAnn(term) != null)
            throw new IllegalArgumentException("Term already contains a ProofScript annotation.");
        term.getAnns().add(ann);
    }
    
}
