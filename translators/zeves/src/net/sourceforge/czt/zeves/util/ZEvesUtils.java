/*
 * ZEvesUtils.java
 *
 * Created on 29 November 2005, 16:59
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.zeves.util;

import java.net.InetAddress;
import java.net.UnknownHostException;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.ast.TermA;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;



/**
 *
 * @author leo
 */
public class ZEvesUtils {
    
    /** Creates a new instance of ZEvesUtils */
    protected ZEvesUtils() {
    }
    
    public static String getLocalHost() {
        try {
            return InetAddress.getLocalHost().getHostName();
        } catch (UnknownHostException e) {
            return "localhost";
        }
    }    
    
    public static Ability getDefaultAbility() {
        return Ability.none;
    }
    
    public static Usage getDefaultUsage() {
        return Usage.none;
    }   
    
    /* Annotation related methods for Z/Eves productions not present in CZT */
    
    /**
     * Returns wether the given term is a conjecture or not. Conjectures can contain ProofScript
     * annotations. The terms which allow proof script annotations are ConjPara or Pred.
     */
    public static boolean isConjecture(TermA term) {
        return (term instanceof ConjPara || term instanceof Pred);
    }
    
    public static boolean isPara(Term term) {
        return (term instanceof Para);
    }
    
    public static Ability getAbilityAnn(TermA term) {
        if (!isPara(term))
            throw new IllegalArgumentException("Z/Eves location is allowed only for Para terms");
        return (Ability)term.getAnn(Ability.class);
    }
    
    public static Location getLocationAnn(TermA term) {
        if (!isPara(term))
            throw new IllegalArgumentException("Z/Eves location is allowed only for Para terms");
        return (Location)term.getAnn(Location.class);
    }
    
    public static Usage getUsageAnn(TermA term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves usage is allowed only for ConjPara and Pred terms");
        return (Usage)term.getAnn(Usage.class);
    }
    
    public static Label getLabelAnn(TermA term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves label is allowed only for ConjPara and Pred terms");
        Label l = (Label)term.getAnn(Label.class);
        return l;
    }    
        
    public static Label createLabel(TermA term) {        
        return createLabel(term, getDefaultAbility(), getDefaultUsage());
    }
    
    public static Label createLabel(TermA term, Ability ability, Usage usage) {        
        String fromClsStr = term.getClass().getName();
        fromClsStr = fromClsStr.substring(fromClsStr.lastIndexOf(".")+1);
        String thmName = fromClsStr + term.hashCode();
        return createLabel(thmName, ability, usage);
    }
    
    public static Label createLabel(String name, Ability ability, Usage usage) {                
        Label result = new Label(name, ability, usage);
        return result;
    }
    
    public static void addLabelAnn(TermA term, Label ann) {        
        if (getLabelAnn(term) != null)
            throw new IllegalArgumentException("Term already contains a Label annotation.");
        term.getAnns().add(ann);
    }    
}
