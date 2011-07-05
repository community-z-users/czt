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
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;



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
    public static boolean isConjecture(Term term) {
        return (term instanceof ConjPara || term instanceof Pred);
    }
    
    public static boolean isPara(Term term) {
        return (term instanceof Para);
    }
    
    public static Ability getAbilityAnn(Term term) {
        if (!isPara(term))
            throw new IllegalArgumentException("Z/Eves location is allowed only for Para terms");
        return (Ability)term.getAnn(Ability.class);
    }
    
    public static Location getLocationAnn(Term term) {
        if (!isPara(term))
            throw new IllegalArgumentException("Z/Eves location is allowed only for Para terms");
        return (Location)term.getAnn(Location.class);
    }
    
    public static Usage getUsageAnn(Term term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves usage is allowed only for ConjPara and Pred terms");
        return (Usage)term.getAnn(Usage.class);
    }
    
    public static Label getLabelAnn(Term term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves label is allowed only for ConjPara and Pred terms");
        Label l = (Label)term.getAnn(Label.class);
        return l;
    }
    
    public static ZName getZNameAnn(Term term) {
        if (!isConjecture(term))
            throw new IllegalArgumentException("Z/Eves name is allowed only for ConjPara and Pred terms");
        ZName name = (ZName)term.getAnn(ZName.class);
        return name;
    }    
        
    public static Label createLabel(Term term) {        
        return createLabel(term, getDefaultAbility(), getDefaultUsage());
    }
    
    public static Label createLabel(Term term, Ability ability, Usage usage) {        
        String fromClsStr = term.getClass().getName();
        fromClsStr = fromClsStr.substring(fromClsStr.lastIndexOf(".")+1);
//        String thmName = fromClsStr + term.hashCode();
        // using just term.hashCode() sometimes gives a negative number, which Z/Eves does not accept
        // instead, go to unsigned Hex (as in Object.toString())
        String thmName = fromClsStr + Integer.toHexString(term.hashCode());
        return createLabel(thmName, ability, usage);
    }
    
    public static Label createLabel(String name, Ability ability, Usage usage) {                
        Label result = new Label(name, ability, usage);
        return result;
    }
    
    public static void addLabelAnn(Term term, Label ann) {        
        if (getLabelAnn(term) != null)
            throw new IllegalArgumentException("Term already contains a Label annotation.");
        term.getAnns().add(ann);
    }    
}
