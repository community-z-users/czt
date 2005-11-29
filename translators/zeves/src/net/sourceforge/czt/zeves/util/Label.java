/*
 * Label.java
 *
 * Created on 16 September 2005, 13:36
 */

package net.sourceforge.czt.zeves.util;

/**
 *
 * @author leo
 */
public class Label {
    
    private final Usage fUsage;
    private final Ability fAbility;
    private final String fTheoremName;
    
    /** Creates a new instance of Label */
    public Label(String thmName, Ability a, Usage u) {        
        if (thmName == null || thmName.equals(""))
            throw new IllegalArgumentException("Z/Eves labels must have at least a theorem name");
        fTheoremName = thmName;
        fAbility = a;
        fUsage = u;
    }
    
    public String getAbility() {
        return fAbility != null ? fUsage.toString().toLowerCase() : "";
    }
    
    public String getUsage() {
        return fUsage != null ? fUsage.toString().toLowerCase() : "" ;
    }
    
    public String getTheoremName() {
        assert fTheoremName != null && !fTheoremName.equals("");
        return fTheoremName;
    }
    
    public String toString() {
        return "ZEves<<" + getAbility() + " " + getUsage() + " " + getTheoremName() + ">>";
    }
}
