/*
 * Ability.java
 *
 * Created on 15 September 2005, 16:17
 */

package net.sourceforge.czt.zeves.util;

/**
 *
 * @author leo
 */
public enum Ability {    
    none, enabled, disabled;    
    
    public String toString() {
        if (this == none)
            return "";
        else
            return super.toString();
    }
}
