/*
 * Usage.java
 *
 * Created on 15 September 2005, 15:01
 */

package net.sourceforge.czt.zeves.util;

/**
 *
 * @author leo
 */
public enum Usage {    
    none, axiom, rule, grule, frule;    
    
    public String toString() {
        if (this == none)
            return "";
        else
            return super.toString();
    }
}
