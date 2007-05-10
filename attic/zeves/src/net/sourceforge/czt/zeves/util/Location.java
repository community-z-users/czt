/*
 * ZEvesLocation.java
 *
 * Created on 15 September 2005, 16:52
 */

package net.sourceforge.czt.zeves.util;

/**
 *
 * @author leo
 */
public class Location {
    
    private final String fLocation;
    
    /** Creates a new instance of ZEvesLocation */
    public Location(String loc) {        
        if (loc == null || loc.equals(""))
            throw new IllegalArgumentException("Invalid Z/Eves location. It can be neither null nor empty.");
        fLocation = loc;
    }
    
    public String getLocation() {        
        assert fLocation != null && !fLocation.equals("");
        return fLocation;
    }
}
