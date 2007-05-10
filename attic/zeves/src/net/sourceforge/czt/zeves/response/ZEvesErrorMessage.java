/*
 * ZEvesErrorMessage.java
 *
 * Created on 21 September 2005, 13:46
 */

package net.sourceforge.czt.zeves.response;

import java.text.MessageFormat;

/**
 *
 * @author leo
 */
public class ZEvesErrorMessage {
    
    private final String fPrelude;
    private final String fName;
    private final String fClass;
    private final String fContents;
    
    /** Creates a new instance of ZEvesErrorMessage */
    protected ZEvesErrorMessage(String prelude, String name, String namecls, String contents) {
        fPrelude = prelude;
        fName = name;
        fClass = namecls;
        fContents = contents;
    }
    
    public String getPrelude() {
        return fPrelude;
    }
    
    public String getName() {
        return fName;
    }
    
    public String getNameClass() {
        return fClass;
    }
    
    public String getContents() {
        return fContents;
    }
    
    public String toString() {
        return MessageFormat.format("<errormessage>{0}<name ident=\"{1}\" class=\"{2}\">{3}</errormessage>", 
                fPrelude, fName, fClass, fContents);
    }
    
    public String asString() {
        return getName() + ": " + getContents();
    }
}
