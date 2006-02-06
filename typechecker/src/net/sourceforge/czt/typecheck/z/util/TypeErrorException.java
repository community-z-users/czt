/*
 * TypeErrorException.java
 *
 * Created on 18 November 2005, 10:11
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.typecheck.z.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.typecheck.z.ErrorAnn;

/**
 *
 * @author leo
 */
public class TypeErrorException extends RuntimeException {    
    
    private final List<ErrorAnn> fErrors = new ArrayList<ErrorAnn>();
    
    /** Creates a new instance of TypeErrorException */
    public TypeErrorException(String message, List<? extends ErrorAnn> errors) {
        super(message);
        fErrors.addAll(errors);
    }
    
    public TypeErrorException(String message, Throwable cause, List<? extends ErrorAnn> errors) {
        super(message,  cause);
        fErrors.addAll(errors);
    }
    
    public List<ErrorAnn> errors() {
        return Collections.unmodifiableList(fErrors);
    }
}
