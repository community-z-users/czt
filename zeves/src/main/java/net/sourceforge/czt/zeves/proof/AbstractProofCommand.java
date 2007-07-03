/*
 * AbstractProofCommand.java
 *
 * Created on 16 September 2005, 15:56
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

/**
 *
 * @author leo
 */
public abstract class AbstractProofCommand implements ProofCommand {
    
    private final List fAttributes;
    final CZT2ZEvesPrinter fZPrinter;
    
    AbstractProofCommand() {
        fZPrinter = null;
        fAttributes = Collections.emptyList();
    }
    
    /** Creates a new instance of AbstractProofCommand */
    AbstractProofCommand(CZT2ZEvesPrinter zprinter, Object... attrs) {
        if (zprinter == null)
            throw new NullPointerException("Invalid CZT to Z/Eves XML converter.");
        if (attrs == null || attrs.length == 0)
            throw new NullPointerException("Invalid proof command attributes.");
        fZPrinter = zprinter;        
        for(Object o : attrs) {
            if (o == null) {
                throw new IllegalArgumentException("Proof command attribute cannot be null");
            }
        }
        fAttributes = Collections.unmodifiableList(Arrays.asList(attrs));        
    }    
    
    protected String format(Object... attrs) {
        assert attrs == null || attrs.length == 0 : "invalid proof command attributes";
        return "";
    }
    
    public abstract ProofCommandType getType();
    
    public abstract String getName();
    
    public final String getCommand() {
        String result = getName() + " " + format(fAttributes.toArray());
        assert !result.equals(" ");
        return result;
    }
    
    public final Iterator attributes() {
        return fAttributes.iterator();
    }
    
    public final int attributeCount() {
        return fAttributes.size();
    }
    
    public final String toString() {
        return getCommand();
    }
}
