/*
 * ProofCommand.java
 *
 * Created on 16 September 2005, 15:39
 */

package net.sourceforge.czt.zeves.proof;

import java.util.Iterator;

/**
 *
 * @author leo
 */
public interface ProofCommand {
    
    /**
     * Returns the command unique name
     */
    public String getName();
    
    /**
     * Returns the number of attributes for this proof command.
     */
    public int attributeCount();
    
    /**
     * Returns each attribute of this proof command.
     */
    public Iterator attributes();    
    
    /**
     * Returns the proof command in Z/Eves XML format
     */
    public String getCommand();
    
    /**
     * Returns the proof command type dividedd according to the sectioning of the reference manual.
     */
    public ProofCommandType getType();
    
    /**
     * Same as getCommand();
     */
    public String toString();
}