/*
 * SimpleCaseCommand.java
 *
 * Created on 16 September 2005, 16:34
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

/**
 *
 * @author leo
 */
public class SimpleCommand extends AbstractProofCommand {    
    
    private final String fName;
    private final ProofCommandType fProofCommandType;
    
    /** Creates a new instance of SimpleCaseCommand */
    SimpleCommand(String name, ProofCommandType type) {
        super();
        validate(name, type);
        fName = name;
        fProofCommandType = type;
    }  
    
    SimpleCommand(String name, ProofCommandType type, CZT2ZEvesPrinter zprinter, Object... attrs) {
        super(zprinter, attrs);
        validate(name, type);
        fName = name;
        fProofCommandType = type;
    }
    
    private void validate(String name, ProofCommandType type) {
        if (name == null || name.equals(""))
            throw new IllegalArgumentException("Invalid proof command name");
        if (type == null)
            throw new IllegalArgumentException("Invalid proof command type");
    }
    
    public ProofCommandType getType() {
        return fProofCommandType;
    }

    public String getName() {
        return fName;
    }
}
