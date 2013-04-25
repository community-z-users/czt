/*
 * WarningManager.java
 *
 * Created on 02 May 2007, 13:46
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circustime;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.z.ast.Para;

/**
 *
 * @author leo
 */
public class WarningManager extends
    net.sourceforge.czt.print.circus.WarningManager {
    
    public WarningManager() {
        super();
    }
    
    /** Creates a new instance of WarningManager */
    public WarningManager(Class<?> forLogger) {
        super(forLogger);
    }
    


    public void warn(CircusTimePrintMessage cpm, Object... arguments) {
        warn(cpm.getMessage(), arguments);
    }

    
    public void warnMissingFor(String msg, BasicProcess term) {
        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_MISSING_ENTITY, msg, term);
    }
    
    public void warnBadParagraphFor(String msg, Para para, BasicProcess term) {
        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_BAD_PARAGRAPH, msg, para, term);
    }
    
    public void warnLocalOnTheFly(Term para, BasicProcess term) {
        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_LOCAL_ONTHEFLY_PARAGRAPH, para, term);
    }
    
    public void warnDuplicatedState(Term term) {
        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_DUPLICATED_STATE_PARAGRAPH, term);
    }

    
}
