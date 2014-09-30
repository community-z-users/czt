/*
 * WarningManager.java
 *
 * Created on 02 May 2007, 13:46
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circusconf;


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
    


    public void warn(CircusConfPrintMessage cpm, Object... arguments) {
        warn(cpm.getMessage(), arguments);
    }

    
    
}
