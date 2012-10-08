/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.editors.actions;

import org.eclipse.osgi.util.NLS;

/**
 * @author Chengdong Xu
 */
public final class EditorActionMessages extends NLS
{
  private static final String BUNDLE_NAME= "org.eclipse.jdt.internal.ui.actions.ActionMessages";//$NON-NLS-1$

    private EditorActionMessages() {
        // Do not instantiate
    }
    
    static {
        NLS.initializeMessages(BUNDLE_NAME, EditorActionMessages.class);
    }
}
