/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.util;

/**
 * Central access point for the CZT plug-in (id <code>"net.sourceforge.czt.eclipse"</code>).
 * <p>
 * This class provides static methods and fields only; it is not intended to be
 * instantiated or subclassed by clients.
 * </p>
 * @author Chengdong Xu
 *
 */
public final class CztUI
{
//    private static ISharedImages fgSharedImages= null;
    
    private CztUI() {
        // prevent instantiation of CztUI.
    }
        
    /**
     * The id of the Character Map view
     * (value {@code net.sourceforge.czt.eclipse.ui.views.ZCharMap}).
     */
    public static final String ID_CHARMAP = "net.sourceforge.czt.eclipse.ui.views.ZCharMap";
    
    /**
     * The id of the Z conversion page view
     * (value {@code net.sourceforge.czt.eclipse.ui.views.ZConversion}).
     */
    public static final String ID_CONVERSIONVIEW = "net.sourceforge.czt.eclipse.ui.views.ZConversion";
    
    /**
     * The id of the new CZT project wizard
     * (value <code>"net.sourceforge.czt.eclipse.wizards.NewCZTProjectWizard"</code>).
     */
    public static final String ID_NEW_CZT_PROJECT_WIZARD = "net.sourceforge.czt.eclipse.wizards.NewCZTProjectWizard";
    
    /**
     * The id of the new CZT project wizard
     * (value <code>"net.sourceforge.czt.eclipse.wizards.NewZSpecificationWizard"</code>).
     */
    public static final String ID_NEW_CZT_SPECIFICATION_WIZARD = "net.sourceforge.czt.eclipse.wizards.NewZSpecificationWizard";
    
    /**
     * The name of the status line group item
     * (value <code>"net.sourceforge.czt.eclipse.status.group"</code>).
     */
    public static final String STATUS_LINE_GROUP = "net.sourceforge.czt.eclipse.status.group";
    
    /**
     * The id of the status line contribution item - Editing Mode
     * (value <code>"net.sourceforge.czt.eclipse.status.edit.mode"</code>).
     */
    public static final String ID_STATUS_LINE_EDIT_MODE = "net.sourceforge.czt.eclipse.status.edit.mode";
    
    /**
     * Returns the shared images for the CZT UI.
     *
     * @return the shared images manager
     */
 //   public static ISharedImages getSharedImages() {
 //       if (fgSharedImages == null)
 //           fgSharedImages= new SharedImages();
            
 //       return fgSharedImages;
 //   }
}
