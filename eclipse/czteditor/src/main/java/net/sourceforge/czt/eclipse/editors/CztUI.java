/**
 * 
 */
package net.sourceforge.czt.eclipse.editors;

/**
 * Central access point for the CZT plug-in (id <code>"net.sourceforge.czt.eclipse"</code>).
 * This class provides static methods for:
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
     * The id of the CZT plug-in (value <code>"net.sourceforge.czt.eclipse"</code>).
     */ 
    public static final String ID_PLUGIN= "net.sourceforge.czt.eclipse"; //$NON-NLS-1$
    
    /**
     * The id of the CZT perspective
     * (value <code>"net.sourceforge.czt.eclipse.perspectives"</code>).
     */ 
    public static final String ID_PERSPECTIVE=      "net.sourceforge.czt.eclipse.perspectives"; //$NON-NLS-1$
    
    
    /**
     * The id of the Z editor
     * (value <code>"net.sourceforge.czt.eclipse.editors.zeditor"</code>).
     */ 
    public static final String ID_Z_EDITOR = "net.sourceforge.czt.eclipse.editors.zeditor"; //$NON-NLS-1$
    
    /**
     * The id of the Character Map view
     * (value <code>"net.sourceforge.czt.eclipse.views.ZCharMapView"</code>).
     */
    public static final String ID_CHARMAP = "net.sourceforge.czt.eclipse.views.ZCharMapView";
    
    /**
     * The id of the Z conversion page view
     * (value <code>"net.sourceforge.czt.eclipse.views.ZConversionView"</code>).
     */
    public static final String ID_CONVERSIONVIEW = "net.sourceforge.czt.eclipse.views.ZConversionView";
    
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
