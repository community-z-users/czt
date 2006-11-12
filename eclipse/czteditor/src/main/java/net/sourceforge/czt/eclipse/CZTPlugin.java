/**
 * The main plugin class to be used in the desktop.
 */

package net.sourceforge.czt.eclipse;

import java.util.MissingResourceException;
import java.util.ResourceBundle;

import net.sourceforge.czt.eclipse.editors.CZTTextTools;
import net.sourceforge.czt.eclipse.editors.CztUI;
import net.sourceforge.czt.eclipse.editors.ImageDescriptorRegistry;
import net.sourceforge.czt.eclipse.editors.latex.ZLatexPartitionScanner;
import net.sourceforge.czt.eclipse.editors.unicode.ZUnicodePartitionScanner;
import net.sourceforge.czt.eclipse.util.CZTColorManager;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Spec;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.osgi.framework.BundleContext;

/**
 * 
 */
public class CZTPlugin extends AbstractUIPlugin
{

  //The shared instance.
  private static CZTPlugin plugin;

  //Resource bundle.
  private ResourceBundle resourceBundle;

  private RuleBasedPartitionScanner fZDefaultPartitionScanner;

  private RuleBasedPartitionScanner fZLatexPartitionScanner;

  private RuleBasedPartitionScanner fZUnicodePartitionScanner;

  private CZTColorManager fColorManager;

  private SectionManager fSectionManager;

  private ImageDescriptorRegistry fImageDescriptorRegistry;

  /**
   * Property change listener on this plugin's preference store.
   * 
   * @since 3.0
   */
  private IPropertyChangeListener fPropertyChangeListener;

  private IPropertyChangeListener fFontPropertyChangeListener;

  /**
   * The combined preference store.
   * @since 3.0
   */
  private IPreferenceStore fCombinedPreferenceStore;

  /**
   * The shared Z properties file document provider.
   * @since 3.1
   */
  private IDocumentProvider fPropertiesFileDocumentProvider;

  /**
   * 
   */
  private CZTTextTools fCZTTextTools;

  /**
   * The constructor.
   */
  public CZTPlugin()
  {
    super();
    plugin = this;

    try {
      resourceBundle = ResourceBundle
          .getBundle("net.sourceforge.czt.eclipse.CZTPluginResources");
    } catch (MissingResourceException x) {
      resourceBundle = null;
    }
  }

  /**
   * This method is called upon plug-in activation
   */
  public void start(BundleContext context) throws Exception
  {
    super.start(context);
    this.fSectionManager = createSectionManager();
  }

  /**
   * This method is called when the plug-in is stopped
   */
  public void stop(BundleContext context) throws Exception
  {
    try {
      if (fImageDescriptorRegistry != null)
        fImageDescriptorRegistry.dispose();

      if (fCZTTextTools != null) {
        fCZTTextTools.dispose();
        fCZTTextTools = null;
      }

      //			uninstallPreferenceStoreBackwardsCompatibility();
    } finally {
      super.stop(context);
    }

    plugin = null;
  }

  /**
   * Returns the shared instance.
   */
  public static CZTPlugin getDefault()
  {
    return plugin;
  }

  /**
   * Returns an image descriptor for the image file at the given
   * plug-in relative path.
   *
   * @param path the path
   * @return the image descriptor
   */
  public static ImageDescriptor getImageDescriptor(String path)
  {
    return imageDescriptorFromPlugin(
        CztUI.ID_PLUGIN, path);
  }

  public static IWorkspace getWorkspace()
  {
    return ResourcesPlugin.getWorkspace();
  }

  public static IWorkbenchWindow getActiveWorkbenchWindow()
  {
    return getDefault().getWorkbench().getActiveWorkbenchWindow();
  }

  public static IWorkbenchPage getActivePage()
  {
    IWorkbenchWindow window = getActiveWorkbenchWindow();
    if (window == null)
      return null;

    return window.getActivePage();
  }

  public static Shell getActiveWorkbenchShell()
  {
    IWorkbenchWindow window = getActiveWorkbenchWindow();
    if (window == null)
      return null;

    return window.getShell();
  }

  public static IEditorPart getActiveEditor()
  {
    IWorkbenchPage page = getActivePage();
    IEditorPart part = page.getActiveEditor();
    if (!(part instanceof AbstractTextEditor))
      return null;
    return part;
  }

  /**
   * Returns an array of all editors that have an unsaved content. If the identical content is 
   * presented in more than one fEditor, only one of those fEditor parts is part of the result.
   * 
   * @return an array of all dirty fEditor parts.
   */
  //	public static IEditorPart[] getDirtyEditors() {
  //		Set inputs= new HashSet();
  //		List result= new ArrayList(0);
  //		IWorkbench workbench= getDefault().getWorkbench();
  //		IWorkbenchWindow[] windows= workbench.getWorkbenchWindows();
  //		for (int i= 0; i < windows.length; i++) {
  //			IWorkbenchPage[] pages= windows[i].getPages();
  //			for (int x= 0; x < pages.length; x++) {
  //				IEditorPart[] editors= pages[x].getDirtyEditors();
  //				for (int z= 0; z < editors.length; z++) {
  //					IEditorPart ep= editors[z];
  //					IEditorInput input= ep.getEditorInput();
  //					if (!inputs.contains(input)) {
  //						inputs.add(input);
  //						result.add(ep);
  //					}
  //				}
  //			}
  //		}
  //		return (IEditorPart[])result.toArray(new IEditorPart[result.size()]);
  //	}
  /**
   * Returns an array of all instanciated editors.
   * @return the list of instantiated editors
   */
  //	public static IEditorPart[] getInstanciatedEditors() {
  //		List result= new ArrayList(0);
  //		IWorkbench workbench= getDefault().getWorkbench();
  //		IWorkbenchWindow[] windows= workbench.getWorkbenchWindows();
  //		for (int windowIndex= 0; windowIndex < windows.length; windowIndex++) {
  //			IWorkbenchPage[] pages= windows[windowIndex].getPages();
  //			for (int pageIndex= 0; pageIndex < pages.length; pageIndex++) {
  //				IEditorReference[] references= pages[pageIndex].getEditorReferences();
  //				for (int refIndex= 0; refIndex < references.length; refIndex++) {
  //					IEditorPart fEditor= references[refIndex].getEditor(false);
  //					if (fEditor != null)
  //						result.add(fEditor);
  //				}
  //			}
  //		}
  //		return (IEditorPart[])result.toArray(new IEditorPart[result.size()]);
  //	}
  /**
   * Returns the string from the plugin's resource bundle,
   * or 'key' if not found.
   */
  public static String getResourceString(String key)
  {
    ResourceBundle bundle = CZTPlugin.getDefault().getResourceBundle();
    try {
      return (bundle != null) ? bundle.getString(key) : key;
    } catch (MissingResourceException e) {
      return key;
    }
  }

  /**
   * Returns the plugin's resource bundle,
   */
  public ResourceBundle getResourceBundle()
  {
    return resourceBundle;
  }

  public synchronized CZTTextTools getCZTTextTools()
  {
    if (fCZTTextTools == null)
      fCZTTextTools = new CZTTextTools(getPreferenceStore());
    return fCZTTextTools;
  }

  /**
   * Return a scanner for creating z partitions.
   */
  public RuleBasedPartitionScanner getZPartitionScanner(String fileType)
  {
    if ((fileType == null) || fileType.equals("")) {
      return fZDefaultPartitionScanner;
    }
    else if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(fileType)) {
      if (fZLatexPartitionScanner == null)
        fZLatexPartitionScanner = new ZLatexPartitionScanner();
      return fZLatexPartitionScanner;
    }
    else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(fileType)
        || IZFileType.FILETYPE_UTF16.equalsIgnoreCase(fileType)) {
      if (fZUnicodePartitionScanner == null)
        fZUnicodePartitionScanner = new ZUnicodePartitionScanner();
      return fZUnicodePartitionScanner;
    }
    else {
      if (fZDefaultPartitionScanner == null)
        fZDefaultPartitionScanner = new RuleBasedPartitionScanner();
      return fZDefaultPartitionScanner;
    }
  }

  /**
   * Returns the singleton color provider.
   */
  public CZTColorManager getCZTColorManager()
  {
    if (fColorManager == null)
      fColorManager = new CZTColorManager();
    return fColorManager;
  }

  /**
   * Returns an section manager for parsing and type checking
   */
  public SectionManager getSectionManager()
  {
    if (this.fSectionManager == null) {
      System.out.println("Create a new section manager");
      this.fSectionManager = createSectionManager();
    }
    //		this.fSectionManager.reset();
    //		return this.fSectionManager;
    return (SectionManager) this.fSectionManager.clone();
  }

  private SectionManager createSectionManager()
  {
    SectionManager sectManager = new SectionManager();
    /**
     * Initialize the section manager
     */
    try {
      Source source = new StringSource("\\begin{zsection} "
          + "\\SECTION ZEclipseDefault " + "\\parents standard\\_toolkit "
          + "\\end{zsection}");
      source.setMarkup(Markup.LATEX);
      sectManager.put(new Key("ZEclipseDefault", Source.class), source);
      sectManager.get(new Key("ZEclipseDefault", Spec.class));
    } catch (CommandException ce) {
      System.out.println("Error in creating a new section manager:");
      ce.printStackTrace();
      return null;
    }

    return sectManager;
  }

  /*
   * @see org.eclipse.ui.plugin.AbstractUIPlugin#createImageRegistry()
   */
  protected ImageRegistry createImageRegistry()
  {
    return CZTPluginImages.getImageRegistry();
  }

  public static ImageDescriptorRegistry getImageDescriptorRegistry()
  {
    return getDefault().internalGetImageDescriptorRegistry();
  }

  private synchronized ImageDescriptorRegistry internalGetImageDescriptorRegistry()
  {
    if (fImageDescriptorRegistry == null)
      fImageDescriptorRegistry = new ImageDescriptorRegistry();
    return fImageDescriptorRegistry;
  }

  /**
   * Returns a combined preference store, this store is read-only.
   * 
   * @return the combined preference store
   * 
   * @since 3.0
   */
  public IPreferenceStore getCombinedPreferenceStore()
  {
    if (fCombinedPreferenceStore == null) {
      IPreferenceStore generalTextStore = EditorsUI.getPreferenceStore();
      fCombinedPreferenceStore = new ChainedPreferenceStore(
          new IPreferenceStore[]{getPreferenceStore(), generalTextStore});
    }
    return fCombinedPreferenceStore;
  }

  public static void log(IStatus status)
  {
    getDefault().getLog().log(status);
  }

  public static void logErrorMessage(String message)
  {
    log(new Status(IStatus.ERROR, getPluginID(), 1001, message, null));
  }

  public static void logErrorStatus(String message, IStatus status)
  {
    if (status == null) {
      logErrorMessage(message);
      return;
    }
    MultiStatus multi = new MultiStatus(getPluginID(), 1001, message, null);
    multi.add(status);
    log(multi);
  }

  public static void log(Throwable e)
  {
    log(new Status(IStatus.ERROR, getPluginID(), 1001,
        "CZTUIMessages.JavaPlugin_internal_error", e));
  }

  public static String getPluginID()
  {
    return CztUI.ID_PLUGIN;
  }
}
