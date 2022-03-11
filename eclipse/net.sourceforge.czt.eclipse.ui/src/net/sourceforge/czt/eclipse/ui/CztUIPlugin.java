package net.sourceforge.czt.eclipse.ui;

import net.sourceforge.czt.eclipse.ui.document.IDocumentEditTracker;
import net.sourceforge.czt.eclipse.ui.internal.editors.CZTTextTools;
import net.sourceforge.czt.eclipse.ui.internal.editors.ImageDescriptorRegistry;
import net.sourceforge.czt.eclipse.ui.internal.editors.latex.ZLatexPartitionScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.unicode.ZUnicodePartitionScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.DocumentEditTracker;
import net.sourceforge.czt.eclipse.ui.internal.preferences.CztFontLoad;
import net.sourceforge.czt.eclipse.ui.internal.preferences.PreferenceConstants;
import net.sourceforge.czt.eclipse.ui.internal.util.CZTColorManager;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.DefaultSectionParents;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.util.ZUtils;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;
import org.osgi.framework.BundleContext;

/**
 * The main plugin class to be used in the desktop.
 */
public class CztUIPlugin extends AbstractUIPlugin
{

  // The plug-in ID
  public static final String PLUGIN_ID = "net.sourceforge.czt.eclipse.ui"; //$NON-NLS-1$

  //The shared instance.
  private static CztUIPlugin plugin;

  private RuleBasedPartitionScanner fZDefaultPartitionScanner;

  private RuleBasedPartitionScanner fZLatexPartitionScanner;

  private RuleBasedPartitionScanner fZUnicodePartitionScanner;

  private CZTColorManager fColorManager;

  private SectionManager fSectionManager;

  private ImageDescriptorRegistry fImageDescriptorRegistry;

  /**
   * Property change listener on this plugin's preference store.
   */
  private IPropertyChangeListener fPropertyChangeListener;

//  private IPropertyChangeListener fFontPropertyChangeListener;

  /**
   * The combined preference store.
   */
  private IPreferenceStore fCombinedPreferenceStore;

//  /**
//   * The shared Z properties file document provider.
//   * @since 3.1
//   */
//  private IDocumentProvider fPropertiesFileDocumentProvider;

  /**
   *
   */
  private CZTTextTools fCZTTextTools;
  
  /**
   * A tracker for document edits - listeners can register to listen to document changes within
   * editors.
   */
  private DocumentEditTracker editTracker;

  /**
   * The constructor.
   */
  public CztUIPlugin()
  {
    super();
    plugin = this;
  }

  /**
   * This method is called upon plug-in activation
   */
  public void start(BundleContext context) throws Exception
  {
    super.start(context);

    loadCztFont();

    String defaultDialect = getPreferenceStore().getString(
              PreferenceConstants.PROP_DIALECT);
    initSectionManager(Dialect.valueOf(defaultDialect.toUpperCase()));

    fPropertyChangeListener= new IPropertyChangeListener() {
      public void propertyChange(PropertyChangeEvent event) {
        String property = event.getProperty();
        if (PreferenceConstants.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS.equals(property) ||
            PreferenceConstants.PROP_TYPECHECK_RECURSIVE_TYPES.equals(property) ||
            PreferenceConstants.PROP_TYPECHECK_USE_STRONG_TYPING.equals(property)) {
          fSectionManager.setProperty(property, String.valueOf(event.getNewValue()));
        }
        else if (PreferenceConstants.PROP_DIALECT.equals(property)) {
          String dialect = String.valueOf(event.getNewValue());
          initSectionManager(Dialect.valueOf(dialect.toUpperCase()));
        }
      }
    };
    getPreferenceStore().addPropertyChangeListener(fPropertyChangeListener);
    
    editTracker = new DocumentEditTracker();
    editTracker.init();
  }

  /**
   * This method is called when the plug-in is stopped
   */
  public void stop(BundleContext context) throws Exception
  {
    
    if (editTracker != null) {
      editTracker.dispose();
      editTracker = null;
    }
    
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
  public static CztUIPlugin getDefault()
  {
    return plugin;
  }
  
  /**
   * Retrieves a document edit tracker, which notifies when documents are edited within Eclipse.
   * @return the tracker for the plugin
   * @see IDocumentEditTracker
   */
  public static IDocumentEditTracker getEditTracker() {
    return getDefault().editTracker;
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
    return imageDescriptorFromPlugin(PLUGIN_ID, path);
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
   * Returns a section manager for parsing and type checking.
   * Note that this returns a <em>clone</em> of an internal section manager
   * each time it is called.  The standard library has already been loaded
   * and parsed before the clone,
   */
  public SectionManager getSectionManager()
  {
    if (fSectionManager == null) {
      initSectionManager(Dialect.Z);
    }
    //System.out.println("Cloning section manager "+fSectionManager.hashCode());
    return (SectionManager) fSectionManager.clone();
  }
  
  public static final String ZECLIPSE_LATEX_DEFAULT_SECTION = "ZEclipseDefault";

  /** Initialises fSectionManager, which is the default internal section
   *  manager that is available via getSectionManager.
   *  This creates a new section manager for the given dialect of Z,
   *  then loads, parses and typechecks the standard toolkit.
   *
   * @param dialect as in Dialect class.
   */
  private void initSectionManager(Dialect dialect)
  {
    SectionManager sectManager = new SectionManager(dialect);

    //System.out.println("Created new SectionManager(Dialect) -> "+sectManager.hashCode());
    IPreferenceStore store = getPreferenceStore();
    /**
     * Sets the properties of the section manager
     */
    sectManager.setProperty(PreferenceConstants.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS, String.valueOf(store.getBoolean(PreferenceConstants.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS)));
    sectManager.setProperty(PreferenceConstants.PROP_TYPECHECK_RECURSIVE_TYPES, String.valueOf(store.getBoolean(PreferenceConstants.PROP_TYPECHECK_RECURSIVE_TYPES)));
    sectManager.setProperty(PreferenceConstants.PROP_TYPECHECK_USE_STRONG_TYPING, String.valueOf(store.getBoolean(PreferenceConstants.PROP_TYPECHECK_USE_STRONG_TYPING)));

    /**
     * Initialize the section manager
     */
    try {
    	// debug SM
      //sectManager.setTracing(true);
    	
       // get default parents for the same as ANONYMOUS sections (i.e. most encompasing possible, per dialect).
      DefaultSectionParents dsp = sectManager.get(new Key<DefaultSectionParents>(ZECLIPSE_LATEX_DEFAULT_SECTION, DefaultSectionParents.class));
      String defaultParents = ZUtils.parentsAsString(dsp.defaultParents(Section.ANONYMOUS.getName()));
      defaultParents = defaultParents.replaceAll("_", "\\\\_");
      
      Source source = new StringSource("\\begin{zsection} "
          + "\\SECTION " + ZECLIPSE_LATEX_DEFAULT_SECTION + "\\parents " + defaultParents
          + "\\end{zsection}");
      
      source.setMarkup(Markup.LATEX);
      sectManager.put(new Key<Source>(ZECLIPSE_LATEX_DEFAULT_SECTION, Source.class), source);
      // make sure it (and the standard toolkit) are parsed
      sectManager.get(new Key<Spec>(ZECLIPSE_LATEX_DEFAULT_SECTION, Spec.class));
      //System.out.println("GOT TO PARSING");
      // and typechecked
      sectManager.get(new Key<SectTypeEnvAnn>(ZECLIPSE_LATEX_DEFAULT_SECTION,
                                              SectTypeEnvAnn.class));
    } catch (CommandException ce) {
	  if (ce.getCause() instanceof TypeErrorException)
      {
        TypeErrorException typeErrorException = (TypeErrorException) ce.getCause();
        for (ErrorAnn next : typeErrorException.getErrors())
        {
          if (next.getErrorType().equals(ErrorType.ERROR))
          {  
        	log(next.getMessage(), typeErrorException);  
          }
          else 
          {
        	log(new Status(IStatus.WARNING, PLUGIN_ID, 1001, next.getMessage(), typeErrorException));  
          }
        }
      }
      // propagate this exception so it is visible to users.
	  else
		 throw new RuntimeException("Error creating a new section manager", ce);
    }
    fSectionManager = sectManager;
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
    log(new Status(IStatus.ERROR, PLUGIN_ID, 1001, message, null));
  }

  public static void logErrorStatus(String message, IStatus status)
  {
    if (status == null) {
      logErrorMessage(message);
      return;
    }
    MultiStatus multi = new MultiStatus(PLUGIN_ID, 1001, message, null);
    multi.add(status);
    log(multi);
  }

  public static void log(Throwable e)
  {
    log(e.getMessage(), e);
  }

  public static void log(String message, Throwable e)
  {
    log(new Status(IStatus.ERROR, PLUGIN_ID, 1001, message, e));
  }

  private static void loadCztFont() {

    Display display = Display.getCurrent();
    if (display != null) {
      // already UI thread - use it without postponing
      // to avoid editors initialising with incorrect font
      CztFontLoad.loadCztFont();

    } else {

      // non-UI thread - load in the UI thread
      Display.getDefault().asyncExec(new Runnable() {
        @Override
        public void run() {
          CztFontLoad.loadCztFont();
        }
      });
    }
  }

}
