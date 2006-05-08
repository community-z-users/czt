/**
 * The main plugin class to be used in the desktop.
 */
package net.sourceforge.czt.eclipse;

import java.util.MissingResourceException;
import java.util.ResourceBundle;

import net.sourceforge.czt.eclipse.editors.ZCodeScanner;
import net.sourceforge.czt.eclipse.editors.ZPartitionScanner;
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
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.osgi.framework.BundleContext;

/**
 * 
 */
public class CZTPlugin extends AbstractUIPlugin {

	//The shared instance.
	private static CZTPlugin plugin;
	//Resource bundle.
	private ResourceBundle resourceBundle;
	//The Plugin ID
	public static final String PLUGIN_ID = "net.sourceforge.czt.eclipse";
	
	public final static String Z_PARTITIONING= "__zed_partitioning";   //$NON-NLS-1$

	private ZPartitionScanner fZPartitionScanner_Default;
	private ZPartitionScanner fZPartitionScanner_Latex;
	private ZPartitionScanner fZPartitionScanner_Utf8;
	private ZPartitionScanner fZPartitionScanner_Utf16;
	private ZPartitionScanner fZPartitionScanner_Utf16be;
	private ZPartitionScanner fZPartitionScanner_Utf16le;
	
	private CZTColorManager fColorManager;
	private ZCodeScanner fCodeScanner;
	private SectionManager fSectionManager;
		
	
	/**
	 * The constructor.
	 */
	public CZTPlugin() {
		super();
		plugin = this;
		
		try {
			resourceBundle = ResourceBundle.getBundle("net.sourceforge.czt.eclipse.CZTPluginResources");
		} catch (MissingResourceException x) {
			resourceBundle = null;
		}
	}

	/**
	 * This method is called upon plug-in activation
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		this.fSectionManager = createSectionManager();
	}

	/**
	 * This method is called when the plug-in is stopped
	 */
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
		plugin = null;
	}

	/**
	 * Returns the shared instance.
	 */
	public static CZTPlugin getDefault() {
		return plugin;
	}

	/**
	 * Returns an image descriptor for the image file at the given
	 * plug-in relative path.
	 *
	 * @param path the path
	 * @return the image descriptor
	 */
	public static ImageDescriptor getImageDescriptor(String path) {
		return AbstractUIPlugin.imageDescriptorFromPlugin("net.sourceforge.czt", path);
	}
	
	
	public static IWorkspace getWorkspace() {
		return ResourcesPlugin.getWorkspace();
	}
	
	public static IWorkbenchWindow getActiveWorkbenchWindow() {
		return getDefault().getWorkbench().getActiveWorkbenchWindow();
	}
	
	public static IWorkbenchPage getActivePage() {
		IWorkbenchWindow window= getActiveWorkbenchWindow();
		if (window == null)
			return null;
		
		return window.getActivePage();
	}

	public static Shell getActiveWorkbenchShell() {
		 IWorkbenchWindow window= getActiveWorkbenchWindow();
		 if (window == null)
			 return null;
		 
		 return window.getShell();
	}
	
	public static IEditorPart getActiveEditor() {
		IWorkbenchPage page = getActivePage();
		IEditorPart part = page.getActiveEditor();
		if (!(part instanceof AbstractTextEditor))
			return null;
		return part;
	}
	
	/**
	 * Returns an array of all editors that have an unsaved content. If the identical content is 
	 * presented in more than one editor, only one of those editor parts is part of the result.
	 * 
	 * @return an array of all dirty editor parts.
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
//					IEditorPart editor= references[refIndex].getEditor(false);
//					if (editor != null)
//						result.add(editor);
//				}
//			}
//		}
//		return (IEditorPart[])result.toArray(new IEditorPart[result.size()]);
//	}

	/**
	 * Returns the string from the plugin's resource bundle,
	 * or 'key' if not found.
	 */
	public static String getResourceString(String key) {
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
	public ResourceBundle getResourceBundle() {
		return resourceBundle;
	}
	
	/**
	 * Return a scanner for creating java partitions.
	 */
	public ZPartitionScanner getZedPartitionScanner(String fileType) {
		if ((fileType == null) || fileType.equals("")) {
			return fZPartitionScanner_Default;
		}
		else if (fileType.equals(IZFileType.FILETYPE_LATEX)) {
			if (fZPartitionScanner_Latex == null)
				fZPartitionScanner_Latex = new ZPartitionScanner(IZFileType.FILETYPE_LATEX);
			return fZPartitionScanner_Latex;
		}
		else if (fileType.equals(IZFileType.FILETYPE_UTF8)) {
			if (fZPartitionScanner_Utf8 == null)
				fZPartitionScanner_Utf8 = new ZPartitionScanner(IZFileType.FILETYPE_UTF8);
			return fZPartitionScanner_Utf8;
		}
		else if (fileType.equals(IZFileType.FILETYPE_UTF16)) {
			if (fZPartitionScanner_Utf16 == null)
				fZPartitionScanner_Utf16 = new ZPartitionScanner(IZFileType.FILETYPE_UTF16);
			return fZPartitionScanner_Utf16;
		}
		else if (fileType.equals(IZFileType.FILETYPE_UTF16_BE)) {
			if (fZPartitionScanner_Utf16be == null)
				fZPartitionScanner_Utf16be = new ZPartitionScanner(IZFileType.FILETYPE_UTF16_BE);
			return fZPartitionScanner_Utf16be;
		}
		else if (fileType.equals(IZFileType.FILETYPE_UTF16_LE)) {
			if (fZPartitionScanner_Utf16le == null)
				fZPartitionScanner_Utf16le = new ZPartitionScanner(IZFileType.FILETYPE_UTF16_LE);
			return fZPartitionScanner_Utf16le;
		}
		else {
			return fZPartitionScanner_Default;
		}
	}
	
	/**
	 * Returns the singleton scanner.
	 */
	public RuleBasedScanner getZedCodeScanner() {
		if (fCodeScanner == null)
			fCodeScanner = new ZCodeScanner(getCZTColorManager());
		return fCodeScanner;
	}
	
	/**
	 * Returns the singleton color provider.
	 */
	public CZTColorManager getCZTColorManager() {
		if (fColorManager == null)
			fColorManager = new CZTColorManager();
		return fColorManager;
	}
	
	/**
	 * Returns an section manager for parsing and type checking
	 */
	public SectionManager getSectionManager() {
		if (this.fSectionManager == null) {
			System.out.println("Create a new section manager");
			this.fSectionManager = createSectionManager();
		}
//		this.fSectionManager.reset();
//		return this.fSectionManager;
		return (SectionManager)this.fSectionManager.clone();
	}
	
	private SectionManager createSectionManager() {
		SectionManager sectManager = new SectionManager();
		/**
		 * Initialize the section manager
		 */
		try {
			Source source = new StringSource("\\begin{zsection} "
				       + "\\SECTION ZEclipseDefault "
				       + "\\parents standard\\_toolkit "
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
}



