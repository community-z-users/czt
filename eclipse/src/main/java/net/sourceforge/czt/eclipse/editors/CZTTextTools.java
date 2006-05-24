package net.sourceforge.czt.eclipse.editors;

import net.sourceforge.czt.eclipse.editors.latex.ZLatexCodeScanner;
import net.sourceforge.czt.eclipse.editors.latex.ZLatexPartitionScanner;
import net.sourceforge.czt.eclipse.editors.unicode.ZUnicodeCodeScanner;
import net.sourceforge.czt.eclipse.editors.unicode.ZUnicodePartitionScanner;
import net.sourceforge.czt.eclipse.util.CZTColorManager;
import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.core.runtime.Preferences;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.DefaultPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;

/**
 * Tools required to configure a CZT editor.
 * The color manager and all scanner exist only one time, i.e.
 * the same instances are returned to all clients. Thus, clients
 * share those tools.
 * <p>
 * This class may be instantiated; it is not intended to be subclassed.
 * </p>
 */
public class CZTTextTools {
	/**
	 * Array with legal content types.
	 * @since 3.0
	 */
	private final static String[] LEGAL_CONTENT_TYPES= new String[] {
		IZPartitions.JAVA_DOC,
		IZPartitions.JAVA_MULTI_LINE_COMMENT,
		IZPartitions.JAVA_SINGLE_LINE_COMMENT,
		IZPartitions.JAVA_STRING,
		IZPartitions.JAVA_CHARACTER
	};

	/**
	 * This tools' preference listener.
	 */
	private class PreferenceListener implements IPropertyChangeListener, Preferences.IPropertyChangeListener {
		public void propertyChange(PropertyChangeEvent event) {
//			adaptToPreferenceChange(event);
		}
		public void propertyChange(Preferences.PropertyChangeEvent event) {
//			adaptToPreferenceChange(new PropertyChangeEvent(event.getSource(), event.getProperty(), event.getOldValue(), event.getNewValue()));
		}
	}

	/** The color manager. */
	private CZTColorManager fColorManager;
	/** The Z source code scanner for latex encoding. */
	private RuleBasedScanner fZLatexCodeScanner;
	/** The Z source code scanner for UTF-8 and UTF-16 encoding. */
	private RuleBasedScanner fZUnicodeCodeScanner;
	/** The Java string scanner. */
//	private SingleTokenJavaScanner fStringScanner;
	/** The Java partitions scanner. */
//	private FastJavaPartitionScanner fPartitionScanner;
	private RuleBasedPartitionScanner fZDefaultPartitionScanner;
	private RuleBasedPartitionScanner fZLatexPartitionScanner;
	private RuleBasedPartitionScanner fZUnicodePartitionScanner;
	/** The preference store. */
	private IPreferenceStore fPreferenceStore;
	/**
	 * The core preference store.
	 * @since 2.1
	 */
	private Preferences fCorePreferenceStore;
	/** The preference change listener */
	private PreferenceListener fPreferenceListener= new PreferenceListener();


	/**
	 * Creates a new Java text tools collection.
	 *
	 * @param store the preference store to initialize the text tools. The text tool
	 *			instance installs a listener on the passed preference store to adapt itself to
	 *			changes in the preference store. In general <code>PreferenceConstants.
	 *			getPreferenceStore()</code> should be used to initialize the text tools.
	 * @see org.eclipse.jdt.ui.PreferenceConstants#getPreferenceStore()
	 * @since 2.0
	 */
	public CZTTextTools(IPreferenceStore store) {
		this(store, null, true);
	}

	/**
	 * Creates a new Java text tools collection.
	 *
	 * @param store the preference store to initialize the text tools. The text tool
	 *			instance installs a listener on the passed preference store to adapt itself to
	 *			changes in the preference store. In general <code>PreferenceConstants.
	 *			getPreferenceStore()</code> should be used to initialize the text tools.
	 * @param autoDisposeOnDisplayDispose if <code>true</code>  the color manager
	 *			automatically disposes all managed colors when the current display gets disposed
	 *			and all calls to {@link org.eclipse.jface.text.source.ISharedTextColors#dispose()} are ignored.
	 * @see org.eclipse.jdt.ui.PreferenceConstants#getPreferenceStore()
	 * @since 2.1
	 */
	public CZTTextTools(IPreferenceStore store, boolean autoDisposeOnDisplayDispose) {
		this(store, null, autoDisposeOnDisplayDispose);
	}

	/**
	 * Creates a new Java text tools collection.
	 * @param store the preference store to initialize the text tools. The text tool
	 *			instance installs a listener on the passed preference store to adapt itself to
	 *			changes in the preference store. In general <code>PreferenceConstants.
	 *			getPreferenceStore()</code> should be used to initialize the text tools.
	 * @param coreStore optional preference store to initialize the text tools. The text tool
	 *			instance installs a listener on the passed preference store to adapt itself to
	 *			changes in the preference store.
	 * @see org.eclipse.jdt.ui.PreferenceConstants#getPreferenceStore()
	 * @since 2.1
	 */
	public CZTTextTools(IPreferenceStore store, Preferences coreStore) {
		this(store, coreStore, true);
	}

	/**
	 * Creates a new Java text tools collection.
	 *
	 * @param store the preference store to initialize the text tools. The text tool
	 *			instance installs a listener on the passed preference store to adapt itself to
	 *			changes in the preference store. In general <code>PreferenceConstants.
	 *			getPreferenceStore()</code> should be used to initialize the text tools.
	 * @param coreStore optional preference store to initialize the text tools. The text tool
	 *			instance installs a listener on the passed preference store to adapt itself to
	 *			changes in the preference store.
	 * @param autoDisposeOnDisplayDispose 	if <code>true</code>  the color manager
	 *			automatically disposes all managed colors when the current display gets disposed
	 *			and all calls to {@link org.eclipse.jface.text.source.ISharedTextColors#dispose()} are ignored.
	 * @see org.eclipse.jdt.ui.PreferenceConstants#getPreferenceStore()
	 * @since 2.1
	 */
	public CZTTextTools(IPreferenceStore store, Preferences coreStore, boolean autoDisposeOnDisplayDispose) {
		fPreferenceStore= store;
		fPreferenceStore.addPropertyChangeListener(fPreferenceListener);

		fCorePreferenceStore= coreStore;
		if (fCorePreferenceStore != null)
			fCorePreferenceStore.addPropertyChangeListener(fPreferenceListener);

//		fColorManager= new CZTColorManager(autoDisposeOnDisplayDispose);
		fColorManager= new CZTColorManager();
		fZLatexCodeScanner= new ZLatexCodeScanner(fColorManager);
		fZUnicodeCodeScanner = new ZUnicodeCodeScanner(fColorManager);
		fZDefaultPartitionScanner= new RuleBasedPartitionScanner();
		fZLatexPartitionScanner= new ZLatexPartitionScanner();
		fZUnicodePartitionScanner= new ZUnicodePartitionScanner();
	}

	/**
	 * Disposes all the individual tools of this tools collection.
	 */
	public void dispose() {

		fZLatexCodeScanner= null;
		fZUnicodeCodeScanner = null;
		fZDefaultPartitionScanner = null;
		fZLatexPartitionScanner = null;
		fZUnicodePartitionScanner = null;
//		fMultilineCommentScanner= null;
//		fSinglelineCommentScanner= null;
//		fStringScanner= null;
//		fJavaDocScanner= null;
//		fPartitionScanner= null;

		if (fColorManager != null) {
			fColorManager.dispose();
			fColorManager= null;
		}

		if (fPreferenceStore != null) {
			fPreferenceStore.removePropertyChangeListener(fPreferenceListener);
			fPreferenceStore= null;

			if (fCorePreferenceStore != null) {
				fCorePreferenceStore.removePropertyChangeListener(fPreferenceListener);
				fCorePreferenceStore= null;
			}

			fPreferenceListener= null;
		}
	}

	/**
	 * Returns the color manager which is used to manage
	 * any Java-specific colors needed for such things like syntax highlighting.
	 *
	 * @return the color manager to be used for Java text viewers
	 */
	public CZTColorManager getColorManager() {
		return fColorManager;
	}
	
	/**
	 * Returns a scanner which is configured to scan Z source code.
	 *
	 * @return a Z source code scanner
	 * @deprecated As of 3.0, replaced by {@link JavaSourceViewerConfiguration#getCodeScanner()}
	 */
	public RuleBasedScanner getZCodeScanner(String fileType) {
		if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(fileType))
			return fZLatexCodeScanner;
		else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(fileType)
				|| IZFileType.FILETYPE_UTF16.equalsIgnoreCase(fileType))
			return fZUnicodeCodeScanner;
		else
			return null;
	}
	/**
	 * Returns a scanner which is configured to scan
	 * Z-specific partitions.
	 *
	 * @return a Z partition scanner
	 */
	public IPartitionTokenScanner getPartitionScanner(String fileType) {
		if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(fileType))
			return fZLatexPartitionScanner;
		else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(fileType)
				|| IZFileType.FILETYPE_UTF16.equalsIgnoreCase(fileType))
			return fZUnicodePartitionScanner;
		else
			return fZDefaultPartitionScanner;
	}

	/**
	 * Factory method for creating a Z-specific document partitioner
	 * using this object's partitions scanner. This method is a
	 * convenience method.
	 *
	 * @return a newly created Java document partitioner
	 */
	public IDocumentPartitioner createDocumentPartitioner(String fileType) {
		return new FastPartitioner(getPartitionScanner(fileType), LEGAL_CONTENT_TYPES);
	}

	/**
	 * Determines whether the preference change encoded by the given event
	 * changes the behavior of one its contained components.
	 *
	 * @param event the event to be investigated
	 * @return <code>true</code> if event causes a behavioral change
	 * @since 2.0
	 * @deprecated As of 3.0, replaced by {@link org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration#affectsTextPresentation(PropertyChangeEvent)}
	 */
/*	public boolean affectsBehavior(PropertyChangeEvent event) {
		return  fLatexCodeScanner.affectsBehavior(event) ||
					fMultilineCommentScanner.affectsBehavior(event) ||
					fSinglelineCommentScanner.affectsBehavior(event) ||
					fStringScanner.affectsBehavior(event) ||
					fJavaDocScanner.affectsBehavior(event);
	}
*/
	/**
	 * Adapts the behavior of the contained components to the change
	 * encoded in the given event.
	 *
	 * @param event the event to which to adapt
	 * @since 2.0
	 * @deprecated As of 3.0, no replacement
	 */
/*	protected void adaptToPreferenceChange(PropertyChangeEvent event) {
		if (fLatexCodeScanner.affectsBehavior(event))
			fLatexCodeScanner.adaptToPreferenceChange(event);
		if (fMultilineCommentScanner.affectsBehavior(event))
			fMultilineCommentScanner.adaptToPreferenceChange(event);
		if (fSinglelineCommentScanner.affectsBehavior(event))
			fSinglelineCommentScanner.adaptToPreferenceChange(event);
		if (fStringScanner.affectsBehavior(event))
			fStringScanner.adaptToPreferenceChange(event);
		if (fJavaDocScanner.affectsBehavior(event))
			fJavaDocScanner.adaptToPreferenceChange(event);
	}
*/
	/**
	 * Sets up the Java document partitioner for the given document for the default partitioning.
	 *
	 * @param document the document to be set up
	 * @since 3.0
	 */
	public void setupJavaDocumentPartitioner(IDocument document, String fileType) {
		setupJavaDocumentPartitioner(document, IDocumentExtension3.DEFAULT_PARTITIONING, fileType);
	}

	/**
	 * Sets up the Java document partitioner for the given document for the given partitioning.
	 *
	 * @param document the document to be set up
	 * @param partitioning the document partitioning
	 * @since 3.0
	 */
	public void setupJavaDocumentPartitioner(IDocument document, String partitioning, String fileType) {
		IDocumentPartitioner partitioner= createDocumentPartitioner(fileType);
		if (document instanceof IDocumentExtension3) {
			IDocumentExtension3 extension3= (IDocumentExtension3) document;
			extension3.setDocumentPartitioner(partitioning, partitioner);
		} else {
			document.setDocumentPartitioner(partitioner);
		}
		partitioner.connect(document);
	}

	/**
	 * Returns this text tool's preference store.
	 *
	 * @return the preference store
	 * @since 3.0
	 */
	protected IPreferenceStore getPreferenceStore() {
		return fPreferenceStore;
	}

	/**
	 * Returns this text tool's core preference store.
	 *
	 * @return the core preference store
	 * @since 3.0
	 */
	protected Preferences getCorePreferenceStore() {
		return fCorePreferenceStore;
	}
}
