
package net.sourceforge.czt.eclipse.ui.internal.editors;

import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.internal.editors.latex.ZLatexPartitionScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.unicode.ZUnicodePartitionScanner;
import net.sourceforge.czt.eclipse.ui.internal.util.CZTColorManager;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;

/**
 * Tools required to configure a Z fEditor.
 * The color manager and all scanner exist only one time, i.e.
 * the same instances are returned to all clients. Thus, clients
 * share those tools.
 * <p>
 * This class may be instantiated; it is not intended to be subclassed.
 * </p>
 * 
 * @author Chengdong Xu
 */
public class CZTTextTools
{
  /**
   * Array with legal latex content types.
   */
  private static final String[] LEGAL_CONTENT_TYPES_LATEX = new String[]{
      IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR,
      IZPartitions.Z_PARAGRAPH_LATEX_ZED,
      IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION,
      IZPartitions.Z_PARAGRAPH_LATEX_AXDEF,
      IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA,
      IZPartitions.Z_PARAGRAPH_LATEX_GENAX,
      IZPartitions.Z_PARAGRAPH_LATEX_THEOREM,
      IZPartitions.Z_PARAGRAPH_LATEX_PROOFSCRIPT};

  /**
   * Array with legal unicode content types.
   */
  private static final String[] LEGAL_CONTENT_TYPES_UNICODE = new String[]{
      IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION,
      IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF,
      IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA,
      IZPartitions.Z_PARAGRAPH_UNICODE_GENAX,
      IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH,
      IZPartitions.Z_PARAGRAPH_UNICODE_PROOFSCRIPT};
  
  /**
   * Array with legai default content types.
   */
  private static final String[] LEGAL_CONTENT_TYPES_DEFAULT = new String[] {
    
  };

  /**
   * This tools' preference listener.
   */
@SuppressWarnings("deprecation")
private class PreferenceListener
      implements
        IPropertyChangeListener,
        // TODO: FIX THIS AND ALL OTHER DEPRECATED STUFF 
        org.eclipse.core.runtime.Preferences.IPropertyChangeListener
  {
    public void propertyChange(PropertyChangeEvent event)
    {
      //			adaptToPreferenceChange(event);
    }

    public void propertyChange(org.eclipse.core.runtime.Preferences.PropertyChangeEvent event)
    {
      //			adaptToPreferenceChange(new PropertyChangeEvent(event.getSource(), event.getProperty(), event.getOldValue(), event.getNewValue()));
    }
  }

  /** The color manager. */
  private CZTColorManager fColorManager;

  /** The Z source code scanner for latex encoding. */
  private RuleBasedScanner fZLatexCodeScanner;

  /** The Z source code scanner for UTF-8 and UTF-16 encoding. */
  private RuleBasedScanner fZUnicodeCodeScanner;


  /** The Z default partitions scanner. */
  private RuleBasedPartitionScanner fZDefaultPartitionScanner;
  
  /** The Z latex partitions scanner. */
  private RuleBasedPartitionScanner fZLatexPartitionScanner;
  
  /** The Z unicode partitions scanner. */
  private RuleBasedPartitionScanner fZUnicodePartitionScanner;

  /** The preference store. */
  private IPreferenceStore fPreferenceStore;

  /**
   * The core preference store.
   */
  @SuppressWarnings("deprecation")
private org.eclipse.core.runtime.Preferences fCorePreferenceStore;

  /** The preference change listener */
  private PreferenceListener fPreferenceListener = new PreferenceListener();

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
  public CZTTextTools(IPreferenceStore store)
  {
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
  public CZTTextTools(IPreferenceStore store,
      boolean autoDisposeOnDisplayDispose)
  {
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
  public CZTTextTools(IPreferenceStore store, @SuppressWarnings("deprecation") org.eclipse.core.runtime.Preferences coreStore)
  {
    this(store, coreStore, true);
  }

  /**
   * Creates a new CZT text tools collection.
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
   * @see net.sourceforge.czt.eclipse.ui.internal.preferences.PreferenceConstants#getPreferenceStore()
   * @since 2.1
   */
  @SuppressWarnings("deprecation")
public CZTTextTools(IPreferenceStore store, org.eclipse.core.runtime.Preferences coreStore,
      boolean autoDisposeOnDisplayDispose)
  {
    fPreferenceStore = store;
    fPreferenceStore.addPropertyChangeListener(fPreferenceListener);

    fCorePreferenceStore = coreStore;
    if (fCorePreferenceStore != null)
      fCorePreferenceStore.addPropertyChangeListener(fPreferenceListener);

    //		fColorManager= new CZTColorManager(autoDisposeOnDisplayDispose);
    fColorManager = new CZTColorManager();
//    fZLatexCodeScanner = new ZLatexCodeScanner(fColorManager);
//    fZUnicodeCodeScanner = new ZUnicodeCodeScanner(fColorManager);
    fZDefaultPartitionScanner = new RuleBasedPartitionScanner();
    fZLatexPartitionScanner = new ZLatexPartitionScanner();
    fZUnicodePartitionScanner = new ZUnicodePartitionScanner();
  }

  /**
   * Disposes all the individual tools of this tools collection.
   */
  @SuppressWarnings("deprecation")
public void dispose()
  {

    fZLatexCodeScanner = null;
    fZUnicodeCodeScanner = null;
    fZDefaultPartitionScanner = null;
    fZLatexPartitionScanner = null;
    fZUnicodePartitionScanner = null;

    if (fColorManager != null) {
      fColorManager.dispose();
      fColorManager = null;
    }

    if (fPreferenceStore != null) {
      fPreferenceStore.removePropertyChangeListener(fPreferenceListener);
      fPreferenceStore = null;

      if (fCorePreferenceStore != null) {
        fCorePreferenceStore.removePropertyChangeListener(fPreferenceListener);
        fCorePreferenceStore = null;
      }

      fPreferenceListener = null;
    }
  }

  /**
   * Returns the color manager which is used to manage
   * any Java-specific colors needed for such things like syntax highlighting.
   *
   * @return the color manager to be used for Java text viewers
   */
  public CZTColorManager getColorManager()
  {
    return fColorManager;
  }

  /**
   * Returns a scanner which is configured to scan Z source code.
   *
   * @return a Z source code scanner
   */
  public RuleBasedScanner getZCodeScanner(String fileType)
  {
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
  public IPartitionTokenScanner getPartitionScanner(String fileType)
  {
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
  public IDocumentPartitioner createDocumentPartitioner(String fileType)
  {
    if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(fileType))
      return new FastPartitioner(fZLatexPartitionScanner, LEGAL_CONTENT_TYPES_LATEX);
    else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(fileType)
        || IZFileType.FILETYPE_UTF16.equalsIgnoreCase(fileType))
      return new FastPartitioner(fZUnicodePartitionScanner, LEGAL_CONTENT_TYPES_UNICODE);
    else
      return new FastPartitioner(fZDefaultPartitionScanner, LEGAL_CONTENT_TYPES_DEFAULT);
  }
  
  /**
   * Sets up the Java document partitioner for the given document for the default partitioning.
   *
   * @param document the document to be set up
   * @since 3.0
   */
  public void setupCZTDocumentPartitioner(IDocument document, String fileType)
  {
    setupCZTDocumentPartitioner(document,
        IDocumentExtension3.DEFAULT_PARTITIONING, fileType);
  }

  /**
   * Sets up the Java document partitioner for the given document for the given partitioning.
   *
   * @param document the document to be set up
   * @param partitioning the document partitioning
   * @since 3.0
   */
  public void setupCZTDocumentPartitioner(IDocument document,
      String partitioning, String fileType)
  {
    IDocumentPartitioner partitioner = createDocumentPartitioner(fileType);
    if (document instanceof IDocumentExtension3) {
      IDocumentExtension3 extension3 = (IDocumentExtension3) document;
      extension3.setDocumentPartitioner(partitioning, partitioner);
    }
    else {
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
  protected IPreferenceStore getPreferenceStore()
  {
    return fPreferenceStore;
  }

  /**
   * Returns this text tool's core preference store.
   *
   * @return the core preference store
   * @since 3.0
   */
  @SuppressWarnings("deprecation")
protected org.eclipse.core.runtime.Preferences getCorePreferenceStore()
  {
    return fCorePreferenceStore;
  }
  
  public ITypedRegion getPartition(IDocument document, int offset, String partitioning) {
    if (document == null || offset < 0)
      return null;
    
    ITypedRegion partition = null;
    
    try {
      if (document instanceof IDocumentExtension3) {
        IDocumentExtension3 extension3 = (IDocumentExtension3) document;
        try {
          partition = extension3.getPartition(partitioning, offset,
              false);
        } catch (BadPartitioningException be) {
          partition = null;
        }
      }
      else
        partition = document.getPartition(offset);
    } catch (BadLocationException ble) {
      partition = null;
    }
    
    return partition;
  }
  
  public ITypedRegion[] getPartitions(IDocument document, String partitioning) {
    ITypedRegion[] partitions = null;
    try {
      if (document instanceof IDocumentExtension3) {
        IDocumentExtension3 extension3 = (IDocumentExtension3) document;
        partitions = extension3.computePartitioning(partitioning,
            0, document.getLength(), false);
      }
      else {
        partitions = document.computePartitioning(0, document.getLength());
      }
    } catch (BadLocationException ble) {
      partitions = null;
    } catch (BadPartitioningException bpe) {
      partitions = null;
    }
    
    return partitions;
  }
}
