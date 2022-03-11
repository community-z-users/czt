package net.sourceforge.czt.eclipse.ui.internal.editors.zeditor;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.ResourceBundle;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ZCompiler;
import net.sourceforge.czt.parser.util.CztErrorImpl;
import net.sourceforge.czt.parser.util.LocInfoImpl;

/**
 * This class encapsulates functionality directly related to storing and synchronizing
 * Z editor model. Z Editor contents are represented as a parsed and typechecked CZT
 * AST, encapsulated in a {@link ParsedData} structure.
 * 
 * The model allows executing reconcile of the text-to-model. It tracks document versions
 * which are incremented via {@link #incrementDocumentVersion()} (e.g. by the editor upon
 * document change). Since multiple threads can execute {@link #reconcile()}, there
 * is synchronization with document versions to avoid that - reconcile is done only
 * once for a particular document version.
 * 
 * @author Andrius Velykis
 */
public class ZEditorModel
{

  private final ZEditor editor;

  /**
   * A lock to synchronize read and write of model data (i.e. versions and parsedData).
   */
  private final ReadWriteLock lock = new ReentrantReadWriteLock(true);
  
  /**
   * The version of the currently edited document. This version is being incremented 
   * with each edit and is used as a baseline to check whether the underlying 
   * ParsedData model matches the document. The version is used by the parser to 
   * tag the model (ParsedData) version.
   */
  private BigInteger documentVersion;
  
  /**
   * The currently executing (or last executed) reconcile version. This is used to
   * prevent multiple reconcile runs for the same document version. Note that
   * documentVersion >= reconcilingVersion >= parsedData.getDocumentVersion(). 
   */
  private BigInteger reconcilingVersion;
  
  /**
   * Reconcile results as the parsed AST
   */
  private ParsedData parsedData;
  
  public ZEditorModel(ZEditor editor)
  {
    super();
    this.editor = editor;
    
    // Initialize parsed data with version ZERO, and mark the document version as ONE
    // This means that initial reconcile is required and is not done in the constructor
    BigInteger initialVersion = BigInteger.ZERO; 
    this.reconcilingVersion = initialVersion;
    this.parsedData = emptyData(initialVersion);
    this.documentVersion = initialVersion.add(BigInteger.ONE);
  }
  
  private ParsedData emptyData(BigInteger version) {
    return new ParsedData(version, CztUIPlugin.getDefault().getSectionManager());
  }
  
  private void setParsedData(ParsedData parsedData) {
    writeLock().lock();
    
    if (parsedData.getDocumentVersion().compareTo(this.parsedData.getDocumentVersion()) <= 0) {
      // this parsed data is out-of-date: reconcile of a newer parsed data has been completed,
      // therefore just throw this away
      return;
    }
    
    this.parsedData = parsedData;
    writeLock().unlock();
  }
  
  public ParsedData getParsedData() {
    readLock().lock();
    try {
      return this.parsedData;
    } finally {
      readLock().unlock();
    }
  }
  
  private Lock readLock() {
    return lock.readLock();
  }
  
  private Lock writeLock() {
    return lock.writeLock();
  }
  
  public void reconcile() {
    
    readLock().lock();
    
    try {
      
      if (!needReconcile()) {
        return;
      }
      
    } finally {
      readLock().unlock();
    }

    BigInteger version;
    
    /*
     * Now capture the write lock to set the reconciling version. Note that
     * the lock used here does not allow to upgrade read lock to write lock,
     * therefore we released the read lock and check the condition again
     * in the write lock.
     */
    writeLock().lock();
    
    try {
      
      if (!needReconcile()) {
        // conditions have changed - another reconcile has been started
        // so just ignore this one
        return;
      }
      
      // mark that we are reconciling the current document version
      version = documentVersion;
      this.reconcilingVersion = version;
      
    } finally {
      writeLock().unlock();
    }
    
    ParsedData newData = safeParse(version);
    setParsedData(newData);
  }
  
  private ParsedData safeParse(BigInteger version) {
    
    // to avoid CZT errors crashing the system (e.g. stack overflow for section parents)
    // we try and catch all Throwables, but maybe relax this and use SafeRunner in
    // the future
    try {
      return ZCompiler.INSTANCE.parse(editor, version);
    } catch (Throwable e) {
      CztUIPlugin.log("Error in CZT during reconcile: " + e.getMessage(), e);
      
      // still return an empty parsed data with correct version
      ParsedData parsedData = emptyData(version);
      // set the caught error to the parsed data - it should be displayed to the user then
      parsedData.setErrors(Arrays.asList(
          new ZCompilerError("Error in Z compiler: " + e.getMessage())));
      return parsedData;
    }
  }
  
  /*
   * Checks if document version is newer than the currently reconciling 
   * one (already reconciled one). If not, it means we do not need to do 
   * another reconcile - it has already finished or is happening at 
   * the moment.
   */
  private boolean needReconcile() {
    return documentVersion.compareTo(reconcilingVersion) > 0;
  }
  
  public BigInteger getDocumentVersion() {
    readLock().lock();
    try {
      return this.documentVersion;
    } finally {
      readLock().unlock();
    }
  }
  
  public void incrementDocumentVersion() {
    writeLock().lock();
    try {
      this.documentVersion = this.documentVersion.add(BigInteger.ONE);
    } finally {
      writeLock().unlock();
    }
  }
  
  /**
   * A CZT error to store unexpected compiler errors. For that reason,
   * its location is 0,0.
   * 
   * @author Andrius Velykis
   */
  private static class ZCompilerError extends CztErrorImpl
  {
    
    public ZCompilerError(String message)
    {
    	// TODO: Andrius is this okay? (Leo)
      super(CztUIPlugin.getDefault().getSectionManager(), message, new Object[0], 
    		  new LocInfoImpl(CztUIPlugin.getDefault().getSectionManager().getDialect(), null, 0, 0));
    }

    @Override
    public String getMessage()
    {
      return getMessageKey();
    }

    @Override
    protected ResourceBundle getResourceBundle()
    {
      throw new UnsupportedOperationException();
    }
  }
  
}
