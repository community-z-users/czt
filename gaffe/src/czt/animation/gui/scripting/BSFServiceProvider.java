package czt.animation.gui.scripting;
import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServices;
import com.ibm.bsf.BSFManager;
import java.util.Iterator;

/**
 * Provides access to scripting with the BSF manager via bean contexts.
 */
public final class BSFServiceProvider implements BeanContextServiceProvider {
  /**
   * The BSFManager to provide.
   */
  protected BSFManager bsfManager;
  /**
   * Create a BSFServiceProvider.
   * @param bsfm The BSFManager to use.
   */
  public BSFServiceProvider(BSFManager bsfm) {bsfManager=bsfm;};
  
  /**
   * Returns the BSFManager.  Inherits from BeanContextServiceProvider.
   */
  public Object getService(BeanContextServices bcs, Object requestor, 
			   Class serviceClass, Object serviceSelector) {
    return bsfManager;
  };

  /**
   * Does Nothing.  Required because inherited from BeanContextServiceProvider.
   */
  public void releaseService(BeanContextServices bcs, Object requestor, Object service) {
    //do nothing
  };  

  /**
   * Does Nothing.  Required because inherited from BeanContextServiceProvider.
   */
  public Iterator getCurrentServiceSelectors(BeanContextServices bcs, Class serviceClass) {
    //do nothing
    return null;
  };
};
