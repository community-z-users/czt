/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.List;

import net.sourceforge.czt.eclipse.ui.internal.util.IColorManager;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.rules.IRule;

/**
 * @author Chengdong Xu
 *
 */
public class SingleTokenZScanner extends AbstractZCodeScanner
{
  
  private String[] fTokenProperties;
  
  /**
   * @param manager
   * @param store
   */
  public SingleTokenZScanner(IColorManager manager, IPreferenceStore store, String defaultProperty)
  {
    super(manager, store);
    fTokenProperties = new String[] { defaultProperty };
    initialize();
  }

  /*
   * @see net.sourceforge.czt.eclipse.ui.editors.AbstractZCodeScanner#getTokenProperties()
   */
  @Override
  protected String[] getTokenProperties()
  {
    return fTokenProperties;
  }

  /*
   * @see net.sourceforge.czt.eclipse.ui.editors.AbstractZCodeScanner#createRules()
   */
  @Override
  protected List<IRule> createRules()
  {
    setDefaultReturnToken(getToken(fTokenProperties[0]));
    return null;
  }

}
