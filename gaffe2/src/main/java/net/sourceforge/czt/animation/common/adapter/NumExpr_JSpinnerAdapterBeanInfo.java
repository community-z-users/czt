
package net.sourceforge.czt.animation.common.adapter;

import java.beans.BeanDescriptor;
import java.beans.IntrospectionException;
import java.beans.PropertyDescriptor;
import java.beans.SimpleBeanInfo;

// Correct path, but it no longer builds under Maven and Java 8! e.g. see bug JDK-6778491:
// http://bugs.java.com/bugdatabase/view_bug.do?bug_id=6778491
// FIXME Thus commenting out to enable compilation - is anyone using this?
// import com.sun.beans.editors.ColorEditor;
// import com.sun.beans.editors.FontEditor;

/**
 * @author Linan Zhang
 *
 */
public class NumExpr_JSpinnerAdapterBeanInfo extends SimpleBeanInfo
{
  PropertyDescriptor[] pds = new PropertyDescriptor[2];     // Bean Property Descriptor

  /**
   * Constructor
   */
  public NumExpr_JSpinnerAdapterBeanInfo()
  {
    super();
  }

  /* (non-Javadoc)
   * @see java.beans.BeanInfo#getPropertyDescriptors()
   */
  public PropertyDescriptor[] getPropertyDescriptors()
  {
    try {

      pds[0] = new PropertyDescriptor("font", NumExpr_JSpinnerAdapter.class);
      pds[1] = new PropertyDescriptor("background",
          NumExpr_JSpinnerAdapter.class);
      // FIXME commented out as does not compile under Java 8!
//      pds[0].setPropertyEditorClass(FontEditor.class);
//      pds[1].setPropertyEditorClass(ColorEditor.class);
      pds[0].setBound(true);
      pds[1].setBound(true);
      return pds;
    } catch (IntrospectionException ie) {
      ie.printStackTrace();
      return null;
    }
  }

  /* (non-Javadoc)
   * @see java.beans.BeanInfo#getBeanDescriptor()
   */
  public BeanDescriptor getBeanDescriptor()
  {
    return new BeanDescriptor(NumExpr_JSpinnerAdapter.class);
  }
}
