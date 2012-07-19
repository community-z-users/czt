
package net.sourceforge.czt.animation.common.adapter;

import java.beans.BeanDescriptor;
import java.beans.IntrospectionException;
import java.beans.PropertyDescriptor;
import java.beans.SimpleBeanInfo;

import sun.beans.editors.ColorEditor;
import sun.beans.editors.FontEditor;

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
      pds[0].setPropertyEditorClass(FontEditor.class);
      pds[1].setPropertyEditorClass(ColorEditor.class);
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
