package czt.animation.gui.design;

import java.util.EventObject;

class BeanSelectedEvent extends EventObject {
  private Object bean;
  //XXX should it have the beanwrapper/component for the bean as well as/instead of the bean.
  public BeanSelectedEvent(FormDesign beansForm, Object selectedBean) {
    super(beansForm);
    bean=selectedBean;
  };
  
  public FormDesign getSelectedBeansForm() {
    return (FormDesign)getSource();
  };
  public Object getSelectedBean() {
    return bean;
  };
};
