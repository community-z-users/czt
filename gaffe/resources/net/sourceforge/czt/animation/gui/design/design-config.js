importClass(java.lang.System);
importClass(java.beans.Introspector);
importClass(Packages.net.sourceforge.czt.animation.gui.util.IntrospectionHelper);

System.err.println("In the distribution config file...");
//Utility functions for working on BeanInfos
function forPropertyDescriptor(theClass, theProperty, toRun) {
  try {
    var bi=Introspector.getBeanInfo(theClass);
    IntrospectionHelper.rememberBeanInfo(bi);
    var pds=bi.getPropertyDescriptors();
    for(var i=0;i<pds.length;i++)
      if(pds[i].name==theProperty) toRun(pds[i]);
  } catch(ex) {
    System.err.println("Warning: could not get property descriptor for "+theClass+"."
		       +theProperty+".");
    System.err.println(ex);
  }
}
function forEventSetDescriptor(theClass, theListenerType, toRun) {
  try {
    var bi=Introspector.getBeanInfo(theClass);
    IntrospectionHelper.rememberBeanInfo(bi);
    var esds=bi.getEventSetDescriptors();
    for(var i=0;i<esds.length;i++)
      if(esds[i].listenerType==theListenerType) toRun(esds[i]);
  } catch(ex) {
    System.err.println("Warning: could not get event set descriptor for "+theClass+"."
		       +theListenerType+".");
    System.err.println(ex);
  }
}
function forBeanDescriptor(theClass, toRun) {
  try {
    var bi=Introspector.getBeanInfo(theClass);
    IntrospectionHelper.rememberBeanInfo(bi);
    toRun(bi.getBeanDescriptor());
  } catch (ex) {
    System.err.println("Warning: could not get bean descriptor for "+theClass+".");
    System.err.println(ex);
  }
}
function setHidden(descriptor) {descriptor.hidden=true;};
function setExpert(descriptor) {descriptor.expert=true;};
function setPreferred(descriptor) {descriptor.preferred=true;};

function setAttribute(attribute,value) {  
  return function(descriptor) {descriptor.setValue(attribute,value);};
};
setTransient=setAttribute("transient",true);


//Setting attributes on descriptors from BeanInfos.
importPackage(Packages.net.sourceforge.czt.animation.gui.beans);
forPropertyDescriptor(FormFiller,"beanContext",setTransient);
forPropertyDescriptor(FormFiller,"beanContextChildPeer",setTransient);

importClass(Packages.net.sourceforge.czt.animation.gui.Form);
forPropertyDescriptor(Form,"bounds",setTransient);
forPropertyDescriptor(Form,"border",setTransient);
forPropertyDescriptor(Form,"x",setTransient);
forPropertyDescriptor(Form,"y",setTransient);
forPropertyDescriptor(Form,"location",setTransient);



importClass(java.beans.beancontext.BeanContextProxy);
forPropertyDescriptor(BeanContextProxy,"beanContextProxy",setHidden);

importClass(java.beans.beancontext.BeanContextChild);
forPropertyDescriptor(BeanContextChild,"beanContext",setHidden);
importClass(java.beans.beancontext.BeanContextChildSupport);
forPropertyDescriptor(BeanContextChildSupport,"beanContext",setHidden);
forPropertyDescriptor(BeanContextChildSupport,"beanContextChildPeer",setHidden);
forPropertyDescriptor(BeanContextChildSupport,"class",setHidden);
forPropertyDescriptor(BeanContextChildSupport,"delegated",setHidden);

//Setting Persistence Delegates.
importPackage(Packages.net.sourceforge.czt.animation.gui.persistence.delegates);
BeanLinkDelegate.registerDelegate();
BeanWrapperDelegate.registerDelegate();
FormDelegate.registerDelegate();

//Setting Property Editors
importClass(java.beans.PropertyEditorManager);
importPackage(Packages.net.sourceforge.czt.animation.gui.design.properties.editors);
PropertyEditorManager.registerEditor(java.awt.Color, ColorEditor);

//Setting Propert Renderers
importClass(Packages.net.sourceforge.czt.animation.gui.design.properties.PropertiesWindow);
importPackage(Packages.net.sourceforge.czt.animation.gui.design.properties.renderers);
PropertiesWindow.addDefaultRenderer(java.awt.Color, new ColorRenderer());
PropertiesWindow.addDefaultRenderer(java.awt.Font, new FontRenderer());

System.err.println("...Finished the distribution config file.");

