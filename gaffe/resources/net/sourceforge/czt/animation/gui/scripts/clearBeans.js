java.lang.System.err.println("Loading clearBeans...");
function clearBeans(form) {
  if(form==null) return;
  
  importClass(java.awt.Component);
  importClass(java.awt.Label);
  importClass(java.awt.TextComponent);
  importClass(Packages.javax.swing.JLabel);
  importClass(Packages.javax.swing.JTable);
  importClass(Packages.javax.swing.text.JTextComponent);
  importClass(Packages.net.sourceforge.czt.animation.ZLocator);

  importPackage(Packages.net.sourceforge.czt.animation.gui.beans.table);
  importPackage(Packages.net.sourceforge.czt.animation.gui.temp);

  function clearBean(component) {
    if(component instanceof TextComponent || component instanceof JTextComponent
       || component instanceof Label || component instanceof JLabel)
      component.setText("");
    else if(component instanceof JTable)
      if(component.model instanceof RelationModel)     component.model.relation=null;
      else if(component.model instanceof BindingModel) component.model.binding=null;
    //XXX Fill in here for more types of components.
  };
  
  var beans=form.beans;
  for(var i in beans) {
    //Only interested in Components, with a name that we can use.
    //A name with a ' ' in can't be a valid Z name, so the last test means that any component that should
    //not be affected can be protected by putting a ' ' in its name.
    if(beans[i] instanceof Component && beans[i].name!=null && beans[i].name.indexOf(' ')<0)
      clearBean(beans[i]);
  }
};
  

