java.lang.System.err.println("Loading clearBeans...");
function clearBeans(form) {
  if(form==null) return;
  
  importClass(java.awt.Label);
  importClass(java.awt.TextComponent);
  importClass(Packages.javax.swing.JLabel);
  importClass(Packages.javax.swing.JTable);
  importClass(Packages.javax.swing.text.JTextComponent);
  importPackage(Packages.net.sourceforge.czt.animation.gui.beans.table);
  importPackage(Packages.net.sourceforge.czt.animation.gui.temp);

  function clearBean(component) {
    if(component instanceof TextComponent || component instanceof JTextComponent
       || component instanceof Label || component instanceof JLabel)
      component.text="";
    else if(component instanceof JTable)
      if(component.model instanceof RelationModel)     component.model.relation=null;
      else if(component.model instanceof BindingModel) component.model.binding=null;
    //XXX Fill in here for more types of components.
  };
  
  var beans=form.components;
  for(var i in beans) {
    clearBean(beans[i]);
  }
};
  

