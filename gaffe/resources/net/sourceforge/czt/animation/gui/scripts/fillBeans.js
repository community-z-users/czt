function fillBeans(form) {
  if(form==null) return;
  
  importClass(java.awt.Label);
  importClass(java.awt.TextComponent);
  importClass(Packages.javax.swing.JLabel);
  importClass(Packages.javax.swing.JTable);
  importClass(Packages.javax.swing.text.JTextComponent);
  importPackage(Packages.net.sourceforge.czt.animation.gui.beans.table);
  importPackage(Packages.net.sourceforge.czt.animation.gui.temp);

  function fillBean(component, value) {
    if(component instanceof TextComponent || component instanceof JTextComponent
       || component instanceof Label || component instanceof JLabel) 
      component.text=value.toString();
    else if(component instanceof JTable)
      if(component.model instanceof RelationModel)
        if(value instanceof ZSet)     component.model.relation=value;
        else                          component.model.relation=null;
      else if(component.model instanceof BindingModel)
        if(value instanceof ZBinding) component.model.binding=value;
	else                          component.model.binding=null;
    //XXX Fill in here for more types of components.
  };
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
    var name=beans[i].name;
    if(name!=null) try {
      binding=History.currentSolution;
      if(binding!=null)
	fillBean(beans[i], ZLocator.fromString(name).apply(binding));
      else
	clearBean(beans[i]);
    } catch (ex) {
      clearBean(beans[i]);
    };
  }
};
  

