java.lang.System.err.println("Loading fillBeans...");
function fillBeans(form) {
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

  function fillBean(component, value) {
    if(component instanceof TextComponent || component instanceof JTextComponent
       || component instanceof Label || component instanceof JLabel) 
      component.setText(value.toString());
    else if(component instanceof JTable)
      if(component.model instanceof RelationModel)
        if(value instanceof ZSet)     component.model.relation=value;
        else                          component.model.relation=null;
      else if(component.model instanceof BindingModel)
        if(value instanceof ZBinding) component.model.binding=value;
	else                          component.model.binding=null;
      else if(component.model instanceof SetModel)
        if(value instanceof ZSet) component.model.set=value;
	else                      component.model.set=null;
    //XXX Fill in here for more types of components.
  };
  function clearBean(component) {
    if(component instanceof TextComponent || component instanceof JTextComponent
       || component instanceof Label || component instanceof JLabel)
      component.setText("");
    else if(component instanceof JTable)
      if(component.model instanceof RelationModel)     component.model.relation=null;
      else if(component.model instanceof BindingModel) component.model.binding=null;
      else if(component.model instanceof SetModel) component.model.set=null;
    //XXX Fill in here for more types of components.
  };
  
  var beans=form.beans;
  for(var i in beans) {
    var name=beans[i].name;
    //Only interested in Components, with a name that we can use.
    //A name with a ' ' in can't be a valid Z name, so the last test means that any component that should
    //not be affected can be protected by putting a ' ' in its name.
    if(beans[i] instanceof Component && name!=null && name.indexOf(' ')<0)
      try {
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
  

