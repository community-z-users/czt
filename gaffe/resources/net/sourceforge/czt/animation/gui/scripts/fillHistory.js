function fillHistory(form) {
  if(form==null) return;
  
  importClass(java.awt.TextComponent);
  importClass(Packages.javax.swing.JTable);
  importClass(Packages.javax.swing.text.JTextComponent);
  importPackage(Packages.net.sourceforge.czt.animation.gui.beans.table);
  importPackage(Packages.net.sourceforge.czt.animation.gui.temp);

  function fillVar(component) {
    if(component instanceof TextComponent || component instanceof JTextComponent) 
      History.addInput(ZLocator.fromString(component.name, new ZGiven(component.getText())));
    //XXX Fill in here for more types of components.
  };
  
  var beans=form.components;
  for(var i in beans) {
    var name=beans[i].name;
    if(name!=null) 
      fillVar(beans[i]);
    //XXX Do something to only add values that are appropriate inputs?
  };
};
  

