java.lang.System.err.println("Loading fillHistory...");
function fillHistory(form) {
  if(form==null) return;
  
  importClass(java.awt.Component);
  importClass(java.awt.TextComponent);
  importClass(Packages.javax.swing.JTable);
  importClass(Packages.javax.swing.text.JTextComponent);
  importClass(Packages.net.sourceforge.czt.animation.ZLocator);

  importPackage(Packages.net.sourceforge.czt.animation.gui.beans.table);
  importPackage(Packages.net.sourceforge.czt.animation.gui.temp);

  function fillVar(component) {
    if(component instanceof TextComponent || component instanceof JTextComponent) 
      History.addInput(ZLocator.fromString(component.name), new ZGiven(component.getText()));
    //XXX Fill in here for more types of components.
  };
  
  var beans=form.beans;
  for(var i in beans) {
    var name=beans[i].name;
    //Only interested in Components, with a name that we can use.
    //A name with a ' ' in can't be a valid Z name, so the last test means that any component that should
    //not be affected can be protected by putting a ' ' in its name.
    if(beans[i] instanceof Component && name!=null && name.indexOf(' ')<0)
      fillVar(beans[i]);
    //XXX Do something to only add values that are appropriate inputs?
  };
};
  

