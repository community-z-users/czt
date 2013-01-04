importClass(java.lang.System);

System.err.println("In the distribution config file...");

//Run the persistence config file
function getScript(resource) {
  importClass(Packages.org.apache.bsf.util.IOUtils);
  importClass(java.io.InputStreamReader);
  importClass(java.lang.ClassLoader);
  var stream=ClassLoader.getSystemResourceAsStream(resource);
  if(stream==null) {
    System.err.println("stream==null");
    return "";
  }
  return String(IOUtils.getStringFromReader(new InputStreamReader(stream)));
};

eval(getScript("net/sourceforge/czt/animation/gui/persistence/persistence-config.js"));


//Setting Property Editors
importClass(java.beans.PropertyEditorManager);
importPackage(Packages.net.sourceforge.czt.animation.gui.design.properties.editors);
PropertyEditorManager.registerEditor(java.awt.Color, ColorEditor);
PropertyEditorManager.registerEditor(Packages.javax.swing.Icon, IconEditor);
PropertyEditorManager.registerEditor(Packages.javax.swing.border.Border, BorderEditor);
PropertyEditorManager.registerEditor(Packages.javax.swing.table.TableModel, TableModelEditor);

//Setting Property Renderers
importClass(Packages.net.sourceforge.czt.animation.gui.design.properties.PropertiesWindow);
importPackage(Packages.net.sourceforge.czt.animation.gui.design.properties.renderers);
PropertiesWindow.addDefaultRenderer(java.awt.Color, new ColorRenderer());
PropertiesWindow.addDefaultRenderer(java.awt.Font, new FontRenderer());
PropertiesWindow.addDefaultRenderer(Packages.javax.swing.Icon, new IconRenderer());

//XXX The default borders may be component specific so can't wrap around the label used by the renderer
//PropertiesWindow.addDefaultRenderer(Packages.javax.swing.border.Border, new BorderRenderer());

//Setting Table Models
importClass(java.lang.Class);
TableModelEditor.registerTableModel(Class
	.forName("net.sourceforge.czt.animation.gui.beans.table.BindingModel"));
TableModelEditor.registerTableModel(Class
	.forName("net.sourceforge.czt.animation.gui.beans.table.RelationModel"));

//Setting Tool Classes
ToolClasses.add(Class.forName("javax.swing.JButton"));
ToolClasses.add(Class.forName("javax.swing.JCheckBox"));
ToolClasses.add(Class.forName("javax.swing.JLabel"));
ToolClasses.add(Class.forName("javax.swing.JPanel"));
ToolClasses.add(Class.forName("javax.swing.JScrollPane"));
ToolClasses.add(Class.forName("javax.swing.JTable"));
ToolClasses.add(Class.forName("javax.swing.JTextField"));
ToolClasses.add(Class.forName("net.sourceforge.czt.animation.gui.beans.Script"));
ToolClasses.add(Class.forName("net.sourceforge.czt.animation.gui.beans.HistoryProxy"));
//  ToolClasses.add(Class.forName("net.sourceforge.czt.animation.gui.beans.FormFiller"));

//Registering scripts from library with Init script's dialog
DesignerCore.registerScriptLibrary("fillBeans","net/sourceforge/czt/animation/gui/scripts/fillBeans.js");
DesignerCore.registerScriptLibrary("clearBeans","net/sourceforge/czt/animation/gui/scripts/clearBeans.js");
DesignerCore.registerScriptLibrary("fillHistory","net/sourceforge/czt/animation/gui/scripts/fillHistory.js");

System.err.println("...Finished the distribution config file.");

