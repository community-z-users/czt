package net.sourceforge.czt.animation.gui.generation;

import java.util.Arrays;
import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.plugins.*;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.*;
 
import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;

public final class Generator {
  private static PluginList plugins
  =new PluginList(new Class[] {SpecSource.class,                  SchemaExtractor.class,
			       SchemaIdentifier.class,            VariableExtractor.class, 
			       DOMBeanChooser.class/*,              DOMInterfaceGenerator.class*/},
		  new Class[] {SpecReaderSource.class,            VisitorSchemaExtractor.class,
			       CommandLineSchemaIdentifier.class, DefaultVariableExtractor.class,
			       BasicDOMBeanChooser.class/*,         BasicInterfaceGenerator.class*/},
		  "Generator",
		  "Generates a (.gaffe) interface file from a (.zml) Z specification.");
  

  public static void main(String[] args) {
    plugins.processOptions(args);
    
    Term specification=((SpecSource)plugins.getPlugin(SpecSource.class)).obtainSpec();
    List/*<ConstDecl<SchExpr>>*/ schemas
      =((SchemaExtractor)plugins.getPlugin(SchemaExtractor.class)).getSchemas(specification);
    ((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).identifySchemas(specification,schemas);
    ConstDecl/*<SchExpr>*/ stateSchema
      =((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).getStateSchema();
    ConstDecl/*<SchExpr>*/ initSchema
      =((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).getInitSchema();
    List/*<ConstDecl<SchExpr>>*/ operationSchemas
      =((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).getOperationSchemas();
    
    ((DOMInterfaceGenerator)plugins.getPlugin(DOMInterfaceGenerator.class))
      .generateInterface(specification, schemas, stateSchema, initSchema, operationSchemas, 
			 ((VariableExtractor)plugins.getPlugin(VariableExtractor.class)),
			 ((DOMBeanChooser)plugins.getPlugin(DOMBeanChooser.class)),
			 System.out);//XXX add output plugin
  };
};

