package net.sourceforge.czt.animation.gui.generation.plugins.impl;  

import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Vector;

import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.OptionHandler;
import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaIdentifier;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;

public final class CommandLineSchemaIdentifier implements SchemaIdentifier {
  public Option[] getOptions() {
    return new Option[]{
      new Option("initSchema", Option.MUST, "schema name", "Name of the initialisation schema to use.",
		 initHandler),
      new Option("stateSchema", Option.MUST, "schema name", "Name of the state schema to use.",
		 stateHandler),
      new Option("opSchema", Option.MUST, "schema name", "Name of an operation schema to use.",
		 opHandler)
    };
  };
  public String getHelp() {return "Identifies state, initialisation, and operation schemas.";};  

  private String initSchemaName=null, stateSchemaName=null;
  private List/*<String>*/ operationSchemaNames=new Vector();

  private final OptionHandler initHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	initSchemaName=argument;
      };
    };
  private final OptionHandler stateHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	stateSchemaName=argument;
      };
    };
  private final OptionHandler opHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	operationSchemaNames.add(argument);
      };
    };
  
  private ConstDecl/*<SchExpr>*/ stateSchema=null;
  private ConstDecl/*<SchExpr>*/ initSchema=null;
  private List/*<ConstDecl<SchExpr>>*/ operationSchemas=null;
  public ConstDecl/*<SchExpr>*/ getStateSchema() {return stateSchema;};
  public ConstDecl/*<SchExpr>*/ getInitSchema()  {return initSchema;};
  public List/*<ConstDecl<SchExpr>>*/ getOperationSchemas() {return operationSchemas;};

  public void identifySchemas(Term specification, List/*<ConstDecl<SchExpr>>*/ schemas) 
    throws IllegalStateException {
    if(stateSchemaName==null) 
      throw new IllegalStateException("The CommandLineSchemaIdentifier needs an argument giving a name for "
				      +"the state schema.");
    if(initSchemaName==null) initSchemaName="Init"+stateSchemaName;
    for(Iterator it=schemas.iterator();it.hasNext();) {
      ConstDecl/*<SchExpr>*/ schema=(ConstDecl/*<SchExpr>*/)it.next();
      String schemaName=Name2String.toString(schema.getDeclName());
      if(schemaName.equals(initSchemaName)) initSchema=schema;
      if(schemaName.equals(stateSchemaName)) stateSchema=schema;
      if(operationSchemaNames.contains(schemaName)) {
	operationSchemas.add(schema);
	operationSchemaNames.remove(schemaName);
      }
    }
    if(initSchema==null)
      throw new IllegalStateException("The CommandLineSchemaIdentifier could not find an init schema.");
    if(stateSchema==null)
      throw new IllegalStateException("The CommandLineSchemaIdentifier could not find a t schema.");
    if(!operationSchemaNames.isEmpty()) 
      throw new IllegalStateException("The CommandLineSchemaIdentifier could not find a schema by the "
				      +"name:"+operationSchemaNames.get(0));
  };
};
