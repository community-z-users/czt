package net.sourceforge.czt.animation.gui.generation.plugins.impl;  

import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Vector;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaIdentifier;

import net.sourceforge.czt.core.ast.ConstDecl;
import net.sourceforge.czt.core.ast.Term;

public final class CommandLineSchemaIdentifier implements SchemaIdentifier {
  private ConstDecl/*<SchExpr>*/ stateSchema=null;
  private ConstDecl/*<SchExpr>*/ initSchema=null;
  private List/*<ConstDecl<SchExpr>>*/ operationSchemas=null;
  public ConstDecl/*<SchExpr>*/ getStateSchema() {return stateSchema;};
  public ConstDecl/*<SchExpr>*/ getInitSchema()  {return initSchema;};
  public List/*<ConstDecl<SchExpr>>*/ getOperationSchemas() {return operationSchemas;};
    
  private String initSchemaName=null, stateSchemaName=null;
  List/*<String>*/ operationSchemaNames=new Vector();
  public void handleArgs(ListIterator args) throws BadArgumentsException {
    for(;args.hasNext();) {
      String arg=(String)args.next();
      if(arg.equals("-initSchema")) {
	if(!args.hasNext()) 
	  throw new BadArgumentsException("-initSchema requires an argument giving the name of the "
					  +"initialisation schema.");
	initSchemaName=(String)args.next();
      } else if (arg.equals("-stateSchema")) {
	if(!args.hasNext())
	  throw new BadArgumentsException("-stateSchema requires an argument giving the name of the "
					  +"state schema.");
	stateSchemaName=(String)args.next();
      } else if (arg.equals("-opSchema")) {
	if(!args.hasNext())
	  throw new BadArgumentsException("-opSchema requires an argument giving the name of an operation "
					  +" schema.");
	operationSchemaNames.add(args.next());
      } else {
	args.previous();
	return;
      }
    }
  };
  public void identifySchemas(Term specification, List/*<ConstDecl<SchExpr>>*/ schemas) 
    throws IllegalStateException {
    if(stateSchemaName==null) throw new IllegalStateException("The CommandLineSchemaIdentifier needs an argument giving a name for the state schema.");
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
