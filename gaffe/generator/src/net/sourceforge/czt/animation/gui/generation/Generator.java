package net.sourceforge.czt.animation.gui.generation;

import java.util.Arrays;
import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.plugins.*;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.*;
 
import net.sourceforge.czt.core.ast.ConstDecl;
import net.sourceforge.czt.core.ast.DeclName;
import net.sourceforge.czt.core.ast.Term;

public final class Generator {

  public static interface InterfaceGenerator extends Plugin {
    public void generateInterface(Term specification, List/*<ConstDecl<SchExpr>>*/ schemas, 
				  ConstDecl/*<SchExpr>*/ stateSchema, ConstDecl/*<SchExpr>*/ initSchema, 
				  List/*<ConstDecl<SchExpr>>*/ operationSchemas, 
				  VariableExtractor variableExtractor);
  };

  private static SpecSource specificationSource=null;
  private static SchemaExtractor schemaExtractor=null;
  private static SchemaIdentifier schemaIdentifier=null;
  private static VariableExtractor variableExtractor=null;
  private static final Plugin pluginSetter=new Plugin() {
      public void handleArgs(ListIterator args) throws BadArgumentsException {
	for(;args.hasNext();) {
	  String arg=(String)args.next();
	  if(arg.equals("-source-plugin")) {
	    if(!args.hasNext())
	      throw new BadArgumentsException("-source-plugin requires an argument giving a class name of a "
					      +"SpecSource plugin.");
	    try {
	      Class pluginClass=Class.forName((String)args.next());
	      specificationSource=(SpecSource)pluginClass.newInstance();
	    } catch(ClassNotFoundException ex) {
	      throw new BadArgumentsException("The argument to -source-plugin must be a subclass of "
					      +"SpecSource that is in the class path.");
	    } catch(ClassCastException ex) {
	      throw new BadArgumentsException("The argument to -source-plugin must be a subclass of "
					      +"SpecSource.");
	    } catch(Exception ex) {
	      throw new BadArgumentsException("Creating the source plugin (-source-plugin) failed:"+ex);
	    };
	  } else if (arg.equals("-extractor-plugin")) {
	    if(!args.hasNext())
	      throw new BadArgumentsException("-extractor-plugin requires an argument giving a class name "
					      +"of a SchemaExtractor plugin.");
	    try {
	      Class pluginClass=Class.forName((String)args.next());
	      schemaExtractor=(SchemaExtractor)pluginClass.newInstance();
	    } catch(ClassNotFoundException ex) {
	      throw new BadArgumentsException("The argument to -extractor-plugin must be a subclass of "
					      +"SchemaExtractor that is in the class path.");
	    } catch(ClassCastException ex) {
	      throw new BadArgumentsException("The argument to -extractor-plugin must be a subclass of "
					      +"SchemaExtractor.");
	    } catch(Exception ex) {
	      throw new BadArgumentsException("Creating the schema extractor plugin (-extractor-plugin) "
					      +"failed:"+ex);
	    };
	  } else if (arg.equals("-identifier-plugin")) {
	    if(!args.hasNext())
	      throw new BadArgumentsException("-identifier-plugin requires an argument giving a class name "
					      +"of a SchemaIdentifier plugin.");
	    try {
	      Class pluginClass=Class.forName((String)args.next());
	      schemaIdentifier=(SchemaIdentifier)pluginClass.newInstance();
	    } catch(ClassNotFoundException ex) {
	      throw new BadArgumentsException("The argument to -identifier-plugin must be a subclass of "
					      +"SchemaIdentifier that is in the class path.");
	    } catch(ClassCastException ex) {
	      throw new BadArgumentsException("The argument to -identifier-plugin must be a subclass of "
					      +"SchemaIdentifier.");
	    } catch(Exception ex) {
	      throw new BadArgumentsException("Creating the schema identifier plugin (-identifier-plugin) "
					      +"failed:"+ex);
	    };
	  } else if (arg.equals("-variable-plugin")) {
	    if(!args.hasNext())
	      throw new BadArgumentsException("-variable-plugin requires an argument giving a class name "
					      +"of a VariableExtractor plugin.");
	    try {
	      Class pluginClass=Class.forName((String)args.next());
	      variableExtractor=(VariableExtractor)pluginClass.newInstance();
	    } catch(ClassNotFoundException ex) {
	      throw new BadArgumentsException("The argument to -variable-plugin must be a subclass of "
					      +"VariableExtractor that is in the class path.");
	    } catch(ClassCastException ex) {
	      throw new BadArgumentsException("The argument to -variable-plugin must be a subclass of "
					      +"VariableExtractor.");
	    } catch(Exception ex) {
	      throw new BadArgumentsException("Creating the variable extractor plugin (-variable-plugin) "
					      +"failed:"+ex);
	    };
	  } else {
	    args.previous();
	    return;
	  }
	}
      };
    };
  
  public static void main(String[] args) {
    List argsList=Arrays.asList(args);
    ListIterator iterator=argsList.listIterator();
    try {
      while(iterator.hasNext()) {
	int nextIndex=iterator.nextIndex();
	pluginSetter.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle

	if(specificationSource==null) specificationSource=new SpecReaderSource();
	specificationSource.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle

	if(schemaExtractor==null) schemaExtractor=new VisitorSchemaExtractor();
	schemaExtractor.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle

	if(schemaIdentifier==null) schemaIdentifier=new CommandLineSchemaIdentifier();
	schemaIdentifier.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycel

	if(variableExtractor==null) variableExtractor=new DefaultVariableExtractor();
	variableExtractor.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle
      } 
    } catch(Exception ex) {
      System.err.println(ex);
      return;
    }

    Term specification=specificationSource.obtainSpec();
    List/*<ConstDecl<SchExpr>>*/ schemas=schemaExtractor.getSchemas(specification);
    schemaIdentifier.identifySchemas(specification,schemas);
    ConstDecl/*<SchExpr>*/ stateSchema=schemaIdentifier.getStateSchema();
    ConstDecl/*<SchExpr>*/ initSchema=schemaIdentifier.getInitSchema();
    List/*<ConstDecl<SchExpr>>*/ operationSchemas=schemaIdentifier.getOperationSchemas();
    
    
  };
};

