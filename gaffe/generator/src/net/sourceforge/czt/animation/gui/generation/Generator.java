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
  private static SpecSource specificationSource=null;
  private static SchemaExtractor schemaExtractor=null;
  private static SchemaIdentifier schemaIdentifier=null;
  private static VariableExtractor variableExtractor=null;
  private static DOMBeanChooser beanChooser=null;
  private static DOMInterfaceGenerator interfaceGenerator=null;
  
  private static final Plugin pluginSetter=new Plugin() {
      public String getArgsDocumentation() {
	return "-source-plugin <className>     className=name of the SpecSource plugin\n"
	      +"-extractor-plugin <className>  className=name of the SchemaExtractor plugin\n"
	      +"-identifier-plugin <className> className=name of the SchemaIdentifier plugin\n"
   	      +"-variable-plugin <className>   className=name of the VariableExtractor plugin\n"
	      +"-bean-plugin <className>       className=name of the BeanChooser plugin\n";
      };
  
      public void handleArgs(ListIterator args) throws BadArgumentsException {
	for(;args.hasNext();) {
	  String arg=(String)args.next();
	  if(arg.equals("-source-plugin")) {
	    if(specificationSource!=null)
	      throw new BadArgumentsException("-source-plugin has already been specified.");
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
	    if(schemaExtractor!=null)
	      throw new BadArgumentsException("-extractor-plugin has already been specified.");
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
	    if(schemaIdentifier!=null)
	      throw new BadArgumentsException("-identifier-plugin has already been specified.");
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
	    if(variableExtractor!=null)
	      throw new BadArgumentsException("-variable-plugin has already been specified.");
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
	  } else if (arg.equals("-bean-plugin")) {
	    if(beanChooser!=null)
	      throw new BadArgumentsException("-bean-plugin has already been specified.");
	    if(!args.hasNext())
	      throw new BadArgumentsException("-bean-plugin requires an argument giving a class name "
					      +"of a DOMBeanChooser plugin.");
	    try {
	      Class pluginClass=Class.forName((String)args.next());
	      beanChooser=(DOMBeanChooser)pluginClass.newInstance();
	    } catch(ClassNotFoundException ex) {
	      throw new BadArgumentsException("The argument to -bean-plugin must be a subclass of "
					      +"DOMBeanChooser that is in the class path.");
	    } catch(ClassCastException ex) {
	      throw new BadArgumentsException("The argument to -bean-plugin must be a subclass of "
					      +"DOMBeanChooser.");
	    } catch(Exception ex) {
	      throw new BadArgumentsException("Creating the bean chooser plugin (-bean-plugin) "
					      +"failed:"+ex);
	    };
	  } else {
	    args.previous();
	    return;
	  }
	}
      };
    };
  
  private static final Plugin helpPlugin=new Plugin() {
      public String getArgsDocumentation() {
	return "-help         = display help for this program";
      };
      public void handleArgs(ListIterator args) throws BadArgumentsException {
	if(args.hasNext()) {
	  String arg=(String)args.next();
	  if(arg.equals("-help")||arg.equals("-?")||arg.equals("--help")) {
	    System.err.println("Generator [<select plugin options>] -help");
	    System.err.println("Generator [<select plugin options>] <per plugin options>");
	    System.err.println();
	    System.err.println("Select Plugin Options:");
	    System.err.println(pluginSetter.getArgsDocumentation());
	    
	    System.err.println("Per Plugin Options:");
	    System.err.println("Source Plugin:");
	    System.err.println(specificationSource.getArgsDocumentation());
	    System.err.println("Schema Extractor Plugin:");
	    System.err.println(schemaExtractor.getArgsDocumentation());
	    System.err.println("Schema Identifier Plugin:");
	    System.err.println(schemaIdentifier.getArgsDocumentation());
	    System.err.println("Variable Extractor Plugin:");
	    System.err.println(variableExtractor.getArgsDocumentation());
	    System.err.println("Bean Chooser Plugin:");
	    System.err.println(beanChooser.getArgsDocumentation());
	    System.err.println("Interface Generator Plugin:");
	    System.err.println(interfaceGenerator.getArgsDocumentation());
	    
	    System.exit(0);
	  } else {
	    args.previous();
	    return;
	  }
	}
      };
    };
  
  /**
   * @return true if all arguments were processed or false if there are arguments left unprocessed
   */
  public static void processArguments(ListIterator/*<String>*/ iterator, Plugin[] plugins) throws Exception {
    mainloop: while(iterator.hasNext()) {
      int nextIndex=iterator.nextIndex();
      for(int pIt=0;pIt<plugins.length;pIt++) {
	plugins[pIt].handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex())//If it has consumed some of the arguments then restart the cycle
	  continue mainloop;
      }
      break mainloop;
    }
  };
  public static void processArguments(List/*<String>*/ args, Plugin[] plugins) throws Exception {
    processArguments(args.listIterator(), plugins);
  };
  public static void processArguments(String[] args, Plugin[] plugins) throws Exception {
    processArguments(Arrays.asList(args), plugins);
  };
  

  public static void main(String[] args) {
    List argsList=Arrays.asList(args);
    ListIterator iterator=argsList.listIterator();
    try {
      processArguments(args, new Plugin[]{pluginSetter});
      if(specificationSource==null) specificationSource=new SpecReaderSource();
      if(schemaExtractor==null) schemaExtractor=new VisitorSchemaExtractor();
      if(schemaIdentifier==null) schemaIdentifier=new CommandLineSchemaIdentifier();
      if(variableExtractor==null) variableExtractor=new DefaultVariableExtractor();
      if(beanChooser==null) beanChooser=new BasicDOMBeanChooser();
      //      if(interfaceGenerator==null) interfaceGenerator=new BasicInterfaceGenerator();

      processArguments(args, new Plugin[]{helpPlugin});
      processArguments(args, new Plugin[]{specificationSource, schemaExtractor, schemaIdentifier, 
					  variableExtractor, beanChooser, interfaceGenerator});
      if(iterator.hasNext())
	throw new BadArgumentsException("Argument not handled: "+iterator.next());
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
    
    interfaceGenerator.generateInterface(specification, schemas, stateSchema, initSchema, operationSchemas, 
					 variableExtractor, beanChooser, System.out);//XXX add output plugin
  };
};

