package net.sourceforge.czt.animation.gui.generation;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Vector;


final class PluginList {
  private final HashMap/*<Class, Class>*/ defaultImplLookup=new HashMap();
  private final HashMap/*<Class, Plugin>*/ implementationLookup=new HashMap();
  private final HashMap/*<String, Class>*/ byOptNameLookup=new HashMap();
  private final Vector/*<String>*/ pluginOrder=new Vector();

  private final String programName;
  private final String programHelp;

  public Plugin getPlugin(Class pluginClass) {
    if(!implementationLookup.containsKey(pluginClass) 
       || implementationLookup.get(pluginClass)==null)
      if(defaultImplLookup.containsKey(pluginClass)) try {
	implementationLookup.put(pluginClass,
				 ((Class)defaultImplLookup.get(pluginClass))
				 .newInstance());
      } catch (InstantiationException ex) {
	throw new Error("Could not create the plugin "+pluginClass.getName()
			+".");
      } catch (IllegalAccessException ex) {
	throw new Error("Could not create the plugin "+pluginClass.getName()
			+".");
      } else
	throw new Error("getPlugin must be given a class in the PluginList");
    return (Plugin)implementationLookup.get(pluginClass);
  };
  public Plugin getPlugin(String optionName) {
    return getPlugin((Class)byOptNameLookup.get(optionName));
  };
  

  public static String getPluginName(Class pluginClass) {
    try {
      return (String)pluginClass.getField("name").get(null);
    } catch (Exception ex) {
      throw new Error("Plugin classes must have a static final String field "
		      +"\"name\", which must be available to "
		      +"PluginList via reflection.");
    }
  };
  public static String getPluginName(Plugin plugin) {
    return getPluginName(plugin.getClass());
  };
  
  public static String getPluginOptionName(Class pluginClass) {
    try {
      return (String)pluginClass.getField("optionName")
	.get(null);
    } catch (Exception ex) {
      throw new Error("Plugin classes must have a static final String field "
		      +"\"optionName\", which must be available to "
		      +"PluginList via reflection.");
    }
  };
  public static String getPluginOptionName(Plugin plugin) {
    return getPluginOptionName(plugin.getClass());    
  };
  
  public PluginList(Class[] pluginClasses, Class[] defaultImplClasses,
		    String programName, String programHelp) {
    if(pluginClasses.length!=defaultImplClasses.length) 
      throw new Error("The constructor for PluginList must be given an "
		      +"implementation class for each plugin class.");
    for(int i=0;i<pluginClasses.length;i++) {
      if(!Plugin.class.isAssignableFrom(pluginClasses[i]))
	throw new Error("The plugin classes given to the constructor for "
			+"PluginList must all be subclasses of Plugin.");
      if(!pluginClasses[i].isAssignableFrom(defaultImplClasses[i]))
	throw new Error("The default implementation classes given to the "
			+"constructor for PluginList must all be subclasses "
			+"of the corresponding plugin classes.");
      defaultImplLookup.put(pluginClasses[i], defaultImplClasses[i]);
      byOptNameLookup.put(getPluginOptionName(pluginClasses[i]),
			  pluginClasses[i]);
      pluginOrder.add(i, getPluginOptionName(pluginClasses[i]));
    }
    this.programName=programName;
    this.programHelp=programHelp;
  };
  
  
  private final PluginSelector pluginSelector=new PluginSelector();
  
  private final class PluginSelector implements Plugin, OptionHandler {
    public static final String optionName="selector";
    public static final String name="Plugin Selector";
    
    public Option[] getOptions() {
      Option[] options=new Option[pluginOrder.size()];
      for(int i=0;i<options.length;i++) {
	String pluginOptName=(String)pluginOrder.get(i);
	options[i]=new Option(pluginOptName+"-plugin", Option.MUST,
				     "class name",
				     "Select the implementation class for "
				     +"the \""
				     +getPluginName((Class)byOptNameLookup
						    .get(pluginOptName))
				     +"\".", this);
      };
      return options;
    };
    public String getHelp() {
      return "Selects the implementation to use for each plugin type.";
    };
    public void handleOption(Option option, String argument) {
      String pluginOptName=option.optionName;
      pluginOptName
	=pluginOptName.substring(0,pluginOptName.lastIndexOf("-plugin"));
      Class pluginClass=(Class)byOptNameLookup.get(pluginOptName);
      if(implementationLookup.containsKey(pluginClass)
	 && implementationLookup.get(pluginClass)!=null)
	throw new Error("An implementation for the \""
			+getPluginName(pluginClass)+"("+pluginOptName
			+")\" has already been set.");
      Class implClass;
      try {
	implClass=Class.forName(argument);
      } catch (ClassNotFoundException ex) {
	throw new Error("The class name given to -"+option.optionName
			+" needs to be a full class name (including package)"
			+" that can be found in the classpath.");
      }
      if(!pluginClass.isAssignableFrom(implClass))
	throw new Error("The class name given to -"+option.optionName
			+" needs to be a subclass of \""
			+getPluginName(pluginClass)+"("+pluginOptName
			+")\".");
      defaultImplLookup.put(pluginClass,implClass);
      getPlugin(pluginClass);
    };
  };

  private final HelpPlugin helpPlugin=new HelpPlugin();

  private final class HelpPlugin implements Plugin, OptionHandler {
    public static final String optionName="help";
    public static final String name="Help Plugin";
    
    private final Option[] options=new Option[] {
	new Option("help",Option.MAY,"plugin name",
			  "Show this help.",HelpPlugin.this),
	new Option("-help",Option.MAY,"plugin name",
			  HelpPlugin.this),
	new Option("?",Option.MAY,"plugin name",
			  HelpPlugin.this),
      };
    public Option[] getOptions() {
      return options;
    };
    public String getHelp() {
      return "Displays help for all plugins.";
    };
    public void handleOption(Option option, String argument) {
      System.err.println(programName+" help");
      System.err.println(programHelp);
      System.err.println();
      System.err.println(programName+" [<plugin selector options>] -help");
      System.err.println(programName
			 +" [<plugin selector options>]"
			 +" [<per plugin options>]");
      System.err.println();
      
      if(argument!=null) {
	if(argument.equals("help"))
	   showHelpFor(this);
	else if(argument.equals("selector"))
	  showHelpFor(pluginSelector);
	else if(byOptNameLookup.get(argument)==null)
	  throw new Error("The help option must take a plugins option name.  "
			  +"Run '"+programName+" -help' (option names are in "
			  +"brackets.");
	else {
	  showHelpFor(getPlugin(argument));
	};
      } else {
	showHelpFor(this);
	showHelpFor(pluginSelector);
	for(Iterator it=pluginOrder.iterator();it.hasNext();)
	  showHelpFor(getPlugin((String)it.next()));
      };
      System.exit(0);
    };
    private void showHelpFor(Plugin plugin) {
      System.err.println(getPluginName(plugin)+" ("
			 +getPluginOptionName(plugin)+"):");
      System.err.println(plugin.getHelp());
      Option[] options=plugin.getOptions();
      final String space="                                        ";
      for(int i=0;i<options.length;i++) {
	if(!options[i].showInHelp) continue;
	String line1="  ";
	if(options[i].optionName!=null)
	  line1+="-"+options[i].optionName+" ";
	if(options[i].takesArgument==Option.MAY) line1+="[";
	if(options[i].takesArgument!=Option.MUSTNOT)
	  line1+="<"+(options[i].argumentName==null?
		      "argument":
		      options[i].argumentName)+">";
	if(options[i].takesArgument==Option.MAY) line1+="]";
	  
	if(options[i].help!=null && options[i].help[0]!=null 
	   && options[i].help[0].length()>0) {
	  try {
	    line1+=space.substring(line1.length());
	  } catch (StringIndexOutOfBoundsException ex) {//Don't add anything then
	  };
	  line1+="  "+options[i].help[0];
	  System.err.println(line1);
	  for(int j=1;j<options[i].help.length;j++)
	    System.err.println(space+"  "+options[i].help[j]);
	}
      }
      System.err.println();
    };
  };
  
  public Option findOption(String option, Plugin plugin) {
    Option[] options=plugin.getOptions();
    for(int j=0;j<options.length;j++)
      if(options[j].optionName.equals(option))
	return options[j];
    return null;
  };
  public Option findOption(String option) {
    for(Iterator it=pluginOrder.iterator();it.hasNext();) {
      Plugin plugin=getPlugin((String)it.next());
      Option opt=findOption(option,plugin);
      if(opt!=null) return opt;
    }
    return null;
  };
  
  public void processOptions(String[] options) {
    processOptions(Arrays.asList(options));
  };
  public void processOptions(List/*<String>*/ options) {
    processOptions(options.listIterator());
  };
  public void processOptions(ListIterator/*<String>*/ it) {
    //XXX add code so that you can specify which plugin an option goes to.
    //XXX e.g. 'Generator -help:help' or 'Generator -selector:bean-plugin'
    boolean inSelectorOptions=true;
    for(;it.hasNext();) {
      String option=(String)it.next();
      String argument=null;
      if(!option.startsWith("-")) {//Options start with '-' if it isn't there
	argument=option;           //we have an anonymous option with an
	option=null;               //argument.
      } else if(it.hasNext()) {
	argument=(String)it.next();
	if(argument.startsWith("-")) {//If the next string starts with a '-'
	  argument=null;              //then it is an option, not an argument 
	  it.previous();
	}
      }
      if(option!=null)//Chop off the leading '-'
	option=option.substring(1);
      
      Option optToRun=null;
      //-help should only happen immediately after selector options
      if(inSelectorOptions && (optToRun=findOption(option,helpPlugin))!=null) inSelectorOptions=false;
      
      else {
	//selector options should all happen together near the start.
	inSelectorOptions=inSelectorOptions && (optToRun=findOption(option,pluginSelector))!=null;
	if(!inSelectorOptions) optToRun=findOption(option);
      }
      if(optToRun==null) {
	String optArgPair;
	if(option==null) optArgPair=argument;
	else if(argument==null) optArgPair="-"+option;
	else optArgPair="-"+option+" "+argument;
	throw new Error("The option \""+optArgPair
			+"\" wasn't handled by any plugin.");
      }
      //If the option doesn't take an argument, then the argument is obviously
      //seperate from this option.
      if(optToRun.takesArgument==Option.MUSTNOT && argument!=null) {
	argument=null;
	it.previous();
      }
      if(optToRun.takesArgument==Option.MUST && argument==null)
	throw new Error("Option -"+option+" must take an argument.");
      optToRun.handler.handleOption(optToRun,argument);
    }
  };
  public void displayHelp() {
    helpPlugin.handleOption(helpPlugin.getOptions()[0],null);
  };  
};
