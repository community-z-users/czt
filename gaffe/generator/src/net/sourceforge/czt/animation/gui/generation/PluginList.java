/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley
 
 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.generation;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Vector;

/**
 * Collection for plugin types.  Handles selection of implementation classes for plugins, and processing of 
 * the command line.
 */
public final class PluginList
{
  /**
   * Map from interface class to default implementation classes.
   */
  private final HashMap<Class, Class> defaultImplLookup = new HashMap<Class, Class>();

  /**
   * Map from interface class to created plugin.
   */
  private final HashMap<Class, Plugin> implementationLookup = new HashMap<Class, Plugin>();

  /**
   * Map from plugin option name to interface class.
   * <em>Invariant:</em> The returned class should have the static member optionName equal to the map's key.
   */
  private final HashMap<String, Class> byOptNameLookup = new HashMap<String, Class>();

  /**
   * List of all of the plugins' option names giving the order of the options.
   */
  private final Vector<String> pluginOrder = new Vector<String>();

  /**
   * Name of the program.  Used in help displays.
   */
  private final String programName;

  /**
   * Help text for the program.  Used in help displays.
   */
  private final String programHelp;

  /**
   * Looks up a plugin by its interface class.
   * Also creates the plugin, if it has not yet been created.  Once this is done, the implementation class
   * can no longer be changed, e.g. with the {@link #pluginSelector pluginSelector}.
   * @param pluginClass the interface class of the plugin to return.
   * @return the plugin.
   */
  public Plugin getPlugin(Class pluginClass)
      throws PluginInstantiationException
  {
    if (pluginClass == null)
      throw new NullPointerException(
          "PluginList.getPlugin(Class) cannot take a null argument.");
    if (!implementationLookup.containsKey(pluginClass)
        || implementationLookup.get(pluginClass) == null)
      if (defaultImplLookup.containsKey(pluginClass))
        try {
          implementationLookup.put(pluginClass, ((Plugin) defaultImplLookup
              .get(pluginClass).newInstance()));
        } catch (InstantiationException ex) {
          throw new PluginInstantiationException("Could not create the plugin "
              + pluginClass.getName() + ".", ex);
        } catch (IllegalAccessException ex) {
          throw new PluginInstantiationException("Could not create the plugin "
              + pluginClass.getName() + ".", ex);
        }
      else
        throw new PluginInstantiationException(
            "PluginList.getPlugin(Class) must be given a class in the "
                + "PluginList");
    return (Plugin) implementationLookup.get(pluginClass);
  };

  /**
   * Looks up a plugin by its interface class's option name.
   * Also creates the plugin, if it has not yet been created.  Once this is done, the implementation class
   * can no longer be changed, e.g. with the {@link #pluginSelector pluginSelector}.
   * @param optionName the option name of the interface class of the plugin to return.
   * @return the plugin.
   */
  public Plugin getPlugin(String optionName)
      throws PluginInstantiationException
  {
    if (optionName == null)
      throw new NullPointerException(
          "PluginList.getPlugin(Stromg) cannot take a null argument.");
    Class c = (Class) byOptNameLookup.get(optionName);
    if (c == null)
      throw new PluginInstantiationException(
          "PluginList.getPlugin(String) must be given the option name of "
              + "a plugin in the PluginList.");
    return getPlugin(c);
  };

  /**
   * Gets a plugin's name given its interface class.
   * Uses reflection to read the <tt>name</tt> static field.
   * @param pluginClass the interface class to find the name for.
   * @return the plugin class's name.
   */
  public static String getPluginName(Class pluginClass)
  {
    try {
      return (String) pluginClass.getField("name").get(null);
    } catch (Exception ex) {
      throw new Error("Plugin classes must have a static final String field "
          + "\"name\", which must be available to "
          + "PluginList via reflection.");
    }
  };

  /**
   * Gets a plugin's name.
   * Uses reflection to read the <tt>name</tt> static field.
   * @param plugin the plugin to find the name for.
   * @return the plugin's interface class's name.
   */
  public static String getPluginName(Plugin plugin)
  {
    return getPluginName(plugin.getClass());
  };

  /**
   * Gets a plugin's option name given its interface class.
   * Uses reflection to read the <tt>optionName</tt> static field.
   * @param pluginClass the interface class to find the option name for.
   * @return the plugin class's option name.
   */
  public static String getPluginOptionName(Class pluginClass)
  {
    try {
      return (String) pluginClass.getField("optionName").get(null);
    } catch (Exception ex) {
      throw new Error("Plugin classes must have a static final String field "
          + "\"optionName\", which must be available to "
          + "PluginList via reflection.");
    }
  };

  /**
   * Gets a plugin's option name.
   * Uses reflection to read the <tt>optionName</tt> static field.
   * @param plugin the plugin to find the option name for.
   * @return the plugin's interface class's option name.
   */
  public static String getPluginOptionName(Plugin plugin)
  {
    return getPluginOptionName(plugin.getClass());
  };

  /**
   * Constructor.
   * @param pluginClasses An array of the interface classes.
   * @param defaultImplClasses An array of the default implementation classes for each interface class.
   * @param programName The name of the program (used by help).
   * @param programHelp Help text for the program.
   */
  public PluginList(Class<? extends Plugin>[] pluginClasses,
      Class<? extends Plugin>[] defaultImplClasses, String programName,
      String programHelp)
  {
    if (pluginClasses.length != defaultImplClasses.length)
      throw new Error("The constructor for PluginList must be given an "
          + "implementation class for each plugin class.");
    for (int i = 0; i < pluginClasses.length; i++) {
      if (!Plugin.class.isAssignableFrom(pluginClasses[i]))
        throw new Error("The plugin classes given to the constructor for "
            + "PluginList must all be subclasses of Plugin.");
      if (!pluginClasses[i].isAssignableFrom(defaultImplClasses[i]))
        throw new Error("The default implementation classes given to the "
            + "constructor for PluginList must all be subclasses "
            + "of the corresponding plugin classes.");
      defaultImplLookup.put(pluginClasses[i], defaultImplClasses[i]);
      byOptNameLookup.put(getPluginOptionName(pluginClasses[i]),
          pluginClasses[i]);
      pluginOrder.add(i, getPluginOptionName(pluginClasses[i]));
    }
    this.programName = programName;
    this.programHelp = programHelp;
  };

  /**
   * Plugin for handling command line options for selecting implementation classes for the plugin types.
   */
  private final PluginSelector pluginSelector = new PluginSelector();

  /**
   * Class for {@link #pluginSelector pluginSelector}.
   */
  private final class PluginSelector implements Plugin, OptionHandler
  {
    /**
     * The selector plugin's option name.
     */
    public static final String optionName = "selector";

    /**
     * The selector plugin's name.
     */
    public static final String name = "Plugin Selector";

    /**
     * Returns the selector's options.
     * For each plugin in the list there is an option of the form: 
     * <tt>&lt;plugin option name&gt;-plugin</tt>.  These options select the implementation class to use for
     * the plugins.
     */
    public Option[] getOptions()
    {
      Option[] options = new Option[pluginOrder.size()];
      for (int i = 0; i < options.length; i++) {
        String pluginOptName = (String) pluginOrder.get(i);
        options[i] = new Option(pluginOptName + "-plugin", Option.MUST,
            "class name", "Select the implementation class for " + "the \""
                + getPluginName((Class) byOptNameLookup.get(pluginOptName))
                + "\".", this);
      };
      return options;
    };

    /**
     * Help text for the selector plugin.
     */
    public String getHelp()
    {
      return "Selects the implementation to use for each plugin type.";
    };

    /**
     * Handler method for all of the selector's options.
     * Checks that the class name argument given to it is okay, that the plugin hasn't already been created, 
     * and then creates the plugin (via {@link #getPlugin(Class) getPlugin(Class)}). 
     */
    public void handleOption(Option option, String argument)
        throws BadOptionException
    {
      String pluginOptName = option.optionName;
      pluginOptName = pluginOptName.substring(0, pluginOptName
          .lastIndexOf("-plugin"));
      Class<Plugin> pluginClass = (Class<Plugin>) byOptNameLookup
          .get(pluginOptName);
      if (implementationLookup.containsKey(pluginClass)
          && implementationLookup.get(pluginClass) != null)
        throw new BadOptionException("An implementation for the \""
            + getPluginName(pluginClass) + "(" + pluginOptName
            + ")\" has already been set.");
      Class<Plugin> implClass;
      try {
        implClass = (Class<Plugin>) Class.forName(argument);
      } catch (ClassNotFoundException ex) {
        throw new BadOptionException("The class name given to -"
            + option.optionName
            + " needs to be a full class name (including package)"
            + " that can be found in the classpath.");
      }
      if (!pluginClass.isAssignableFrom(implClass))
        throw new BadOptionException("The class name given to -"
            + option.optionName + " needs to be a subclass of \""
            + getPluginName(pluginClass) + "(" + pluginOptName + ")\".");
      defaultImplLookup.put(pluginClass, implClass);
      try {
        getPlugin(pluginClass);
      } catch (PluginInstantiationException ex) {
        throw new BadOptionException(ex);
      }
    };
  };

  /**
   * Plugin for handling the "-help" command line option
   */
  private final HelpPlugin helpPlugin = new HelpPlugin();

  /**
   * Class for {@link #helpPlugin helpPlugin}.
   */
  private final class HelpPlugin implements Plugin, OptionHandler
  {
    /**
     * The help plugin's option name.
     */
    public static final String optionName = "help";

    /**
     * The help plugin's name.
     */
    public static final String name = "Help Plugin";

    /**
     * The help plugin's options.
     * "-help", "--help", and "-?".  A help description is given only for "-help".
     */
    private final Option[] options = new Option[]{
        new Option("help", Option.MAY, "plugin name", "Show this help.",
            HelpPlugin.this),
        new Option("-help", Option.MAY, "plugin name", HelpPlugin.this),
        new Option("?", Option.MAY, "plugin name", HelpPlugin.this),};

    /**
     * Returns {@linkplain #options the help plugin's options}.
     */
    public Option[] getOptions()
    {
      return options;
    };

    /**
     * Help text for the help plugin.
     */
    public String getHelp()
    {
      return "Displays help for all plugins.";
    };

    /**
     * Handler for all of the help plugin's options.
     * If an argument is given tries to give help on only the plugin with that option name.
     * Otherwise gives help for all plugins.
     */
    public void handleOption(Option option, String argument)
        throws BadOptionException
    {
      System.err.println(programName + " help");
      System.err.println(programHelp);
      System.err.println();
      System.err.println(programName + " [<plugin selector options>] -help");
      System.err.println(programName + " [<plugin selector options>]"
          + " [<per plugin options>]");
      System.err.println();

      if (argument != null) {
        if (argument.equals("help"))
          showHelpFor(this);
        else if (argument.equals("selector"))
          showHelpFor(pluginSelector);
        else if (byOptNameLookup.get(argument) == null)
          throw new BadOptionException(
              "The help option's argument must be a plugins option name.  "
                  + "Run '" + programName + " -help' (option names are in "
                  + "brackets).");
        else
          try {
            showHelpFor(getPlugin(argument));
          } catch (PluginInstantiationException ex) {
            throw new BadOptionException(ex);
          };
      }
      else {
        showHelpFor(this);
        showHelpFor(pluginSelector);
        for (Iterator it = pluginOrder.iterator(); it.hasNext();)
          try {
            showHelpFor(getPlugin((String) it.next()));
          } catch (PluginInstantiationException ex) {
            throw new BadOptionException(ex);
          };
      };
      System.exit(0);
    };

    /**
     * Gives help for one plugin.
     */
    private void showHelpFor(Plugin plugin)
    {
      System.err.println(getPluginName(plugin) + " ("
          + getPluginOptionName(plugin) + "):");
      System.err.println(plugin.getHelp());
      Option[] options = plugin.getOptions();
      final String space = "                                        ";
      for (int i = 0; i < options.length; i++) {
        if (!options[i].showInHelp)
          continue;
        String line1 = "  ";
        if (options[i].optionName != null)
          line1 += "-" + options[i].optionName + " ";
        if (options[i].takesArgument == Option.MAY)
          line1 += "[";
        if (options[i].takesArgument != Option.MUSTNOT)
          line1 += "<"
              + (options[i].argumentName == null
                  ? "argument"
                  : options[i].argumentName) + ">";
        if (options[i].takesArgument == Option.MAY)
          line1 += "]";

        if (options[i].help != null && options[i].help[0] != null
            && options[i].help[0].length() > 0) {
          try {
            line1 += space.substring(line1.length());
          } catch (StringIndexOutOfBoundsException ex) {//Don't add anything then
          };
          line1 += "  " + options[i].help[0];
          System.err.println(line1);
          for (int j = 1; j < options[i].help.length; j++)
            System.err.println(space + "  " + options[i].help[j]);
        }
      }
      System.err.println();
    };
  };

  /**
   * Finds an option supplied by a particular plugin.
   * @param option The name of the option being looked for.
   * @param plugin The plugin to look in.
   * @return The found <tt>Option</tt>, or null if it was not found.
   */
  public Option findOption(String option, Plugin plugin)
  {
    Option[] options = plugin.getOptions();
    for (int j = 0; j < options.length; j++)
      if (options[j].optionName == null && option == null)
        return options[j];
      else if (options[j].optionName != null
          && options[j].optionName.equals(option))
        return options[j];
    return null;
  };

  /**
   * Finds an option supplied by any plugin.
   * @param option The name of the option being looked for.
   * @return The found <tt>Option</tt>, or null if it was not found.
   */
  public Option findOption(String option) throws BadOptionException
  {
    for (Iterator it = pluginOrder.iterator(); it.hasNext();)
      try {
        Plugin plugin = getPlugin((String) it.next());
        Option opt = findOption(option, plugin);
        if (opt != null)
          return opt;
      } catch (PluginInstantiationException ex) {
        throw new BadOptionException(ex);
      }
    return null;
  };

  /**
   * Processes all command line options.
   * Looks up options, creates actual plugins, and runs the appropriate options through the appropriate 
   * plugins.
   * @param options The String array containing the options.
   */
  public void processOptions(String[] options) throws BadOptionException
  {
    processOptions(Arrays.asList(options));
  };

  /**
   * Processes all command line options.
   * Looks up options, creates actual plugins, and runs the appropriate options through the appropriate 
   * plugins.
   * @param options The String list containing the options.
   */
  public void processOptions(List<String> options) throws BadOptionException
  {
    processOptions(options.listIterator());
  };

  /**
   * Processes all command line options.
   * Looks up options, creates actual plugins, and runs the appropriate options through the appropriate 
   * plugins.<br/>
   * When option processing has finished it runs the handlers for all anonymous options that don't 
   * <em>require</em> an argument.
   * @param it The String list iterator containing the options.
   */
  public void processOptions(ListIterator<String> it) throws BadOptionException
  {
    //XXX add code so that you can specify which plugin an option goes to.
    //XXX e.g. 'Generator -help:help' or 'Generator -selector:bean-plugin'
    boolean inSelectorOptions = true;
    for (; it.hasNext();) {
      String option = (String) it.next();
      String argument = null;
      if (!option.startsWith("-")) {//Options start with '-' if it isn't there
        argument = option; //we have an anonymous option with an
        option = null; //argument.
      }
      else if (it.hasNext()) {
        argument = (String) it.next();
        if (argument.startsWith("-")) {//If the next string starts with a '-'
          argument = null; //then it is an option, not an argument 
          it.previous();
        }
      }
      if (option != null)//Chop off the leading '-'
        option = option.substring(1);

      Option optToRun = null;
      //-help should only happen immediately after selector options
      if (inSelectorOptions
          && (optToRun = findOption(option, helpPlugin)) != null)
        inSelectorOptions = false;

      else {
        //selector options should all happen together near the start.
        inSelectorOptions = (inSelectorOptions && (optToRun = findOption(
            option, pluginSelector)) != null);
        if (!inSelectorOptions)
          optToRun = findOption(option);
      }
      if (optToRun == null) {
        String optArgPair;
        if (option == null)
          optArgPair = argument;
        else if (argument == null)
          optArgPair = "-" + option;
        else
          optArgPair = "-" + option + " " + argument;
        throw new BadOptionException("The option \"" + optArgPair
            + "\" wasn't handled by any plugin.");
      }
      //If the option doesn't take an argument, then the argument is obviously
      //seperate from this option.
      if (optToRun.takesArgument == Option.MUSTNOT && argument != null) {
        argument = null;
        it.previous();
      }
      if (optToRun.takesArgument == Option.MUST && argument == null)
        throw new BadOptionException("Option -" + option
            + " must take an argument.");
      optToRun.handler.handleOption(optToRun, argument);
    }
    //Call anonymous handlers without arguments to let the options know that option processing has finished.
    for (Iterator pIt = pluginOrder.iterator(); pIt.hasNext();)
      try {
        Plugin plugin = getPlugin((String) pIt.next());
        Option opt = findOption(null, plugin);
        if (opt != null && opt.takesArgument != Option.MUST)
          opt.handler.handleOption(opt, null);
      } catch (PluginInstantiationException ex) {
        throw new BadOptionException(ex);
      }
  };

  /**
   * Displays all program help on System.err.
   * Just calls the <tt>handleOption</tt> method for {@link #helpPlugin helpPlugin}.
   */
  public void displayHelp()
  {
    try {
      helpPlugin.handleOption(helpPlugin.getOptions()[0], null);
    } catch (BadOptionException ex) {
      throw new Error(
          "The help plugin's handleOption method shouldn't throw an exception when it's "
              + "argument parameter is null.", ex);
    };
  };
};
