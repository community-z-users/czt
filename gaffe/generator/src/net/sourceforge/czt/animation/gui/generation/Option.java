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

/**
 * Description of a command line option.
 * @author Nicholas Daley
 */
public final class Option
{
  /**
   * The name of the option.  On the command line this appears with a - in front
   * of it.  e.g. If optionName was "help", then this option would be accessed
   * on the command line as "-help".<br/>
   * If <tt>optionName</tt> is <tt>null</tt>, and it takes an argument, then it
   * is an anoynymous option; i.e. an argument appears by itself, without an
   * option preceding it.<br/>
   * When {@link PluginList} stops processing <tt>Option</tt>s, it runs
   * OptionHandlers for anonymous options that <em>don't</em> take arguments.
   * i.e. <tt>optionName==null && takesArgument!=MUST</tt>.<br/>
   * <br/>
   * This String should follow the pattern ^[a-zA-Z][a-zA-Z0-9_\-]*$.  That is,
   * it should start with a letter, and may follow with a sequence of letters,
   * digits, underscores and dashes.  Any other punctuation is reserved, and may
   * be used by {@link PluginList} for its own purposes, especially . and :
   * which may be used for namespacing options in future versions.
   */
  public final String optionName;

  /**
   * Indicates whether this command line option takes an argument.
   * This is used by {@link PluginList PluginList} when processing command line options, and displaying help.
   * Can be: {@link #MUST MUST}, {@link #MAY MAY}, or {@link #MUSTNOT MUSTNOT}.
   */
  public final int takesArgument;

  /**
   * Constant for {@link #takesArgument takesArgument}.
   * Indicates that this command line option is required to take one argument.
   */
  public final static int MUST = 0;

  /**
   * Constant for {@link #takesArgument takesArgument}.
   * Indicates that this command line option may take either zero or one arguments.
   */
  public final static int MAY = 1;

  /**
   * Constant for {@link #takesArgument takesArgument}.
   * Indicates that this command line option must not take any arguments.
   */
  public final static int MUSTNOT = 2;

  /**
   * Name of this option's argument.  Used in help displays.
   */
  public final String argumentName;

  /**
   * Flag indicating whether this option should appear in help displays.
   */
  public final boolean showInHelp;

  /** 
   * Text for use in help displays.
   */
  public final String[] help;

  /**
   * OptionHandler to run when this option is used.
   * Similar in purpose to a Listener in java beans.
   */
  public final OptionHandler handler;

  /**
   * Constructor.
   * {@link #showInHelp showInHelp} is set to true unless hlp is null.
   * @param name Sets {@link #optionName optionName}.
   * @param takeArg Sets {@link #takesArgument takesArgument}.
   * @param argName Sets {@link #argumentName argumentName}.
   * @param hlp Sets {@link #help help}.
   * @param handl Sets {@link #handler handler}.
   */
  public Option(String name, int takeArg, String argName, String[] hlp,
      OptionHandler handl)
  {
    optionName = name;
    takesArgument = takeArg;
    argumentName = argName;
    showInHelp = (hlp != null);
    help = hlp;
    handler = handl;
  };

  /**
   * Constructor.
   * {@link #showInHelp showInHelp} is set to false. {@link #help help} is set to null.
   * @param name Sets {@link #optionName optionName}.
   * @param takeArg Sets {@link #takesArgument takesArgument}.
   * @param argName Sets {@link #argumentName argumentName}.
   * @param handler Sets {@link #handler handler}.
   */
  public Option(String name, int takeArg, String argName, OptionHandler handler)
  {
    this(name, takeArg, argName, (String[]) null, handler);
  };

  /**
   * Constructor.
   * {@link #showInHelp showInHelp} is set to true.
   * @param name Sets {@link #optionName optionName}.
   * @param takeArg Sets {@link #takesArgument takesArgument}.
   * @param argName Sets {@link #argumentName argumentName}.
   * @param hlp Sets {@link #help help} to be only one line equaling hlp.
   * @param handl Sets {@link #handler handler}.
   */
  public Option(String name, int takeArg, String argName, String hlp,
      OptionHandler handl)
  {
    this(name, takeArg, argName, new String[]{hlp}, handl);
  };

  /**
   * Constructor.
   * Constructs an option to handle the end of option processing.
   * (Anonymous option with no argument).
   */
  public Option(OptionHandler handl)
  {
    this(null, MUSTNOT, (String) null, (String[]) null, handl);
  };
};
