package net.sourceforge.czt.animation.gui.generation;

public final class Option {
  public final String optionName;

  public final int takesArgument;
  public final static int MUST=0;
  public final static int MAY=1;
  public final static int MUSTNOT=2;
  public final String argumentName;

  public final boolean showInHelp;
  public final String[] help;

  public final OptionHandler handler;
    
  public Option(String name, int takeArg, String argName, String[] hlp, 
		OptionHandler handl) {
    optionName=name;
    takesArgument=takeArg;
    argumentName=argName;
    showInHelp=(hlp!=null);
    help=hlp;
    handler=handl;
  };
  public Option(String name, int takeArg, String argName, 
		OptionHandler handler) {
    this(name,takeArg,argName,(String[])null,handler);
  };
  public Option(String name, int takeArg, String argName, String hlp, 
		OptionHandler handl) {
    this(name,takeArg,argName,new String[]{hlp},handl);
  };
};
