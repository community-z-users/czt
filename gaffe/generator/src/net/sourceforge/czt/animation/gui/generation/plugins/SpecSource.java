package net.sourceforge.czt.animation.gui.generation.plugins;

import java.net.URL;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.base.ast.Term;

public interface SpecSource extends Plugin {
  public static final String optionName="source";
  public static final String name="Specification Source";

  public Term obtainSpec() throws IllegalStateException;
  public URL getURL();  
};
