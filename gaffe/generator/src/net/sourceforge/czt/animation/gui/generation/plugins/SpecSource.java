package net.sourceforge.czt.animation.gui.generation.plugins;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.core.ast.Term;

public interface SpecSource extends Plugin {
  public Term obtainSpec() throws IllegalStateException;
};
