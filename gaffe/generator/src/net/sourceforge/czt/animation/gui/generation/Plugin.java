package net.sourceforge.czt.animation.gui.generation;

import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;

public interface Plugin {
  public void handleArgs(ListIterator args) throws BadArgumentsException;
};
  
