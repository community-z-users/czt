package net.sourceforge.czt.animation.gui.generation.plugins;

import java.io.OutputStream;

import java.net.URL;

import net.sourceforge.czt.animation.gui.generation.Plugin;

public interface InterfaceDestination extends Plugin {
  public static final String optionName="destination";
  public static final String name="Interface Destination";

  public OutputStream obtainOutputStream(URL inputURL) throws IllegalStateException;
};
