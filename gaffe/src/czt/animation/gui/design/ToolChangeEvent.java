package czt.animation.gui.design;

import java.util.EventObject;

class ToolChangeEvent extends EventObject {
  private ToolWindow.Tool tool;

  public ToolChangeEvent(Object source, ToolWindow.Tool tool) {
    super(source);
    this.tool=tool;
  };
  
  public ToolWindow.Tool getTool() {
    return tool;
  };
};
