package czt.animation.gui.design;

import java.util.EventObject;

class ToolChangeEvent extends EventObject {
  private ToolWindow.Tool tool;
  private ToolWindow.Tool oldTool;
  public ToolChangeEvent(Object source, ToolWindow.Tool tool, ToolWindow.Tool oldTool) {
    super(source);
    this.tool=tool;
    this.oldTool=oldTool;
  };
  
  public ToolWindow.Tool getTool() {
    return tool;
  };
  public ToolWindow.Tool getOldTool() {
    return oldTool;
  };
};
