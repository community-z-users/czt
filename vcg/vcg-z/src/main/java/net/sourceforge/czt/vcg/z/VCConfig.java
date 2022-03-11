package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.z.ast.ZNameList;

public class VCConfig
{
  
  public enum Precedence {
    BEFORE,
    AFTER
  }
  
  private final String type;
  private final Precedence precedence;
  private final ZNameList vcGenParams;
  
  public VCConfig(String type, Precedence precedence)
  {
    this(type, precedence, null);
  }
  
  public VCConfig(String type, Precedence precedence, ZNameList vcGenParams)
  {
    super();
    
    this.type = type;
    this.precedence = precedence;
    this.vcGenParams = vcGenParams;
  }

  public String getType()
  {
    return type;
  }

  public Precedence getPrecedence()
  {
    return precedence;
  }

  public ZNameList getGenParams()
  {
    return vcGenParams;
  }

}
