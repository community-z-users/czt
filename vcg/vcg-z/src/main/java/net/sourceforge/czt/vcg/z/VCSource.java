package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.z.ast.Para;

public class VCSource
{
  private final Para sourcePara;
  private final VC<?> sourceVC;
  
  public VCSource(Para sourcePara) {
    this.sourcePara = sourcePara;
    this.sourceVC = null;
  }
  
  public VCSource(VC<?> sourceVC) {
    this.sourcePara = sourceVC.getVCPara();
    this.sourceVC = sourceVC;
  }

  public Para getSourcePara()
  {
    return sourcePara;
  }

  public VC<?> getSourceVC()
  {
    return sourceVC;
  }
  
}
