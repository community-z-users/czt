
  private net.sourceforge.czt.zpatt.util.Deduction deduction_;

  public net.sourceforge.czt.zpatt.util.Deduction getDeduction()
  {
    return deduction_;
  }

  public void setDeduction(net.sourceforge.czt.zpatt.util.Deduction deduction)
  {
    deduction_ = deduction;
    deduction_.setConclusion(this);
  }

