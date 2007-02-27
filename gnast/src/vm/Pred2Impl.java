  public Pred getLeftPred()
  {
    Pred result = null;
    if (getPred().size() > 0) {
      result = getPred().get(0);
    }
    return result;
  }

  public void setLeftPred(Pred pred)
  {
    if (getPred().size() > 0) {
      getPred().set(0, pred);
    }
    else {
      getPred().add(pred);
    }
  }

  public Pred getRightPred()
  {
    Pred result = null;
    if (getPred().size() > 1) {
      result = getPred().get(1);
    }
    return result;
  }

  public void setRightPred(Pred pred)
  {
    if (getPred().size() == 0) {
      getPred().add(null);
    }
    if (getPred().size() > 1) {
      getPred().set(1, pred);
    }
    else {
      getPred().add(pred);
    }
  }
