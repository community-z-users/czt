package net.sourceforge.czt.z2alloy.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class Func {

  private final String label;

  private final boolean isPred;

  private final List<ExprVar> params;

  private final AlloyExpr returnDecl;

  private AlloyExpr body;

  public Func(String label, List<ExprVar> params, AlloyExpr returnDecl) {
    this.label = label;
    this.isPred = false;
    this.params = Collections.unmodifiableList(params);
    this.returnDecl = returnDecl;
    body = ExprConstant.TRUE;
  }

  public Func(String label, List<ExprVar> params) {
    this.label = label;
    this.isPred = true;
    this.params = Collections.unmodifiableList(params);
    this.returnDecl = null;
    body = ExprConstant.TRUE;
  }

  public AlloyExpr getBody() {
    return body;
  }

  public AlloyExpr setBody(AlloyExpr body) {
    AlloyExpr temp = this.body;
    this.body = body;
    return temp;
  }

  public ExprCall call(List<? extends AlloyExpr> args) {
    return new ExprCall(this, args);
  }

  public ExprCall call(AlloyExpr... args) {
    return new ExprCall(this, Arrays.asList(args));
  }

  public String toString() {
    if (isPred)
      return "pred " + label;
    return "fun " + label;
  }

  public String label() {
    return label;
  }

  public boolean pred() {
    return isPred;
  }

  public boolean fun() {
    return !pred();
  }

  public List<ExprVar> params() {
    List<ExprVar> params = new ArrayList<ExprVar>();
    for (ExprVar param : this.params)
      params.add(param);
    return params;
  }

  public AlloyExpr returnDecl() {
    return returnDecl;
  }

  public AlloyExpr body() {
    return body;
  }

}
