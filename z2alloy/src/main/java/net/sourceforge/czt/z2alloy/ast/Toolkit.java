package net.sourceforge.czt.z2alloy.ast;

import static net.sourceforge.czt.z2alloy.ast.Sig.UNIV;
import static net.sourceforge.czt.z2alloy.ast.Sig.SIGINT;

import java.util.ArrayList;
import java.util.List;

public class Toolkit extends Module {

  public Toolkit() {
    super();
  }

  public Func getFunc(String label) {
    Func ret = super.getFunc(label);
    if (ret == null) {
      ret = libFunc(label);
      if (ret == null) {
        ret = add(label);
        if (ret != null) {
          super.addFunc(ret);
        }
      }
    }
    return ret;
  }
  
  private Func libFunc(String label) {
    ExprVar x = new ExprVar("x", UNIV);
    ExprVar y = new ExprVar("y", UNIV);
    List<ExprVar> twoArgs = new ArrayList<ExprVar>();
    twoArgs.add(x);
    twoArgs.add(y);
    List<ExprVar> oneArg = new ArrayList<ExprVar>();
    oneArg.add(x);
    if (label.equals("negate")) {
      return new Func("integer/negate", oneArg, SIGINT);
    }
    else if (label.equals("sub")) {
      return new Func("integer/sub", twoArgs, SIGINT);
    }
    else if (label.equals("add")) {
      return new Func("integer/add", twoArgs, SIGINT);
    }
    else if (label.equals("mul")) {
      return new Func("integer/mul", twoArgs, SIGINT);
    }
    else if (label.equals("div")) {
      return new Func("integer/div", twoArgs, SIGINT);
    }
    else if (label.equals("rem")) {
      return new Func("integer/rem", twoArgs, SIGINT);
    }
    else if (label.equals("next")) {
      return new Func("integer/next", oneArg, SIGINT);
    }
    else if (label.equals("append")) {
      List<ExprVar> vars = new ArrayList<ExprVar>();
      vars.add(new ExprVar("s1", UNIV.seq()));
      vars.add(new ExprVar("s2", UNIV.seq()));
      return new Func("seq/append", vars, UNIV.seq());
    }
    else if (label.equals("last")) {
        List<ExprVar> vars = new ArrayList<ExprVar>();
        vars.add(new ExprVar("s", UNIV.seq()));
        return new Func("seq/last", vars, UNIV.one());
    }
    else if (label.equals("front")) {
      List<ExprVar> vars = new ArrayList<ExprVar>();
      vars.add(new ExprVar("s", UNIV.seq()));
      return  new Func("seq/front", vars, UNIV.seq());
    }
    else {
      return null;
    }
  }

  private Func add(String label) {
    if (label.equals("ndres")) {
      return ndres();
    }
    else if (label.equals("dom")) {
      return dom();
    }
    else if (label.equals("ran")) {
      return ran();
    }
    else {
      return null;
    }

  }

  private Func ndres() {
    List<ExprVar> vars = new ArrayList<ExprVar>();
    ExprVar r = new ExprVar("r", UNIV.product(UNIV));
    vars.add(r);
    Func dom = new Func("dom", vars, UNIV.setOf());

    ExprVar ex = new ExprVar("ex", UNIV.setOf());
    r = new ExprVar("r", UNIV.product(UNIV));
    vars.clear();
    vars.add(ex);
    vars.add(r);
    Func ndres = new Func("ndres", vars, UNIV.product(UNIV));
    dom.setBody(r.join(UNIV));
    ndres.setBody((dom.call(r)).minus(ex).domain(r));
    return ndres;
  }

  private Func dom() {
    List<ExprVar> vars = new ArrayList<ExprVar>();
    ExprVar r = new ExprVar("r", UNIV.product(UNIV));
    vars.add(r);
    Func dom = new Func("dom", vars, UNIV.setOf());
    dom.setBody(r.join(UNIV));
    return dom;
  }

  private Func ran() {
    List<ExprVar> vars = new ArrayList<ExprVar>();
    ExprVar r = new ExprVar("r", UNIV.product(UNIV));
    vars.add(r);
    Func dom = new Func("ran", vars, UNIV.setOf());
    dom.setBody(UNIV.join(r));
    return dom;
  }

}
