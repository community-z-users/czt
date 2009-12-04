package net.sourceforge.czt.z2alloy.ast;

import static net.sourceforge.czt.z2alloy.ast.Sig.UNIV;

import java.util.ArrayList;
import java.util.List;

public class Toolkit extends Module {

  public Toolkit() {
    super();
//    addFunc(ndres());
//    addFunc(append());
//    addFunc(dom());
//    addFunc(ran());
//    addFunc(last());
//    addFunc(front());
  }

  public Func getFunc(String label) {
    Func ret = super.getFunc(label);
    if (ret == null) {
        ret = add(label);
        if (ret != null) {
          super.addFunc(ret);
        }
    }
    return ret;
  }
  
  private Func add(String label) {
    if (label.equals("ndres")) {
      return ndres();
    }
    else if (label.equals("append")) {
      return append();
    }
    else if (label.equals("dom")) {
      return dom();
    }
    else if (label.equals("ran")) {
      return ran();
    }
    else if (label.equals("last")) {
      return last();
    }
    else if (label.equals("front")) {
      return front();
    }
    return null;
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

  private Func append() {
    ExprVar s1 = new ExprVar("s1", UNIV.seq());
    ExprVar s2 = new ExprVar("s2", UNIV.seq());
    List<ExprVar> vars = new ArrayList<ExprVar>();
    vars.add(s1);
    vars.add(s2);
    AlloyExpr res = UNIV.seq();
    Func append = new Func("append", vars, res);

    Func seqappend = new Func("seq/append", vars, res);

    append.setBody(seqappend.call(s1, s2));
    return append;
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

  private Func last() {
    ExprVar s = new ExprVar("s", UNIV.seq());
    List<ExprVar> vars = new ArrayList<ExprVar>();
    vars.add(s);
    AlloyExpr ret = UNIV.oneOf();
    Func last = new Func("last", vars, ret);
    Func seqlast = new Func("seq/last", vars, ret);

    last.setBody(seqlast.call(s));
    return last;
  }

  private Func front() {
    ExprVar s = new ExprVar("s", UNIV.seq());
    List<ExprVar> vars = new ArrayList<ExprVar>();
    vars.add(s);
    AlloyExpr ret = UNIV.seq();

    Func front = new Func("front", vars, ret);
    Func butLast = new Func("seq/butlast", vars, ret);

    front.setBody(butLast.call(s));
    return front;
  }
}
