package net.sourceforge.czt.z2alloy.ast;


/**
 * Represents an Alloy Command. These have the form:
 * <pre>cmdDecl ::= [name ":"] ["run"|"check"] [name|block] scope</pre>
 * These do not support changes in scope at this time
 */
public class Command {
  /** The name of the command (optional) */
  private final String label;
  /** True if the command is a 'check', false if it is a 'run' */
  private final boolean isCheck;
  /** The body of the expression the command must satisfy. If it satisfies a function, it is null */
  private final AlloyExpr bodyExpr;
  /** The function the command must satisfy. If it satisfies an expression, it is null */
  private final Func bodyFunc;

  /** Used to give unnamed commands different command */
  private static int i = 0;

  /**
   * Creates a command without a given name which satisfies a given expression
   * @param isCheck True if the command is a 'check', false if it is a 'run'
   * @param bodyExpr The body of the expression the command must satisfy
   * */
  public Command (boolean isCheck, AlloyExpr bodyExpr) {
    this(isCheck ? "check_" : "run " + i++, isCheck, bodyExpr);
  }

  /**
   * Creates a command without a given name which has a body in the form: <pre>func</pre>
   * @param isCheck True if the command is a 'check', false if it is a 'run'
   * @param bodyFunc The function the command must satisfy
   */
  public Command (boolean isCheck, Func bodyFunc) {
    this(isCheck ? "check_" : "run " + i++, isCheck, bodyFunc);
  }

  /**
   * Creates a command with a given label which satisfies a given expression
   * @param label The label of the command
   * @param isCheck True if the command is a 'check', false if it is a 'run'
   * @param bodyExpr The expression the command must satisfy
   */
  public Command (String label, boolean isCheck, AlloyExpr bodyExpr) {
    this.label = label;
    this.isCheck = isCheck;
    this.bodyExpr = bodyExpr;
    this.bodyFunc = null;
  }

  /**
   * Creates a command with a given label which satisfies the given function
   * @param label The label of the command
   * @param isCheck True if the command is a 'check', false if it is a 'run'
   * @param bodyFunc The function the command must satisfy
   */
  public Command (String label, boolean isCheck, Func bodyFunc) {
    this.label = label;
    this.isCheck = isCheck;
    this.bodyExpr = null;
    this.bodyFunc = bodyFunc;
  }

  public Command (Command that) {
    this.label = that.label;
    this.isCheck = that.isCheck;
    this.bodyExpr = that.bodyExpr == null ? null : that.bodyExpr;
    this.bodyFunc = that.bodyFunc == null ? null : that.bodyFunc;
  }

  public String label() {
    return label;
  }

  public boolean check() {return isCheck;}
  public boolean run() {return !check();}
  public AlloyExpr bodyExpr() {return bodyExpr == null ? null : bodyExpr;}
  public Func bodyFunc() {return bodyFunc == null ? null : bodyFunc;}

  public String toString() {
    return label;
  }
}
