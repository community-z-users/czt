package net.sourceforge.czt.typecheck.util.typeerror;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class TypeException extends Throwable
{
  private int kind_;
  private Term term1_;
  private Term term2_;

  public TypeException (int kind, Term term)
  {
    kind_ = kind;
    term1_ = term;
  }

  public TypeException (int kind, Term term1, Term term2)
  {
    kind_ = kind;
    term1_ = term1;
    term2_ = term2;
  }

  public String toString()
  {
    String cause = ErrorKind.getCase(kind_);
    /*
      String name = null;
      String cause = null;
      switch (kind_) {
        case REDECLARATION:
        if (term instanceof DeclName) {
          name = ((DeclName) term).getName().getId();
          cause
        }
        case UNKNOWN_ERROR:
        default:
          break;
      }
    */
    return cause;
  }
}
