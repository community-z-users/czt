package net.sourceforge.czt.typecheck.util.typeerror;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class TypeException extends RuntimeException
{
  //the type of error (see class ErrorKind)
  private int kind_;  

  //the two terms causing the conflict
  private Term term1_;
  private Term term2_;

  //an error message
  private String message_;

  public TypeException(String message)
  {
    this(-1, null, null, message);
  }

  public TypeException (int kind, Term term)
  {
    this(kind, term, null, null);
  }

  public TypeException (int kind, Term term1, String message)
  {
    this(kind, term1, null, message);
  }

  public TypeException (int kind, Term term1, Term term2)
  {
    this(kind, term1, term2, null);
  }

  public TypeException (int kind, Term term1, Term term2, String message)
  {
    kind_ = kind;
    term1_ = term1;
    term2_ = term2;
    message_ = message;
  }

  public int getKind()
  {
    return kind_;
  }

  public Term getTerm1()
  {
    return term1_;
  }

  public void setTerm1(Term term)
  {
    term1_ = term;
  }

  public Term getTerm2()
  {
    return term2_;
  }

  public void setTerm2(Term term)
  {
    term2_ = term;
  }

  public String getMessage()
  {
    return message_;
  }

  public void setMessage(String message)
  {
    message_ = message;
  }

  public String toString()
  {
    String cause = new String();

    if (kind_ != -1) {
      cause += ErrorKind.getCase(kind_);
    }

    if (message_ != null) {
      cause += "\n" + message_;
    }
    return cause;
  }
}
