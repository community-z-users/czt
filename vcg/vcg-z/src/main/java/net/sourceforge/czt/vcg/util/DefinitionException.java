/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 *
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.vcg.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorImpl;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.LocAnn;

public class DefinitionException extends InfoTable.InfoTableException
        implements CztErrorList, CztError
{

  /**
	 * 
	 */
	private static final long serialVersionUID = 966184787203124820L;
private final LocAnn locAnn_;
  private final List<DefinitionException> exceptions_;
  private ErrorType errorType_ = ErrorType.ERROR;
  private int transitiveErrors_ = 0;
  private List<DefinitionException> transitiveExp_ = null;


  public DefinitionException(Dialect d, String message)
  {
    this(d, null, message);
  }

  public DefinitionException(Dialect d, String message, List<DefinitionException> exceptions)
  {
    this(d, null, message, exceptions);
  }

  public DefinitionException(Dialect d, Term term, String message)
  {
    this(d, term.getAnn(LocAnn.class), message);
  }

  public DefinitionException(Dialect d, Term term, String message, Throwable cause)
  {
    this(d, term.getAnn(LocAnn.class), message, cause);
  }

  public DefinitionException(Dialect d, Term term, String message, List<DefinitionException> exceptions)
  {
    this(d, term.getAnn(LocAnn.class), message, exceptions);
  }

  public DefinitionException(Dialect d, LocAnn loc, String message)
  {
    super(d, message);
    locAnn_ = loc;
    exceptions_ = Collections.emptyList();
  }
  
  public DefinitionException(Dialect d, LocAnn loc, String message, Throwable cause)
  {
    super(d, message, cause);
    locAnn_ = loc;
    exceptions_ = Collections.emptyList();
  }

  public DefinitionException(Dialect d, LocAnn loc, String message, List<DefinitionException> exceptions)
  {
    super(d, message);
    locAnn_ = loc;
    exceptions_ = Collections.unmodifiableList(exceptions);
  }

  public LocAnn getLoc()
  {
    return locAnn_;
  }

  public List<DefinitionException> getExceptions()
  {
    return exceptions_;
  }

  public List<DefinitionException> getTransitiveExceptions()
  {
    if (transitiveExp_ == null)
    {
      transitiveExp_ = new ArrayList<DefinitionException>();
      transitiveExp_.add(this);
      for (DefinitionException de : exceptions_)
      {
        transitiveExp_.addAll(de.getTransitiveExceptions());
      }
    }
    assert transitiveExp_.size() >= exceptions_.size();
    return transitiveExp_;
  }

  public int totalNumberOfErrors()
  {
    if (transitiveErrors_ == 0)
    {
      transitiveErrors_ = 1;
      for(DefinitionException de : exceptions_)
      {
        transitiveErrors_ += de.totalNumberOfErrors();
      }
    }
    assert transitiveErrors_ >= exceptions_.size();
    return transitiveErrors_;
  }

/*
  public DefinitionException getError(int index)
  {
    if (index <= 0)
      return this;
    else if (index > 0 && index < exceptions_.size())
      return exceptions_.get(index-1);
    else
      return exceptions_.
  }*/

  private static int innerExpDepth_ = 0;
  private static String asMany(char ch, int count)
  {
    StringBuilder builder = new StringBuilder(count);
    while (count > 0)
    {
      builder.append(ch);
      count--;
    }
    return builder.toString();
  }
  
  private static synchronized final void increaseInnerExprDepth()
  {
	  innerExpDepth_++;
  }

  private static synchronized final void decreaseInnerExprDepth()
  {
	  innerExpDepth_--;
  }

  public String getMessage(boolean printInner)
  {
    final String s = super.getMessage();
    StringBuilder result = null;
    if (!exceptions_.isEmpty() && printInner)
    {
      increaseInnerExprDepth();
      // previous msg + msg below + about 30 in length for each exception +/-
      result = new StringBuilder(s.length() + 40 + (exceptions_.size()+1 * 30));
      result.append(" with inner definition exceptions list as:");
      for(DefinitionException de : exceptions_)
      {
        result.append('\n');
        result.append(asMany('\t', innerExpDepth_));
        result.append(de.getMessage());
      }
      decreaseInnerExprDepth();
    }
    return s + (result != null ? result.toString() : "");
  }

  @Override
  public String getMessage()
  {
    return getMessage(true);
  }

  @Override
  public List<? extends CztError> getErrors()
  {
    return getTransitiveExceptions();
  }

  @Override
  public ErrorType getErrorType()
  {
    return errorType_;
  }

  public void setErrorType(ErrorType errorType)
  {
    errorType_ = errorType;
  }

  @Override
  public String getInfo()
  {

    return transitiveErrors_ > 0 ? "\t with " + transitiveErrors_ + " inner error(s)" : null;
  }

  @Override
  public int getLine()
  {
    return locAnn_ != null ? locAnn_.getLine().intValue() : -1;
  }

  @Override
  public int getColumn()
  {
    return locAnn_ != null ? locAnn_.getCol().intValue() : -1;
  }

  @Override
  public int getStart()
  {
    return locAnn_ != null ? locAnn_.getStart().intValue() : -1;
  }

  @Override
  public int getLength()
  {
    return locAnn_ != null ? locAnn_.getLength().intValue() : -1;
  }

  @Override
  public String getSource()
  {
    return locAnn_ != null ? locAnn_.getLoc() : "";
  }

  @Override
  public int compareTo(CztError o)
  {
    return CztErrorImpl.compareCztErrorPositionTypeAndMessage(this, o);
  }
  
  @Override
  public int hashCode()
  {
	  return CztErrorImpl.baseHashCodeCztError(this);
  }
  
  @Override
  public boolean equals(Object o)
  {
	  return CztErrorImpl.compareCztErrorsEquals(this, o);
  }

@Override
public boolean hasSectionInfo() {
	// TODO Auto-generated method stub
	return false;
}

@Override
public SectionInfo getSectionInfo() {
	// TODO Auto-generated method stub
	return null;
}
}
