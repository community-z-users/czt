/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.modeljunit;

import java.util.List;

/** Exceptions related to failed tests. */
@SuppressWarnings("serial")
public class TestFailureException extends RuntimeException
{
  /** The model that was used to generate the failed test. */
  private FsmModel model;
  
  /** The name of the model that was used to generate the failed test. */
  private String modelName;
  
  /** The action that caused the failure. */
  private String actionName;
  
  /** The state of the model just before the failure. */
  private Object state;

  /** The complete sequence of actions leading to the failure.
   *  May be null if this was not recorded.
   */
  private List<Transition> sequence;
  
  /**
   * @return the actionName
   */
  public String getActionName()
  {
    return actionName;
  }

  public void setActionName(String actionName)
  {
    this.actionName = actionName;
  }

  /**
   * @return the model used to generate the failed test.
   */
  public FsmModel getModel()
  {
    return model;
  }

  public void setModel(FsmModel model)
  {
    this.model = model;
  }

  /**
   * @return the modelName
   */
  public String getModelName()
  {
    return modelName;
  }

  public void setModelName(String modelName)
  {
    this.modelName = modelName;
  }

  /**
   * @return the entire sequence of transitions before the test failure.
   *   This may be null if it was not recorded.
   */
  public List<Transition> getSequence()
  {
    return sequence;
  }

  public void setSequence(List<Transition> sequence)
  {
    this.sequence = sequence;
  }

  /**
   * @return the state of the model just before the test failure.
   */
  public Object getState()
  {
    return state;
  }

  public void setState(Object state)
  {
    this.state = state;
  }

  public TestFailureException() {
    super();
  }

  public TestFailureException(String message) {
    super(message);
  }

  public TestFailureException(String message, Throwable cause) {
    super(message, cause);
  }

  public TestFailureException(Throwable cause) {
    super(cause);
  }
}
