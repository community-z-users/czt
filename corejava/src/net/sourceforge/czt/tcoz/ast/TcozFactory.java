
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE CoreFactory.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004 Mark Utting
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
******************************************************************************/

package net.sourceforge.czt.tcoz.ast;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;

/**
 * <p>The object factory for the AST.
 * This interface contains factory methods
 * for each concrete Z term.</p>
 *
 * <p>This object factory allows the programmer to programatically
 * construct new instances of concrete Z terms.
 * There is a factory method that does not require arguments
 * (called default factory method)
 * and a factory method where all the children (except annotations)
 * of that particular Z term can be provided.</p>
 *
 * @author Gnast version 0.1
 */
public interface TcozFactory
  extends net.sourceforge.czt.oz.ast.OzFactory
{
  /**
   * Creates an instance of {@link RecProExpr}.
   *
   * @return the new instance of RecProExpr.
   */
  RecProExpr createRecProExpr();

  /**
   * Creates an instance of {@link RecProExpr} with the given children.
   *
   * @return the new instance of RecProExpr.
   */
  RecProExpr createRecProExpr(net.sourceforge.czt.z.ast.RefName opName, net.sourceforge.czt.oz.ast.OperationExpr operationExpr);

  /**
   * Creates an instance of {@link WaitUntilProExpr}.
   *
   * @return the new instance of WaitUntilProExpr.
   */
  WaitUntilProExpr createWaitUntilProExpr();

  /**
   * Creates an instance of {@link WaitUntilProExpr} with the given children.
   *
   * @return the new instance of WaitUntilProExpr.
   */
  WaitUntilProExpr createWaitUntilProExpr(net.sourceforge.czt.oz.ast.OperationExpr operationExpr, net.sourceforge.czt.z.ast.Expr1 waitUntil);

  /**
   * Creates an instance of {@link DeadlineProExpr}.
   *
   * @return the new instance of DeadlineProExpr.
   */
  DeadlineProExpr createDeadlineProExpr();

  /**
   * Creates an instance of {@link DeadlineProExpr} with the given children.
   *
   * @return the new instance of DeadlineProExpr.
   */
  DeadlineProExpr createDeadlineProExpr(net.sourceforge.czt.oz.ast.OperationExpr operationExpr, net.sourceforge.czt.z.ast.Expr1 deadline);

  /**
   * Creates an instance of {@link WaitProExpr}.
   *
   * @return the new instance of WaitProExpr.
   */
  WaitProExpr createWaitProExpr();

  /**
   * Creates an instance of {@link WaitProExpr} with the given children.
   *
   * @return the new instance of WaitProExpr.
   */
  WaitProExpr createWaitProExpr(net.sourceforge.czt.z.ast.Expr expr);

  /**
   * Creates an instance of {@link DivergeProExpr}.
   *
   * @return the new instance of DivergeProExpr.
   */
  DivergeProExpr createDivergeProExpr();

  /**
   * Creates an instance of {@link SynPllProExpr}.
   *
   * @return the new instance of SynPllProExpr.
   */
  SynPllProExpr createSynPllProExpr();

  /**
   * Creates an instance of {@link SynPllProExpr} with the given children.
   *
   * @return the new instance of SynPllProExpr.
   */
  SynPllProExpr createSynPllProExpr(EventSet events);

  /**
   * Creates an instance of {@link InterruptProExpr}.
   *
   * @return the new instance of InterruptProExpr.
   */
  InterruptProExpr createInterruptProExpr();

  /**
   * Creates an instance of {@link InterruptProExpr} with the given children.
   *
   * @return the new instance of InterruptProExpr.
   */
  InterruptProExpr createInterruptProExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp);

  /**
   * Creates an instance of {@link InterleaveProExpr}.
   *
   * @return the new instance of InterleaveProExpr.
   */
  InterleaveProExpr createInterleaveProExpr();

  /**
   * Creates an instance of {@link AtProExpr}.
   *
   * @return the new instance of AtProExpr.
   */
  AtProExpr createAtProExpr();

  /**
   * Creates an instance of {@link AtProExpr} with the given children.
   *
   * @return the new instance of AtProExpr.
   */
  AtProExpr createAtProExpr(Event event, net.sourceforge.czt.z.ast.Expr expr, net.sourceforge.czt.oz.ast.OperationExpr operationExpr);

  /**
   * Creates an instance of {@link Connection}.
   *
   * @return the new instance of Connection.
   */
  Connection createConnection();

  /**
   * Creates an instance of {@link Connection} with the given children.
   *
   * @return the new instance of Connection.
   */
  Connection createConnection(net.sourceforge.czt.oz.ast.RefNameList leftProcess, net.sourceforge.czt.oz.ast.RefNameList rightProcess, net.sourceforge.czt.oz.ast.RefNameList channels);

  /**
   * Creates an instance of {@link InterruptTimeOpExpr}.
   *
   * @return the new instance of InterruptTimeOpExpr.
   */
  InterruptTimeOpExpr createInterruptTimeOpExpr();

  /**
   * Creates an instance of {@link InterruptTimeOpExpr} with the given children.
   *
   * @return the new instance of InterruptTimeOpExpr.
   */
  InterruptTimeOpExpr createInterruptTimeOpExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp);

  /**
   * Creates an instance of {@link GuardProExpr}.
   *
   * @return the new instance of GuardProExpr.
   */
  GuardProExpr createGuardProExpr();

  /**
   * Creates an instance of {@link GuardProExpr} with the given children.
   *
   * @return the new instance of GuardProExpr.
   */
  GuardProExpr createGuardProExpr(net.sourceforge.czt.z.ast.SchText guard, net.sourceforge.czt.oz.ast.OperationExpr operationExpr);

  /**
   * Creates an instance of {@link StopProExpr}.
   *
   * @return the new instance of StopProExpr.
   */
  StopProExpr createStopProExpr();

  /**
   * Creates an instance of {@link SkipProExpr}.
   *
   * @return the new instance of SkipProExpr.
   */
  SkipProExpr createSkipProExpr();

  /**
   * Creates an instance of {@link ChannelExpr}.
   *
   * @return the new instance of ChannelExpr.
   */
  ChannelExpr createChannelExpr();

  /**
   * Creates an instance of {@link ChannelExpr} with the given children.
   *
   * @return the new instance of ChannelExpr.
   */
  ChannelExpr createChannelExpr(net.sourceforge.czt.z.ast.Expr expr, ChannelType channelType);

  /**
   * Creates an instance of {@link EventSet}.
   *
   * @return the new instance of EventSet.
   */
  EventSet createEventSet();

  /**
   * Creates an instance of {@link EventSet} with the given children.
   *
   * @return the new instance of EventSet.
   */
  EventSet createEventSet(java.util.List event);

  /**
   * Creates an instance of {@link Event}.
   *
   * @return the new instance of Event.
   */
  Event createEvent();

  /**
   * Creates an instance of {@link Event} with the given children.
   *
   * @return the new instance of Event.
   */
  Event createEvent(net.sourceforge.czt.z.ast.RefName name, net.sourceforge.czt.z.ast.Expr expr);

  /**
   * Creates an instance of {@link TopologyProExpr}.
   *
   * @return the new instance of TopologyProExpr.
   */
  TopologyProExpr createTopologyProExpr();

  /**
   * Creates an instance of {@link TopologyProExpr} with the given children.
   *
   * @return the new instance of TopologyProExpr.
   */
  TopologyProExpr createTopologyProExpr(java.util.List connection);

  /**
   * Creates an instance of {@link TimeoutEndProExpr}.
   *
   * @return the new instance of TimeoutEndProExpr.
   */
  TimeoutEndProExpr createTimeoutEndProExpr();

  /**
   * Creates an instance of {@link TimeoutEndProExpr} with the given children.
   *
   * @return the new instance of TimeoutEndProExpr.
   */
  TimeoutEndProExpr createTimeoutEndProExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp);

  /**
   * Creates an instance of {@link TimeoutStartProExpr}.
   *
   * @return the new instance of TimeoutStartProExpr.
   */
  TimeoutStartProExpr createTimeoutStartProExpr();

  /**
   * Creates an instance of {@link TimeoutStartProExpr} with the given children.
   *
   * @return the new instance of TimeoutStartProExpr.
   */
  TimeoutStartProExpr createTimeoutStartProExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp);

}
