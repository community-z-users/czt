
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE CoreFactoryImpl.vm.
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

package net.sourceforge.czt.tcoz.impl;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.tcoz.ast.*;

/**
 * <p>An implementation of the object factory for constructing
 * concrete Z terms.  Each factory method returns an instance
 * of the corresponding class provided in this package.</p>
 *
 * @author Gnast version 0.1
 */
public class TcozFactoryImpl
  extends net.sourceforge.czt.oz.impl.OzFactoryImpl
  implements net.sourceforge.czt.tcoz.ast.TcozFactory
{
  public RecProExpr createRecProExpr()
  {
    RecProExpr zedObject = new RecProExprImpl();
    return zedObject;
  }

  public RecProExpr createRecProExpr(net.sourceforge.czt.z.ast.RefName opName, net.sourceforge.czt.oz.ast.OperationExpr operationExpr)
  {
    RecProExpr zedObject = createRecProExpr();
    zedObject.setOpName(opName);
    zedObject.setOperationExpr(operationExpr);
    return zedObject;
  }

  public WaitUntilProExpr createWaitUntilProExpr()
  {
    WaitUntilProExpr zedObject = new WaitUntilProExprImpl();
    return zedObject;
  }

  public WaitUntilProExpr createWaitUntilProExpr(net.sourceforge.czt.oz.ast.OperationExpr operationExpr, net.sourceforge.czt.z.ast.Expr1 waitUntil)
  {
    WaitUntilProExpr zedObject = createWaitUntilProExpr();
    zedObject.setOperationExpr(operationExpr);
    zedObject.setWaitUntil(waitUntil);
    return zedObject;
  }

  public DeadlineProExpr createDeadlineProExpr()
  {
    DeadlineProExpr zedObject = new DeadlineProExprImpl();
    return zedObject;
  }

  public DeadlineProExpr createDeadlineProExpr(net.sourceforge.czt.oz.ast.OperationExpr operationExpr, net.sourceforge.czt.z.ast.Expr1 deadline)
  {
    DeadlineProExpr zedObject = createDeadlineProExpr();
    zedObject.setOperationExpr(operationExpr);
    zedObject.setDeadline(deadline);
    return zedObject;
  }

  public WaitProExpr createWaitProExpr()
  {
    WaitProExpr zedObject = new WaitProExprImpl();
    return zedObject;
  }

  public WaitProExpr createWaitProExpr(net.sourceforge.czt.z.ast.Expr expr)
  {
    WaitProExpr zedObject = createWaitProExpr();
    zedObject.setExpr(expr);
    return zedObject;
  }

  public DivergeProExpr createDivergeProExpr()
  {
    DivergeProExpr zedObject = new DivergeProExprImpl();
    return zedObject;
  }

  public SynPllProExpr createSynPllProExpr()
  {
    SynPllProExpr zedObject = new SynPllProExprImpl();
    return zedObject;
  }

  public SynPllProExpr createSynPllProExpr(EventSet events)
  {
    SynPllProExpr zedObject = createSynPllProExpr();
    zedObject.setEvents(events);
    return zedObject;
  }

  public InterruptProExpr createInterruptProExpr()
  {
    InterruptProExpr zedObject = new InterruptProExprImpl();
    return zedObject;
  }

  public InterruptProExpr createInterruptProExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp)
  {
    InterruptProExpr zedObject = createInterruptProExpr();
    zedObject.setNormalOp(normalOp);
    zedObject.setIntOrTimeout(intOrTimeout);
    zedObject.setHandlerOp(handlerOp);
    return zedObject;
  }

  public InterleaveProExpr createInterleaveProExpr()
  {
    InterleaveProExpr zedObject = new InterleaveProExprImpl();
    return zedObject;
  }

  public AtProExpr createAtProExpr()
  {
    AtProExpr zedObject = new AtProExprImpl();
    return zedObject;
  }

  public AtProExpr createAtProExpr(Event event, net.sourceforge.czt.z.ast.Expr expr, net.sourceforge.czt.oz.ast.OperationExpr operationExpr)
  {
    AtProExpr zedObject = createAtProExpr();
    zedObject.setEvent(event);
    zedObject.setExpr(expr);
    zedObject.setOperationExpr(operationExpr);
    return zedObject;
  }

  public Connection createConnection()
  {
    Connection zedObject = new ConnectionImpl();
    return zedObject;
  }

  public Connection createConnection(net.sourceforge.czt.oz.ast.RefNameList leftProcess, net.sourceforge.czt.oz.ast.RefNameList rightProcess, net.sourceforge.czt.oz.ast.RefNameList channels)
  {
    Connection zedObject = createConnection();
    zedObject.setLeftProcess(leftProcess);
    zedObject.setRightProcess(rightProcess);
    zedObject.setChannels(channels);
    return zedObject;
  }

  public InterruptTimeOpExpr createInterruptTimeOpExpr()
  {
    InterruptTimeOpExpr zedObject = new InterruptTimeOpExprImpl();
    return zedObject;
  }

  public InterruptTimeOpExpr createInterruptTimeOpExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp)
  {
    InterruptTimeOpExpr zedObject = createInterruptTimeOpExpr();
    zedObject.setNormalOp(normalOp);
    zedObject.setIntOrTimeout(intOrTimeout);
    zedObject.setHandlerOp(handlerOp);
    return zedObject;
  }

  public GuardProExpr createGuardProExpr()
  {
    GuardProExpr zedObject = new GuardProExprImpl();
    return zedObject;
  }

  public GuardProExpr createGuardProExpr(net.sourceforge.czt.z.ast.SchText guard, net.sourceforge.czt.oz.ast.OperationExpr operationExpr)
  {
    GuardProExpr zedObject = createGuardProExpr();
    zedObject.setGuard(guard);
    zedObject.setOperationExpr(operationExpr);
    return zedObject;
  }

  public StopProExpr createStopProExpr()
  {
    StopProExpr zedObject = new StopProExprImpl();
    return zedObject;
  }

  public SkipProExpr createSkipProExpr()
  {
    SkipProExpr zedObject = new SkipProExprImpl();
    return zedObject;
  }

  public ChannelExpr createChannelExpr()
  {
    ChannelExpr zedObject = new ChannelExprImpl();
    return zedObject;
  }

  public ChannelExpr createChannelExpr(net.sourceforge.czt.z.ast.Expr expr, ChannelType channelType)
  {
    ChannelExpr zedObject = createChannelExpr();
    zedObject.setExpr(expr);
    zedObject.setChannelType(channelType);
    return zedObject;
  }

  public EventSet createEventSet()
  {
    EventSet zedObject = new EventSetImpl();
    return zedObject;
  }

  public EventSet createEventSet(java.util.List event)
  {
    EventSet zedObject = createEventSet();
    if (event != null) {
      zedObject.getEvent().addAll(event);
    }
    return zedObject;
  }

  public Event createEvent()
  {
    Event zedObject = new EventImpl();
    return zedObject;
  }

  public Event createEvent(net.sourceforge.czt.z.ast.RefName name, net.sourceforge.czt.z.ast.Expr expr)
  {
    Event zedObject = createEvent();
    zedObject.setName(name);
    zedObject.setExpr(expr);
    return zedObject;
  }

  public TopologyProExpr createTopologyProExpr()
  {
    TopologyProExpr zedObject = new TopologyProExprImpl();
    return zedObject;
  }

  public TopologyProExpr createTopologyProExpr(java.util.List connection)
  {
    TopologyProExpr zedObject = createTopologyProExpr();
    if (connection != null) {
      zedObject.getConnection().addAll(connection);
    }
    return zedObject;
  }

  public TimeoutEndProExpr createTimeoutEndProExpr()
  {
    TimeoutEndProExpr zedObject = new TimeoutEndProExprImpl();
    return zedObject;
  }

  public TimeoutEndProExpr createTimeoutEndProExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp)
  {
    TimeoutEndProExpr zedObject = createTimeoutEndProExpr();
    zedObject.setNormalOp(normalOp);
    zedObject.setIntOrTimeout(intOrTimeout);
    zedObject.setHandlerOp(handlerOp);
    return zedObject;
  }

  public TimeoutStartProExpr createTimeoutStartProExpr()
  {
    TimeoutStartProExpr zedObject = new TimeoutStartProExprImpl();
    return zedObject;
  }

  public TimeoutStartProExpr createTimeoutStartProExpr(net.sourceforge.czt.oz.ast.OperationExpr normalOp, net.sourceforge.czt.z.ast.Expr1 intOrTimeout, net.sourceforge.czt.oz.ast.OperationExpr handlerOp)
  {
    TimeoutStartProExpr zedObject = createTimeoutStartProExpr();
    zedObject.setNormalOp(normalOp);
    zedObject.setIntOrTimeout(intOrTimeout);
    zedObject.setHandlerOp(handlerOp);
    return zedObject;
  }

}
