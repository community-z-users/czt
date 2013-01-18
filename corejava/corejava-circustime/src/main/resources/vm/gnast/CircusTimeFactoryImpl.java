
// c?x@N ---> A
public PrefixingTimeAction createAtPrefixingAction( CircusAction  circusAction, Communication  communication, net.sourceforge.czt.z.ast.Name name)
{
	return createPrefixingTimeAction(circusAction, communication, name, null);
}

// c?x --expr--> A
public PrefixingTimeAction createPrefixingExprAction( CircusAction  circusAction, Communication  communication, net.sourceforge.czt.z.ast.Expr expr)
{
	return createPrefixingTimeAction(circusAction, communication, null, expr);
}

//c?x@N --expr--> A
public PrefixingTimeAction createAtPrefixingExprAction( CircusAction  circusAction, Communication  communication, net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Expr expr)
{
	return createPrefixingTimeAction(circusAction, communication, name, expr);
}

// wait Expr: This just creates wait dummy: Expr @ Skip
public WaitExprAction createWaitAction(net.sourceforge.czt.z.ast.Expr expr)
{
	return createWaitExprAction(createSkipAction(), expr, net.sourceforge.czt.circus.util.CircusUtils.createAnonymousZName());
}