// c?x@N ---> A
public net.sourceforge.czt.circustime.ast.PrefixingTimeAction createAtPrefixingAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Name name)
{
	return createPrefixingTimeAction(circusAction, null, communication, name);
}

// c?x --expr--> A
public net.sourceforge.czt.circustime.ast.PrefixingTimeAction createPrefixingExprAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Expr expr)
{
	return createPrefixingTimeAction(circusAction, expr, communication, null);
}

//c?x@N --expr--> A
public net.sourceforge.czt.circustime.ast.PrefixingTimeAction createAtPrefixingExprAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Expr expr)
{
	return createPrefixingTimeAction(circusAction, expr, communication, name);
}
