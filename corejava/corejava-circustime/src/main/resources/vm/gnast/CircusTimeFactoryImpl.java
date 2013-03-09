
// c?x@N ---> A
public net.sourceforge.czt.circus.ast.PrefixingTimeAction createAtPrefixingAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Name name)
{
	return createPrefixingTimeAction(circusAction, communication, name, null);
}

// c?x --expr--> A
public net.sourceforge.czt.circus.ast.PrefixingTimeAction createPrefixingExprAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Expr expr)
{
	return createPrefixingTimeAction(circusAction, communication, null, expr);
}

//c?x@N --expr--> A
public net.sourceforge.czt.circus.ast.PrefixingTimeAction createAtPrefixingExprAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Expr expr)
{
	return createPrefixingTimeAction(circusAction, communication, name, expr);
}
