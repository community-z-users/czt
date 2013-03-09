
// c?x@N ---> A
net.sourceforge.czt.circustime.ast.PrefixingTimeAction createAtPrefixingAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Name name);

// c?x --expr--> A
net.sourceforge.czt.circustime.ast.PrefixingTimeAction createPrefixingExprAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Expr expr);

//c?x --expr--> A
net.sourceforge.czt.circustime.ast.PrefixingTimeAction createAtPrefixingExprAction( net.sourceforge.czt.circus.ast.CircusAction  circusAction, net.sourceforge.czt.circus.ast.Communication  communication, net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Expr expr);
