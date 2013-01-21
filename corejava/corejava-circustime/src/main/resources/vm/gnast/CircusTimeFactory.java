
// c?x@N ---> A
PrefixingTimeAction createAtPrefixingAction( CircusAction  circusAction, Communication  communication, net.sourceforge.czt.z.ast.Name name);

// c?x --expr--> A
PrefixingTimeAction createPrefixingExprAction( CircusAction  circusAction, Communication  communication, net.sourceforge.czt.z.ast.Expr expr);

//c?x --expr--> A
PrefixingTimeAction createAtPrefixingExprAction( CircusAction  circusAction, Communication  communication, net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Expr expr);
