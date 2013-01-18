 public boolean isBasicWaitAction()
 {
	 assert isWaitExprActionConsistent();
	 return getExpr() != null && (getCircusAction() instanceof net.sourceforge.czt.circus.ast.SkipAction);
 }
 public boolean isWaitExprAction()
 {
	 assert isWaitExprActionConsistent();
	 return getExpr() != null;
 }
 
 private boolean isWaitExprActionConsistent()
 {
	 return getExpr() != null && getCircusAction() != null;
 }