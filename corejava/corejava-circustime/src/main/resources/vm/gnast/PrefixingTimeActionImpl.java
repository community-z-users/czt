 public boolean isAtPrefixingAction()
 {
	 assert isPrefixingTimeActionConsistent();
	 return getChannelElapsedTime() != null && getExpr() == null;
 }
 public boolean isPrefixingExprAction()
 {
	 assert isPrefixingTimeActionConsistent();
	 return getChannelElapsedTime() == null && getExpr() != null;
 }
 public boolean isAtPrefixingExprAction()
 {
	 assert isPrefixingTimeActionConsistent();
	 return getChannelElapsedTime() != null && getExpr() != null;
 }
 
 private boolean isPrefixingTimeActionConsistent()
 {
	 return !(getChannelElapsedTime() == null && getExpr() == null);
 }