 public boolean isAtPrefixingAction()
 {
	 assert isPrefixingTimeActionConsistent();
	 return getChannelElapsedTimeDeclName() != null && getExpr() == null;
 }
 public boolean isPrefixingExprAction()
 {
	 assert isPrefixingTimeActionConsistent();
	 return getChannelElapsedTimeDeclName() == null && getExpr() != null;
 }
 public boolean isAtPrefixingExprAction()
 {
	 assert isPrefixingTimeActionConsistent();
	 return getChannelElapsedTimeDeclName() != null && getExpr() != null;
 }
 
 private boolean isPrefixingTimeActionConsistent()
 {
	 return !(getChannelElapsedTimeDeclName() == null && getExpr() == null);
 }
