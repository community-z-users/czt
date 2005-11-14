
    private RefExpr reSynch_ = createRefExpr(createZRefName("Synch", java.util.Arrays.<Stroke>asList(), 
            createZDeclName("Synch", java.util.Arrays.<Stroke>asList(), null)), createZExprList(), Boolean.FALSE);
    
    /** Creates a list of synchronisation channels. This is a convenience method */
    public ChannelDecl createSynchChannelDecl(java.util.List<? extends DeclName> chans) {
      return createChannelDecl(java.util.Arrays.<DeclName>asList(), createVarDecl(chans, reSynch_));
    }
    
    /** Creates a parameterless call action. This is a convenience method */
    public CallAction createCallAction(RefName name) {
      return createCallAction(name, createZExprList());
    }

    /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
    public CallProcess createCallProcess(RefName name, CallType ctype) {
      return createCallProcess(name, createZExprList(), createZExprList(), ctype);
    }
    
    /** Creates an empty BasicNameSet. This is a convenience method */
    public NameSet createEmptyNameSet() {
      return createBasicNameSet(createZRefNameList());
    }
    
    /** Creates an empty BasicChannelSet. This is a convenience method */
    public ChannelSet createEmptyChannelSet() {
      return createBasicChannelSet(createZRefNameList());
    }
    
    /** Creates an interleave action with empty (basic) name sets. This is a convenience method */    
    public InterleaveAction createInterleaveAction(CircusAction left, CircusAction right) {
      return createInterleaveAction(left, right, createEmptyNameSet(), createEmptyNameSet());
    }
