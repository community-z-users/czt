
    /** Creates a parameterless call action. This is a convenience method */
    public CallAction createCallAction(net.sourceforge.czt.z.ast.Name name) {
      return createCallAction(name, createZExprList());
    }

    /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
    public CallProcess createCallProcess(net.sourceforge.czt.z.ast.Name name) {
      return createCallProcess(createRefExpr(name, createZExprList(), Boolean.FALSE, Boolean.TRUE), 
		createZExprList(), CallKind.Param);
    }
    
    /** Creates an empty BasicNameSet. This is a convenience method */
    public CircusNameSet createEmptyCircusNameSet() {
      return createCircusNameSet(createSetExpr(createZExprList()));
    }
    
    /** Creates an empty BasicChannelSet. This is a convenience method */
    public CircusChannelSet createEmptyCircusChannelSet() {
      return createCircusChannelSet(createSetExpr(createZExprList()));
    }
    
    private <E> java.util.List<E> newList(E... elems)
  {
    java.util.List<E> result = new java.util.ArrayList<E>();
    result.addAll(java.util.Arrays.asList(elems));
    return result;
  }
  
  public CircusProcessSignature createCircusProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    ProcessKind kind)
  {
    return createCircusProcessSignature(name, genFormals,
      newList(
        // list0 = ZSignatureList getMainSignatures()
        createZSignatureList(
          // list0.0 = Signature paramOrIndexes
          // list0.1 = Signature usedChannels
          newList(paramOrIndexes, usedChannels)
        )
      ),
      kind);
  }
  
  public BasicProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    ProcessKind kind,
    net.sourceforge.czt.z.ast.Signature usedNameSets,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ZSignatureList localZParagraphs,
    ActionSignatureList processActions,
    StateUpdate stateUpdate)
  {
    return createBasicProcessSignature(name, genFormals,
      newList(
        // list0 = ZSignatureList getMainSignatures()
        createZSignatureList(
          // list0.0 = Signature paramOrIndexes
          // list0.1 = Signature usedChannels
          // list0.2 = Signature usedNameSets
          // list0.3 = Signature stateSignature
          newList(paramOrIndexes, usedChannels, 
                  usedNameSets, stateSignature)
        ),
        // list1 = ZSignatureList getLocalZSignatures()
        localZParagraphs,
        // list2 = ActionSignatureList getActionSignatures()
        processActions
      ),
      kind, 
      stateUpdate);
  }


  public BasicProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    ProcessKind kind,
    net.sourceforge.czt.z.ast.Signature usedNameSets,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ZSignatureList localZParagraphs,
    ActionSignatureList processActions)
  {
    return createBasicProcessSignature(name, genFormals,
      paramOrIndexes, usedChannels, kind, usedNameSets, 
      stateSignature, localZParagraphs, processActions,      
      createStateUpdate());
  }