private <E> java.util.List<E> newList(E... elems)
{
	java.util.List<E> result = new java.util.ArrayList<E>();
	result.addAll(java.util.Arrays.asList(elems));
	return result;
}

private java.math.BigInteger proofStep_ = java.math.BigInteger.ZERO;

private void countStep()
{
	proofStep_ = proofStep_.add(java.math.BigInteger.ONE);
}

public void resetProofSteps()
{
	proofStep_ = java.math.BigInteger.ZERO;
}

public long currentProofStep()
{
	return proofStep_.longValue();
}

public ApplyCommand createGlobalApplyCommand(Name name)
{
	countStep();
	return createApplyCommand(proofStep_, null, createZNameList(newList(name)), null, null);
}

public ApplyCommand createApplyToExprCommand(Name name, Expr expr)
{
	countStep();
	return createApplyCommand(proofStep_, null, createZNameList(newList(name)), expr, null);
}

public ApplyCommand createApplyToPredCommand(Name name, Pred pred)
{
	countStep();
	return createApplyCommand(proofStep_, null, createZNameList(newList(name)), null, pred);
}

public SimplificationCommand createSimplifyCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, RewriteKind.Simplify, RewritePower.None);
}

public SimplificationCommand createRewriteCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, RewriteKind.Rewrite, RewritePower.None);
}

public SimplificationCommand createReduceCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, RewriteKind.Reduce, RewritePower.None);
}

public SimplificationCommand createProveBySimplifyCommand()
{
	throw new UnsupportedOperationException("Prove command can only be by rewrite or reduce");
}

public SimplificationCommand createProveByRewriteCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, RewriteKind.Rewrite, RewritePower.Prove);
}

public SimplificationCommand createProveByReduceCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, RewriteKind.Reduce, RewritePower.Prove);
}

public SimplificationCommand createTrivialSimplifyCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, RewriteKind.Simplify, RewritePower.Trivial);
}

public SimplificationCommand createTrivialRewriteCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, RewriteKind.Rewrite, RewritePower.Trivial);
}

public SimplificationCommand createTrivialReduceCommand()
{
	throw new UnsupportedOperationException("Trivial command can only be by rewrite or simplify");
}

public NormalizationCommand createConjunctiveCommand()
{
	countStep();
	return createNormalizationCommand(proofStep_, null, NormalizationKind.Conjunctive);
}

public NormalizationCommand createDisjunctiveCommand()
{
	countStep();
	return createNormalizationCommand(proofStep_, null, NormalizationKind.Disjunctive);
}

public NormalizationCommand createRearrangeCommand()
{
	countStep();
	return createNormalizationCommand(proofStep_, null, NormalizationKind.Rearrange);
}

public NormalizationCommand createWithNormalizationCommand(ProofCommand cmd)
{
	countStep();
	return createNormalizationCommand(proofStep_, cmd, NormalizationKind.Command);
}

public CaseAnalysisCommand createCasesCommand()
{
	countStep();
	return createCaseAnalysisCommand(proofStep_, null, CaseAnalysisKind.Cases);
}

public CaseAnalysisCommand createNextCommand()
{
	countStep();
	return createCaseAnalysisCommand(proofStep_, null, CaseAnalysisKind.Next);
}

public CaseAnalysisCommand createSplitCommand(Pred toSplitOver)
{
	countStep();
	return createCaseAnalysisCommand(proofStep_, toSplitOver, CaseAnalysisKind.Split);
}

public WithCommand createWithEnabledCommand(NameList nl, ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, nl, null, null, true);
}

public WithCommand createWithDisabledCommand(NameList nl, ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, nl, null, null, false);
}

public WithCommand createWithPredicateCommand(Pred pred, ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, null, null, pred, null);
}

public WithCommand createWithExpressionCommand(Expr expr, ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, null, expr, null, null);
}

public SubstitutionCommand createGlobalEqualitySubstituteCommand()
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, null, null, SubstitutionKind.Equality);
}

public SubstitutionCommand createGlobalInvokeCommand()
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, null, null, SubstitutionKind.Invoke);
}

public SubstitutionCommand createEqualitySubstituteCommand(Expr expr)
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, expr, null, SubstitutionKind.Equality);
}

public SubstitutionCommand createInvokeCommand(Name name)
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, createZNameList(newList(name)), null, null, SubstitutionKind.Invoke);
}

public SubstitutionCommand createInvokePredicateCommand(Pred pred)
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, null, pred, SubstitutionKind.Invoke);
}

public QuantifiersCommand createPrenexCommand()
{
	countStep();
	return createQuantifiersCommand(proofStep_, null);
}

public QuantifiersCommand createInstantiateCommand(InstantiationList inst)
{
	countStep();
	return createQuantifiersCommand(proofStep_, inst);
}

public UseCommand createUseCommand(RefExpr thmRef)
{
	countStep();
	return createUseCommand(proofStep_, null, thmRef);
}

public UseCommand createUseCommand(RefExpr thmRef, InstantiationList inst)
{
	countStep();
	return createUseCommand(proofStep_, inst, thmRef);
}