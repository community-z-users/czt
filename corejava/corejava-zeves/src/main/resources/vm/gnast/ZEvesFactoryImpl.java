private <E> java.util.List<E> newList(@SuppressWarnings("unchecked")E... elems)
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

public net.sourceforge.czt.zeves.ast.ApplyCommand createGlobalApplyCommand(net.sourceforge.czt.z.ast.Name name)
{
	countStep();
	return createApplyCommand(proofStep_, null, createZNameList(newList(name)), null, null);
}

public net.sourceforge.czt.zeves.ast.ApplyCommand createApplyToExprCommand(net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Expr expr)
{
	countStep();
	return createApplyCommand(proofStep_, null, createZNameList(newList(name)), expr, null);
}

public net.sourceforge.czt.zeves.ast.ApplyCommand createApplyToPredCommand(net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Pred pred)
{
	countStep();
	return createApplyCommand(proofStep_, null, createZNameList(newList(name)), null, pred);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createSimplifyCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, net.sourceforge.czt.zeves.ast.RewriteKind.Simplify, net.sourceforge.czt.zeves.ast.RewritePower.None);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createRewriteCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, net.sourceforge.czt.zeves.ast.RewriteKind.Rewrite, net.sourceforge.czt.zeves.ast.RewritePower.None);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createReduceCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, net.sourceforge.czt.zeves.ast.RewriteKind.Reduce, net.sourceforge.czt.zeves.ast.RewritePower.None);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createProveBySimplifyCommand()
{
	throw new UnsupportedOperationException("Prove command can only be by rewrite or reduce");
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createProveByRewriteCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, net.sourceforge.czt.zeves.ast.RewriteKind.Rewrite, net.sourceforge.czt.zeves.ast.RewritePower.Prove);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createProveByReduceCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, net.sourceforge.czt.zeves.ast.RewriteKind.Reduce, net.sourceforge.czt.zeves.ast.RewritePower.Prove);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createTrivialSimplifyCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, net.sourceforge.czt.zeves.ast.RewriteKind.Simplify, net.sourceforge.czt.zeves.ast.RewritePower.Trivial);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createTrivialRewriteCommand()
{
	countStep();
	return createSimplificationCommand(proofStep_, net.sourceforge.czt.zeves.ast.RewriteKind.Rewrite, net.sourceforge.czt.zeves.ast.RewritePower.Trivial);
}

public net.sourceforge.czt.zeves.ast.SimplificationCommand createTrivialReduceCommand()
{
	throw new UnsupportedOperationException("Trivial command can only be by rewrite or simplify");
}

public net.sourceforge.czt.zeves.ast.NormalizationCommand createConjunctiveCommand()
{
	countStep();
	return createNormalizationCommand(proofStep_, null, net.sourceforge.czt.zeves.ast.NormalizationKind.Conjunctive);
}

public net.sourceforge.czt.zeves.ast.NormalizationCommand createDisjunctiveCommand()
{
	countStep();
	return createNormalizationCommand(proofStep_, null, net.sourceforge.czt.zeves.ast.NormalizationKind.Disjunctive);
}

public net.sourceforge.czt.zeves.ast.NormalizationCommand createRearrangeCommand()
{
	countStep();
	return createNormalizationCommand(proofStep_, null, net.sourceforge.czt.zeves.ast.NormalizationKind.Rearrange);
}

public net.sourceforge.czt.zeves.ast.NormalizationCommand createWithNormalizationCommand(net.sourceforge.czt.zeves.ast.ProofCommand cmd)
{
	countStep();
	return createNormalizationCommand(proofStep_, cmd, net.sourceforge.czt.zeves.ast.NormalizationKind.Command);
}

public net.sourceforge.czt.zeves.ast.CaseAnalysisCommand createCasesCommand()
{
	countStep();
	return createCaseAnalysisCommand(proofStep_, null, net.sourceforge.czt.zeves.ast.CaseAnalysisKind.Cases);
}

public net.sourceforge.czt.zeves.ast.CaseAnalysisCommand createNextCommand()
{
	countStep();
	return createCaseAnalysisCommand(proofStep_, null, net.sourceforge.czt.zeves.ast.CaseAnalysisKind.Next);
}

public net.sourceforge.czt.zeves.ast.CaseAnalysisCommand createSplitCommand(net.sourceforge.czt.z.ast.Pred toSplitOver)
{
	countStep();
	return createCaseAnalysisCommand(proofStep_, toSplitOver, net.sourceforge.czt.zeves.ast.CaseAnalysisKind.Split);
}

public net.sourceforge.czt.zeves.ast.WithCommand createWithEnabledCommand(net.sourceforge.czt.z.ast.NameList nl, net.sourceforge.czt.zeves.ast.ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, nl, null, null, true);
}

public net.sourceforge.czt.zeves.ast.WithCommand createWithDisabledCommand(net.sourceforge.czt.z.ast.NameList nl, net.sourceforge.czt.zeves.ast.ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, nl, null, null, false);
}

public net.sourceforge.czt.zeves.ast.WithCommand createWithPredicateCommand(net.sourceforge.czt.z.ast.Pred pred, net.sourceforge.czt.zeves.ast.ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, null, null, pred, null);
}

public net.sourceforge.czt.zeves.ast.WithCommand createWithExpressionCommand(net.sourceforge.czt.z.ast.Expr expr, net.sourceforge.czt.zeves.ast.ProofCommand cmd)
{
	countStep();
	return createWithCommand(proofStep_, cmd, null, expr, null, null);
}

public net.sourceforge.czt.zeves.ast.SubstitutionCommand createGlobalEqualitySubstituteCommand()
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, null, null, net.sourceforge.czt.zeves.ast.SubstitutionKind.Equality);
}

public net.sourceforge.czt.zeves.ast.SubstitutionCommand createGlobalInvokeCommand()
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, null, null, net.sourceforge.czt.zeves.ast.SubstitutionKind.Invoke);
}

public net.sourceforge.czt.zeves.ast.SubstitutionCommand createEqualitySubstituteCommand(net.sourceforge.czt.z.ast.Expr expr)
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, expr, null, net.sourceforge.czt.zeves.ast.SubstitutionKind.Equality);
}

public net.sourceforge.czt.zeves.ast.SubstitutionCommand createInvokeCommand(net.sourceforge.czt.z.ast.Name name)
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, createZNameList(newList(name)), null, null, net.sourceforge.czt.zeves.ast.SubstitutionKind.Invoke);
}

public net.sourceforge.czt.zeves.ast.SubstitutionCommand createInvokePredicateCommand(net.sourceforge.czt.z.ast.Pred pred)
{
	countStep();
	return createSubstitutionCommand(proofStep_, null, null, null, pred, net.sourceforge.czt.zeves.ast.SubstitutionKind.Invoke);
}

public net.sourceforge.czt.zeves.ast.QuantifiersCommand createPrenexCommand()
{
	countStep();
	return createQuantifiersCommand(proofStep_, null);
}

public net.sourceforge.czt.zeves.ast.QuantifiersCommand createInstantiateCommand(net.sourceforge.czt.zeves.ast.InstantiationList inst)
{
	countStep();
	return createQuantifiersCommand(proofStep_, inst);
}

public net.sourceforge.czt.zeves.ast.UseCommand createUseCommand(net.sourceforge.czt.z.ast.RefExpr thmRef)
{
	countStep();
	return createUseCommand(proofStep_, null, thmRef);
}

public net.sourceforge.czt.zeves.ast.UseCommand createUseCommand(net.sourceforge.czt.z.ast.RefExpr thmRef, net.sourceforge.czt.zeves.ast.InstantiationList inst)
{
	countStep();
	return createUseCommand(proofStep_, inst, thmRef);
}

public net.sourceforge.czt.zeves.ast.SorryCommand createSorryCommand(boolean keepGoal)
{
	countStep();
	return createSorryCommand(proofStep_, keepGoal);
}