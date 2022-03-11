void resetProofSteps();
long currentProofStep();

ApplyCommand createGlobalApplyCommand(net.sourceforge.czt.z.ast.Name name);
ApplyCommand createApplyToExprCommand(net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Expr expr);
ApplyCommand createApplyToPredCommand(net.sourceforge.czt.z.ast.Name name, net.sourceforge.czt.z.ast.Pred pred);

SimplificationCommand createSimplifyCommand();
SimplificationCommand createRewriteCommand();
SimplificationCommand createReduceCommand();
SimplificationCommand createProveBySimplifyCommand();
SimplificationCommand createProveByRewriteCommand();
SimplificationCommand createProveByReduceCommand();
SimplificationCommand createTrivialSimplifyCommand();
SimplificationCommand createTrivialRewriteCommand();
SimplificationCommand createTrivialReduceCommand();

NormalizationCommand createConjunctiveCommand();
NormalizationCommand createDisjunctiveCommand();
NormalizationCommand createRearrangeCommand();
NormalizationCommand createWithNormalizationCommand(ProofCommand cmd);

CaseAnalysisCommand createCasesCommand();
CaseAnalysisCommand createNextCommand();
CaseAnalysisCommand createSplitCommand(net.sourceforge.czt.z.ast.Pred toSplitOver);

WithCommand createWithEnabledCommand(net.sourceforge.czt.z.ast.NameList nl, ProofCommand cmd);
WithCommand createWithDisabledCommand(net.sourceforge.czt.z.ast.NameList nl, ProofCommand cmd);
WithCommand createWithPredicateCommand(net.sourceforge.czt.z.ast.Pred pred, ProofCommand cmd);
WithCommand createWithExpressionCommand(net.sourceforge.czt.z.ast.Expr expr, ProofCommand cmd);

SubstitutionCommand createGlobalEqualitySubstituteCommand();
SubstitutionCommand createGlobalInvokeCommand();
SubstitutionCommand createEqualitySubstituteCommand(net.sourceforge.czt.z.ast.Expr expr);
SubstitutionCommand createInvokeCommand(net.sourceforge.czt.z.ast.Name name);
SubstitutionCommand createInvokePredicateCommand(net.sourceforge.czt.z.ast.Pred pred);

QuantifiersCommand createPrenexCommand();
QuantifiersCommand createInstantiateCommand(InstantiationList inst);

UseCommand createUseCommand(net.sourceforge.czt.z.ast.RefExpr thmRef);
UseCommand createUseCommand(net.sourceforge.czt.z.ast.RefExpr thmRef, InstantiationList inst);

SorryCommand createSorryCommand(boolean keepGoal);

