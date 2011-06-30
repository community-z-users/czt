void resetProofSteps();
long currentProofStep();

ApplyCommand createGlobalApplyCommand(Name name);
ApplyCommand createApplyToExprCommand(Name name, Expr expr);
ApplyCommand createApplyToPredCommand(Name name, Pred pred);

SimplificationCommand createSimplifyCommand();
SimplificationCommand createRewriteCommand();
SimplificationCommand createReduceCommand();
SimplificationCommand createProveBySimplifyCommand();
SimplificationCommand createProveByRewriteCommand();
SimplificationCommand createProveByReduceCommand();
SimplificationCommand createTrivialSimplifyCommand();
SimplificationCommand createTrivialRewriteCommand();
SimplificationCommand createTrivialReduceCommand();

NormalisationCommand createConjunctiveCommand();
NormalisationCommand createDisjunctiveCommand();
NormalisationCommand createRearrangeCommand();
NormalisationCommand createWithNormalisationCommand(ProofCommand cmd);

CaseAnalysisCommand createCasesCommand();
CaseAnalysisCommand createNextCommand();
CaseAnalysisCommand createSplitCommand(Pred toSplitOver);

WithCommand createWithEnabledCommand(NameList nl, ProofCommand cmd);
WithCommand createWithDisabledCommand(NameList nl, ProofCommand cmd);
WithCommand createWithPredicateCommand(Pred pred, ProofCommand cmd);
WithCommand createWithExpressionCommand(Expr expr, ProofCommand cmd);

SubstitutionCommand createGlobalEqualitySubstituteCommand();
SubstitutionCommand createGlobalInvokCommandCommand();
SubstitutionCommand createEqualitySubstituteCommand(Expr expr);
SubstitutionCommand createInvokeCommand(Name name);
SubstitutionCommand createInvokePredicateCommand(Pred pred);

QuantifiersCommand createPrenexCommand();
QuantifiersCommand createInstantiateCommand(Instantiations inst);

UseCommand createUseCommand(RefExpr thmRef);
UseCommand createUseCommand(RefExpr thmRef, Instantiations inst);

