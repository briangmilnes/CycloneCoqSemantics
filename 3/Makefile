-include coq.depends
all: TAGS src tactic lemma  test proof experiment TODOS

SRCFILES=FormalSyntax.vo DynamicSemanticsTypeSubstitution.vo DynamicSemanticsHeapObjects.vo DynamicSemantics.vo StaticSemanticsKindingAndContextWellFormedness.vo StaticSemanticsTypingHeapObjects.vo StaticSemantics.vo Tacticals.vo TacticNotations.vo TypeSafety.vo ContextExtensionRelation.vo

TESTFILES=TestUtilities.vo FormalSyntaxTest.vo DynamicSemanticsHeapObjectsTest.vo DynamicSemanticsTypeSubstitutionTest.vo DynamicSemanticsTest.vo StaticSemanticsTest.vo StaticSemanticsKindingAndContextWellFormednessTest.vo StaticSemanticsTypingHeapObjectsTest.vo MutualRecursionProof.vo KindingTest.vo ContextExtensionTest.vo

LEMMAFILES= NatLemmas.vo VarLemmas.vo ListLemmas.vo PathLemmas.vo AlphaConversion.vo GetLemmasRelation.vo StaticSemanticsHeapObjectsLemmas.vo StaticSemanticsKindingLemmas.vo StaticSemanticsLemmas.vo StaticSemanticsTypingLemmas.vo StaticSemanticsWellFormednessLemmas.vo ContextExtensionLemmas.vo ValueLemmas.vo

PROOFFILES=TypeSafetyProof.vo ContextWeakeningProof.vo TermWeakeningProof.vo HeapWeakeningProof.vo SubstitutionsProof.vo TypingWellFormednessProof.vo ReturnPreservationProof.vo CannonicalFormsProof.vo PathExtensionProof.vo HeapObjectSafetyProof.vo TermPreservationProof.vo TermProgressProof.vo

TACTICFILES=CpdtTactics.vo Case.vo

EXPERIMENTFILES=KindingExperiments.vo PFunExperiment.vo

# You can't name the module the same as the file! LOL.
MODULES=VariablesSigDef.vo VariablesDef.vo VariablesProofsSigDef.vo NonceSigDef.vo VariablesProofsFunDef.vo TVarDef.vo EVarDef.vo TypingInfoSigDef.vo TauTypingInfoDef.vo TypingInfoProofsSigDef.vo TauTypingInfoFunDef.vo ContextSigDef.vo


%.vo: %.v 
	coqc $<

src:  TAGS depends $(SRCFILES)

tactic: TAGS src $(TACTICFILES)

test: TAGS depends tactic src $(TESTFILES)

lemma: TAGS depends tactic src $(LEMMAFILES)

proof: TAGS depends tactic lemma src $(PROOFFILES)

experiment: TAGS depends tactic src lemma proof $(PROOFFILES)

modules: $(MODULES)

clean:
	rm -f *.vo
	rm -f #*#
	rm -f *~ 
	rm -f *.glob
	rm -f TAGS

clean-modules:
	rm -f $(MODULES)

tar:
	tar zcvf backup.tar.gz *.v Makefile

TAGS:  
	~/bin/coqtags *.v

count: 
	echo "Source "
	ls -1 *.v | grep -vi Test | grep -v Dead | grep -v Proof | grep -v Subset | grep -v Cpdt | grep -v Lemma | xargs wc -l 
	echo "Test "
	ls -1 *.v | grep -i Test | xargs wc -l 
	echo "Lemma" 
	ls -1 *.v | grep -i Lemma | xargs wc -l 
	echo "Proof"
	ls -1 *.v | grep -i Proof | grep -v Subset | xargs wc -l 

depends: 
	coqdep -I . *.v > coq.depends 

TODOS:
	grep admit *.v | grep -v Proof | wc -l
	grep Admitted *.v | grep -v Proof | wc -l
	grep Admitted *.v | grep Proof | wc -l
	grep TODO TODO *.v | wc -l
	grep '?' *.v | grep -v Tacticals | wc -l
	grep -e Admitted -e TODO -e '?' *.v | wc -l

BUGS:
	grep Bug *.v 
	grep Bug *.v | wc -l
	grep 'Test Bug' *.v | wc -l
	grep 'Dan Bug' *.v | wc -l

ttpbis:
	echo "To Prove"
	grep -e Lemma -e Theorem *Proof.v | grep -v Subset | wc -l
	echo "Proven".
	grep -e Qed *Proof.v | grep -v Subset | wc -l
	echo "Cases missing".
	grep admit *.v | grep Proof | wc -l


dan: 
	echo "Ask Dan's"
	grep -e Dan *.v | grep -v formal | wc -l

theorems:
	grep -e 'Lemma ' -e Theorem -e Qed -e admit -e AdmitAlphaConversion -e Admitted $(PROOFS)

lemmas:
	grep -e 'Lemma ' -e Theorem -e Qed -e admit -e AdmitAlphaConversion -e Admitted $(LEMMAS)

lemmasused:
	grep -i 'apply ' *.v | grep -v IH | grep -v ' H' | grep -v SR | grep -v SL | grep -v SS | grep -v ind | grep -v ' K_' | grep -v 'S_' | grep -v 'L_' | grep -v 'R_' | grep -v 'A_' | grep -v ex_intro  | grep -v beq | grep -v Value
