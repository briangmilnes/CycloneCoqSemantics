-include coq.depends
all: TAGS src tactic lemma test proof experiment 

SRCFILES=BoolEqualitySigDef.vo  ContextFunDef.vo  ContextSigDef.vo  DeltaModuleDef.vo  EVarModuleDef.vo  EVarPathModuleDef.vo  GammaModuleDef.vo  KappaModuleDef.vo  NonceSigDef.vo  PathModuleDef.vo  PhiModuleDef.vo  TauModuleDef.vo  TVarModuleDef.vo  UpsilonModuleDef.vo  VariablesFunDef.vo  VariablesSigDef.vo TermModuleDef.vo HeapModuleDef.vo LanguageModuleDef.vo DynamicSemanticsTypeSubstitution.vo DynamicSemanticsHeapObjects.vo DynamicSemantics.vo StaticSemanticsKindingAndContextWellFormedness.vo StaticSemanticsTypingHeapObjects.vo StaticSemantics.vo TypeSafety.vo

TESTFILES=TestUtilities.vo FormalSyntaxTest.v DynamicSemanticsTypeSubstitutionTest.vo DynamicSemanticsTest.vo DynamicSemanticsHeapObjectsTest.vo StaticSemanticsKindingAndContextWellFormednessTest.v StaticSemanticsTest.vo StaticSemanticsTypingHeapObjectsTest.vo KindingTest.vo

LEMMAFILES=NatLemmas.vo StaticSemanticsHeapObjectsLemmas.vo StaticSemanticsKindingAndContextWellFormednessLemmas.vo StaticSemanticsKindingLemmas.vo StaticSemanticsWellFormednessLemmas.vo

PROOFFILES=SubstitutionsProof.v ReturnPreservationProof.v 

TACTICFILES=CpdtTactics.vo Case.vo TacticNotations.vo AlphaConversion.vo Tacticals.vo MoreTacticals.vo

EXPERIMENTFILES=

%.vo: %.v 
	coqc $<

src:  TAGS depends $(SRCFILES)

tactic: TAGS src $(TACTICFILES)

test: TAGS depends tactic src $(TESTFILES)

lemma: TAGS depends tactic src $(LEMMAFILES)

proof: TAGS depends tactic lemma src $(PROOFFILES)

experiment: TAGS depends tactic src lemma proof $(PROOFFILES)

clean:
	rm -f *.vo
	rm -f #*#
	rm -f *~ 
	rm -f *.glob
	rm -f TAGS

clean-modules:
	rm -f $(MODULES)

tar:
	tar zcvf backup.tar.gz *.vo Makefile

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

theorems:
	grep -e 'Lemma ' -e Theorem -e Qed -e admit -e AdmitAlphaConversion -e Admitted $(PROOFS)

lemmas:
	grep -e 'Lemma ' -e Theorem -e Qed -e admit -e AdmitAlphaConversion -e Admitted $(LEMMAS)

lemmasused:
	grep -i 'apply ' *.v | grep -v IH | grep -v ' H' | grep -v SR | grep -v SL | grep -v SS | grep -v ind | grep -v ' K_' | grep -v 'S_' | grep -v 'L_' | grep -v 'R_' | grep -v 'A_' | grep -v ex_intro  | grep -v beq | grep -v Value
