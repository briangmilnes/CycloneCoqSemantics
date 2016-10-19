-include coq.depends
all: src tactic test proof TODO

SRCFILES=FormalSyntax.vo DynamicSemanticsTypeSubstitution.vo DynamicSemanticsHeapObjects.vo DynamicSemantics.vo StaticSemanticsKindingAndContextWellFormedness.vo StaticSemanticsTypingHeapObjects.vo StaticSemantics.vo TypeSafety.vo

TESTFILES=TestUtilities.vo FormalSyntaxTest.vo DynamicSemanticsHeapObjectsTest.vo DynamicSemanticsTypeSubstitutionTest.vo DynamicSemanticsTest.vo StaticSemanticsTest.vo StaticSemanticsKindingAndContextWellFormednessTest.vo StaticSemanticsTypingHeapObjectsTest.vo MutualRecursionProof.vo TestingTheHeap.v

PROOFFILES=TypeSafetyProof.vo TypeSafetyProofEmptySubset.vo TypeSafetyProofIntSubset.vo 

TACTICFILES=Tacticals.vo CpdtTactics.vo

%.vo: %.v 
	coqc $<

src:  depends $(SRCFILES)

tactic: src $(TACTICFILES)

test: depends src tactic $(TESTFILES)

proof: depends src tactic $(PROOFFILES)

clean:
	rm -f *.vo
	rm -f *~ 
	rm -f *.glob
	rm -f TAGS

tar:
	tar zcvf backup.tar.gz *.v Makefile

TAGS:  
	~/bin/coqtags *.v

count: 
	echo "Source "
	ls -1 *.v | grep -vi Test | grep -v Dead | grep -v Proof | grep -v Cpdt | xargs wc -l 
	echo "Test "
	ls -1 *.v | grep -i Test | xargs wc -l 
	echo "TypeSafety "
	ls -1 *.v | grep -i Proof | xargs wc -l 

depends: 
	coqdep -I . *.v > coq.depends 

TODO:
	grep Admitted *.v | grep -v Proof | wc -l
	grep Admitted *.v | grep Proof | wc -l
	grep TODO *.v | wc -l
	grep '?' *.v | grep -v Tacticals | wc -l
	grep -e Admitted -e TODO -e '?' *.v | wc -l

BUGS:
	grep Bug *.v 
	grep Bug *.v | wc -l
	grep 'Test Bug' *.v | wc -l
	grep 'Dan Bug' *.v | wc -l
