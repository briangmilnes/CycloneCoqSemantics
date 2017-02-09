-include coq.depends
all: TAGS src tactic lemma test proof experiment 

SRCFILES= Case.vo LibPath.vo LibVarPath.vo LibVarPathEnv.vo Cyclone_Formal_Syntax.vo Cyclone_LN_FSET.vo Cyclone_LN_Types.vo Cyclone_LN_Terms.vo Cyclone_LN_Types_In_Terms.vo Cyclone_Classes.vo Cyclone_Inductions.vo Cyclone_LN_Env.vo Cyclone_LN_Tactics.vo Cyclone_LN_Extra_Lemmas_And_Automation.vo Cyclone_Dynamic_Semantics_Heap_Objects.vo Cyclone_Dynamic_Semantics.vo Cyclone_Static_Semantics_Typing_Heap_Objects.vo Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness.vo Cyclone_Static_Semantics.vo Cyclone_Test_Utilities.vo 

TESTFILES=Cyclone_Test_Utilities.vo Cyclone_Formal_Syntax_Test_Env.vo Cyclone_Formal_Syntax_Test.vo Cyclone_LN_Tactics_Test_Notin.vo Cyclone_Static_Semantics_Typing_Heap_Objects_Test.vo Cyclone_Static_Semantics_Kinding_And_Context_Well_Formedness_Test.vo Cyclone_LN_Env_Test.vo Cyclone_Dynamic_Semantics_Test.vo Cyclone_Kinding_Test.vo Cyclone_Static_Semantics_Test.v

LEMMAFILES=Cyclone_LN_Terms_Lemmas.vo Cyclone_LN_Types_In_Terms_Lemmas.vo Cyclone_LN_Types_Lemmas.vo Cyclone_Gettype_Lemmas.vo  Cyclone_WFU_Lemmas.vo Cyclone_WFD_Lemmas.vo Cyclone_WFDG_Lemmas.vo Cyclone_Get_Lemmas.vo Cyclone_Fset_Lemmas.vo Cyclone_Ok_Lemmas.vo Cyclone_WFC_Lemmas.vo  Cyclone_Admit_Environment.vo Cyclone_Subst_Lemmas.vo

PROOFFILES=Cyclone_Canonical_Forms_Proof.vo Cyclone_Commuting_Substitutions_Proof.vo Cyclone_Commuting_Substitutions_Proof.vo Cyclone_Context_Weakening_Proof.vo Cyclone_Heap_Object_Safety_Proof.vo Cyclone_Heap_Weakening_Proof.vo Cyclone_Path_Extension_Proof.vo Cyclone_Return_Preservation_Proof.vo Cyclone_Substitutions_Proof.vo Cyclone_Term_Preservation_Proof.vo Cyclone_Term_Progress_Proof.vo Cyclone_Term_Weakening_Proof_Admitted.vo Cyclone_Term_Weakening_Proof.vo Cyclone_Typing_Well_Formedness_Proof.vo Cyclone_Useless_Substitutions_Proof.vo Cyclone_Type_Safety_Proof.vo

TACTICFILES=

EXPERIMENTFILES=

COQC=/home/milnes/opam-coq.8.5.2/4.01.0/bin/coqc

COQ_MAKEFILE=/home/milnes/opam-coq.8.5.2/4.01.0/bin/coq_makefile 

%.vo: %.v 
	$(COQC) $<

src:  TAGS depends $(SRCFILES)

tactic: TAGS src $(TACTICFILES)

test: TAGS depends tactic src $(TESTFILES)

lemma: TAGS depends tactic src $(LEMMAFILES)

proof: TAGS depends tactic lemma src $(PROOFFILES)

experiment: TAGS depends tactic src lemma proof $(PROOFFILES)

clean:
	rm -f *.vo
	rm -f \#*\#
	rm -f .\#*
	rm -f *~ 
	rm -f *.glob
	rm -f TAGS
	rm -f .*.aux
	rm -f coq.depends

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
	/home/milnes/opam-coq.8.5.2/4.01.0/bin/coqdep *.v > coq.depends 

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


#
#theorems:
#	grep -e 'Lemma ' -e Theorem -e Qed -e admit -e AdmitAlphaConversion -e Admitted $(PROOFS)
#
#lemmas:
#	grep -e 'Lemma ' -e Theorem -e Qed -e admit -e AdmitAlphaConversion -e Admitted $(LEMMAS)
#
#lemmasused:
#	grep -i 'apply ' *.v | grep -v IH | grep -v ' H' | grep -v SR | grep -v SL | grep -v SS | grep -v ind | grep -v ' K_' | grep -v 'S_' | grep -v 'L_' | grep -v 'R_' | grep -v 'A_' | grep -v ex_intro  | grep -v beq | grep -v Value

