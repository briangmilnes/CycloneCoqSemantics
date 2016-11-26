-include coq.depends
all: TAGS src tactic lemma test proof experiment 

SRCFILES= LibPath.vo LibVarPath.vo LibVarPathEnv.vo Cyclone_Formal_Syntax.vo Cyclone_LN_FSET.vo Cyclone_LN_Types.vo Cyclone_LN_Terms.vo Cyclone_LN_Types_In_Terms.vo Cyclone_LN_Tactics.vo 

TESTFILES=Cyclone_Formal_Syntax_Test_Env.vo Cyclone_LN_Tactics_Test_Notin.vo

LEMMAFILES=

PROOFFILES= Cyclone_LN_Types_Lemmas.vo Cyclone_LN_Terms_Lemmas.vo Cyclone_LN_Types_In_Terms_Lemmas.vo

TACTICFILES=

EXPERIMENTFILES=

COQC=/home/milnes/opam-coq.8.5.2/4.01.0/bin/coqc

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
	/home/milnes/opam-coq.8.5.2/4.01.0/bin/coqdep -I . *.v > coq.depends 

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
