#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.5pl2     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile LibPath LibVarPath LibVarPathEnv Cyclone_Formal_Syntax Cyclone_LN_FSET Cyclone_LN_Types Cyclone_LN_Terms Cyclone_LN_Types_In_Terms Cyclone_LN_Env Cyclone_LN_Tactics Cyclone_Dynamic_Semantics_Heap_Objects Cyclone_Dynamic_Semantics Cyclone_Static_Semantics_Typing_Heap_Objects -o Makefile.coq 
#

.DEFAULT_GOAL := all

# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# TIMECMD set a command to log .v compilation time;
# TIMED if non empty, use the default time command as TIMECMD;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f "$* (user: %U mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

vo_to_obj = $(addsuffix .o,\
  $(filter-out Warning: Error:,\
  $(shell $(COQBIN)coqtop -q -noinit -batch -quiet -print-mod-uid $(1))))

##########################
#                        #
# Libraries definitions. #
#                        #
##########################


##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?="$(HOME)/.local/share"
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL="${COQLIB}user-contrib"
COQDOCINSTALL="${DOCDIR}user-contrib"
COQTOPINSTALL="${COQLIB}toploop"
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: ./LibPath\
  ./LibVarPath\
  ./LibVarPathEnv\
  ./Cyclone_Formal_Syntax\
  ./Cyclone_LN_FSET\
  ./Cyclone_LN_Types\
  ./Cyclone_LN_Terms\
  ./Cyclone_LN_Types_In_Terms\
  ./Cyclone_LN_Env\
  ./Cyclone_LN_Tactics\
  ./Cyclone_Dynamic_Semantics_Heap_Objects\
  ./Cyclone_Dynamic_Semantics\
  ./Cyclone_Static_Semantics_Typing_Heap_Objects

.PHONY: all archclean beautify byte clean cleanall gallina gallinahtml html install install-doc install-natdynlink install-toploop opt printenv quick uninstall userinstall validate vio2vo ./LibPath ./LibVarPath ./LibVarPathEnv ./Cyclone_Formal_Syntax ./Cyclone_LN_FSET ./Cyclone_LN_Types ./Cyclone_LN_Terms ./Cyclone_LN_Types_In_Terms ./Cyclone_LN_Env ./Cyclone_LN_Tactics ./Cyclone_Dynamic_Semantics_Heap_Objects ./Cyclone_Dynamic_Semantics ./Cyclone_Static_Semantics_Typing_Heap_Objects

###################
#                 #
# Subdirectories. #
#                 #
###################

./LibPath:
	+cd "./LibPath" && $(MAKE) all

./LibVarPath:
	+cd "./LibVarPath" && $(MAKE) all

./LibVarPathEnv:
	+cd "./LibVarPathEnv" && $(MAKE) all

./Cyclone_Formal_Syntax:
	+cd "./Cyclone_Formal_Syntax" && $(MAKE) all

./Cyclone_LN_FSET:
	+cd "./Cyclone_LN_FSET" && $(MAKE) all

./Cyclone_LN_Types:
	+cd "./Cyclone_LN_Types" && $(MAKE) all

./Cyclone_LN_Terms:
	+cd "./Cyclone_LN_Terms" && $(MAKE) all

./Cyclone_LN_Types_In_Terms:
	+cd "./Cyclone_LN_Types_In_Terms" && $(MAKE) all

./Cyclone_LN_Env:
	+cd "./Cyclone_LN_Env" && $(MAKE) all

./Cyclone_LN_Tactics:
	+cd "./Cyclone_LN_Tactics" && $(MAKE) all

./Cyclone_Dynamic_Semantics_Heap_Objects:
	+cd "./Cyclone_Dynamic_Semantics_Heap_Objects" && $(MAKE) all

./Cyclone_Dynamic_Semantics:
	+cd "./Cyclone_Dynamic_Semantics" && $(MAKE) all

./Cyclone_Static_Semantics_Typing_Heap_Objects:
	+cd "./Cyclone_Static_Semantics_Typing_Heap_Objects" && $(MAKE) all

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

userinstall:
	+$(MAKE) USERINSTALL=true install

install:
	+cd ./LibPath && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./LibPath" install
	+cd ./LibVarPath && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./LibVarPath" install
	+cd ./LibVarPathEnv && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./LibVarPathEnv" install
	+cd ./Cyclone_Formal_Syntax && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_Formal_Syntax" install
	+cd ./Cyclone_LN_FSET && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_LN_FSET" install
	+cd ./Cyclone_LN_Types && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_LN_Types" install
	+cd ./Cyclone_LN_Terms && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_LN_Terms" install
	+cd ./Cyclone_LN_Types_In_Terms && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_LN_Types_In_Terms" install
	+cd ./Cyclone_LN_Env && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_LN_Env" install
	+cd ./Cyclone_LN_Tactics && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_LN_Tactics" install
	+cd ./Cyclone_Dynamic_Semantics_Heap_Objects && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_Dynamic_Semantics_Heap_Objects" install
	+cd ./Cyclone_Dynamic_Semantics && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_Dynamic_Semantics" install
	+cd ./Cyclone_Static_Semantics_Typing_Heap_Objects && $(MAKE) DSTROOT="$(DSTROOT)" INSTALLDEFAULTROOT="$(INSTALLDEFAULTROOT)/./Cyclone_Static_Semantics_Typing_Heap_Objects" install

install-doc:

uninstall_me.sh: Makefile.coq
	echo '#!/bin/sh' > $@
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/$(INSTALLDEFAULTROOT) && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "$(INSTALLDEFAULTROOT)" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	chmod +x $@

uninstall: uninstall_me.sh
	sh $<

.merlin:
	@echo 'FLG -rectypes' > .merlin
	@echo "B $(COQLIB) kernel" >> .merlin
	@echo "B $(COQLIB) lib" >> .merlin
	@echo "B $(COQLIB) library" >> .merlin
	@echo "B $(COQLIB) parsing" >> .merlin
	@echo "B $(COQLIB) pretyping" >> .merlin
	@echo "B $(COQLIB) interp" >> .merlin
	@echo "B $(COQLIB) printing" >> .merlin
	@echo "B $(COQLIB) intf" >> .merlin
	@echo "B $(COQLIB) proofs" >> .merlin
	@echo "B $(COQLIB) tactics" >> .merlin
	@echo "B $(COQLIB) tools" >> .merlin
	@echo "B $(COQLIB) toplevel" >> .merlin
	@echo "B $(COQLIB) stm" >> .merlin
	@echo "B $(COQLIB) grammar" >> .merlin
	@echo "B $(COQLIB) config" >> .merlin

clean::
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml uninstall_me.sh
	+cd ./LibPath && $(MAKE) clean
	+cd ./LibVarPath && $(MAKE) clean
	+cd ./LibVarPathEnv && $(MAKE) clean
	+cd ./Cyclone_Formal_Syntax && $(MAKE) clean
	+cd ./Cyclone_LN_FSET && $(MAKE) clean
	+cd ./Cyclone_LN_Types && $(MAKE) clean
	+cd ./Cyclone_LN_Terms && $(MAKE) clean
	+cd ./Cyclone_LN_Types_In_Terms && $(MAKE) clean
	+cd ./Cyclone_LN_Env && $(MAKE) clean
	+cd ./Cyclone_LN_Tactics && $(MAKE) clean
	+cd ./Cyclone_Dynamic_Semantics_Heap_Objects && $(MAKE) clean
	+cd ./Cyclone_Dynamic_Semantics && $(MAKE) clean
	+cd ./Cyclone_Static_Semantics_Typing_Heap_Objects && $(MAKE) clean

archclean::
	rm -f *.cmx *.o
	+cd ./LibPath && $(MAKE) archclean
	+cd ./LibVarPath && $(MAKE) archclean
	+cd ./LibVarPathEnv && $(MAKE) archclean
	+cd ./Cyclone_Formal_Syntax && $(MAKE) archclean
	+cd ./Cyclone_LN_FSET && $(MAKE) archclean
	+cd ./Cyclone_LN_Types && $(MAKE) archclean
	+cd ./Cyclone_LN_Terms && $(MAKE) archclean
	+cd ./Cyclone_LN_Types_In_Terms && $(MAKE) archclean
	+cd ./Cyclone_LN_Env && $(MAKE) archclean
	+cd ./Cyclone_LN_Tactics && $(MAKE) archclean
	+cd ./Cyclone_Dynamic_Semantics_Heap_Objects && $(MAKE) archclean
	+cd ./Cyclone_Dynamic_Semantics && $(MAKE) archclean
	+cd ./Cyclone_Static_Semantics_Typing_Heap_Objects && $(MAKE) archclean

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

###################
#                 #
# Implicit rules. #
#                 #
###################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

