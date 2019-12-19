COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "." Casper

SOURCE := preamble.v ListExtras.v ListSetExtras.v RealsExtras.v sorted_lists.v protocol.v common.v definitions.v fullnode.v lightnode.v binary.v ctl.v vlsm.v vlsm_run.v indexed_vlsm.v indexed_vlsm_projections.v commute.v vlsmfull.v

VO_FILE := $(shell find "." -type f -name '*.vo')
GLOB_FILE := $(shell find "." -type f -name '*.glob')
AUX_FILE := $(shell find "." -type f -name '*.vo.aux')

$(SOURCE:%.v=%.vo): %.vo: %.v
			@echo COQC $*.v
			@$(COQC) $(COQ_FLAG) $*.v

dep:
	@$(COQDEP) $(COQ_FLAG) $(SOURCE) > .depend

all: $(SOURCE:%.v=%.vo)
	
clean:
	@rm $(VO_FILE) $(GLOB_FILE) $(AUX_FILE)

.DEFAULT_GOAL := all

include .depend

