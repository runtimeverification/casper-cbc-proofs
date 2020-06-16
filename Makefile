COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "." Casper

SRC_DIR := .
SOURCE := $(wildcard $(SRC_DIR)/*.v) $(wildcard $(SRC_DIR)/Lib/*.v) $(wildcard $(SRC_DIR)/CBC/*.v) $(wildcard $(SRC_DIR)/VLSM/*.v)

VO_FILE := $(wildcard $(SRC_DIR)/**/*.vo)
VOK_FILE := $(wildcard $(SRC_DIR)/**/*.vok)
VOS_FILE := $(wildcard $(SRC_DIR)/**/*.vos)
GLOB_FILE := $(wildcard $(SRC_DIR)/**/*.glob)
AUX_FILE := $(wildcard $(SRC_DIR)/**/.*.aux)

$(SOURCE:%.v=%.vo): %.vo: %.v
			@echo COQC $*.v
			@$(COQC) $(COQ_FLAG) $*.v

dep:
	@$(COQDEP) $(COQ_FLAG) $(SOURCE) > .depend

all: $(SOURCE:%.v=%.vo)
	
clean:
	@rm $(VO_FILE) $(VOK_FILE) $(VOS_FILE) $(GLOB_FILE) $(AUX_FILE)

.DEFAULT_GOAL := all

include .depend

