FSTAR ?= fstar.exe
FSTAR_CACHE_DIR ?= .fstar-cache
FSTAR_SRC := fstar/Catcat.Core.fst
FSTAR_OUT := generated
EXTRACTED := $(FSTAR_OUT)/Catcat_Core.ml

# Mechanized specification and reference interpreter. Modules are numbered so
# that dependency order and reading order coincide; `sort` therefore gives a
# valid build order. Interfaces must be checked before their implementations.
SPEC_DIR  := P01_Specification
REF_DIR   := P02_Reference
ELAB_DIR  := P03_Elaboration
SPEC_SRC  := $(sort $(wildcard $(SPEC_DIR)/M*.fst))
ELAB_SRC  := $(sort $(wildcard $(ELAB_DIR)/E*.fsti)) $(sort $(wildcard $(ELAB_DIR)/E*.fst))
ELAB_IMPL := $(sort $(wildcard $(ELAB_DIR)/E*.fst))
# Interfaces first, then implementations. Plain `sort` over both would put
# `R01.fst` before `R01.fsti`, which happens to work but only because F* loads
# an interface implicitly; being explicit keeps it robust.
REF_SRC   := $(sort $(wildcard $(REF_DIR)/R*.fsti)) $(sort $(wildcard $(REF_DIR)/R*.fst))

FSTAR_INC := --include $(SPEC_DIR) --include $(REF_DIR) --include $(ELAB_DIR)
FSTAR_CHK := $(FSTAR) --cache_dir $(FSTAR_CACHE_DIR) --cache_checked_modules $(FSTAR_INC)

# Modules that make up the runnable reference interpreter.
REF_MODULES := +M01_Kinds +M02_Stacks +M03_Signatures +M04_Effects +M05_Terms \
               +M06_Typing +R01_Runtime +R02_Machine +R03_Prelude +R04_Erasure \
               +R05_Driver

# ...plus the elaborator, for the REPL.
ALL_MODULES := $(REF_MODULES) +E01_Lexer +E02_Ast +E03_Parser +E04_Elaborate \
               +E05_Locate +E06_Repl

.PHONY: all extract repl catcat verify verify-spec verify-ref verify-elab interp admits clean

all: repl

$(EXTRACTED): $(FSTAR_SRC)
	mkdir -p $(FSTAR_OUT) $(FSTAR_CACHE_DIR)
	$(FSTAR) \
		--cache_dir $(FSTAR_CACHE_DIR) \
		--codegen OCaml \
		--extract '+Catcat.Core' \
		--odir $(FSTAR_OUT) \
		$(FSTAR_SRC)

extract: $(EXTRACTED)

repl: extract
	dune build bin/main.exe

# Typecheck everything. Gaps are explicit `admit`/`assume` occurrences, which
# `make admits` inventories.
verify: verify-spec verify-ref verify-elab

verify-spec:
	@mkdir -p $(FSTAR_CACHE_DIR)
	@for m in $(SPEC_SRC); do \
		echo "--- $$m"; $(FSTAR_CHK) $$m || exit 1; \
	done

verify-ref:
	@mkdir -p $(FSTAR_CACHE_DIR)
	@for m in $(REF_SRC); do \
		echo "--- $$m"; $(FSTAR_CHK) $$m || exit 1; \
	done

verify-elab:
	@mkdir -p $(FSTAR_CACHE_DIR)
	@for m in $(ELAB_SRC); do \
		echo "--- $$m"; $(FSTAR_CHK) $$m || exit 1; \
	done

# Extract the reference interpreter to OCaml.
#
# One invocation per implementation, because a module with an interface has
# only its .fsti loaded when something else depends on it -- so a single
# whole-program invocation would never process the .fst bodies and would emit
# no code for them.
REF_IMPL := $(sort $(wildcard $(REF_DIR)/R*.fst))

generated/E06_Repl.ml: $(SPEC_SRC) $(REF_SRC) $(ELAB_SRC)
	@mkdir -p generated $(FSTAR_CACHE_DIR)
	$(FSTAR_CHK) --codegen OCaml --extract '$(ALL_MODULES)' \
		--odir generated $(SPEC_DIR)/M06_Typing.fst
	@for m in $(REF_IMPL) $(ELAB_IMPL); do \
		echo "--- extract $$m"; \
		$(FSTAR_CHK) --codegen OCaml \
			--extract "+$$(basename $$m .fst)" \
			--odir generated $$m || exit 1; \
	done

interp: generated/E06_Repl.ml
	dune build bin/interp.exe
	./_build/default/bin/interp.exe

# The REPL: read a line of catcat, elaborate, typecheck, evaluate, print.
catcat: generated/E06_Repl.ml
	dune build bin/catcat.exe
	@echo "built ./_build/default/bin/catcat.exe"

admits:
	@grep -rn 'admit ()\|^assume val' $(SPEC_SRC) $(REF_SRC) || echo "no admits"

clean:
	rm -rf _build $(FSTAR_CACHE_DIR) $(FSTAR_OUT)/Catcat_Core.ml $(FSTAR_OUT)/Catcat_Core.mli