FSTAR ?= fstar.exe
FSTAR_CACHE_DIR ?= .fstar-cache
FSTAR_SRC := fstar/Catcat.Core.fst
FSTAR_OUT := generated
EXTRACTED := $(FSTAR_OUT)/Catcat_Core.ml

.PHONY: all extract repl clean

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

clean:
	rm -rf _build $(FSTAR_CACHE_DIR) $(FSTAR_OUT)/Catcat_Core.ml $(FSTAR_OUT)/Catcat_Core.mli