# ===================================================================
# Copyright 2024 Zhengpu Shi
#  This file is part of FinMatrix. It is distributed under the MIT
#  "expat license". You should have recieved a LICENSE file with it.
# ===================================================================

COQMAKEFILE ?= Makefile.coq

MY_HTML_ROOT = doc/FinMatrix
MY_HTML_ROOT_WITH_VERSION = $(MY_HTML_ROOT)/v1.3

HTML_EXTRA_DIR = html-extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage \
  --no-lib-name \
  --with-header $(HTML_EXTRA_DIR)/header.html \
  --with-footer $(HTML_EXTRA_DIR)/footer.html \
  # --parse-comments
export COQDOCFLAGS

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

html: $(COQMAKEFILE)
	rm -rf html/
	rm -rf $(MY_HTML_ROOT_WITH_VERSION)
	mkdir -p $(MY_HTML_ROOT)
	$(MAKE) -f $^ $@
	mv html $(MY_HTML_ROOT_WITH_VERSION)
	cp $(HTML_EXTRA_DIR)/index.html $(MY_HTML_ROOT)/
	cp $(HTML_EXTRA_DIR)/header.html $(MY_HTML_ROOT_WITH_VERSION)/
	cp $(HTML_EXTRA_DIR)/footer.html $(MY_HTML_ROOT_WITH_VERSION)/
	cp $(HTML_EXTRA_DIR)/resources $(MY_HTML_ROOT_WITH_VERSION)/ -R

# generate dependent graph
dep:
	@./make_dep_graph.sh

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $^ uninstall

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall

cleanall: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

.PHONY: all clean cleanall html install uninstall
