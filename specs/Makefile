SYSTEM = tabulator
ELECTION_PRELUDE = ~/Sandboxes/Elections/EBON/elections_domain_model.bon
INFORMAL_BON_FILES = $(SYSTEM)_informal.bon
STATIC_MODEL_FILES = $(SYSTEM)_static_model.bon
DYNAMIC_MODEL_FILES = $(SYSTEM)_dynamic_model.bon
FORMAL_BON_FILES = $(SYSTEM)_formal.bon
REQUIREMENTS = 
BON_FILES = $(ELECTION_PRELUDE) $(INFORMAL_BON_FILES) $(FORMAL_BON_FILES) $(REQUIREMENTS)

.PHONY: all clean realclean \
	typecheck typecheck-consistency \
	typecheck-informal typecheck-formal \
	typecheck-static typecheck-dynamic

all: typecheck $(SYSTEM)-iig.dot index.txt index.html html/index.html

typecheck: typecheck-informal typecheck-formal \
	typecheck-static typecheck-dynamic typecheck-consistency

typecheck-consistency:
	bonc -cc -tc $(ELECTION_PRELUDE) $(INFORMAL_BON_FILES) $(FORMAL_BON_FILES)

typecheck-informal:
	bonc -tc -i -ci $(ELECTION_PRELUDE) $(INFORMAL_BON_FILES)

typecheck-formal:
	bonc -tc -f -cf $(ELECTION_PRELUDE) $(FORMAL_BON_FILES)

typecheck-static:
	bonc -tc -i -ci $(ELECTION_PRELUDE) $(INFORMAL_BON_FILES) $(STATIC_MODEL_FILES)

typecheck-dynamic:
	bonc -tc -i -ci $(ELECTION_PRELUDE) $(INFORMAL_BON_FILES) $(DYNAMIC_MODEL_FILES)

realclean:
	rm -rf html

clean:
	rm -f $(SYSTEM)-icg.dot $(SYSTEM)-iig.dot index.txt index.html
	rm -rf html/*

$(SYSTEM)-icg.dot: $(BON_FILES)
	bonc -g ICG $(BON_FILES) > $(SYSTEM)-icg.dot

$(SYSTEM)-iig.dot: $(BON_FILES)
	bonc -p IIG -po $(SYSTEM)-iig.dot $(BON_FILES)

index.txt: $(BON_FILES)
	bonc -po index.txt -p TXT $(BON_FILES)

index.html: $(BON_FILES)
	bonc -po index.html -p HTML $(BON_FILES)

html/index.html: $(BON_FILES)
	mkdir -p html
	bonc -p NEWHTML -po html $(BON_FILES)
