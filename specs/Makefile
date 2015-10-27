SYSTEM = tabulator
ELECTION_PRELUDE = ~/Sandboxes/Elections/EBON/elections_domain_model.bon
INFORMAL_BON_FILES = tabulator.bon
FORMAL_BON_FILES = 
REQUIREMENTS = 
BON_FILES = $(ELECTION_PRELUDE) $(INFORMAL_BON_FILES) $(FORMAL_BON_FILES) $(REQUIREMENTS)

.PHONY: all clean realclean

all: $(SYSTEM)-iig.dot index.txt index.html html/index.html

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
