AGDA_EXEC?=agda
AGDA_OPTIONS_RTS=+RTS -M5G -RTS

AGDA=$(AGDA_EXEC) $(AGDA_OPTIONS_RTS)

AGDA_STDLIB=agda-stdlib/standard-library.agda-lib
LIBRARIES=libraries

ARMOR_SRC=src
ARMOR_BUILD=$(ARMOR_SRC)/MAlonzo
ARMOR_MAIN=$(ARMOR_SRC)/Armor/Main.agda

.PHONY: libraries
libraries:
	echo `pwd`/$(AGDA_STDLIB) > $(LIBRARIES)

default: libraries
	$(AGDA) --library-file=`pwd`/$(LIBRARIES) -c $(ARMOR_MAIN)

.PHONY: clean
clean:
	find . -type f -name '*.agdai' -delete
	rm -rf $(ARMOR_BUILD)
	rm $(ARMOR_SRC)/Main
