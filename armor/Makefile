AGDA_EXEC?=agda
AGDA_OPTIONS_RTS=+RTS -M5G -RTS
AGDA_OPTIONS_LIB=--library-file=`pwd`/$(LIBRARIES)

AGDA=$(AGDA_EXEC) $(AGDA_OPTIONS_LIB) $(AGDA_OPTIONS_RTS)

AGDA_STDLIB=agda-stdlib/standard-library.agda-lib
LIBRARIES=libraries

ARMOR_SRC=src
ARMOR_BUILD=$(ARMOR_SRC)/MAlonzo
ARMOR_MAIN=$(ARMOR_SRC)/Armor/Main.agda
ARMOR_MAIN_HS=$(ARMOR_BUILD)/Code/Armor/Main.hs
ARMOR_DRIVER_BIN=../armor-driver/armor-bin

STACK_GHC_EXE=stack --compiler ghc-8.8.4 exec ghc --
STACK_GHC_OPTIONS=-O -Werror -fwarn-incomplete-patterns

.PHONY: all
all: $(ARMOR_MAIN_HS)
	$(STACK_GHC_EXE) $(STACK_GHC_OPTIONS) -o $(ARMOR_DRIVER_BIN) -i$(ARMOR_SRC) -main-is MAlonzo.Code.Armor.Main $(ARMOR_MAIN_HS) --make

libraries:
	echo `pwd`/$(AGDA_STDLIB) > $(LIBRARIES)

.PHONY: haskell
$(ARMOR_MAIN_HS): libraries
	$(AGDA) --ghc-dont-call-ghc -c $(ARMOR_MAIN)

.PHONY: default
default: libraries
	$(AGDA) -c $(ARMOR_MAIN)
	mv $(ARMOR_SRC)/Main $(ARMOR_DRIVER_BIN)

.PHONY: clean
clean:
	find . -type f -name '*.agdai' -delete
	rm -rf $(ARMOR_BUILD)
	rm $(ARMOR_DRIVER_BIN)
