# Makefile for dafny file "sumplete.dfy"

# Variables
DAFNY=dafny
PROGRAM_NAME=sumplete
SOURCE_FILE=$(PROGRAM_NAME).dfy
COMPILED_FILE=$(PROGRAM_NAME).cs

CS_FILE=externalMethods.cs

# Default target
all: $(SOURCE_FILE)
	$(DAFNY) run $(SOURCE_FILE) --input $(CS_FILE)

# Rule for cleanup
clean:
	rm -f $(COMPILED_FILE) *.dll *.runtimeconfig.json

.PHONY: all clean
