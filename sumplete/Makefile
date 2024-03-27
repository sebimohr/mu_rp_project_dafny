# Makefile for dafny file "sumplete.dfy"

# Variables
DAFNY=dafny
DAFNY_FLAGS=/compile:3 /spillTargetCode:2
PROGRAM_NAME=sumplete
SOURCE_FILE=$(PROGRAM_NAME).dfy
COMPILED_FILE=$(PROGRAM_NAME).cs

CS_FILE=externalMethods.cs

# Default target
all: $(SOURCE_FILE)
	$(DAFNY) $(SOURCE_FILE) $(DAFNY_FLAGS) $(CS_FILE)

# Rule for cleanup
clean:
	rm -f $(COMPILED_FILE) *.dll *.runtimeconfig.json

.PHONY: all clean
