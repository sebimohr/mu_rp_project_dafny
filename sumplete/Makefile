# Makefile for dafny file "sumplete.dfy"

# Variables
DAFNY=dafny
DAFNY_FLAGS=/compile:3 /spillTargetCode:2 /out
PROGRAM_NAME=sumplete
SOURCE_FILE=$(PROGRAM_NAME).dfy
EXECUTABLE_FILE=$(PROGRAM_NAME).exe

# Default target
all: $(EXECUTABLE_FILE)

# Rule for compiling Dafny to executable
$(EXECUTABLE_FILE): $(SOURCE_FILE)
	$(DAFNY) $(DAFNY_FLAGS):$(EXECUTABLE_FILE) $(SOURCE_FILE)

# Rule for running the program
run: $(EXECUTABLE_FILE)
	./$(EXECUTABLE_FILE)

# Rule for cleanup
clean:
	rm -f $(EXECUTABLE_FILE) *.dll *.runtimeconfig.json *.cs

.PHONY: all run clean
