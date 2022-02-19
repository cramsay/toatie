# Typecheck all files in the `good` and `bad` dirs.
# All good files should typecheck and exit with success
# All bad files should fail typechecking and exit with failure

examples   := $(addsuffix .example , $(basename $(shell find examples/ -type f -name '*.tt')))
good_tests := $(addsuffix .goodtest, $(basename $(shell find good/ -type f -name '*.tt')))
bad_tests  := $(addsuffix .badtest , $(basename $(shell find bad/ -type f -name '*.tt')))

.PHONY : test %.goodtest %.badtest %.example

test : $(good_tests) $(bad_tests) $(examples)

%.example : %.tt
	@toatie -fTypeCheckOnly $< > /dev/null || \
	(echo "Example file $@ failed type checking" && exit 1)

%.goodtest : %.tt
	@toatie -fTypeCheckOnly $< > /dev/null || \
	(echo "Test $@ failed" && exit 1)

%.badtest : %.tt
	@! toatie -fTypeCheckOnly $< > /dev/null || \
	(echo "Test $@ failed" && exit 1)

all : test
	@echo "Success, all tests passed."
