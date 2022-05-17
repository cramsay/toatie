# Typecheck all files in the `good` and `bad` dirs.
# All good files should typecheck and exit with success
# All bad files should fail typechecking and exit with failure

netlistsvg := $(shell which netlistsvg)
examples   := $(addsuffix .example , $(basename $(shell find Examples/ -maxdepth 1 -name '*.tt')))
good_tests := $(addsuffix .goodtest, $(basename $(shell find good/ -name '*.tt')))
bad_tests  := $(addsuffix .badtest , $(basename $(shell find bad/ -name '*.tt')))
good_synth_tests := $(addsuffix .goodsynthtest, $(basename $(shell find good_synth/ -name '*.tt')))
bad_synth_tests := $(addsuffix .badsynthtest, $(basename $(shell find bad_synth/ -name '*.tt')))

good_synth_clean := $(addsuffix .vhd, $(basename $(shell find good_synth/ -name '*.tt'))) \
                    $(shell find good_synth/ -type f -name 'wave.vcd') \
                    $(shell find good_synth/ -type f -name 'schem.json') \
                    $(shell find good_synth/ -type f -name 'schem.svg') \
bad_synth_clean := $(addsuffix .vhd, $(basename $(shell find bad_synth/ -name '*.tt'))) \
                    $(shell find bad_synth/ -type f -name 'wave.vcd')
ghdl_lib_clean := $(shell find . -type f -name '*.cf')

.PHONY : test %.goodtest %.badtest %.goodsynthtest %.badsynthtest %.example

test : $(good_tests) $(bad_tests) $(good_synth_tests) $(bad_synth_tests) $(examples)

%.example : %.tt
	@toatie -fTypeCheckOnly $< > /dev/null || \
	(echo "Example file $@ failed type checking" && exit 1)

%.goodtest : %.tt
	@toatie -fTypeCheckOnly $< > /dev/null || \
	(echo "Test $@ failed" && exit 1)

%.badtest : %.tt
	@! toatie -fTypeCheckOnly $< > /dev/null || \
	(echo "Test $@ failed" && exit 1)

%.goodsynthtest : %.tt
	@toatie -fNetlist=$(basename $(@F)) -fOutDir=$(@D) $< > /dev/null && \
	ghdl -i --work=$(subst /,_,$(@D)) $(patsubst %.tt,%.vhd   ,$<   ) && \
	ghdl -i --work=$(subst /,_,$(@D)) $(patsubst %.tt,%_tb.vhd,$<   ) && \
	ghdl -m --work=$(subst /,_,$(@D)) $(patsubst %.tt,%       ,$(<F)) && \
	ghdl -m --work=$(subst /,_,$(@D)) $(patsubst %.tt,%_tb    ,$(<F)) && \
	ghdl -r --work=$(subst /,_,$(@D)) $(patsubst %.tt,%_tb    ,$(<F)) --vcd=$(@D)/wave.vcd > /dev/null && \
	yosys -m ghdl -p "ghdl --work=$(subst /,_,$(@D)) $(patsubst %.tt,%       ,$(<F)); synth -top $(patsubst %.tt,%       ,$(<F)); write_json -compat-int $(@D)/schem.json" > /dev/null && \
	node $(netlistsvg) $(@D)/schem.json -o $(@D)/schem.svg || \
	(echo "Test $@ failed" && exit 1)

%.badsynthtest : %.tt
	@!(toatie -fNetlist=$(basename $(@F)) -fOutDir=$(@D) $< > /dev/null && \
	ghdl -i --work=$(subst /,_,$(@D)) $(patsubst %.tt,%.vhd   ,$<   ) && \
	ghdl -i --work=$(subst /,_,$(@D)) $(patsubst %.tt,%_tb.vhd,$<   ) && \
	ghdl -m --work=$(subst /,_,$(@D)) $(patsubst %.tt,%       ,$(<F)) && \
	ghdl -m --work=$(subst /,_,$(@D)) $(patsubst %.tt,%_tb    ,$(<F)) && \
	ghdl -r --work=$(subst /,_,$(@D)) $(patsubst %.tt,%_tb    ,$(<F)) --vcd=$(@D)/wave.vcd > /dev/null) || \
	(echo "Test $@ failed" && exit 1)

all : test
	@echo "Success, all tests passed."

clean:
	rm $(good_synth_clean) $(bad_synth_clean) $(ghdl_lib_clean)
