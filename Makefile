srcs := $(shell find src/ -type f -name '*.idr')
bin := ./build/exec/toatie

.PHONY : all bin test

all : $(bin) test

$(bin): $(srcs) toatie.ipkg
	idris2 --build toatie.ipkg

test: $(bin)
	make -C Test -k all

clean:
	rm -r build
