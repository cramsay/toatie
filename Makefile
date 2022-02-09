srcs := $(shell find src/ -type f -name '*.idr')
bin := ./build/exec/toatie

.PHONY : all bin check install

all : $(bin) check

$(bin): $(srcs) toatie.ipkg
	idris2 --build toatie.ipkg

bin: $(bin)

check: $(bin)
	make -C Test -k all

install: $(bin)
	mkdir -p $(out)/bin
	cp -r build/exec/* $(out)/bin

clean:
	rm -r build
