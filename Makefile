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
	mkdir -p $(out)/exec
	cp -r build/exec/* $(out)/exec
	cp -r libs $(out)/
	echo '#! /bin/bash' > $(out)/bin/toatie
	echo 'TOATIE_PATH=$(out)/libs $(out)/exec/toatie $$@' >> $(out)/bin/toatie
	chmod +x $(out)/bin/toatie

clean:
	rm -r build
	make -C Test -k clean
