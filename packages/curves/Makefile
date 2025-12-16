.PHONY: all clean build install-deps test

all: install-deps build

install-deps:
	cd ../.. && npm install

build: install-deps 
	cd ../.. && $(MAKE) build-crypto
	npx spago build

test: build
	npx spago test

clean:
	rm -rf output ../../node_modules