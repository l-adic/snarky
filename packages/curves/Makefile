.PHONY: all clean build-napi install-deps build test

NAPI_DIR = curves-napi

all: install-deps build

install-deps:
	cd ../.. && npm install

build-napi:
	cd $(NAPI_DIR) && npm run build

build: install-deps build-napi
	npx spago build

test: build
	npx spago test

clean:
	rm -rf output ../../node_modules
	cd $(NAPI_DIR) && cargo clean && rm -f *.node
	rm -f ../../package-lock.json