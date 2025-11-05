.PHONY: all clean build-napi install-napi-deps build test

NAPI_DIR = curves-napi
FFI_DIR = src/Snarky/Curves

all: install-napi-deps build-napi build

install-napi-deps:
	cd $(NAPI_DIR) && npm install

build-napi:
	cd $(NAPI_DIR) && npm run build

build: build-napi
	spago build
	mkdir -p output/Snarky.Curves.Pallas output/Snarky.Curves.Vesta output/Snarky.Curves.BN254
	cp $(FFI_DIR)/pallas-napi.node output/Snarky.Curves.Pallas/pallas-napi.node
	cp $(FFI_DIR)/vesta-napi.node output/Snarky.Curves.Vesta/vesta-napi.node
	cp $(FFI_DIR)/bn254-napi.node output/Snarky.Curves.BN254/bn254-napi.node

test: build
	spago test

clean:
	rm -f $(FFI_DIR)/*.node
	rm -rf output
	cd $(NAPI_DIR) && cargo clean
	rm -f $(NAPI_DIR)/*.d.ts $(NAPI_DIR)/*.js $(NAPI_DIR)/*.node