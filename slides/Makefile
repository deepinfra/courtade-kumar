bun ?= bun

.PHONY: build local_deploy run present runnocompile check test clean

build local_deploy:
	$(bun) tools/build.ts

run present:
	$(bun) tools/server.ts --build

runnocompile:
	$(bun) tools/server.ts

check:
	$(bun) run check

test:
	$(bun) test

clean:
	rm -rf build
