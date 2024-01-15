.SILENT:

build: Main.lean
	lake build

run: build
	./.lake/build/bin/lean-ml

clean:
	lake clean