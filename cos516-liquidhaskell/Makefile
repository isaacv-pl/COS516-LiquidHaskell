bin/%: src/%.hs
	ghc $< -o $@ || true

all: $(patsubst src/%.hs,bin/%,$(wildcard src/*.hs))

clean:
	git clean -dfX
