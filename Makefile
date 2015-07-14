.PHONY: build repl clean docs web dash lint

LIB_SOURCE_FILES = $(wildcard src-lib/**/*hs)
LHS_FILES = $(wildcard src-lib/**/*.lhs)
SANDBOX = /home/vagrant/pigment-sandbox

build: build/index.html build/assets/index.css build/assets/all.js

repl: $(SANDBOX)
	cabal repl

# http://blog.jgc.org/2015/04/the-one-line-you-should-add-to-every.html
print-%: ; @echo $*=$($*)

clean:
	git clean -xf

$(SANDBOX)/bin/pigment.jsexe/all.js: $(SANDBOX) $(LIB_SOURCE_FILES) src-web/hs/Main.hs
	cabal install --ghcjs --flag ghcjs --disable-documentation --disable-library-profiling --disable-benchmarks

$(SANDBOX):
	cabal sandbox init --sandbox $(SANDBOX)
	cabal sandbox add-source ../react-haskell

build/assets/index.html: src-web/index.html
	cp src-web/index.html build/assets/
	
build/assets/index.css: src-web/css/index.css
	cp src-web/index.css build/assets/

build/assets/all.js: $(SANDBOX)/bin/pigment.jsexe/all.js
	cp $(SANDBOX)/bin/pigment.jsexe/all.js build/assets/

# This has a hidden dependency on global `hscolour`.
dist/doc/html/pigment/index.html: $(SANDBOX) $(LIB_SOURCE_FILES)
	cabal haddock --hyperlink-source

# this has a hidden dependency on sandbox-installed dash-haskell
dash: dist/doc/html/pigment/index.html
	rm -rf docsets
	../sandbox/.cabal-sandbox/bin/dash-haskell -c pigment.cabal -o docsets

lint:
	../sandbox/.cabal-sandbox/bin/hlint src-lib

# *caution*
docs:
	rm -rf docs
	mkdir docs
	cd lib; rsync -R $(LHS_FILES) docs; cd -
	cd docs; find . -name "*.lhs" -exec rename -v 's/\.lhs$$/\.md/i' "{}" ";"; cd -
	cd docs; ls | xargs sed -i '' -e's/^> /    /'; cd -
	mkdocs build
