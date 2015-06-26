.PHONY: build repl clean docs web install_less_deps dash lint

LIB_SOURCE_FILES = $(wildcard src-lib/**/*hs)
LHS_FILES = $(wildcard src-lib/**/*.lhs)
SANDBOX = /home/vagrant/pigment-sandbox

build: build/index.css build/mui.css build/index.html build/all.js

repl: $(SANDBOX)
	cabal repl

install_less_deps:
	npm install -g less less-plugin-autoprefix

# http://blog.jgc.org/2015/04/the-one-line-you-should-add-to-every.html
print-%: ; @echo $*=$($*)

clean:
	git clean -xf

$(SANDBOX)/bin/pigment.jsexe/all.js: $(SANDBOX) $(LIB_SOURCE_FILES) src-web/Main.hs
	cabal install --ghcjs --flag ghcjs --disable-documentation --disable-library-profiling --disable-benchmarks

$(SANDBOX):
	cabal sandbox init --sandbox $(SANDBOX)
	cabal sandbox add-source ../react-haskell
	cabal sandbox add-source ../material-ui

build/index.css: src-web/css/index.less src-web/css/mui.css
	lessc src-web/css/index.less build/index.css --autoprefix=""

build/mui.css: src-web/css/mui.css
	cp src-web/css/mui.css build/

build/index.html: src-web/index.html
	cp src-web/index.html build/

build/all.js: $(SANDBOX)/bin/pigment.jsexe/all.js
	cp $(SANDBOX)/bin/pigment.jsexe/all.js build/

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
