.PHONY: build clean docs web install_less_deps dash lint

SOURCE_FILES = $(wildcard src/**/*hs)
LHS_FILES = $(wildcard src/**/*.lhs)
SANDBOX = /home/vagrant/pigment-sandbox

build: build/index.css build/mui.css build/index.html build/all.js

install_less_deps:
	npm install -g less less-plugin-autoprefix

# http://blog.jgc.org/2015/04/the-one-line-you-should-add-to-every.html
print-%: ; @echo $*=$($*)

clean:
	git clean -xf

web:
	cp -r src/{index.html,css,js,Main.js} web
	cp dist/build/pigment/pigment.jsexe/all.js web/js/

$(SANDBOX)/bin/pigment.jsexe/all.js: $(SANDBOX) $(SOURCE_FILES)
	cabal install --ghcjs --disable-documentation --disable-library-profiling --disable-benchmarks

$(SANDBOX):
	cabal sandbox init --sandbox $(SANDBOX)
	cabal sandbox add-source ../react-haskell
	cabal sandbox add-source ../material-ui

build/index.css: src/css/index.less src/css/mui.css
	lessc src/css/index.less build/index.css --autoprefix=""

build/mui.css: src/css/mui.css
	cp src/css/mui.css build/

build/index.html: src/index.html
	cp src/index.html build/

build/all.js: $(SANDBOX)/bin/pigment.jsexe/all.js
	cp $(SANDBOX)/bin/pigment.jsexe/all.js build/

# This has a hidden dependency on global `hscolour`.
dist/doc/html/pigment/index.html: $(SANDBOX) $(SOURCE_FILES)
	cabal haddock --hyperlink-source

# this has a hidden dependency on sandbox-installed dash-haskell
dash: dist/doc/html/pigment/index.html
	../sandbox/.cabal-sandbox/bin/dash-haskell -c pigment.cabal -o docsets

lint:
	../sandbox/.cabal-sandbox/bin/hlint src

# *caution*
docs:
	rm -rf docs
	mkdir docs
	cd src; rsync -R $(LHS_FILES) docs; cd -
	cd docs; find . -name "*.lhs" -exec rename -v 's/\.lhs$$/\.md/i' "{}" ";"; cd -
	cd docs; ls | xargs sed -i '' -e's/^> /    /'; cd -
	mkdocs build
