.PHONY: build clean docs web install_less_deps

build: build/index.css build/mui.css build/index.html build/all.js

.cabal-sandbox/bin/pigment.jsexe/all.js: .cabal-sandbox $(wildcard src/**/*hs)
	cabal install --ghcjs

.cabal-sandbox:
	cabal sandbox init
	cabal sandbox add-source ../react-haskell
	cabal sandbox add-source ../material-ui

clean:
	git clean -xf
	rm -rf .cabal-sandbox # TODO(joel) - why isn't this part of the git clean?

web:
	cp -r src/{index.html,css,js,Main.js} web
	cp dist/build/pigment/pigment.jsexe/all.js web/js/

build/index.css: src/css/index.less
	lessc src/css/index.less build/index.css --autoprefix=""

build/mui.css: src/css/mui.css
	cp src/css/mui.css build/

build/index.html: src/index.html
	cp src/index.html build/

build/all.js: .cabal-sandbox/bin/pigment.jsexe/all.js
	cp .cabal-sandbox/bin/pigment.jsexe/all.js build/

install_less_deps:
	npm install -g less less-plugin-autoprefix

# *caution*
# docs:
# 	rm -rf docs
# 	mkdir docs
# 	cd src; rsync -R $(wildcard **.lhs) ../docs; cd -
# 	cd docs; find . -name "*.lhs" -exec rename -v 's/\.lhs$$/\.md/i' "{}" ";"; cd -
# 	cd docs; ls | xargs sed -i '' -e's/^> /    /'; cd -
# 	mkdocs build
