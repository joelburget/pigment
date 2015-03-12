.PHONY: build clean docs web install_less_deps

# debug: src/css/index.css
# 	cabal install --ghcjs

build: build/index.css assemble
	cabal install --ghcjs

assemble:
	cp src/index.html build

clean:
	git clean -xf

web:
	cp -r src/{index.html,css,js,Main.js} web
	cp dist/build/pigment/pigment.jsexe/all.js web/js/

build/index.css: src/css/index.less
	lessc src/css/index.less build/index.css --autoprefix=""

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
