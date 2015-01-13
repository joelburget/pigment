.PHONY: build debug clean server docs web

debug: src/css/index.css
	cd src; hastec Main.lhs --with-js=js/react-stubs.js --ddisable-js-opts --debug; say done; cd -

build: src/css/index.css
	cd src; hastec Main.lhs --with-js=js/react-stubs.js; say done; cd -

clean:
	git clean -xf
	cd src; rm -rf main; cd -

server:
	cd src; python -m SimpleHTTPServer 8765

web:
	cp -r src/{index.html,css,js,Main.js} web

src/css/index.css: src/css/index.less
	cd src/css; lessc index.less index.css --autoprefix=""; cd -

# *caution*
# docs:
# 	rm -rf docs
# 	mkdir docs
# 	cd src; rsync -R $(wildcard **.lhs) ../docs; cd -
# 	cd docs; find . -name "*.lhs" -exec rename -v 's/\.lhs$$/\.md/i' "{}" ";"; cd -
# 	cd docs; ls | xargs sed -i '' -e's/^> /    /'; cd -
# 	mkdocs build
