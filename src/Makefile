.PHONY: build debug

build:
	hastec Main.lhs --with-js=js/react-stubs.js; say done

debug:
	hastec Main.lhs --with-js=js/react-stubs.js --ddisable-js-opts --debug; say done

server:
	python -m SimpleHTTPServer 8765
