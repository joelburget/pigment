.PHONY: build debug clean

build:
	hastec Main.lhs --with-js=js/react-stubs.js; say done

debug:
	hastec Main.lhs --with-js=js/react-stubs.js --ddisable-js-opts --debug; say done

clean:
	git clean -xf

server:
	python -m SimpleHTTPServer 8765
