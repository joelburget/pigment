# Pigment

[![](http://pigment.herokuapp.com/badge.svg)](http://pigment.herokuapp.com)

[Pigment](http://pigment.io) is an experiment in programming language design. It's built on top of
the incredible Epigram programming language.

The fundamental design consideration behind Pigment is *cooperation*. The programmer and the programming environment should both do the things that they're good at, to build programs together.

A few examples of things I think the computer is better at than me:

* telling whether a program is correct
* finding all the uses of a function or datatype
* refactoring

I'm sick of the hostile relationship I have with my compiler. It sits there silently while I do all the hard work. Then when I submit a program, most of the time it tells me I've made a mistake. Half the time it's done enough work to fix the program itself, but instead I get a cryptic error message.

# Installing

Installing Pigment yourself is poorly tested at the moment. Please contribute back steps which I've forgotten.

* Install [GHCJS](https://github.com/ghcjs/ghcjs) - Pigment's compiler. The easiest way to do this at the moment is through the [ghcjs-box](https://github.com/joelburget/ghcjs-box) vagrant box. GHCJS 7.10.2 or later is highly recommended.
* Clone this repository - `git clone https://github.com/joelburget/pigment.git`
* `cd pigment`
* `make` builds a javascript executable from the haskell code in `src-web/hs`. We still need to transpile the javascript in `src-web/js`.
* `cd src-web/js` then `webpack`. TODO(joel) put this in the makefile.

# Contributing

The easiest way to contribute back is a pull request to the [official repository](https://github.com/joelburget/pigment).

## More Details

There are several different executables besides the main program. It's useful to first familiarize yourself with them. These are all listed in `pigment.cabal`. Notice that the first two are built by GHCJS, while the others are built by GHC.

* `pigment` (ghcjs) - The programming environment that runs in your browser.
* `designmode` (ghcjs) - A listing of a bunch of different primitive pieces. This is used for styling and simple interaction design.
* `Pig` - This exists for historical purposes. It's used to run old [Epigram](https://en.wikipedia.org/wiki/Epigram_(programming_language)) programs using the current library.
* `Traif` - Used for writing quick test scripts. Think of it as a scratchpad.
* `PigmentPrelude` - Used to export some common definitions to the test suites. Why is it an executable? (I don't know)

It's also worth looking at the `tests` directory!

## Transpiling JavaScript

Much of the code responsible for rendering the interface lives in `src-web/js`. It's written using modern JS features so it must be transpiled into a single file. The same file is used by both `pigment` and `designmode`, but it's placed in different locations. First run `npm install` then use `node design-server.js` or `node pigment-server.js` to serve a hot-loaded version of the result. When the command is running, visit http://localhost:3000/webpack-dev-server/. The webpack dev server automatically recompiles and injects the latest version into the page each time you save so you don't have to reload. To simply build the resulting file, run `webpack` (`npm install -g webpack`) from within `src-web/js`.

# License

Pigment is [MIT licensed](http://opensource.org/licenses/MIT).


[![Bitdeli Badge](https://d2weczhvl823v0.cloudfront.net/joelburget/pigment/trend.png)](https://bitdeli.com/free "Bitdeli Badge")

