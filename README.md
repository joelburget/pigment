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

* Install [GHCJS](https://github.com/ghcjs/ghcjs) - Pigment's compiler. The easiest way to do this at the moment is through the [ghcjs-box](https://github.com/joelburget/ghcjs-box) vagrant box.
* Clone this repository - `git clone https://github.com/joelburget/pigment.git`
* `cd pigment`
* If you've made it this far you can finally run `make` to build the thing!

# Contributing

Please do! I assure you you'll have no problem finding bugs. The easiest way to contribute back is a pull request to the [official repository](https://github.com/joelburget/pigment).

# License

Pigment is [MIT licensed](http://opensource.org/licenses/MIT).


[![Bitdeli Badge](https://d2weczhvl823v0.cloudfront.net/joelburget/pigment/trend.png)](https://bitdeli.com/free "Bitdeli Badge")

