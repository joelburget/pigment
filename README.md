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


## Technologies

This iteration of Pigment was born from a starter kit -- [React Redux Universal Hot Example](https://github.com/erikras/react-redux-universal-hot-example). From which it inherited the following technologies:

* ~~Isomorphic~~ [Universal](https://medium.com/@mjackson/universal-javascript-4761051b7ae9) rendering
* Both client and server make calls to load data from separate API server
* [React](https://github.com/facebook/react)
* [React Router](https://github.com/rackt/react-router)
* [Express](http://expressjs.com)
* [Babel](http://babeljs.io) for ES6 and ES7 magic
* [Webpack](http://webpack.github.io) for bundling
* [Webpack Dev Server](http://webpack.github.io/docs/webpack-dev-server.html)
* [React Hot Loader](https://github.com/gaearon/react-hot-loader)
* [Redux](https://github.com/gaearon/redux)'s futuristic [Flux](https://facebook.github.io/react/blog/2014/05/06/flux.html) implementation
* [Redux Dev Tools](https://github.com/gaearon/redux-devtools) for next generation DX (developer experience). Watch [Dan Abramov's talk](https://www.youtube.com/watch?v=xsSnOQynTHs).
* [redux-form](https://github.com/erikras/redux-form) to manage form state in Redux
* [lru-memoize](https://github.com/erikras/lru-memoize) to speed up form validation
* [style-loader](https://github.com/webpack/style-loader) and [sass-loader](https://github.com/jtangelder/sass-loader) to allow import of stylesheets
* [react-document-meta](https://github.com/kodyl/react-document-meta) to manage title and meta tag information on both server and client
* [webpack-isomorphic-tools](https://github.com/halt-hammerzeit/webpack-isomorphic-tools) to allow require() work for statics both on client and server
* [mocha](https://mochajs.org/) to allow writing unit tests for the project.


## Installation

```
npm install
```

## Running Dev Server

```
npm run dev
```

## Building and Running Production Server

```
npm run build
npm run start
```

## License

Pigment is [MIT licensed](http://opensource.org/licenses/MIT).


[![Bitdeli Badge](https://d2weczhvl823v0.cloudfront.net/joelburget/pigment/trend.png)](https://bitdeli.com/free "Bitdeli Badge")
