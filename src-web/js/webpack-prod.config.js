module.exports = {
  entry: './exports',

  output: {
    path: __dirname + "/../../build/assets/",
    publicPath: '/assets/',
    filename: "jsview.js",
    libraryTarget: "var",
    library: "PigmentView"
  },

  module: {
    loaders: [
      {
        test: /\.js$/,
        exclude: /node_modules/,
        loaders: ['babel-loader?stage=0'],
      },
    ]
  }
};
