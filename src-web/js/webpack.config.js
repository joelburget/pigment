module.exports = {
  entry: "./exports",
  output: {
    path: __dirname + "/../../build/",
    filename: "jsview.js",
    libraryTarget: "var",
    library: "PigmentView"
  },

  module: {
    loaders: [
      {
        test: /\.js$/,
        exclude: /node_modules/,
        loader: 'babel-loader',
        query: {
          stage: 0
        }
      },
    ]
  },

  externals: {
    react: "React"
  }
};
