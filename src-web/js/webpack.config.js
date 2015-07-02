module.exports = {
  entry: "babel!./exports",
  output: {
    path: __dirname + "/../../build/",
    filename: "jsview.js",
    libraryTarget: "var",
    library: "PigmentView"
  },
  externals: {
    react: "React"
  }
};
