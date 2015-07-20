var webpack = require('webpack');
var WebpackDevServer = require('webpack-dev-server');
var config = require('./webpack.config');

// HACK
config.output.path = __dirname + "/../../designmode/assets/";

new WebpackDevServer(webpack(config), {
  publicPath: config.output.publicPath,
  contentBase: '../../designmode/',
  hot: true,
  historyApiFallback: true
}).listen(3000, 'localhost', function (err, result) {
  if (err) {
    console.log(err);
  }

  console.log('Listening at localhost:3000');
});
