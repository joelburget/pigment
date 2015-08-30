var WebpackDevServer = require('webpack-dev-server');
var webpack = require('webpack');
var config = require('./dev.config');
var host = process.env.HOST || 'localhost';
var contentPort = parseInt(process.env.PORT) || 3000;
var port =  contentPort + 1;
var serverOptions = {
    contentBase: 'http://' + host + ':' + contentPort,
    quiet: true,
    noInfo: true,
    hot: true,
    inline: true,
    lazy: false,
    publicPath: config.output.publicPath,
    headers: {"Access-Control-Allow-Origin": "*"},
    stats: {colors: true}
  };
var webpackDevServer = new WebpackDevServer(webpack(config), serverOptions);

webpackDevServer.listen(port, host, function(err) {
  console.info('==> 🚧  Webpack development server listening on %s:%s', host, port);
});
