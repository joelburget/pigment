import React, {Component, PropTypes} from 'react';
import serialize from 'serialize-javascript';
const cdn = '//cdnjs.cloudflare.com/ajax/libs/';

/**
 * Wrapper component containing HTML metadata and boilerplate tags.
 * Used in server-side code only to wrap the string output of the
 * rendered route component.
 *
 * The only thing this component doesn't (and can't) include is the
 * HTML doctype declaration, which is added to the rendered output
 * by the server.js file.
 */
export default class Html extends Component {
  static propTypes = {
    webpackStats: PropTypes.object,
    component: PropTypes.object,
    store: PropTypes.object
  }

  render() {
    const {webpackStats, component, store} = this.props;
    const title = 'Pigment';
    const description = 'Programming Language, Designed';
    const image = 'https://react-redux.herokuapp.com/logo.jpg';
    return (
      <html lang="en-us">
        <head>
          <meta charSet="utf-8"/>
          <title>{title}</title>
          <meta property="og:site_name" content={title}/>
          <meta property="og:image" content={image}/>
          <meta property="og:locale" content="en_US"/>
          <meta property="og:title" content={title}/>
          <meta property="og:description" content={description}/>
          <meta name="twitter:card" content="summary"/>
          <meta property="twitter:site" content="@pigmentio"/>
          <meta property="twitter:creator" content="@pigmentio"/>
          <meta property="twitter:image" content={image}/>
          <meta property="twitter:image:width" content="200"/>
          <meta property="twitter:image:height" content="200"/>
          <meta property="twitter:title" content={title}/>
          <meta property="twitter:description" content={description}/>

          <link rel="shortcut icon" href="/favicon.ico" />
          <link rel="stylesheet" href="https://storage.googleapis.com/code.getmdl.io/1.0.2/material.indigo-pink.min.css" />
          <script src="https://storage.googleapis.com/code.getmdl.io/1.0.2/material.min.js"></script>
          <link rel="stylesheet" href="https://fonts.googleapis.com/icon?family=Material+Icons" />
          {webpackStats.css.files.map((css, i) =>
            <link href={css} key={i} media="screen, projection"
                  rel="stylesheet" type="text/css"/>)}
        </head>
        <body>
          <div id="content" dangerouslySetInnerHTML={{__html: React.renderToString(component)}}/>
          <script dangerouslySetInnerHTML={{__html: `window.__data=${serialize(store.getState())};`}} />
          <script src={webpackStats.script[0]}/>
        </body>
      </html>
    );
  }
}
