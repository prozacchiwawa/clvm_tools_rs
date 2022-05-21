var path = require('path');
var webpack = require('webpack');

module.exports = {
    entry: './index.js',
    output: {
        path: path.resolve(__dirname, '..'),
        filename: 'repl.js'
    },
    target: 'web',
    loader: {
        "foo": 'babel-loader'
    },
    module: {
        noParse: /browserfs\.js/
    },
    stats: {
        colors: true
    },
    plugins: [
        // Have this example work in Edge which doesn't ship `TextEncoder` or
        // `TextDecoder` at this time.
        new webpack.ProvidePlugin({
            TextDecoder: ['text-encoding', 'TextDecoder'],
            TextEncoder: ['text-encoding', 'TextEncoder']
        }),
        new webpack.ProvidePlugin({
            // Make a global `process` variable that points to the `process` package,
            // because the `util` package expects there to be a global variable named `process`.
            // Thanks to https://stackoverflow.com/a/65018686/14239942
            process: 'process/browser.js'
        })
    ],
    resolve: {
        fallback: {
                'fs': 'browserfs/dist/shims/fs.js'
	},
	alias: {
		"util": require.resolve("./util.js"),
	}
    },
    devtool: 'source-map',
};
