import { glob } from 'glob';
import { nodeResolve } from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import replace from '@rollup/plugin-replace';
import terser from '@rollup/plugin-terser';

/** @type {(_: any) => import('rollup').RollupOptions} */
export default _cliArgs => {
    const inputs = glob.sync('dist/*.js')

    const isProduction = process.env.NODE_ENV && process.env.NODE_ENV === 'production';
    const configForInput = fname => ({
    input: fname,
    output: {
        dir: '../.lake/build/js',
        format: 'es',
        // Hax: apparently setting `global` makes some CommonJS modules work ¯\_(ツ)_/¯
        intro: 'const global = window;',
        sourcemap: isProduction ? false : 'inline',
        plugins: isProduction ? [ terser() ] : [],
        compact: isProduction
    },
    external: [
        'react',
        'react-dom',
        'react/jsx-runtime',
        '@leanprover/infoview',
    ],
    plugins: [
        nodeResolve({
            browser: true
        }),
        replace({
            'typeof window': JSON.stringify('object'),
            'process.env.NODE_ENV': JSON.stringify(process.env.NODE_ENV),
            preventAssignment: true // TODO delete when `true` becomes the default
        }),
        commonjs({
            // In some cases the common.js plugin will hoist dynamic `require` calls for Node.js
            // modules which are not ever actually called into a global `import` which we cannot
            // resolve since we are running in a browser. So block all these from being hoisted.
            // Note: one alternative, https://github.com/FredKSchott/rollup-plugin-polyfill-node
            // does not seem to work.
            ignore: [
                'process', 'events', 'stream', 'util', 'path', 'buffer', 'querystring', 'url',
                'string_decoder', 'punycode', 'http', 'https', 'os', 'assert', 'constants',
                'timers', 'console', 'vm', 'zlib', 'tty', 'domain', 'dns', 'dgram', 'child_process',
                'cluster', 'module', 'net', 'readline', 'repl', 'tls', 'fs', 'crypto', 'perf_hooks',
            ],
        })
    ],
    })

    // We need each widget module to be bundled into a standalone .js file.
    // By default, when building a number of modules,
    // Rollup will produce chunk.js files
    // containing code that is shared between the different modules,
    // so we do not get standalone files.
    // This is 'code splitting' and cannot be disabled:
    // https://github.com/rollup/rollup/issues/2756
    // The only way to avoid splitting is to return an array of configs
    // so that Rollup runs on each module separately.
    // Unfortunately, in conjunction with TS typechecking,
    // this rechecks all TS files when bundling each module,
    // resulting in a quadratic build.
    // Instead, we compile TS first with tsc,
    // and then bundle the JS outputs with Rollup.
    return inputs.map(configForInput)
}
