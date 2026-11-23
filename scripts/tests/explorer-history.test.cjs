const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const test = require('node:test');
const vm = require('node:vm');

const explorer = path.join(__dirname, '../../home_page/implications');
const baseUrl = 'https://teorth.github.io/equational_theories/implications/';

function createExplorer(initialQuery = '') {
    const elements = new Map();
    function element(id) {
        if (!elements.has(id)) {
            const classes = new Set();
            elements.set(id, {
                style: {}, dataset: {}, innerHTML: '', textContent: '',
                classList: {
                    add: name => classes.add(name),
                    remove: name => classes.delete(name),
                    contains: name => classes.has(name)
                },
                addEventListener() {},
                querySelector: () => element('header'),
                appendChild() {}
            });
        }
        return elements.get(id);
    }

    const entries = [baseUrl + initialQuery];
    let position = 0;
    const listeners = new Map();
    const window = {
        location: new URL(entries[0]),
        addEventListener: (name, callback) => listeners.set(name, callback)
    };
    const history = {
        pushState(_state, _title, url) {
            entries.splice(position + 1);
            entries.push(new URL(url, window.location.href).href);
            position++;
            window.location = new URL(entries[position]);
        },
        back: () => traverse(-1),
        forward: () => traverse(1)
    };
    function traverse(offset) {
        const next = position + offset;
        if (next < 0 || next >= entries.length) return;
        position = next;
        window.location = new URL(entries[position]);
        listeners.get('popstate')();
    }

    const context = vm.createContext({
        console, URLSearchParams, window, history,
        document: {
            getElementById: element,
            querySelectorAll: selector => selector === '.page'
                ? [element('listPage'), element('detailPage')] : [],
            createDocumentFragment: () => ({}),
            addEventListener() {}
        },
        // These cases use the real built-in sporadic IDs (5093 and 26302),
        // whose detail renderer returns before accessing implication data.
        equations: Array(4694), commentary: {},
        fetch: () => new Promise(() => {}),
        alert: message => assert.fail(message)
    });
    for (const filename of ['find_equation_id.js', 'script.js']) {
        vm.runInContext(fs.readFileSync(path.join(explorer, filename), 'utf8'), context, { filename });
    }

    return {
        visit(id) {
            context.renderImplications(id - 1);
            context.showPage('detailPage');
        },
        history, entries, window, element,
        position: () => position
    };
}

for (const finite of [false, true]) {
    test(`Back and Forward preserve equation history${finite ? ' (finite)' : ''}`, () => {
        const app = createExplorer(finite ? '?finite' : '');
        const suffix = finite ? '&finite' : '';
        app.visit(5093);
        app.visit(26302);
        const expectedEntries = [...app.entries];

        app.history.back();
        assert.equal(app.window.location.href, `${baseUrl}?5093${suffix}`);
        assert.match(app.element('selectedEquation').textContent, /^Equation5093\[/);
        assert.deepEqual(app.entries, expectedEntries, 'Back must not append or discard entries');
        assert.equal(app.position(), 1);

        app.history.back();
        assert.equal(app.position(), 0, 'a second Back must reach the equation list');
        assert.ok(app.element('listPage').classList.contains('active'));
        assert.deepEqual(app.entries, expectedEntries);

        app.history.forward();
        assert.match(app.element('selectedEquation').textContent, /^Equation5093\[/);
        app.history.forward();
        assert.match(app.element('selectedEquation').textContent, /^Equation26302\[/);
        assert.equal(app.position(), 2);
        assert.deepEqual(app.entries, expectedEntries);
    });
}

for (const query of ['?equation=5093', '?finite&5093', '?equation=5093&finite']) {
    test(`Back preserves the supported deep link ${query}`, () => {
        const app = createExplorer(query);
        app.visit(26302);
        const expectedEntries = [...app.entries];

        app.history.back();
        assert.equal(app.window.location.href, baseUrl + query);
        assert.match(app.element('selectedEquation').textContent, /^Equation5093\[/);
        assert.equal(app.position(), 0);
        assert.deepEqual(app.entries, expectedEntries);

        app.history.forward();
        assert.match(app.element('selectedEquation').textContent, /^Equation26302\[/);
        assert.equal(app.position(), 1);
    });
}
