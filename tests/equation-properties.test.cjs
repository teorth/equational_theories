const assert = require('node:assert/strict');
const test = require('node:test');
const { readFileSync } = require('node:fs');
const { join } = require('node:path');
const { Equation } = require('../home_page/implications/find_equation_id.js');
const { describe, compileFilter } = require('../home_page/implications/equation-properties.js');

test('Equation 443 uses multiset union, not the sum of both sides', () => {
    assert.deepEqual(describe(Equation.fromId(443)), {
        order: 4, width: 3, degree: 3,
        content: [['x', 1], ['y', 3], ['z', 1]],
        cancellation: [['y', -3], ['z', -1]], balanced: false
    });
});

test('balanced laws retain their variable multiplicities', () => {
    const commutative = describe(Equation.fromId(43));
    assert.equal(commutative.balanced, true);
    assert.equal(commutative.degree, 1);
    assert.equal(describe(Equation.fromId(4512)).order, 4);
    assert.deepEqual(describe(Equation.fromId(3)).cancellation, [['x', -1]]);
});

test('tags combine with AND, including commentary and case-insensitive input', () => {
    const p = describe(Equation.fromId(443));
    assert.equal(compileFilter(' ORDER:4 width:3 degree:3 UNBALANCED ')(p, false), true);
    assert.equal(compileFilter('order:4 balanced')(p, false), false);
    assert.equal(compileFilter('has-commentary')(p, false), false);
    assert.equal(compileFilter('has-commentary')(p, true), true);
    assert.equal(compileFilter('')(p, false), true);
    for (const query of ['width:-1', 'oder:4', 'order:4oops', 'degree:9007199254740992']) {
        assert.throws(() => compileFilter(query), /Unknown tag/);
    }
});

test('all core equations agree with the independent plain-text catalogue', () => {
    const catalogue = readFileSync(join(__dirname, '../data/equations.txt'), 'utf8').trim().split('\n');
    for (let i = 0; i < catalogue.length; i++) {
        const p = describe(Equation.fromId(i + 1));
        assert.equal(p.order, (catalogue[i].match(/◇/g) || []).length, `order of Equation${i + 1}`);
        assert.equal(p.width, new Set(catalogue[i].match(/[a-z][0-9]*/g)).size, `width of Equation${i + 1}`);
    }
});
