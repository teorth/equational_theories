const assert = require('node:assert/strict');
const test = require('node:test');
const { decodeRLE } = require('../home_page/implications/graph-data.js');

test('a run larger than the JavaScript argument limit decodes completely', () => {
    const decoded = decodeRLE([8, 200000]);
    assert.equal(decoded.length, 200000);
    assert(decoded.every(value => value === 8));
});

test('adjacent runs preserve both boundaries, including empty runs', () => {
    const decoded = decodeRLE([3, 0, 1, 150000, 8, 2, 7, 150000]);
    assert.equal(decoded.length, 300002);
    assert(decoded.slice(0, 150000).every(value => value === 1));
    assert.deepEqual(decoded.slice(150000, 150002), [8, 8]);
    assert(decoded.slice(150002).every(value => value === 7));
    assert.deepEqual(decodeRLE([]), []);
});
