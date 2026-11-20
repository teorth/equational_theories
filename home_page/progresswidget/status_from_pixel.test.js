const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const test = require('node:test');
const vm = require('node:vm');

const source = fs.readFileSync(path.join(__dirname, 'progresswidget.js'), 'utf8');
const sandbox = {};
vm.runInNewContext(source, sandbox);

test('outcome image colors are not all explicit proofs', () => {
  const { statusFromPixel } = sandbox;
  assert.equal(statusFromPixel(0, 192, 255), 'explicit_true');
  assert.equal(statusFromPixel(0, 96, 128), 'implicit_true');
  assert.equal(statusFromPixel(255, 72, 72), 'explicit_false');
  assert.equal(statusFromPixel(128, 0, 0), 'implicit_false');
  assert.equal(statusFromPixel(0, 0, 0), 'unknown');
  assert.equal(statusFromPixel(102, 255, 0), 'explicit_conjecture_true');
  assert.equal(statusFromPixel(0, 128, 0), 'implicit_conjecture_true');
  assert.equal(statusFromPixel(255, 221, 85), 'explicit_conjecture_false');
  assert.equal(statusFromPixel(170, 136, 0), 'implicit_conjecture_false');
});
