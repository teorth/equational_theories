import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { checkLaw, choicesForCell, commutativePuzzle, compileLaw, validateTable }
  from "../../home_page/puzzle/model.mjs";

const database = JSON.parse(readFileSync(new URL("../../tools/fme/src/eqdb.json", import.meta.url)));
const law = id => compileLaw(database[id - 1], id);
const idempotent = law(3), commutative = law(43), associative = law(4512);

function tables(alphabet) {
  return Array.from({ length: alphabet.length ** 4 }, (_, number) => {
    const cells = Array.from({ length: 4 }, () => {
      const value = alphabet[number % alphabet.length];
      number = Math.floor(number / alphabet.length);
      return value;
    });
    return [cells.slice(0, 2), cells.slice(2)];
  });
}

const completeTables = tables([0, 1]);
const direct = (table, id) => {
  for (const x of [0, 1]) for (const y of [0, 1]) for (const z of [0, 1]) {
    if (id === 3 && table[x][x] !== x) return false;
    if (id === 43 && table[x][y] !== table[y][x]) return false;
    if (id === 4512 && table[x][table[y][z]] !== table[table[x][y]][z]) return false;
  }
  return true;
};
const extendsTable = (complete, partial) => partial.every((row, r) =>
  row.every((value, c) => value === null || value === complete[r][c]));

test("all core database equations compile without changing their identifiers", () => {
  database.forEach((record, i) => assert.equal(compileLaw(record, i + 1).id, i + 1));
});

test("every order-two magma agrees with independent direct equation checks", () => {
  for (const table of completeTables) for (const selected of [idempotent, commutative, associative]) {
    assert.equal(checkLaw(table, selected).status, direct(table, selected.id) ? "true" : "false");
  }
});

test("a partial table is never reported true, including a tautology", () => {
  for (const selected of [law(1), idempotent, commutative, associative]) {
    assert.equal(checkLaw([[null, null], [null, null]], selected).status, "undetermined");
  }
});

test("a known partial counterexample includes reproducible values and product cells", () => {
  const table = [[0, 0], [1, null]];
  const result = checkLaw(table, commutative);
  assert.equal(result.status, "false");
  const { assignment: { x, y }, left, right, cells } = result.witness;
  assert.equal(table[x][y], left);
  assert.equal(table[y][x], right);
  assert.notEqual(left, right);
  assert.deepEqual(cells, [[x, y], [y, x]]);
});

test("partial refutations survive every completion, exhaustively at order two", () => {
  for (const partial of tables([null, 0, 1])) {
    for (const selected of [idempotent, commutative, associative]) {
      if (checkLaw(partial, selected).status === "false") {
        for (const complete of completeTables.filter(table => extendsTable(table, partial))) {
          assert.equal(direct(complete, selected.id), false);
        }
      }
    }
  }
});

test("choices never eliminate a valid completion, exhaustively at order two", () => {
  const selected = [idempotent, commutative, associative];
  for (const partial of tables([null, 0, 1])) {
    const completions = completeTables.filter(table => extendsTable(table, partial) &&
      selected.every(equation => direct(table, equation.id)));
    for (let r = 0; r < 2; r += 1) for (let c = 0; c < 2; c += 1) {
      if (partial[r][c] === null) {
        const choices = choicesForCell(partial, r, c, selected);
        for (const complete of completions) assert.ok(choices.includes(complete[r][c]));
      }
    }
  }
});

test("the starter puzzle has a forced reflected product and a valid completed table", () => {
  const table = commutativePuzzle(3);
  assert.deepEqual(choicesForCell(table, 1, 0, [commutative]), [1]);
  for (let row = 0; row < 3; row += 1) for (let column = 0; column < row; column += 1) {
    table[row][column] = table[column][row];
  }
  for (const selected of [idempotent, commutative, associative]) {
    assert.equal(checkLaw(table, selected).status, "true");
  }
});

test("malformed tables and postfix programs are refused", () => {
  for (const table of [[], [[2]], [[NaN]], [[undefined]], [[0, 1]], Array(6).fill(Array(6).fill(0))]) {
    assert.throws(() => validateTable(table));
  }
  for (const lhs of [[], ["+"], ["x", "y"], ["x", "!"]]) {
    assert.throws(() => compileLaw({ lhs, rhs: ["x"] }, 1));
  }
  assert.throws(() => choicesForCell([[0]], 0, 0, [commutative]));
});
