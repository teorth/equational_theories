// The equation programs use the same postfix format as the Finite Magma Explorer.
export const MAX_ORDER = 5;

export function validateTable(table) {
  const size = table.length;
  if (size < 1 || size > MAX_ORDER || table.some(row => !Array.isArray(row) || row.length !== size)) {
    throw new Error(`Use a square table of order 1 to ${MAX_ORDER}.`);
  }
  if (table.some(row => row.some(value => value !== null &&
      (!Number.isInteger(value) || value < 0 || value >= size)))) {
    throw new Error("Each product must be a table element, or unknown.");
  }
  return size;
}

export function compileLaw(record, id) {
  const variables = new Set();
  for (const program of [record.lhs, record.rhs]) {
    if (!Array.isArray(program)) throw new Error("Missing equation program.");
    let depth = 0;
    for (const instruction of program) {
      if (instruction === "+") {
        if (depth < 2) throw new Error("Invalid equation program.");
        depth -= 1;
      } else if (typeof instruction === "string" && /^[a-zA-Z]+$/.test(instruction)) {
        variables.add(instruction);
        depth += 1;
      } else throw new Error("Invalid equation instruction.");
    }
    if (depth !== 1) throw new Error("Invalid equation program.");
  }
  // The database's core laws have at most six variables. Keep interactive work bounded.
  if (variables.size > 6) throw new Error("This equation has too many variables.");
  return { id, equation: record.eqn, lhs: record.lhs, rhs: record.rhs, variables: [...variables] };
}

function evaluate(program, table, assignment, cells) {
  const stack = [];
  for (const instruction of program) {
    if (instruction !== "+") {
      stack.push(assignment[instruction]);
      continue;
    }
    const right = stack.pop();
    const left = stack.pop();
    if (left === null || right === null) stack.push(null);
    else {
      cells.add(`${left},${right}`);
      stack.push(table[left][right]);
    }
  }
  return stack[0];
}

export function checkLaw(table, law) {
  const size = validateTable(table);
  const values = Array(law.variables.length).fill(0);
  const assignment = Object.create(null);
  while (true) {
    law.variables.forEach((variable, i) => { assignment[variable] = values[i]; });
    const cells = new Set();
    const left = evaluate(law.lhs, table, assignment, cells);
    const right = evaluate(law.rhs, table, assignment, cells);
    // An unknown product is not zero, and two unknown expressions are not equal values.
    if (left !== null && right !== null && left !== right) {
      return { status: "false", witness: {
        assignment: { ...assignment }, left, right,
        cells: [...cells].map(key => key.split(",").map(Number)),
      } };
    }
    let i = values.length - 1;
    while (i >= 0 && values[i] === size - 1) { values[i] = 0; i -= 1; }
    if (i < 0) break;
    values[i] += 1;
  }
  return { status: table.some(row => row.includes(null)) ? "undetermined" : "true", witness: null };
}

/** Values not yet refuted by known products; this does not promise a full completion. */
export function choicesForCell(table, row, column, laws) {
  const size = validateTable(table);
  if (!Number.isInteger(row) || !Number.isInteger(column) || row < 0 || column < 0 ||
      row >= size || column >= size || table[row][column] !== null) {
    throw new Error("Select an empty product first.");
  }
  const candidate = table.map(values => [...values]);
  const choices = [];
  for (let value = 0; value < size; value += 1) {
    candidate[row][column] = value;
    if (laws.every(law => checkLaw(candidate, law).status !== "false")) choices.push(value);
  }
  return choices;
}

export function commutativePuzzle(size) {
  if (!Number.isInteger(size) || size < 1 || size > MAX_ORDER) throw new Error("Invalid table order.");
  return Array.from({ length: size }, (_, row) =>
    Array.from({ length: size }, (_, column) => row <= column ? Math.max(row, column) : null));
}
