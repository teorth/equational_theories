import { checkLaw, choicesForCell, commutativePuzzle, compileLaw } from "./model.mjs";

const byId = id => document.getElementById(id);
const defaults = [3, 43, 4512];
let database, laws, table = commutativePuzzle(3), selectedCell = null;
const history = [];

function node(tag, text) {
  const element = document.createElement(tag);
  if (text !== undefined) element.textContent = text;
  return element;
}

function remember() {
  history.push({ table: table.map(row => [...row]), ids: laws.map(law => law.id) });
  if (history.length > 50) history.shift();
}

function useLaws(ids) {
  laws = ids.map(id => compileLaw(database[id - 1], id));
  byId("law-numbers").value = ids.join(", ");
  byId("law-error").textContent = "";
}

function clearHighlights() {
  byId("products").querySelectorAll(".witness").forEach(cell => cell.classList.remove("witness"));
}

function refresh() {
  clearHighlights();
  byId("choice-results").replaceChildren();
  byId("undo").disabled = history.length === 0;
  byId("choices").disabled = !selectedCell || table[selectedCell[0]][selectedCell[1]] !== null;
  const results = byId("law-results");
  results.replaceChildren();
  let allTrue = true;
  for (const law of laws) {
    const result = checkLaw(table, law);
    allTrue &&= result.status === "true";
    const item = node("li");
    const link = node("a", `Equation ${law.id}: ${law.equation}`);
    link.href = `../implications/?${law.id}`;
    const status = node("span", result.status[0].toUpperCase() + result.status.slice(1));
    status.className = `law-status ${result.status}`;
    item.append(link, status);
    if (result.witness) {
      const witness = result.witness;
      const details = node("details");
      const assignments = Object.entries(witness.assignment).map(([key, value]) => `${key} = ${value}`).join(", ");
      details.append(node("summary", "Show counterexample"),
        node("p", `${assignments}. Left side = ${witness.left}; right side = ${witness.right}.`));
      if (witness.cells.length) {
        const highlight = node("button", "Highlight the products used");
        highlight.type = "button";
        highlight.addEventListener("click", () => {
          clearHighlights();
          for (const [row, column] of witness.cells) {
            byId("products").querySelector(`[data-row="${row}"][data-column="${column}"]`)
              .parentElement.classList.add("witness");
          }
        });
        details.append(highlight);
      }
      item.append(details);
    }
    results.append(item);
  }
  const filled = table.flat().filter(value => value !== null).length;
  byId("progress").textContent = allTrue ? "Complete: all selected laws hold for this table." :
    `${filled} of ${table.length ** 2} products filled.`;
}

function renderTable() {
  selectedCell = null;
  const grid = byId("products");
  grid.querySelectorAll("thead, tbody").forEach(child => child.remove());
  const heading = node("tr");
  heading.append(node("th", "◇"));
  for (let column = 0; column < table.length; column += 1) {
    const label = node("th", String(column));
    label.scope = "col";
    heading.append(label);
  }
  const head = node("thead");
  head.append(heading);
  const body = node("tbody");
  table.forEach((values, row) => {
    const tr = node("tr"), label = node("th", String(row));
    label.scope = "row";
    tr.append(label);
    values.forEach((value, column) => {
      const cell = node("td"), select = node("select");
      select.setAttribute("aria-label", `${row} ◇ ${column}`);
      select.dataset.row = row;
      select.dataset.column = column;
      const unknown = node("option", "?");
      unknown.value = "";
      select.append(unknown);
      for (let i = 0; i < table.length; i += 1) select.append(new Option(String(i), String(i)));
      select.value = value === null ? "" : String(value);
      select.addEventListener("focus", () => {
        selectedCell = [row, column];
        byId("choices").disabled = table[row][column] !== null;
        byId("choice-results").replaceChildren();
      });
      select.addEventListener("change", () => {
        remember();
        table[row][column] = select.value === "" ? null : Number(select.value);
        refresh();
      });
      cell.append(select);
      tr.append(cell);
    });
    body.append(tr);
  });
  grid.append(head, body);
  byId("order").value = String(table.length);
  refresh();
}

byId("laws-form").addEventListener("submit", event => {
  event.preventDefault();
  const words = byId("law-numbers").value.trim().split(/[\s,]+/);
  if (words.some(word => !/^\d+$/.test(word))) {
    byId("law-error").textContent = "Enter equation numbers separated by commas.";
    return;
  }
  const ids = [...new Set(words.map(Number))];
  if (ids.length > 8 || ids.some(id => id < 1 || id > database.length)) {
    byId("law-error").textContent = `Choose one to eight equation numbers between 1 and ${database.length}.`;
    return;
  }
  remember();
  useLaws(ids);
  refresh();
});

byId("order").addEventListener("change", () => {
  remember();
  table = Array.from({ length: Number(byId("order").value) }, () => Array(Number(byId("order").value)).fill(null));
  renderTable();
});
byId("new").addEventListener("click", () => {
  remember();
  table = commutativePuzzle(table.length);
  useLaws(defaults);
  renderTable();
});
byId("clear").addEventListener("click", () => {
  remember();
  table = table.map(row => row.map(() => null));
  renderTable();
});
byId("undo").addEventListener("click", () => {
  const previous = history.pop();
  if (!previous) return;
  table = previous.table;
  useLaws(previous.ids);
  renderTable();
});
byId("choices").addEventListener("click", () => {
  if (!selectedCell) return;
  const [row, column] = selectedCell;
  const choices = choicesForCell(table, row, column, laws);
  const target = byId("choice-results");
  target.replaceChildren(node("p", choices.length ? `Values not currently ruled out for ${row} ◇ ${column}:` :
    "Every value conflicts with a selected law. Undo an earlier choice."));
  for (const value of choices) {
    const choice = node("button", String(value));
    choice.type = "button";
    choice.setAttribute("aria-label", `Set ${row} ◇ ${column} to ${value}`);
    choice.addEventListener("click", () => {
      remember();
      table[row][column] = value;
      renderTable();
      byId("products").querySelector(`[data-row="${row}"][data-column="${column}"]`).focus();
    });
    target.append(choice);
  }
});

try {
  const response = await fetch("../fme/eqdb.json");
  if (!response.ok) throw new Error(`HTTP ${response.status}`);
  database = await response.json();
  useLaws(defaults);
  renderTable();
  byId("loading").hidden = true;
  byId("puzzle").hidden = false;
} catch (error) {
  byId("loading").textContent = `The equations could not be loaded. Reload to try again. ${error.message}`;
}
