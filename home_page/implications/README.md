# Equation properties

The Explorer's property filter accepts space-separated tags, combined with AND:

- `order:N`: the total number of magma operations on both sides.
- `width:N`: the number of distinct variables.
- `degree:N`: the largest occurrence count of a variable on either side.
- `balanced` or `unbalanced`: whether each variable occurs equally often on both sides.
- `has-commentary`: whether the written equation has its own commentary entry.

For example, `order:4 width:3 degree:3 unbalanced` includes Equation 443. Its content is the multiset union of both sides, taking the maximum multiplicity, so its content is `x:1, y:3, z:1`. Its cancellation vector (left minus right) is `y:-3, z:-1`.

The tags on an equation's detail page open the corresponding filtered list. Filters are recorded in the URL as `properties`, so a filtered view can be bookmarked or shared. Invalid tags display an error rather than silently searching something different.

Properties belong to the written equation, rather than its equivalence class. Filtering happens before equivalent forms are collapsed; with “Hide equivalent equations” enabled, the list shows one matching form per class. Existing finite-graph, solved-equation, and sporadic-equation controls still apply.

The property calculations and query parser can be tested without Lean or browser dependencies:

```sh
node --test tests/equation-properties.test.cjs
```

The catalogue check compares every core equation's operation and variable counts against `data/equations.txt`.
