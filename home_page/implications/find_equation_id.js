/*
 * Automatically transpiled by Claude from find_equation_id.py
 */
/*
const EQ_SIZE = 4;
const VAR_NAMES = 'xyzwuv';
*/
function showErrorPopup(message) {
    document.getElementById('errorMessage').textContent = message;
    document.getElementById('errorOverlay').style.display = 'block';
}

function showDownloadPopup() {
    document.getElementById('downloadOverlay').style.display = 'block';
}

function closePopup(element_id) {
    document.getElementById(element_id).style.display = 'none';
}

//function tokenize(expr) {
    //return expr.replace(/\./g, '◇').replace(/\*/g, '◇').replace(/\(/g, ' ( ').replace(/\)/g, ' ) ').replace(/◇/g, ' ◇ ')
 //       .split(' ')
  //      .filter(token => token.trim() !== '');
//}
/*
function parseExpr(tokens) {
    function parseElement() {
        if (tokens.length === 0) {
            throw new Error("Unexpected end of expression. Did you forget to complete your equation?");
        }
        if (VAR_NAMES.includes(tokens[0])) {
            return tokens.shift();
        }
        if (tokens[0] === '(') {
            tokens.shift();
            const left = parseElement();
            if (tokens.length === 0 || tokens[0] !== '◇') {
                throw new Error(`Expected '◇' after '${left}' in parentheses. Did you mean to write '(${left} ◇ ...)'?`);
            }
            tokens.shift();
            const right = parseElement();
            if (tokens.length === 0 || tokens[0] !== ')') {
                throw new Error(`Missing closing parenthesis after '(${left} ◇ ${right}'. Did you forget to close the parentheses?`);
            }
            tokens.shift();
            return [left, '◇', right];
        }
        throw new Error(`Unexpected token: '${tokens[0]}'. Valid tokens are variables (${VAR_NAMES}), '◇', '(', or ')'.`);
    }

    let result = parseElement();
    if (tokens.length > 0) {
        if (tokens[0] !== '◇') {
            throw new Error(`Unexpected token '${tokens[0]}' after main element. Did you mean to use '◇' here?`);
        }
        tokens.shift();
        const right = parseElement();
        if (tokens.length > 0) {
            throw new Error(`Unexpected tokens at the end of expression: '${tokens.join(' ')}'. Make sure your equation is properly formatted.`);
        }
        result = [result, '◇', right];
    }
    return result;
}

function canonicalizeEquation(eqStr) {
    const parts = eqStr.split('=');
    if (parts.length !== 2) {
        throw new Error("Your equation should have exactly one '=' sign. Please check your input.");
    }

    function canonicalizeEquationHelp(eqStr) {
        const [lhs, rhs] = eqStr.split('=').map(side => side.trim());
        const lhsTokens = tokenize(lhs);
        const rhsTokens = tokenize(rhs);
        const lhsParsed = parseExpr(lhsTokens);
        const rhsParsed = parseExpr(rhsTokens);

        const varMap = {};
        let nextVarIndex = 0;

        function rewriteExpr(expr) {
            if (typeof expr === 'string') {
                if (expr === '◇') return expr;
                if (!(expr in varMap)) {
                    varMap[expr] = VAR_NAMES[nextVarIndex++];
                }
                return varMap[expr];
            }
            const [left, op, right] = expr;
            return [rewriteExpr(left), op, rewriteExpr(right)];
        }

        const canonLhs = rewriteExpr(lhsParsed);
        const canonRhs = rewriteExpr(rhsParsed);

        function exprToStr(expr) {
            if (typeof expr === 'string') return expr;
            const [left, op, right] = expr;
            return `(${exprToStr(left)} ${op} ${exprToStr(right)})`;
        }

        const lhsStr = exprToStr(canonLhs);
        const rhsStr = exprToStr(canonRhs);

        return lhsStr.length > rhsStr.length ? `${rhsStr} = ${lhsStr}` : `${lhsStr} = ${rhsStr}`;
    }

    const canonEq = canonicalizeEquationHelp(eqStr);
    const [left, right] = canonEq.split('=');
    const flippedEq = canonicalizeEquationHelp(`${right}=${left}`);

    return left.length === right.length && reorder(flippedEq) < reorder(canonEq) ? flippedEq : canonEq;
}

function reorder(expr) {
    return expr.replace(/[xyzwuv]/g, (match) => VAR_NAMES.indexOf(match));
}

function* generateShapes(size) {
    if (size === 0) {
        yield '.';
        return;
    }
    for (let i = 0; i < size; i++) {
        for (const left of generateShapes(i)) {
            for (const right of generateShapes(size - 1 - i)) {
                yield [left, right];
            }
        }
    }
}

function* exprsWithShape(shape, usedVars) {
    if (shape === '.') {
        for (let var_ = 0; var_ <= usedVars; var_++) {
            yield [var_, Math.max(var_ + 1, usedVars)];
        }
    } else {
        const [left, right] = shape;
        for (const [leftExpr, usedVars1] of exprsWithShape(left, usedVars)) {
            for (const [rightExpr, usedVars2] of exprsWithShape(right, usedVars1)) {
                yield [[leftExpr, rightExpr], usedVars2];
            }
        }
    }
}

function renameVars(expr, perm) {
    if (typeof expr === 'number') {
        return perm[expr];
    }
    const [left, right] = expr;
    return [renameVars(left, perm), renameVars(right, perm)];
}

function* eqSymmetries(lhs, rhs, nVars) {
    for (const renaming of permutations(nVars)) {
        yield [renameVars(lhs, renaming), renameVars(rhs, renaming)];
    }
    for (const renaming of permutations(nVars)) {
        yield [renameVars(rhs, renaming), renameVars(lhs, renaming)];
    }
}

function* permutations(n) {
    const range = Array.from({length: n}, (_, i) => i);
    yield* permutationsHelper(range);
}

function* permutationsHelper(arr) {
    if (arr.length <= 1) {
        yield arr;
    } else {
        for (let i = 0; i < arr.length; i++) {
            const rest = [...arr.slice(0, i), ...arr.slice(i + 1)];
            for (const perm of permutationsHelper(rest)) {
                yield [arr[i], ...perm];
            }
        }
    }
}

function* generateAllEqs() {
    const allEqs = new Set();
    for (let size = 0; size <= EQ_SIZE; size++) {
        for (let lhsSize = 0; lhsSize <= size; lhsSize++) {
            for (const lhsShape of generateShapes(lhsSize)) {
                for (const rhsShape of generateShapes(size - lhsSize)) {
                    for (const [lhs, usedVars] of exprsWithShape(lhsShape, 0)) {
                        for (const [rhs, allUsedVars] of exprsWithShape(rhsShape, usedVars)) {
                            let isUnique = true;
                            for (const symmetry of eqSymmetries(lhs, rhs, allUsedVars)) {
                                if (allEqs.has(JSON.stringify(symmetry))) {
                                    isUnique = false;
                                    break;
                                }
                            }
                            if (isUnique && (typeof lhs === 'number' || typeof rhs === 'number' || JSON.stringify(lhs) !== JSON.stringify(rhs))) {
                                allEqs.add(JSON.stringify([lhs, rhs]));
                                yield [lhs, rhs];
                            }
                        }
                    }
                }
            }
        }
    }
}

function formatExpr(expr, outermost = true) {
    if (typeof expr === 'number') {
        return VAR_NAMES[expr];
    }
    const [left, right] = expr;
    const s = `${formatExpr(left, false)} ◇ ${formatExpr(right, false)}`;
    return outermost ? s : `(${s})`;
}

function findEquationNumber(inputEq) {
    const canonicalInput = canonicalizeEquation(inputEq);
    let eqNum = 1;
    for (const [lhs, rhs] of generateAllEqs()) {
        const eqStr = `${formatExpr(lhs)} = ${formatExpr(rhs)}`;
        if (canonicalizeEquation(eqStr) === canonicalInput) {
            return eqNum;
        }
        eqNum++;
    }
    return null;
}
*/


/**
 * This code is a port of find_equation_id.py
 *
 * This module maps magma equations from/to their id
 *
 * It can be used as a script in interactive mode (with the -i switch), as
 *
 *     node find_equation_id.js -i
 *
 * or by passing arguments to it from stdin or as arguments: a (space-separated)
 * list of ids or of equations (in which the operation can be ".", "*", or "◇"),
 * optionally preceeded by "*" to dualize the equation (and characters "[,]" are
 * ignored):
 *
 *     node find_equation_id.js [12, 34] "(w*u)=t*(u*x)" 4567 "*89" "*67" "0=(1*2)*(0*1)"
 *
 * When used as a module imported in javascript code, one can use
 * - eq = Equation.fromId(integer id)
 * - eq = Equation.fromStr(string)
 * - eq.id()
 * - allEqs(integer order)
 * - eq.dual()
 *
 * The theory of magma operations and their labeling is explained in
 * https://teorth.github.io/equational_theories/blueprint/basic-theory-chapter.html
 */

const VAR_NAMES = "xyzwuvrst";

class Equation {
    /**
     * Equation(lhsShape, rhsShape, rhyme) denotes an equation
     *
     * lhsShape and rhsShape are nested pairs (arrays) of null giving how
     * the operation is nested, and rhyme an array of int (starting with 0)
     * giving the rhyme scheme (variable names, as numbers).  For instance,
     * new Equation(null, [[null, null], null], [0, 1, 0, 2]) is x=(y*x)*z.
     */
    constructor(lhsShape, rhsShape, rhyme) {
        this.lhsShape = lhsShape;
        this.rhsShape = rhsShape;
        this.rhyme = rhyme;
    }

    static fromId(eqId) {
        /**Construct an equation given its id.*/
        return _equationFromId(eqId);
    }

    get id() {
        /**Evaluate the id of the equation.*/
        return _equationId(this);
    }

    static fromStr(eqStr) {
        /*Parse and canonicalize an equation given as a string.*/
        return _equationFromStr(eqStr);
    }

    toString() {
        const rhymeIter = this.rhyme[Symbol.iterator]();
        const lhsStr = Equation._exprStr(this.lhsShape, rhymeIter, false);
        const rhsStr = Equation._exprStr(this.rhsShape, rhymeIter, false);
        return `${lhsStr} = ${rhsStr}`;
    }

    static _exprStr(shape, rhymeIter, parenthesize) {
        if (shape === null) {
            const nextVal = rhymeIter.next().value;
            const i = Math.floor(nextVal / VAR_NAMES.length);
            const j = nextVal % VAR_NAMES.length;
            if (i === 0) {
                return VAR_NAMES[j];
            }
            return VAR_NAMES[j] + i.toString();
        }
        const leftStr = this._exprStr(shape[0], rhymeIter, true);
        const rightStr = this._exprStr(shape[1], rhymeIter, true);
        if (parenthesize) {
            return `(${leftStr} ◇ ${rightStr})`;
        }
        return `${leftStr} ◇ ${rightStr}`;
    }

    orders() {
        /**Number of operations on the lhs and rhs as a tuple.*/
        return [shapeOrder(this.lhsShape), shapeOrder(this.rhsShape)];
    }

    numVars() {
        /**Number of distinct variables in the equation.*/
        return Math.max(...this.rhyme) + 1;
    }

    dual() {
        /* Swap all left and right operands, swap lhs and rhs if needed. */
        let lhsShape = shapeDual(this.lhsShape);
        let rhsShape = shapeDual(this.rhsShape);
        const lhsOrder = shapeOrder(this.lhsShape);
        let lhsRhyme = [...this.rhyme.slice(0, lhsOrder + 1)].reverse();
        let rhsRhyme = [...this.rhyme.slice(lhsOrder + 1)].reverse();
        if (shapeLt(rhsShape, lhsShape)) {
            [lhsShape, rhsShape] = [rhsShape, lhsShape];
            [lhsRhyme, rhsRhyme] = [rhsRhyme, lhsRhyme];
        }
        let rhyme = canonicalizeRhyme([...lhsRhyme, ...rhsRhyme]);
        if (JSON.stringify(lhsShape) === JSON.stringify(rhsShape)) {
            rhyme = arrayMin([rhyme, canonicalizeRhyme([...rhsRhyme, ...lhsRhyme])]);
        }
        return new Equation(lhsShape, rhsShape, rhyme);
    }
}

// Parsing an equation string

function _tokenize(expr) {
    /**Convert an expression string into a list of tokens.*/
    expr = expr
        .replace(/\./g, "◇")
        .replace(/\*/g, "◇")
        .replace(/\(/g, " ( ")
        .replace(/\)/g, " ) ")
        .replace(/◇/g, " ◇ ");
    return expr.split(/\s+/).filter(token => token);
}

function _parseExpr(tokens) {
    /*Parse a list of tokens into an expression tree.

    Return nested triplets [left, "◇", right] with variables as str or int.*/

    function parseElement() {
        if (tokens.length === 0) {
            throw new Error("Unexpected end of expression");
        }
        if (tokens[0] === "(") {
            tokens.shift(); // Remove opening parenthesis
            const left = parseElement();
            if (tokens.length === 0 || tokens[0] !== "◇") {
                throw new Error("Expected '◇' after element in parentheses");
            }
            tokens.shift(); // Remove '◇'
            const right = parseElement();
            if (tokens.length === 0 || tokens[0] !== ")") {
                throw new Error("Missing closing parenthesis");
            }
            tokens.shift(); // Remove closing parenthesis
            return [left, "◇", right];
        }
        if (/^[a-zA-Z_$][a-zA-Z0-9_$]*$/.test(tokens[0]) || tokens[0] === "0" ||
            (/^[1-9]/.test(tokens[0]) && /^[0-9]+$/.test(tokens[0]))) {
            return tokens.shift();
        }
        throw new Error(`Unexpected token: ${tokens[0]}`);
    }

    let result = parseElement();
    if (tokens.length > 0) {
        if (tokens[0] !== "◇") {
            throw new Error(`Unexpected token after main element: ${tokens[0]}`);
        }
        tokens.shift(); // Remove '◇'
        const right = parseElement();
        if (tokens.length > 0) {
            throw new Error(
                `Unexpected tokens at the end of expression: ${tokens.join(' ')}`
            );
        }
        result = [result, "◇", right];
    }
    return result;
}

function _deconstructTree(tree) {
    if (typeof tree === 'string') {
        return [null, [tree]];
    }
    const [left, _op, right] = tree;
    const [leftShape, leftRhyme] = _deconstructTree(left);
    const [rightShape, rightRhyme] = _deconstructTree(right);
    return [[leftShape, rightShape], [...leftRhyme, ...rightRhyme]];
}

function _equationFromStr(eqStr) {
    const parts = eqStr.split("=");
    if (parts.length !== 2) {
        throw new Error("No '=' or two '=' found in the equation.");
    }
    const [lhsStr, rhsStr] = parts;
    const lhs = _parseExpr(_tokenize(lhsStr));
    const rhs = _parseExpr(_tokenize(rhsStr));
    let [lhsShape, lhsRhyme] = _deconstructTree(lhs);
    let [rhsShape, rhsRhyme] = _deconstructTree(rhs);
    if (shapeLt(rhsShape, lhsShape)) {
        [lhsShape, rhsShape] = [rhsShape, lhsShape];
        [lhsRhyme, rhsRhyme] = [rhsRhyme, lhsRhyme];
    }
    let rhyme = canonicalizeRhyme([...lhsRhyme, ...rhsRhyme]);
    if (JSON.stringify(lhsShape) === JSON.stringify(rhsShape)) {
        rhyme = arrayMin([rhyme, canonicalizeRhyme([...rhsRhyme, ...lhsRhyme])]);
    }
    return new Equation(lhsShape, rhsShape, rhyme);
}

// On shapes

function shapeDual(shape) {
    if (shape === null) {
        return null;
    }
    return [shapeDual(shape[1]), shapeDual(shape[0])];
}

function shapeOrder(shape) {
    if (shape === null) {
        return 0;
    }
    return 1 + shapeOrder(shape[0]) + shapeOrder(shape[1]);
}

function shapeCmp(shape1, shape2) {
    const shape1Order = shapeOrder(shape1);
    const shape2Order = shapeOrder(shape2);
    if (shape1Order < shape2Order) {
        return -1;
    }
    if (shape1Order > shape2Order) {
        return 1;
    }
    if (shape1 === null && shape2 === null) {
        return 0;
    }
    const leftCmp = shapeCmp(shape1[0], shape2[0]);
    if (leftCmp !== 0) {
        return leftCmp;
    }
    return shapeCmp(shape1[1], shape2[1]);
}

function shapeLt(shape1, shape2) {
    return shapeCmp(shape1, shape2) < 0;
}

// Generating all rhymes, all shapes, all equations

function canonicalizeRhyme(rhyme) {
    /**Canonicalize the rhyme to increasing order.*/
    const variables = new Map();
    for (const x of rhyme) {
        if (!variables.has(x)) {
            variables.set(x, variables.size);
        }
    }
    return rhyme.map(x => variables.get(x));
}

function* allRhymes(n) {
    /**Generate all rhymes of a given length.*/
    if (n === 0) {
        yield [];
        return;
    }
    for (const next of _allRhymesHelp(n, 0)) {
        yield [0, ...next];
    }
}

function* _allRhymesHelp(n, maxUsed) {
    /**Generates all rhymes whose minimum is at most maxUsed + 1*/
    if (n === 0) {
        yield [];
        return;
    }
    for (let x = 0; x < maxUsed + 2; x++) {
        for (const next of _allRhymesHelp(n - 1, Math.max(maxUsed, x))) {
            yield [x, ...next];
        }
    }
}

function* allShapes(order) {
    /**Generate all possible shapes for expressions with a given number of operations.*/
    if (order === 0) {
        yield null;
    }
    for (let i = 0; i < order; i++) {
        for (const left of allShapes(i)) {
            for (const right of allShapes(order - 1 - i)) {
                yield [left, right];
            }
        }
    }
}

function* allEqs(order) {
    /* Generate all unique equations of some order up to symmetry.

    To generate unique equations of all orders, use
    (function*() { for (let n = 0; ; n++) { yield* allEqs(n); } })().
    */
    const half = Math.floor(order / 2) + 1;
    for (let lhsOrder = 0; lhsOrder < half; lhsOrder++) {
        for (const lhsShape of allShapes(lhsOrder)) {
            for (const rhsShape of allShapes(order - lhsOrder)) {
                if (order === lhsOrder * 2 && shapeLt(rhsShape, lhsShape)) {
                    continue;
                }
                const symmetricShape = JSON.stringify(lhsShape) === JSON.stringify(rhsShape);
                for (const rhyme of allRhymes(order + 1)) {
                    if (symmetricShape) {
                        const flipped = [...rhyme.slice(half), ...rhyme.slice(0, half)];
                        if (arrayLt(canonicalizeRhyme(flipped), rhyme)) {
                            continue;
                        }
                        if (arrayEqual(rhyme, flipped) && order > 0) {
                            continue;
                        }
                    }
                    yield new Equation(lhsShape, rhsShape, rhyme);
                }
            }
        }
    }
}

// ##### Recursive approach to mapping from equation number to id and vice-versa

// Counting equations of some order, based on https://oeis.org/A103293, refactored to access intermediate results.

const memoCache = new Map();

function numEqs(n) {
    /**Sequence https://oeis.org/A376640 of the number of magma equations*/
    if (memoCache.has(`numEqs:${n}`)) {
        return memoCache.get(`numEqs:${n}`);
    }
    let result;
    if (n % 2 === 1) {
        result = Math.floor(catalan(n + 1) * bell(n + 2) / 2);
    } else {
        if (n === 0) {
            result = 2;
        } else {
            result = Math.floor(((catalan(n + 1) - catalan(n / 2)) * bell(n + 2)) / 2) +
                     catalan(n / 2) * bellSameShape(n);
        }
    }
    memoCache.set(`numEqs:${n}`, result);
    return result;
}

function bellSameShape(n) {
    /**Number of rhymes when lhs and rhs have the same (n//2)-operations shape*/
    if (memoCache.has(`bellSameShape:${n}`)) {
        return memoCache.get(`bellSameShape:${n}`);
    }
    let result;
    if (n === 0) {
        result = 2;
    } else {
        let sum = 0;
        for (let k = 0; k < n + 3; k++) {
            sum += stirlingSym(n + 2, k);
        }
        result = Math.floor((bell(n + 2) + sum - 2 * bell(1 + Math.floor(n / 2))) / 2);
    }
    memoCache.set(`bellSameShape:${n}`, result);
    return result;
}

function stirlingSym(n, k) {
    /**Number of symmetric k-partitions of range(n), see https://oeis.org/A103293*/
    if (memoCache.has(`stirlingSym:${n}:${k}`)) {
        return memoCache.get(`stirlingSym:${n}:${k}`);
    }
    let result;
    if (n < 2) {
        result = k === n ? 1 : 0;
    } else {
        result = k * stirlingSym(n - 2, k) + stirlingSym(n - 2, k - 1) + stirlingSym(n - 2, k - 2);
    }
    memoCache.set(`stirlingSym:${n}:${k}`, result);
    return result;
}

// Map from shape to id and back

function shapeId(shape) {
    /**Gives the shape id (zero-based) among shapes of a given order*/
    return _shapeIdHelp(shape, shapeOrder(shape));
}

function _shapeIdHelp(shape, n) {
    if (n === 0) {
        return 0;
    }
    const [lhsShape, rhsShape] = shape;
    const lhsN = shapeOrder(lhsShape);
    const rhsN = n - 1 - lhsN;
    let sum = 0;
    for (let n1 = 0; n1 < lhsN; n1++) {
        sum += catalan(n1) * catalan(n - n1 - 1);
    }
    return sum + _shapeIdHelp(lhsShape, lhsN) * catalan(rhsN) + _shapeIdHelp(rhsShape, rhsN);
}

function shapeFromId(nodes, treeNum) {
    if (nodes === 0) {
        if (treeNum !== 0) {
            throw new Error("Invalid tree number for nodes = 0");
        }
        return null;
    }
    for (let n1 = 0; n1 < nodes; n1++) {
        const testNum = catalan(n1) * catalan(nodes - n1 - 1);
        if (treeNum >= testNum) {
            treeNum -= testNum;
            continue;
        }
        const treeNum1 = Math.floor(treeNum / catalan(nodes - n1 - 1));
        const treeNum2 = treeNum % catalan(nodes - n1 - 1);
        return [shapeFromId(n1, treeNum1), shapeFromId(nodes - n1 - 1, treeNum2)];
    }
}

// Map from rhyme to id and back

function _numRhymeHelp(n, maxUsed) {
    /**Number of rhymes of n slots whose minimum number is at most maxUsed + 1*/
    if (memoCache.has(`_numRhymeHelp:${n}:${maxUsed}`)) {
        return memoCache.get(`_numRhymeHelp:${n}:${maxUsed}`);
    }
    let result;
    if (n === 0) {
        result = 1;
    } else {
        result = (maxUsed + 1) * _numRhymeHelp(n - 1, maxUsed) + _numRhymeHelp(n - 1, maxUsed + 1);
    }
    memoCache.set(`_numRhymeHelp:${n}:${maxUsed}`, result);
    return result;
}

function findRhymeId(p) {
    /**Gives the rhyme id (zero-based) among rhymes with a given number of variables*/
    if (p.length === 0 || p[0] !== 0) {
        throw new Error(`Argument of findRhymeId should be [0,...] not ${p}`);
    }
    return _findRhymeIdHelp(p.slice(1), 0);
}

function _findRhymeIdHelp(p, maxUsed) {
    if (p.length === 0) {
        return 0;
    }
    return p[0] * _numRhymeHelp(p.length - 1, maxUsed) +
           _findRhymeIdHelp(p.slice(1), Math.max(p[0], maxUsed));
}

function getRhymeById(n, rhymeNum, maxUsed = 0) {
    /**Find a rhyme scheme for n slots by its number (zero-indexed).*/
    let result = [0];
    while (n > 0) {
        const var1 = Math.min(maxUsed + 1, Math.floor(rhymeNum / _numRhymeHelp(n - 1, maxUsed)));
        result.push(var1);
        rhymeNum -= var1 * _numRhymeHelp(n - 1, maxUsed);
        maxUsed = Math.max(maxUsed, var1);
        n -= 1;
    }
    return result;
}

// Map from equation to id and back.

function _numEqsUnbalanced(n) {
    /**Counts magma equations that have strictly fewer operations on the left than on the right*/
    if (memoCache.has(`_numEqsUnbalanced:${n}`)) {
        return memoCache.get(`_numEqsUnbalanced:${n}`);
    }
    const catalanTerm = n % 2 === 1 ? 0 : catalan(Math.floor(n / 2)) ** 2;
    const result = Math.floor(((catalan(n + 1) - catalanTerm) * bell(n + 2)) / 2);
    memoCache.set(`_numEqsUnbalanced:${n}`, result);
    return result;
}

function _numEqsBalanced(n, l, r) {
    /**Number of balanced equations before lhs/rhs shapes number l, r*/
    return (bell(n + 2) * (catalan(Math.floor(n / 2)) * l - Math.floor(l * (l + 1) / 2) +
                          r - l - (r > l ? 1 : 0)) +
            bellSameShape(n) * (l + (r > l ? 1 : 0)));
}

function _equationId(inputEq) {
    /**Equation id from a processed Equation*/
    const lhsShape = inputEq.lhsShape;
    const rhsShape = inputEq.rhsShape;
    const nLhs = shapeOrder(lhsShape);
    const nRhs = shapeOrder(rhsShape);
    const n = nLhs + nRhs;
    if (nLhs !== nRhs) {
        let sum = 1;
        for (let i = 0; i < n; i++) {
            sum += numEqs(i);
        }
        return sum + bell(n + 2) * shapeId([lhsShape, rhsShape]) + findRhymeId(inputEq.rhyme);
    }
    // For nLhs === nRhs the ordering halves the equations.  For
    // different tree shapes get bell(n + 2) rhymes, otherwise
    // bellSameShape(n).
    const m = catalan(nLhs); // number of tree shapes on each side
    const l = shapeId(lhsShape);
    const r = shapeId(rhsShape);
    let pid;
    if (l !== r) {
        pid = findRhymeId(inputEq.rhyme);
    } else {
        // Slow code here
        pid = 0;
        for (const rhyme of allRhymes(n + 1)) {
            if (arrayEqual(rhyme, inputEq.rhyme)) {
                break;
            }
            const flipped = [...rhyme.slice(nLhs + 1), ...rhyme.slice(0, nLhs + 1)];
            if (arrayLt(canonicalizeRhyme(flipped), rhyme)) {
                continue;
            }
            if (arrayEqual(rhyme, flipped) && n > 0) {
                continue;
            }
            pid += 1;
        }
    }
    let sum = 1;
    for (let i = 0; i < n; i++) {
        sum += numEqs(i);
    }
    return sum + _numEqsUnbalanced(n) + _numEqsBalanced(n, l, r) + pid;
}

function _equationFromId(inputEq) {
    let n = 0;
    let eqNum = inputEq - 1;
    while (eqNum >= (numEqs(n))) {
        eqNum -= numEqs(n);
        n += 1;
    }
    if (eqNum < _numEqsUnbalanced(n)) {
        const treeNum = Math.floor(eqNum / bell(n + 2));
        const rhymeNum = eqNum % bell(n + 2);
        const [lhsShape, rhsShape] = shapeFromId(n + 1, treeNum);
        const rhyme = getRhymeById(n + 1, rhymeNum);
        return new Equation(lhsShape, rhsShape, rhyme);
    }
    eqNum -= _numEqsUnbalanced(n);
    const m = catalan(Math.floor(n / 2));
    const l = Math.floor(((2*m - 1) * bell(n + 2) + 2 * bellSameShape(n) -
                Math.floor(Math.sqrt(((2 * m - 1) * bell(n + 2) + 2 * bellSameShape(n)) ** 2 -
                           8 * bell(n + 2) * eqNum - 1)) - 1) / (2*bell(n + 2)));
    const lhsShape = shapeFromId(Math.floor(n / 2), l);
    eqNum -= _numEqsBalanced(n, l, l);
    if (eqNum < bellSameShape(n)) {
        const rhsShape = lhsShape;
        // Slow code here
        for (const rhyme of allRhymes(n + 1)) {
            const flipped = [...rhyme.slice(Math.floor(n / 2) + 1), ...rhyme.slice(0, Math.floor(n / 2) + 1)];
            if (arrayLt(canonicalizeRhyme(flipped), rhyme)) {
                continue;
            }
            if (arrayEqual(rhyme, flipped) && n > 0) {
                continue;
            }
            if (eqNum === 0) {
                return new Equation(lhsShape, rhsShape, rhyme);
            }
            eqNum -= 1;
        }
    } else {
        eqNum -= bellSameShape(n);
        const shapeDiff = Math.floor(eqNum / bell(n + 2));
        const pid = eqNum % bell(n + 2);
        const rhsShape = shapeFromId(Math.floor(n / 2), l + 1 + shapeDiff);
        const rhyme = getRhymeById(n + 1, pid);
        return new Equation(lhsShape, rhsShape, rhyme);
    }
}

// Utility functions for mathematical operations

function bell(n) {
    /**Bell number calculation*/
    if (memoCache.has(`bell:${n}`)) {
        return memoCache.get(`bell:${n}`);
    }
    if (n === 0) {
        memoCache.set(`bell:${n}`, 1);
        return 1;
    }
    let result = 0;
    for (let k = 0; k <= n; k++) {
        result += stirling2(n, k);
    }
    memoCache.set(`bell:${n}`, result);
    return result;
}

function stirling2(n, k) {
    /**Stirling numbers of the second kind*/
    if (memoCache.has(`stirling2:${n}:${k}`)) {
        return memoCache.get(`stirling2:${n}:${k}`);
    }
    if (n === 0 && k === 0) return 1;
    if (n === 0 || k === 0) return 0;
    if (k > n) return 0;
    const result = k * stirling2(n - 1, k) + stirling2(n - 1, k - 1);
    memoCache.set(`stirling2:${n}:${k}`, result);
    return result;
}

function catalan(n) {
    /**Catalan number calculation*/
    if (memoCache.has(`catalan:${n}`)) {
        return memoCache.get(`catalan:${n}`);
    }
    if (n <= 1) {
        memoCache.set(`catalan:${n}`, 1);
        return 1;
    }
    const result = Math.floor(binomial(2 * n, n) / (n + 1));
    memoCache.set(`catalan:${n}`, result);
    return result;
}

function binomial(n, k) {
    /**Binomial coefficient calculation*/
    if (k > n) return 0;
    if (k === 0 || k === n) return 1;
    k = Math.min(k, n - k); // Take advantage of symmetry
    let result = 1;
    for (let i = 0; i < k; i++) {
        result = Math.floor(result * (n - i) / (i + 1));
    }
    return result;
}

// Utility functions for array operations

function arrayEqual(arr1, arr2) {
    return arr1.length === arr2.length && arr1.every((val, i) => val === arr2[i]);
}

function arrayLt(arr1, arr2) {
    for (let i = 0; i < Math.min(arr1.length, arr2.length); i++) {
        if (arr1[i] < arr2[i]) return true;
        if (arr1[i] > arr2[i]) return false;
    }
    return arr1.length < arr2.length;
}

function arrayMin(arrays) {
    return arrays.reduce((min, current) => arrayLt(current, min) ? current : min);
}

// Code used when the module is used as a script

function processEquation(eqStr) {
    // Process a given equation, printing its id and canonical form.
    eqStr = eqStr.replace(/[\[\],]/g, "").trim();
    let dual = false;
    if (eqStr.startsWith("*")) {
        dual = true;
        eqStr = eqStr.slice(1);
    }
    let inputEq;
    try {
        inputEq = Number(eqStr);
    } catch (e) {
        inputEq = null;
    }
    if (Number.isInteger(inputEq)) {
        const eq = Equation.fromId(inputEq);
        if (dual) {
            const dualEq = eq.dual();
            const eqNum = dualEq.id;
            console.log(`The dual of Equation ${inputEq} is Equation ${eqNum}: ${dualEq}`);
        } else {
            console.log(`Equation ${inputEq}: ${eq}`);
        }
    } else {
        inputEq = Equation.fromStr(eqStr);
        if (dual) {
            const dualEq = inputEq.dual();
            const dualNum = dualEq.id;
            console.log(`The dual of '${eqStr}' is Equation ${dualNum}: ${dualEq}`);
        } else {
            const eqNum = inputEq.id;
            console.log(`The equation '${eqStr}' is Equation ${eqNum}: ${inputEq}`);
        }
    }
}

function main() {
    // Main function to run the program.
    const args = process.argv.slice(2);
    let interactive = false;
    let equations = [];

    // Parse command line arguments
    for (let i = 0; i < args.length; i++) {
        if (args[i] === '--interactive' || args[i] === '-i') {
            interactive = true;
        } else {
            equations.push(args[i]);
        }
    }

    if (interactive) {
        const readline = require('readline');
        const rl = readline.createInterface({
            input: process.stdin,
            output: process.stdout
        });

        console.log("Welcome to the interactive equation canonicalizer!");
        console.log("Type 'exit' or 'quit' to end the session.");

        const askQuestion = () => {
            rl.question("Enter an equation: ", (eq) => {
                eq = eq.trim();
                if (eq.toLowerCase() === 'exit' || eq.toLowerCase() === 'quit') {
                    console.log("Goodbye!");
                    rl.close();
                    return;
                }
                try {
                    processEquation(eq);
                } catch (error) {
                    console.error(`Error: ${error.message}`);
                }
                askQuestion();
            });
        };

        askQuestion();
    } else {
        // Read from stdin if not a TTY
        if (!process.stdin.isTTY) {
            const fs = require('fs');
            const stdinInput = fs.readFileSync(0, 'utf-8');
            const stdinEquations = stdinInput.split(/\s+/).filter(eq => eq.trim());
            equations = [...stdinEquations, ...equations];
        }

        if (equations.length > 0) {
            for (const eq of equations) {
                try {
                    processEquation(eq);
                } catch (error) {
                    console.error(`Error processing '${eq}': ${error.message}`);
                }
            }
        } else {
            console.log("Usage: node find_equation_id.js [-i|--interactive] [equations...]");
            console.log("Examples:");
            console.log("  node find_equation_id.js 12 34");
            console.log("  node find_equation_id.js \"(w*u)=t*(u*x)\" 4567");
            console.log("  node find_equation_id.js -i");
            console.log("  echo \"12 34\" | node find_equation_id.js");
        }
    }
}

/*
// Export functions for module use
if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
        Equation,
        allEqs,
        processEquation,
        main
    };
}

if (require.main === module) {
    main();
}
*/


function findEquation() {
    const inputEq = document.getElementById('equationInput').value;
    const resultDiv = document.getElementById('result');
    let eqNum = 0;

    try {
        // Determine if user entered integer input or equation input
        if (!isNaN(inputEq) && (/^\d+$/.test(inputEq))){
            eqNum = Equation.fromId(parseInt(inputEq)).id;
        }
        else{
            eqNum = Equation.fromStr(inputEq).id;
        }

        if (eqNum) {
            --eqNum;
            renderImplications(eqNum);
            showPage('detailPage');
        } else {
            resultDiv.innerHTML = `The equation '${inputEq}' (canonicalized as '${canonicalizeEquation(inputEq)}') was not found in the generated list`;
        }
    } catch (error) {
        showErrorPopup(error.message);
        resultDiv.innerHTML = '';
    }
    return false;
}
