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

function toBigIntSafe(n) {
    if (typeof n === 'bigint') return n;
    if (typeof n === 'number') return BigInt(n);
    if (typeof n === 'string' && /^\d+$/.test(n)) return BigInt(n);
    throw new Error('Cannot convert to BigInt: ' + n);
}

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
            const nextVal = toBigIntSafe(rhymeIter.next().value);
            const base = BigInt(VAR_NAMES.length);
            const i = nextVal / base;
            const j = nextVal % base;
            const varName = VAR_NAMES[Number(j)];
            if (i === 0n) {
                return varName;
            }
            return varName + i.toString();
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
        if (this.rhyme.length === 0) {
            return 0n;
        }
        let maxVal = 0n;
        for (const value of this.rhyme) {
            const bigVal = toBigIntSafe(value);
            if (bigVal > maxVal) {
                maxVal = bigVal;
            }
        }
        return maxVal + 1n;
    }

    dual() {
        /* Swap all left and right operands, swap lhs and rhs if needed. */
        let lhsShape = shapeDual(this.lhsShape);
        let rhsShape = shapeDual(this.rhsShape);
        const lhsOrder = shapeOrder(this.lhsShape);
        const lhsCount = Number(lhsOrder + 1n);
        let lhsRhyme = [...this.rhyme.slice(0, lhsCount)].reverse();
        let rhsRhyme = [...this.rhyme.slice(lhsCount)].reverse();
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
                throw new Error(`Expected '◇' after '${left}' in parentheses. Did you mean to write '(${left} ◇ ...)'?`);
            }
            tokens.shift(); // Remove '◇'
            const right = parseElement();
            if (tokens.length === 0 || tokens[0] !== ")") {
                throw new Error(`Missing closing parenthesis after '(${left} ◇ ${right}'. Did you forget to close the parentheses?`);
            }
            tokens.shift(); // Remove closing parenthesis
            return [left, "◇", right];
        }
        if (/^[a-zA-Z_$][a-zA-Z0-9_$]*$/.test(tokens[0]) || tokens[0] === "0" ||
            (/^[1-9]/.test(tokens[0]) && /^[0-9]+$/.test(tokens[0]))) {
            return tokens.shift();
        }
        throw new Error(`Unexpected token: '${tokens[0]}'. Valid tokens are variables (${VAR_NAMES}), '◇', '(', or ')'.`);
    }

    let result = parseElement();
    if (tokens.length > 0) {
        if (tokens[0] !== "◇") {
            throw new Error(`Unexpected token '${tokens[0]}' after main element. Did you mean to use '◇' here?`);
        }
        tokens.shift(); // Remove '◇'
        const right = parseElement();
        if (tokens.length > 0) {
            throw new Error(`Unexpected tokens at the end of expression: '${tokens.join(' ')}'. Make sure your equation is properly formatted.`)
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
    if (parts.length !== 2n) {
        throw new Error("Your equation should have exactly one '=' sign. Please check your input.");
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
        return 0n;
    }
    return 1n + shapeOrder(shape[0]) + shapeOrder(shape[1]);
}

function shapeCmp(shape1, shape2) {
    const shape1Order = shapeOrder(shape1);
    const shape2Order = shapeOrder(shape2);
    if (shape1Order < shape2Order) {
        return -1n;
    }
    if (shape1Order > shape2Order) {
        return 1n;
    }
    if (shape1 === null && shape2 === null) {
        return 0n;
    }
    const leftCmp = shapeCmp(shape1[0], shape2[0]);
    if (leftCmp !== 0n) {
        return leftCmp;
    }
    return shapeCmp(shape1[1], shape2[1]);
}

function shapeLt(shape1, shape2) {
    return shapeCmp(shape1, shape2) < 0n;
}

// Generating all rhymes, all shapes, all equations

function canonicalizeRhyme(rhyme) {
    /**Canonicalize the rhyme to increasing order.*/
    const variables = new Map();
    for (const x of rhyme) {
        if (!variables.has(x)) {
            variables.set(x, BigInt(variables.size));
        }
    }
    return rhyme.map(x => variables.get(x));
}

function* allRhymes(n) {
    /**Generate all rhymes of a given length.*/
    if (n === 0n) {
        yield [];
        return;
    }
    for (const next of _allRhymesHelp(n, 0n)) {
        yield [0n, ...next];
    }
}

function* _allRhymesHelp(n, maxUsed) {
    /**Generates all rhymes whose minimum is at most maxUsed + 1n*/
    if (n === 0n) {
        yield [];
        return;
    }
    for (let x = 0n; x < maxUsed + 2n; x++) {
        const nextMax = maxUsed > x ? maxUsed : x;
        for (const next of _allRhymesHelp(n - 1n, nextMax)) {
            yield [x, ...next];
        }
    }
}

function* allShapes(order) {
    /**Generate all possible shapes for expressions with a given number of operations.*/
    if (order === 0n) {
        yield null;
    }
    for (let i = 0n; i < order; i++) {
        for (const left of allShapes(i)) {
            for (const right of allShapes(order - 1n - i)) {
                yield [left, right];
            }
        }
    }
}

function* allEqs(order) {
    /* Generate all unique equations of some order up to symmetry.

    To generate unique equations of all orders, use
    (function*() { for (let n = 0n; ; n++) { yield* allEqs(n); } })().
    */
        const half = order / 2n + 1n;
    for (let lhsOrder = 0n; lhsOrder < half; lhsOrder++) {
        for (const lhsShape of allShapes(lhsOrder)) {
            for (const rhsShape of allShapes(order - lhsOrder)) {
                if (order === lhsOrder * 2n && shapeLt(rhsShape, lhsShape)) {
                    continue;
                }
                const symmetricShape = JSON.stringify(lhsShape) === JSON.stringify(rhsShape);
                for (const rhyme of allRhymes(order + 1n)) {
                    if (symmetricShape) {
                            const halfIndex = Number(half);
                            const flipped = [...rhyme.slice(halfIndex), ...rhyme.slice(0, halfIndex)];
                        if (arrayLt(canonicalizeRhyme(flipped), rhyme)) {
                            continue;
                        }
                        if (arrayEqual(rhyme, flipped) && order > 0n) {
                            continue;
                        }
                    }
                    yield new Equation(lhsShape, rhsShape, rhyme);
                }
            }
        }
    }
}

// Recursive approach to mapping from equation number to id and vice-versa

// Counting equations of some order, based on https://oeis.org/A103293, refactored to access intermediate results.

const memoCache = new Map();

function numEqs(n) {
    /**Sequence https://oeis.org/A376640 of the number of magma equations (BigInt-safe)*/
    const key = `numEqs:${n.toString()}`;
    if (memoCache.has(key)) {
        return memoCache.get(key);
    }

    let result;
    if (n % 2n === 1n) {
        // Odd n
        result = (catalan(n + 1n) * bell(n + 2n)) / 2n;
    } else {
        if (n === 0n) {
            result = 2n;
        } else {
            result = ((catalan(n + 1n) - catalan(n / 2n)) * bell(n + 2n)) / 2n +
                     catalan(n / 2n) * bellSameShape(n);
        }
    }

    memoCache.set(key, result);
    return result;
}

function bellSameShape(n) {
    /**Number of rhymes when lhs and rhs have the same (n//2)-operations shape (BigInt-safe)*/
    const key = `bellSameShape:${n.toString()}`;
    if (memoCache.has(key)) {
        return memoCache.get(key);
    }

    let result;
    if (n === 0n) {
        result = 2n;
    } else {
        let sum = 0n;
        for (let k = 0n; k < n + 3n; k++) {
            sum += stirlingSym(n + 2n, k);
        }

        // Use BigInt integer division directly (flooring is implicit)
        const halfN = n / 2n;
        result = (bell(n + 2n) + sum - 2n * bell(1n + halfN)) / 2n;
    }

    memoCache.set(key, result);
    return result;
}


function stirlingSym(n, k) {
    /**Number of symmetric k-partitions of range(n), see https://oeis.org/A103293*/
    if (memoCache.has(`stirlingSym:${n}:${k}`)) {
        return memoCache.get(`stirlingSym:${n}:${k}`);
    }
    let result;
    if (n < 2n) {
        result = k === n ? 1n : 0n;
    } else {
        result = k * stirlingSym(n - 2n, k) + stirlingSym(n - 2n, k - 1n) + stirlingSym(n - 2n, k - 2n);
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
    if (n === 0n) {
        return 0n;
    }
    const [lhsShape, rhsShape] = shape;
    const lhsN = shapeOrder(lhsShape);
    const rhsN = n - 1n - lhsN;
    let sum = 0n;
    for (let n1 = 0n; n1 < lhsN; n1++) {
        sum += catalan(n1) * catalan(n - n1 - 1n);
    }
    return sum + _shapeIdHelp(lhsShape, lhsN) * catalan(rhsN) + _shapeIdHelp(rhsShape, rhsN);
}

function shapeFromId(nodes, treeNum) {
    if (nodes === 0n) {
        if (treeNum !== 0n) {
            throw new Error("Invalid tree number for nodes = 0n");
        }
        return null;
    }
    for (let n1 = 0n; n1 < nodes; n1++) {
        const testNum = catalan(n1) * catalan(nodes - n1 - 1n);
        if (treeNum >= testNum) {
            treeNum -= testNum;
            continue;
        }
        const denom = catalan(nodes - n1 - 1n);
        const treeNum1 = treeNum / denom;
        const treeNum2 = treeNum % denom;
        return [shapeFromId(n1, treeNum1), shapeFromId(nodes - n1 - 1n, treeNum2)];
    }
}

// Map from rhyme to id and back

function _numRhymeHelp(n, maxUsed) {
    /**Number of rhymes of n slots whose minimum number is at most maxUsed + 1n*/
    if (memoCache.has(`_numRhymeHelp:${n}:${maxUsed}`)) {
        return memoCache.get(`_numRhymeHelp:${n}:${maxUsed}`);
    }
    let result;
    if (n === 0n) {
        result = 1n;
    } else {
        result = (maxUsed + 1n) * _numRhymeHelp(n - 1n, maxUsed) + _numRhymeHelp(n - 1n, maxUsed + 1n);
    }
    memoCache.set(`_numRhymeHelp:${n}:${maxUsed}`, result);
    return result;
}

function findRhymeId(p) {
    /**Gives the rhyme id (zero-based) among rhymes with a given number of variables*/
    if (p.length === 0 || toBigIntSafe(p[0]) !== 0n) {
        throw new Error(`Argument of findRhymeId should be [0n,...] not ${p}`);
    }
    return _findRhymeIdHelp(p.slice(1), 0n);
}

function _findRhymeIdHelp(p, maxUsed) {
    if (p.length === 0) {
        return 0n;
    }
    const first = toBigIntSafe(p[0]);
    const remaining = BigInt(p.length - 1);
    const nextMax = first > maxUsed ? first : maxUsed;
    return first * _numRhymeHelp(remaining, maxUsed) +
           _findRhymeIdHelp(p.slice(1), nextMax);
}

function getRhymeById(n, rhymeNum, maxUsed = 0n) {
    /**Find a rhyme scheme for n slots by its number (zero-indexed).*/
    let result = [0n];
    let slots = n;
    let currentMax = maxUsed;
    let remainder = rhymeNum;
    while (slots > 0n) {
        const helper = _numRhymeHelp(slots - 1n, currentMax);
        let nextVar = remainder / helper;
        const upperBound = currentMax + 1n;
        if (nextVar > upperBound) {
            nextVar = upperBound;
        }
        result.push(nextVar);
        remainder -= nextVar * helper;
        currentMax = currentMax > nextVar ? currentMax : nextVar;
        slots -= 1n;
    }
    return result;
}

// Map from equation to id and back.

function _numEqsUnbalanced(n) {
    /**Counts magma equations that have strictly fewer operations on the left than on the right (BigInt-safe)*/
    const key = `_numEqsUnbalanced:${n.toString()}`;
    if (memoCache.has(key)) {
        return memoCache.get(key);
    }

    const halfN = n / 2n; // BigInt integer division (floored)
    const catalanTerm = n % 2n === 1n ? 0n : catalan(halfN) ** 2n;

    // Integer division on BigInts is already floored
    const result = ((catalan(n + 1n) - catalanTerm) * bell(n + 2n)) / 2n;

    memoCache.set(key, result);
    return result;
}


function _numEqsBalanced(n, l, r) {
    /**Number of balanced equations before lhs/rhs shapes number l, r*/
    const halfN = n / 2n;
    const adjustment = r - l - (r > l ? 1n : 0n);
    const linearTerm = bell(n + 2n) * (catalan(halfN) * l - (l * (l + 1n) / 2n) + adjustment);
    const symmetryTerm = bellSameShape(n) * (l + (r > l ? 1n : 0n));
    return linearTerm + symmetryTerm;
}

function _equationId(inputEq) {
    /**Equation id from a processed Equation*/
    const lhsShape = inputEq.lhsShape;
    const rhsShape = inputEq.rhsShape;
    const nLhs = shapeOrder(lhsShape);
    const nRhs = shapeOrder(rhsShape);
    const n = nLhs + nRhs;
    if (nLhs !== nRhs) {
        let sum = 1n;
        for (let i = 0n; i < n; i++) {
            sum += numEqs(i);
        }
        return sum + bell(n + 2n) * shapeId([lhsShape, rhsShape]) + findRhymeId(inputEq.rhyme);
    }
    // For nLhs === nRhs the ordering halves the equations.  For
    // different tree shapes get bell(n + 2n) rhymes, otherwise
    // bellSameShape(n).
    const m = catalan(nLhs); // number of tree shapes on each side
    const l = shapeId(lhsShape);
    const r = shapeId(rhsShape);
    let pid;
    if (l !== r) {
        pid = findRhymeId(inputEq.rhyme);
    } else {
        // Slow code here
        pid = 0n;
        for (const rhyme of allRhymes(n + 1n)) {
            if (arrayEqual(rhyme, inputEq.rhyme)) {
                break;
            }
            const sliceIndex = Number(nLhs + 1n);
            const flipped = [...rhyme.slice(sliceIndex), ...rhyme.slice(0, sliceIndex)];
            if (arrayLt(canonicalizeRhyme(flipped), rhyme)) {
                continue;
            }
            if (arrayEqual(rhyme, flipped) && n > 0n) {
                continue;
            }
            pid += 1n;
        }
    }
    let sum = 1n;
    for (let i = 0n; i < n; i++) {
        sum += numEqs(i);
    }
    return sum + _numEqsUnbalanced(n) + _numEqsBalanced(n, l, r) + pid;
}

function _equationFromId(inputEq) {
    let n = 0n;
    let eqNum = inputEq - 1n;

    // Find n such that eqNum < numEqs(n)
    while (eqNum >= numEqs(n)) {
        eqNum -= numEqs(n);
        n += 1n;
    }

    // Unbalanced case
    if (eqNum < _numEqsUnbalanced(n)) {
        const treeNum = eqNum / bell(n + 2n);
        const rhymeNum = eqNum % bell(n + 2n);
        const [lhsShape, rhsShape] = shapeFromId(n + 1n, treeNum);
        const rhyme = getRhymeById(n + 1n, rhymeNum);
        return new Equation(lhsShape, rhsShape, rhyme);
    }

    // Balanced cases
    eqNum -= _numEqsUnbalanced(n);
    const m = catalan(n / 2n);

    // --- Integer square root helper ---
    const isqrt = (x) => {
        if (x < 0n) throw new Error("BigInt square root of negative number");
        if (x < 2n) return x;
        let small = isqrt(x >> 2n) << 1n;
        let large = small + 1n;
        return (large * large > x) ? small : large;
    };

    const termA = (2n * m - 1n) * bell(n + 2n) + 2n * bellSameShape(n);
    const termB = 8n * bell(n + 2n) * eqNum + 1n;
    const sqrtPart = isqrt(termA ** 2n - termB);

    const l = ((termA - sqrtPart - 1n) / (2n * bell(n + 2n)));
    const lhsShape = shapeFromId(n / 2n, l);

    eqNum -= _numEqsBalanced(n, l, l);

    if (eqNum < bellSameShape(n)) {
        const rhsShape = lhsShape;
        // Slow code here
        for (const rhyme of allRhymes(n + 1n)) {
            const half = Number(n / 2n) + 1;
            const flipped = [
                ...rhyme.slice(half),
                ...rhyme.slice(0, half)
            ];

            if (arrayLt(canonicalizeRhyme(flipped), rhyme)) continue;
            if (arrayEqual(rhyme, flipped) && n > 0n) continue;

            if (eqNum === 0n) {
                return new Equation(lhsShape, rhsShape, rhyme);
            }
            eqNum -= 1n;
        }
    } else {
        eqNum -= bellSameShape(n);
        const shapeDiff = eqNum / bell(n + 2n);
        const pid = eqNum % bell(n + 2n);
        const rhsShape = shapeFromId(n / 2n, l + 1n + shapeDiff);
        const rhyme = getRhymeById(n + 1n, pid);
        return new Equation(lhsShape, rhsShape, rhyme);
    }
}

// Utility functions for mathematical operations

function bell(n) {
    /**Bell number calculation (BigInt-safe)*/
    const key = `bell:${n.toString()}`;
    if (memoCache.has(key)) {
        return memoCache.get(key);
    }

    if (n === 0n) {
        memoCache.set(key, 1n);
        return 1n;
    }

    let result = 0n;
    for (let k = 0n; k <= n; k++) {
        result += stirling2(n, k);
    }

    memoCache.set(key, result);
    return result;
}


function stirling2(n, k) {
    /**Stirling numbers of the second kind (BigInt-safe)*/
    if (memoCache.has(`stirling2:${n.toString()}:${k.toString()}`)) {
        return memoCache.get(`stirling2:${n.toString()}:${k.toString()}`);
    }

    if (n === 0n && k === 0n) return 1n;
    if (n === 0n || k === 0n) return 0n;
    if (k > n) return 0n;

    const result = k * stirling2(n - 1n, k) + stirling2(n - 1n, k - 1n);

    memoCache.set(`stirling2:${n.toString()}:${k.toString()}`, result);
    return result;
}


function catalan(n) {
    /**Catalan number calculation (BigInt-safe)*/
    if (memoCache.has(`catalan:${n}`)) {
        return memoCache.get(`catalan:${n}`);
    }

    if (n <= 1n) {
        memoCache.set(`catalan:${n}`, 1n);
        return 1n;
    }

    // BigInt division is already floored
    const result = binomial(2n * n, n) / (n + 1n);

    memoCache.set(`catalan:${n}`, result);
    return result;
}


function binomial(n, k) {
    /**Binomial coefficient calculation (BigInt-safe)*/
    if (k > n) return 0n;
    if (k === 0n || k === n) return 1n;

    // Replace Math.min(k, n - k)
    if (k > n - k) {
        k = n - k;
    }

    let result = 1n;
    for (let i = 0n; i < k; i++) {
        // Integer division of BigInts is already floor division
        result = result * (n - i) / (i + 1n);
    }

    return result;
}


// Utility functions for array operations

function arrayEqual(arr1, arr2) {
    return arr1.length === arr2.length && arr1.every((val, i) => val === arr2[i]);
}

function arrayLt(arr1, arr2) {
    const limit = Math.min(arr1.length, arr2.length);
    for (let i = 0; i < limit; i++) {
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
        inputEq = toBigIntSafe(eqStr);
    } catch (e) {
        inputEq = null;
    }
    if (typeof inputEq === 'bigint' || Number.isInteger(inputEq)) {
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
// Commented out to prevent console errors in the browser.
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
    const rawInput = document.getElementById('equationInput').value.trim();
    const resultDiv = document.getElementById('result');

    try {
        if (rawInput.length === 0) {
            showErrorPopup('Please enter an equation number or expression.');
            resultDiv.innerHTML = '';
            return false;
        }

        let eqNum;
        if (/^\d+$/.test(rawInput)) {
            eqNum = toBigIntSafe(rawInput);
        } else {
            const parsed = Equation.fromStr(rawInput);
            eqNum = toBigIntSafe(parsed.id);
        }

        if (eqNum <= 0n) {
            showErrorPopup(`Equation indices start at 1. Received ${eqNum.toString()}.`);
            resultDiv.innerHTML = '';
            return false;
        }

        const zeroBasedIdx = eqNum - 1n;
        renderImplications(zeroBasedIdx);
        showPage('detailPage');
    } catch (error) {
        let message = `${error.name}: ${error.message}`;
        if (error.stack) {
            message += "\n\n" + error.stack;
        }
        console.error(message);
        showErrorPopup(message);
        resultDiv.innerHTML = '';
    }
    return false;
}
