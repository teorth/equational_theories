/*
 * Automatically transpiled by Claude from find_equation_id.py
 */

const EQ_SIZE = 4;
const VAR_NAMES = 'xyzwuv';

function showErrorPopup(message) {
    document.getElementById('errorMessage').textContent = message;
    document.getElementById('errorOverlay').style.display = 'block';
}

function closeErrorPopup() {
    document.getElementById('errorOverlay').style.display = 'none';
}

function tokenize(expr) {
    return expr.replace(/\./g, '◇').replace(/\*/g, '◇').replace(/\(/g, ' ( ').replace(/\)/g, ' ) ').replace(/◇/g, ' ◇ ')
        .split(' ')
        .filter(token => token.trim() !== '');
}

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

function findEquation() {
    const inputEq = document.getElementById('equationInput').value;
    const resultDiv = document.getElementById('result');
    
    try {
        const eqNum = findEquationNumber(inputEq)-1;
        
        if (eqNum) {
            renderImplications(eqNum);
            showPage('detailPage');
        } else {
            resultDiv.innerHTML = `The equation '${inputEq}' (canonicalized as '${canonicalizeEquation(inputEq)}') was not found in the generated list`;
        }
    } catch (error) {
        showErrorPopup(error.message);
        resultDiv.innerHTML = '';
    }
}
