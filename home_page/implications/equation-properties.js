// Properties of the displayed equation, independent of its implication class.
const EquationProperties = (() => {
    function describe(equation) {
        const [left, right] = equation.toString().split(' = ').map(side => {
            const counts = new Map();
            for (const name of side.match(/[a-z][0-9]*/g) || []) {
                counts.set(name, (counts.get(name) || 0) + 1);
            }
            return counts;
        });
        const variables = [...new Set([...left.keys(), ...right.keys()])];
        // Multiset union takes the maximum multiplicity on the two sides.
        const content = variables.map(name => [name, Math.max(left.get(name) || 0, right.get(name) || 0)]);
        const cancellation = variables.map(name => [name, (left.get(name) || 0) - (right.get(name) || 0)])
            .filter(([, count]) => count !== 0);
        const orders = equation.orders();
        return {
            order: Number(orders[0] + orders[1]),
            width: variables.length,
            degree: Math.max(...content.map(([, count]) => count)),
            content,
            cancellation,
            balanced: cancellation.length === 0
        };
    }

    function compileFilter(query) {
        const tests = query.trim().toLowerCase().split(/\s+/).filter(Boolean).map(tag => {
            if (tag === 'balanced' || tag === 'unbalanced') {
                return properties => properties.balanced === (tag === 'balanced');
            }
            if (tag === 'has-commentary') return (properties, hasCommentary) => hasCommentary;
            const match = /^(order|width|degree):(\d+)$/.exec(tag);
            if (!match || !Number.isSafeInteger(Number(match[2]))) {
                throw new Error(`Unknown tag “${tag}”. Use order:N, width:N, degree:N, balanced, unbalanced or has-commentary.`);
            }
            return properties => properties[match[1]] === Number(match[2]);
        });
        return (properties, hasCommentary) => tests.every(test => test(properties, hasCommentary));
    }

    function tags(properties, hasCommentary) {
        return [`order:${properties.order}`, `width:${properties.width}`, `degree:${properties.degree}`,
            properties.balanced ? 'balanced' : 'unbalanced', ...(hasCommentary ? ['has-commentary'] : [])];
    }

    return { describe, compileFilter, tags };
})();

if (typeof module !== 'undefined' && module.exports) module.exports = EquationProperties;
