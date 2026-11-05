// Expand graph runs without passing an entire run as function arguments. A
// valid matrix can contain runs longer than the browser's argument limit.
function decodeRLE(runs) {
    let length = 0;
    for (let i = 1; i < runs.length; i += 2) length += runs[i];
    const decoded = new Array(length);
    let offset = 0;
    for (let i = 0; i < runs.length; i += 2) {
        const end = offset + runs[i + 1];
        decoded.fill(runs[i], offset, end);
        offset = end;
    }
    return decoded;
}

if (typeof module !== 'undefined' && module.exports) module.exports = { decodeRLE };
