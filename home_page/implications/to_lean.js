const TEMPLATE = `import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev EquationEQ1 (G: Type _) [Magma G] := ∀ CODE1

abbrev EquationEQ2 (G: Type _) [Magma G] := ∀ CODE2

theorem EquationEQ1_implies_EquationEQ2 (G: Type _) [Magma G] (h: EquationEQ1 G) : EquationEQ2 G := by
  sorry

theorem EquationEQ1_not_implies_EquationEQ2 : ∃ (G: Type) (_: Magma G), EquationEQ1 G ∧ ¬ EquationEQ2 G := by
  sorry
`;

function convertEquation(input) {
  // Extract the equation part from the input string
  const equationMatch = input.match(/\[(.*?)\]/);
  if (!equationMatch) return "Invalid input format";

  const equation = equationMatch[1];

  // Split the equation into left and right sides
  const [left, right] = equation.split('=').map(s => s.trim());

  // Extract variables from the equation
  const variables = new Set(equation.match(/[a-z]/g));

  // Create the LaTeX-style output
  const latexOutput = `${Array.from(variables).join(' ')} : G, ${left} = ${right}`;

  return latexOutput;
}

function gen_proof_url(eq1, eq2) {
    let string = TEMPLATE.replace(/EQ1/g, eq1+1).replace(/EQ2/g, eq2+1);
    string = string.replace("CODE1", convertEquation(equations[eq1]))
    string = string.replace("CODE2", convertEquation(equations[eq2]))
    return "https://live.lean-lang.org/#codez=" + encode(string);
}

function encode(string) { 
    const keyStrUriSafe = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=";
    return _compress(string, 6, x => keyStrUriSafe.charAt(x))
}
    


/* The following code is the implementation of LZ String.

  https://github.com/pieroxy/lz-string/blob/master/src/_compress.ts

  MIT License

  Copyright (c) 2013 Pieroxy pieroxy@pieroxy.net

  Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

function _compress(
    uncompressed,
    bitsPerChar,
    getCharFromInt,
) {
    if (uncompressed == null) {
        return "";
    }

    let value;
    let context_dictionary = {};
    let context_dictionaryToCreate = {};
    let context_c = "";
    let context_wc = "";
    let context_w = "";
    let context_enlargeIn = 2; // Compensate for the first entry which should not count
    let context_dictSize = 3;
    let context_numBits = 2;
    let context_data = [];
    let context_data_val = 0;
    let context_data_position = 0;

    for (let ii = 0; ii < uncompressed.length; ii += 1) {
        context_c = uncompressed.charAt(ii);
        if (!Object.prototype.hasOwnProperty.call(context_dictionary, context_c)) {
            context_dictionary[context_c] = context_dictSize++;
            context_dictionaryToCreate[context_c] = true;
        }
        context_wc = context_w + context_c;
        if (Object.prototype.hasOwnProperty.call(context_dictionary, context_wc)) {
            context_w = context_wc;
        } else {
            if (Object.prototype.hasOwnProperty.call(context_dictionaryToCreate, context_w)) {
                if (context_w.charCodeAt(0) < 256) {
                    for (let i = 0; i < context_numBits; i++) {
                        context_data_val = context_data_val << 1;
                        if (context_data_position == bitsPerChar - 1) {
                            context_data_position = 0;
                            context_data.push(getCharFromInt(context_data_val));
                            context_data_val = 0;
                        } else {
                            context_data_position++;
                        }
                    }
                    value = context_w.charCodeAt(0);
                    for (let i = 0; i < 8; i++) {
                        context_data_val = (context_data_val << 1) | (value & 1);
                        if (context_data_position == bitsPerChar - 1) {
                            context_data_position = 0;
                            context_data.push(getCharFromInt(context_data_val));
                            context_data_val = 0;
                        } else {
                            context_data_position++;
                        }
                        value = value >> 1;
                    }
                } else {
                    value = 1;
                    for (let i = 0; i < context_numBits; i++) {
                        context_data_val = (context_data_val << 1) | value;
                        if (context_data_position == bitsPerChar - 1) {
                            context_data_position = 0;
                            context_data.push(getCharFromInt(context_data_val));
                            context_data_val = 0;
                        } else {
                            context_data_position++;
                        }
                        value = 0;
                    }
                    value = context_w.charCodeAt(0);
                    for (let i = 0; i < 16; i++) {
                        context_data_val = (context_data_val << 1) | (value & 1);
                        if (context_data_position == bitsPerChar - 1) {
                            context_data_position = 0;
                            context_data.push(getCharFromInt(context_data_val));
                            context_data_val = 0;
                        } else {
                            context_data_position++;
                        }
                        value = value >> 1;
                    }
                }
                context_enlargeIn--;
                if (context_enlargeIn == 0) {
                    context_enlargeIn = Math.pow(2, context_numBits);
                    context_numBits++;
                }
                delete context_dictionaryToCreate[context_w];
            } else {
                value = context_dictionary[context_w];
                for (let i = 0; i < context_numBits; i++) {
                    context_data_val = (context_data_val << 1) | (value & 1);
                    if (context_data_position == bitsPerChar - 1) {
                        context_data_position = 0;
                        context_data.push(getCharFromInt(context_data_val));
                        context_data_val = 0;
                    } else {
                        context_data_position++;
                    }
                    value = value >> 1;
                }
            }
            context_enlargeIn--;
            if (context_enlargeIn == 0) {
                context_enlargeIn = Math.pow(2, context_numBits);
                context_numBits++;
            }
            // Add wc to the dictionary.
            context_dictionary[context_wc] = context_dictSize++;
            context_w = String(context_c);
        }
    }
    // Output the code for w.
    if (context_w !== "") {
        if (Object.prototype.hasOwnProperty.call(context_dictionaryToCreate, context_w)) {
            if (context_w.charCodeAt(0) < 256) {
                for (let i = 0; i < context_numBits; i++) {
                    context_data_val = context_data_val << 1;
                    if (context_data_position == bitsPerChar - 1) {
                        context_data_position = 0;
                        context_data.push(getCharFromInt(context_data_val));
                        context_data_val = 0;
                    } else {
                        context_data_position++;
                    }
                }
                value = context_w.charCodeAt(0);
                for (let i = 0; i < 8; i++) {
                    context_data_val = (context_data_val << 1) | (value & 1);
                    if (context_data_position == bitsPerChar - 1) {
                        context_data_position = 0;
                        context_data.push(getCharFromInt(context_data_val));
                        context_data_val = 0;
                    } else {
                        context_data_position++;
                    }
                    value = value >> 1;
                }
            } else {
                value = 1;
                for (let i = 0; i < context_numBits; i++) {
                    context_data_val = (context_data_val << 1) | value;
                    if (context_data_position == bitsPerChar - 1) {
                        context_data_position = 0;
                        context_data.push(getCharFromInt(context_data_val));
                        context_data_val = 0;
                    } else {
                        context_data_position++;
                    }
                    value = 0;
                }
                value = context_w.charCodeAt(0);
                for (let i = 0; i < 16; i++) {
                    context_data_val = (context_data_val << 1) | (value & 1);
                    if (context_data_position == bitsPerChar - 1) {
                        context_data_position = 0;
                        context_data.push(getCharFromInt(context_data_val));
                        context_data_val = 0;
                    } else {
                        context_data_position++;
                    }
                    value = value >> 1;
                }
            }
            context_enlargeIn--;
            if (context_enlargeIn == 0) {
                context_enlargeIn = Math.pow(2, context_numBits);
                context_numBits++;
            }
            delete context_dictionaryToCreate[context_w];
        } else {
            value = context_dictionary[context_w];
            for (let i = 0; i < context_numBits; i++) {
                context_data_val = (context_data_val << 1) | (value & 1);
                if (context_data_position == bitsPerChar - 1) {
                    context_data_position = 0;
                    context_data.push(getCharFromInt(context_data_val));
                    context_data_val = 0;
                } else {
                    context_data_position++;
                }
                value = value >> 1;
            }
        }
        context_enlargeIn--;
        if (context_enlargeIn == 0) {
            context_enlargeIn = Math.pow(2, context_numBits);
            context_numBits++;
        }
    }
    // Mark the end of the stream
    value = 2;
    for (let i = 0; i < context_numBits; i++) {
        context_data_val = (context_data_val << 1) | (value & 1);
        if (context_data_position == bitsPerChar - 1) {
            context_data_position = 0;
            context_data.push(getCharFromInt(context_data_val));
            context_data_val = 0;
        } else {
            context_data_position++;
        }
        value = value >> 1;
    }
    // Flush the last char
    let loop = true;

    do {
        context_data_val = context_data_val << 1;
        if (context_data_position == bitsPerChar - 1) {
            context_data.push(getCharFromInt(context_data_val));
            loop = false;
        } else context_data_position++;
    } while (loop);

    return context_data.join("");
}
