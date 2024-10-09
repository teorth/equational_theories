// HELPER CLASSES //

function isOperator(op) {
  return ['+'].includes(op);
}

function isOperand(op) {
  return /^[a-zA-Z]+$/.test(op);
}

class Program {
  constructor(instructions) {
    this.instructions = instructions;
  }

  run(operandMatrix, variableAssignments) {
    let stack = [];
    for (let instruction of this.instructions) {
      if (isOperator(instruction)) {
        if (stack.length < 2) {
          throw new Error(`Insufficient operands for operator: ${instruction}`);
        }
        const v1 = stack.pop();
        const v2 = stack.pop();
        const result = operandMatrix[v2][v1];
        stack.push(result);
      } else if (isOperand(instruction)) {
        if (!(instruction in variableAssignments)) {
          throw new Error(`Undefined variable: ${instruction}`);
        }
        stack.push(variableAssignments[instruction]);
      } else {
        throw new Error(`Unknown instruction: ${instruction}`);
      }
    }
    return stack.length === 1 ? stack[0] : 0;
  }
}

class Relation {
  constructor(numInt, eqnString, lhsProgram, rhsProgram) {
    this.num = numInt;
    this.eqn = eqnString;
    this.lhs = lhsProgram;
    this.rhs = rhsProgram;
  }

  check(operandMatrix) {
    const variables = this.getVariables();
    const numVariables = variables.length;
    const bound = operandMatrix.length;

    const assignment = {};
    variables.forEach((variable, i) => {
      assignment[variable] = 0;
    });
    const assignmentArray = Array(numVariables).fill(0);

    while (true) {
      variables.forEach((variable, i) => {
        assignment[variable] = assignmentArray[i];
      });

      const lhsResult = this.lhs.run(operandMatrix, assignment);
      const rhsResult = this.rhs.run(operandMatrix, assignment);

      if (lhsResult !== rhsResult) {
        const name = `${this.eqn} with ${JSON.stringify(assignment)}`;
        return { refuted: true, num: this.num, name: name };
      }

      let i = numVariables - 1;
      while (i >= 0) {
        if (assignmentArray[i] < bound - 1) {
          assignmentArray[i]++;
          break;
        }
        assignmentArray[i] = 0;
        i--;
      }

      if (i < 0) {
        return { refuted: false, num: this.num, name: this.eqn };
      }
    }
  }

  getVariables() {
    const lhsVars = this.lhs.instructions.filter(isOperand);
    const rhsVars = this.rhs.instructions.filter(isOperand);
    return Array.from(new Set([...lhsVars, ...rhsVars]));
  }
}

// HELPER FUNCTIONS FOR INITIALIZATION //

async function loadRelationsFromFile(file) {
  const response = await fetch(file);
  const jsonData = await response.json();
  var num = 0;
  equations = jsonData.map(item => {
    num = num + 1;
    const eqnString = item.eqn;
    const lhsProgram = new Program(item.lhs);
    const rhsProgram = new Program(item.rhs);
    return new Relation(num, eqnString, lhsProgram, rhsProgram);
  });
  return equations;
}
async function loadUnknownsFromFile(file) {
  const response = await fetch(file);
  const jsonData = await response.json();
  unknowns = jsonData.map(item => {
    const lhsNum = parseInt(item.lhs.replace(/\D/g, ''));
    const rhsNum = parseInt(item.rhs.replace(/\D/g, ''));
    return {"lhs": lhsNum, "rhs": rhsNum}
  });
  return unknowns;
}


// MAIN MESSAGE LOOP //

let equations = null;
let unknowns = null;
self.onmessage = function(event) {
  const data = event.data;

  if (data.type === 'init') {
    equations = loadRelationsFromFile('eqdb.json');
    unknowns = loadUnknownsFromFile("unknowns.json");
  }
  if (data.type === 'checkMagma') {
    const op = data.op;
    let satisfied = [];
    let refuted = [];
    let novel = [];

    equations.forEach(e => {
      const result = e.check(op);
      if (result.refuted) {
        refuted.push([result.num, result.name]);
      } else {
        satisfied.push([result.num, result.name]);
      }
    });

    unknowns.forEach(u => {
      const antecedent = satisfied.some(x => x[0] === u.lhs);
      const consequent = !(satisfied.some(x => x[0] === u.rhs));
      if (antecedent && consequent) {
        novel.push([u.lhs, u.rhs]);
      }
    });

    self.postMessage({ satisfied, refuted, novel });
  }
};
