'use strict';

const fs = require('node:fs');

const PAULI_SYMBOLS = Object.freeze(['X', 'Y', 'Z']);
const VALID_SYMBOLS = /^[IXYZ]+$/;

/**
 * Parse one phase-free Pauli generator per non-comment line.
 *
 * This parser intentionally accepts Pauli strings directly.  It does not
 * consume, or translate through, a binary X|Z matrix.
 */
function parsePauliGenerators(text) {
  if (typeof text !== 'string') {
    throw new TypeError('Pauli fixture must be text');
  }

  const generators = text
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0 && !line.startsWith('#'));

  if (generators.length === 0) {
    throw new Error('no Pauli generators found');
  }

  const n = generators[0].length;
  for (let row = 0; row < generators.length; row += 1) {
    const generator = generators[row];
    if (generator.length !== n) {
      throw new Error(
        `all Pauli generators must have the same length; row ${row + 1} ` +
          `has length ${generator.length}, expected ${n}`,
      );
    }
    if (!VALID_SYMBOLS.test(generator)) {
      throw new Error(`row ${row + 1} contains an invalid Pauli symbol`);
    }
  }

  return generators;
}

function loadPauliFile(filePath) {
  return parsePauliGenerators(fs.readFileSync(filePath, 'utf8'));
}

/**
 * Two phase-free Pauli strings commute iff the number of positions carrying
 * distinct non-identity Paulis is even.
 */
function paulisCommute(left, right) {
  assertSameLength(left, right);
  let anticommutesAt = 0;
  for (let qubit = 0; qubit < left.length; qubit += 1) {
    const a = left[qubit];
    const b = right[qubit];
    if (a !== 'I' && b !== 'I' && a !== b) {
      anticommutesAt += 1;
    }
  }
  return anticommutesAt % 2 === 0;
}

/** Multiply Pauli strings modulo the irrelevant global phase. */
function multiplyPaulis(left, right) {
  assertSameLength(left, right);
  let product = '';
  for (let qubit = 0; qubit < left.length; qubit += 1) {
    const a = left[qubit];
    const b = right[qubit];
    if (a === 'I') {
      product += b;
    } else if (b === 'I') {
      product += a;
    } else if (a === b) {
      product += 'I';
    } else if (a !== 'X' && b !== 'X') {
      product += 'X';
    } else if (a !== 'Y' && b !== 'Y') {
      product += 'Y';
    } else {
      product += 'Z';
    }
  }
  return product;
}

function assertSameLength(left, right) {
  if (left.length !== right.length) {
    throw new Error('Pauli strings must have the same length');
  }
}

/**
 * Enumerate all 2^m subset products, retaining the raw product count so a
 * dependent generator list is detected by collisions in the unique set.
 */
function enumerateStabilizerProducts(generators) {
  const n = generators[0].length;
  if (generators.length > 24) {
    throw new Error('refusing to enumerate more than 2^24 generator products');
  }

  const products = ['I'.repeat(n)];
  for (const generator of generators) {
    const priorCount = products.length;
    for (let index = 0; index < priorCount; index += 1) {
      products.push(multiplyPaulis(products[index], generator));
    }
  }

  return {
    subsetProductCount: products.length,
    uniqueProducts: new Set(products),
  };
}

function findAnticommutingPairs(generators) {
  const pairs = [];
  for (let left = 0; left < generators.length; left += 1) {
    for (let right = left + 1; right < generators.length; right += 1) {
      if (!paulisCommute(generators[left], generators[right])) {
        // Human-facing generator row numbers are one-based.
        pairs.push([left + 1, right + 1]);
      }
    }
  }
  return pairs;
}

function forEachSupport(n, weight, callback) {
  const support = new Array(weight);

  function choose(depth, nextQubit) {
    if (depth === weight) {
      callback(support);
      return;
    }

    const positionsNeeded = weight - depth;
    const lastStart = n - positionsNeeded;
    for (let qubit = nextQubit; qubit <= lastStart; qubit += 1) {
      support[depth] = qubit;
      choose(depth + 1, qubit + 1);
    }
  }

  choose(0, 0);
}

function forEachPauliOnSupport(n, support, callback) {
  const symbols = new Array(n).fill('I');

  function assign(depth) {
    if (depth === support.length) {
      callback(symbols.join(''));
      return;
    }

    const qubit = support[depth];
    for (const symbol of PAULI_SYMBOLS) {
      symbols[qubit] = symbol;
      assign(depth + 1);
    }
    symbols[qubit] = 'I';
  }

  assign(0);
}

function binomial(n, k) {
  if (k < 0 || k > n) {
    return 0;
  }
  let value = 1;
  const smaller = Math.min(k, n - k);
  for (let index = 1; index <= smaller; index += 1) {
    value = (value * (n - smaller + index)) / index;
  }
  return value;
}

function scanBoundedWeightErrors(generators, stabilizerSet, maxWeight) {
  const n = generators[0].length;
  const weightCounts = [];
  let minLogicalWeight = null;
  let logicalWitness = null;

  for (let weight = 0; weight <= Math.min(maxWeight, n); weight += 1) {
    const counts = {
      weight,
      totalErrors: binomial(n, weight) * 3 ** weight,
      commutingCount: 0,
      stabilizerCount: 0,
      logicalCount: 0,
    };

    forEachSupport(n, weight, (support) => {
      forEachPauliOnSupport(n, support, (error) => {
        const commuting = generators.every((generator) =>
          paulisCommute(error, generator),
        );
        if (!commuting) {
          return;
        }

        counts.commutingCount += 1;
        if (stabilizerSet.has(error)) {
          counts.stabilizerCount += 1;
          return;
        }

        counts.logicalCount += 1;
        if (minLogicalWeight === null) {
          minLogicalWeight = weight;
          logicalWitness = error;
        }
      });
    });

    weightCounts.push(counts);
  }

  return { logicalWitness, minLogicalWeight, weightCounts };
}

function analyzeGenerators(generators, options = {}) {
  if (!Array.isArray(generators) || generators.length === 0) {
    throw new Error('at least one Pauli generator is required');
  }
  // Reuse the strict parser as an input validator without translating formats.
  const validated = parsePauliGenerators(generators.join('\n'));
  const n = validated[0].length;
  const generatorCount = validated.length;
  const maxWeight = options.maxWeight === undefined ? 5 : options.maxWeight;
  if (!Number.isInteger(maxWeight) || maxWeight < 0 || maxWeight > n) {
    throw new Error(`maxWeight must be an integer between 0 and ${n}`);
  }

  const anticommutingPairs = findAnticommutingPairs(validated);
  const pairwiseCommuting = anticommutingPairs.length === 0;
  const { subsetProductCount, uniqueProducts } =
    enumerateStabilizerProducts(validated);
  const uniqueStabilizerProducts = uniqueProducts.size;
  const generatorRank = Math.log2(uniqueStabilizerProducts);
  if (!Number.isInteger(generatorRank)) {
    throw new Error('internal error: Pauli span size is not a power of two');
  }
  const independent = uniqueStabilizerProducts === subsetProductCount;
  const validStabilizer = pairwiseCommuting && independent;
  const k = pairwiseCommuting ? n - generatorRank : null;

  let scan = {
    logicalWitness: null,
    minLogicalWeight: null,
    weightCounts: [],
  };
  if (pairwiseCommuting) {
    scan = scanBoundedWeightErrors(validated, uniqueProducts, maxWeight);
  }

  return {
    representation: 'phase-free Pauli strings over I/X/Y/Z',
    n,
    generatorCount,
    subsetProductCount,
    uniqueStabilizerProducts,
    generatorRank,
    independent,
    pairwiseCommuting,
    anticommutingPairs,
    validStabilizer,
    k,
    maxWeightScanned: pairwiseCommuting ? maxWeight : null,
    weightCounts: scan.weightCounts,
    minLogicalWeight: scan.minLogicalWeight,
    logicalWitness: scan.logicalWitness,
  };
}

function checkExpectedCode(report, expected) {
  const failures = [];
  const { n, k, distance } = expected;

  if (!Number.isInteger(n) || !Number.isInteger(k) || !Number.isInteger(distance)) {
    throw new Error('expected n, k, and distance must all be integers');
  }
  if (report.n !== n) {
    failures.push(`length is n=${report.n}, expected n=${n}`);
  }
  if (!report.independent) {
    failures.push(
      `generators are not independent: rank ${report.generatorRank} from ` +
        `${report.generatorCount} rows`,
    );
  }
  if (!report.pairwiseCommuting) {
    failures.push('generators do not pairwise commute');
  }
  if (report.k !== k) {
    failures.push(`computed k=${String(report.k)}, expected k=${k}`);
  }

  if (report.maxWeightScanned === null || report.maxWeightScanned < distance) {
    failures.push(
      `exact distance ${distance} is not scanned; maxWeightScanned=` +
        `${String(report.maxWeightScanned)}`,
    );
  } else {
    const lowerLogical = report.weightCounts.find(
      (entry) => entry.weight < distance && entry.logicalCount > 0,
    );
    if (lowerLogical) {
      failures.push(
        `found ${lowerLogical.logicalCount} logical Pauli(s) at weight ` +
          `${lowerLogical.weight}, below expected distance ${distance}`,
      );
    }

    const exact = report.weightCounts.find((entry) => entry.weight === distance);
    if (!exact || exact.logicalCount === 0) {
      failures.push(`found no logical Pauli at exact weight ${distance}`);
    }
  }

  return {
    expected: { n, k, distance },
    pass: failures.length === 0,
    failures,
  };
}

module.exports = {
  analyzeGenerators,
  checkExpectedCode,
  enumerateStabilizerProducts,
  loadPauliFile,
  multiplyPaulis,
  parsePauliGenerators,
  paulisCommute,
  scanBoundedWeightErrors,
};
