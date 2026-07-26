'use strict';

const assert = require('node:assert/strict');
const path = require('node:path');
const test = require('node:test');

const {
  analyzeGenerators,
  checkExpectedCode,
  loadPauliFile,
  multiplyPaulis,
  parsePauliGenerators,
  paulisCommute,
} = require('../src/verifier-b');

const FIXTURES = path.join(__dirname, '..', 'fixtures');

function fixture(name) {
  return loadPauliFile(path.join(FIXTURES, name));
}

function countAt(report, weight) {
  return report.weightCounts.find((entry) => entry.weight === weight);
}

test('parser accepts comments and rejects malformed or unequal Pauli rows', () => {
  assert.deepEqual(parsePauliGenerators('# comment\nXI\nIZ\n'), ['XI', 'IZ']);
  assert.throws(() => parsePauliGenerators('XI\nI\n'), /same length/);
  assert.throws(() => parsePauliGenerators('XA\nIZ\n'), /invalid Pauli symbol/);
  assert.throws(() => parsePauliGenerators('# comments only\n'), /no Pauli generators/);
});

test('single-qubit Pauli multiplication and commutation are explicit', () => {
  assert.equal(multiplyPaulis('I', 'X'), 'X');
  assert.equal(multiplyPaulis('X', 'X'), 'I');
  assert.equal(multiplyPaulis('X', 'Y'), 'Z');
  assert.equal(multiplyPaulis('Y', 'Z'), 'X');
  assert.equal(multiplyPaulis('Z', 'X'), 'Y');
  assert.equal(paulisCommute('X', 'Z'), false);
  assert.equal(paulisCommute('XX', 'ZZ'), true);
  assert.equal(paulisCommute('XYZ', 'ZYX'), true);
});

test('standard [[5,1,3]] code passes exact structural and distance checks', () => {
  const report = analyzeGenerators(fixture('5_1_3.pauli'), { maxWeight: 5 });

  assert.equal(report.n, 5);
  assert.equal(report.generatorCount, 4);
  assert.equal(report.uniqueStabilizerProducts, 16);
  assert.equal(report.generatorRank, 4);
  assert.equal(report.independent, true);
  assert.equal(report.pairwiseCommuting, true);
  assert.equal(report.validStabilizer, true);
  assert.equal(report.k, 1);
  assert.equal(report.minLogicalWeight, 3);
  assert.equal(countAt(report, 1).logicalCount, 0);
  assert.equal(countAt(report, 2).logicalCount, 0);
  assert.ok(countAt(report, 3).logicalCount > 0);
  assert.equal(checkExpectedCode(report, { n: 5, k: 1, distance: 3 }).pass, true);
});

test('table [[14,3,4]] Pauli transcription has rank 11 and exact distance four', () => {
  const report = analyzeGenerators(fixture('14_3_4.pauli'), { maxWeight: 5 });

  assert.equal(report.n, 14);
  assert.equal(report.generatorCount, 11);
  assert.equal(report.uniqueStabilizerProducts, 2048);
  assert.equal(report.generatorRank, 11);
  assert.equal(report.independent, true);
  assert.equal(report.pairwiseCommuting, true);
  assert.equal(report.validStabilizer, true);
  assert.equal(report.k, 3);
  assert.equal(report.minLogicalWeight, 4);
  assert.equal(countAt(report, 1).stabilizerCount, 2);
  assert.equal(countAt(report, 1).logicalCount, 0);
  assert.equal(countAt(report, 2).logicalCount, 0);
  assert.equal(countAt(report, 3).logicalCount, 0);
  assert.ok(countAt(report, 4).logicalCount > 0);
  assert.equal(checkExpectedCode(report, { n: 14, k: 3, distance: 4 }).pass, true);
});

test('duplicate generator is detected from the stabilizer product count', () => {
  const report = analyzeGenerators(fixture('duplicate_generator.pauli'), {
    maxWeight: 1,
  });
  const expected = checkExpectedCode(report, { n: 5, k: 1, distance: 3 });

  assert.equal(report.pairwiseCommuting, true);
  assert.equal(report.uniqueStabilizerProducts, 8);
  assert.equal(report.generatorRank, 3);
  assert.equal(report.independent, false);
  assert.equal(report.validStabilizer, false);
  assert.equal(report.k, 2);
  assert.equal(expected.pass, false);
  assert.ok(expected.failures.some((failure) => failure.includes('independent')));
});

test('one-symbol corruption is rejected for anticommutation', () => {
  const report = analyzeGenerators(fixture('anticommuting_symbol.pauli'), {
    maxWeight: 1,
  });
  const expected = checkExpectedCode(report, { n: 5, k: 1, distance: 3 });

  assert.equal(report.independent, true);
  assert.equal(report.pairwiseCommuting, false);
  assert.deepEqual(report.anticommutingPairs, [[1, 3]]);
  assert.equal(report.validStabilizer, false);
  assert.equal(report.k, null);
  assert.equal(report.weightCounts.length, 0);
  assert.equal(expected.pass, false);
  assert.ok(expected.failures.some((failure) => failure.includes('commute')));
});

test('valid code with a weight-one logical fails a distance-three claim', () => {
  const report = analyzeGenerators(fixture('low_weight_logical.pauli'), {
    maxWeight: 3,
  });
  const expected = checkExpectedCode(report, { n: 5, k: 1, distance: 3 });

  assert.equal(report.validStabilizer, true);
  assert.equal(report.minLogicalWeight, 1);
  assert.equal(countAt(report, 1).logicalCount, 3);
  assert.equal(expected.pass, false);
  assert.ok(expected.failures.some((failure) => failure.includes('weight 1')));
});

test('low-weight commuting stabilizer is membership, not a logical failure', () => {
  const report = analyzeGenerators(fixture('degenerate_membership.pauli'), {
    maxWeight: 3,
  });

  assert.equal(report.n, 6);
  assert.equal(report.k, 1);
  assert.equal(report.validStabilizer, true);
  assert.equal(countAt(report, 1).commutingCount, 1);
  assert.equal(countAt(report, 1).stabilizerCount, 1);
  assert.equal(countAt(report, 1).logicalCount, 0);
  assert.equal(report.minLogicalWeight, 3);
  assert.equal(checkExpectedCode(report, { n: 6, k: 1, distance: 3 }).pass, true);
});

test('target checker requires no logicals below d and at least one at d', () => {
  const report = analyzeGenerators(fixture('5_1_3.pauli'), { maxWeight: 2 });
  const expected = checkExpectedCode(report, { n: 5, k: 1, distance: 3 });

  assert.equal(expected.pass, false);
  assert.ok(expected.failures.some((failure) => failure.includes('not scanned')));
});
