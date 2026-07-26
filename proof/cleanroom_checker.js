#!/usr/bin/env node
"use strict";

/*
 * Independent finite checker for the fragile p03 collision calculation.
 *
 * This file intentionally does not import the primary Python checker, a
 * generated certificate, or any non-stdlib package.  Pauli multiplication
 * modulo phase is represented by XOR on I=0, X=1, Z=2, Y=3.
 */

const assert = require("assert");
const crypto = require("crypto");

const N = 14;
const SYMBOLS = "IXZY";
const REQUIRED_FORM_NAMES = ["disjoint", "p0", "p1", "p2"];

function parsePauli(text) {
  assert.strictEqual(text.length, N, `Pauli word must have length ${N}`);
  return Array.from(text, (symbol) => {
    const value = SYMBOLS.indexOf(symbol);
    assert.notStrictEqual(value, -1, `invalid Pauli symbol ${symbol}`);
    return value;
  });
}

function formatPauli(word) {
  return word.map((value) => SYMBOLS[value]).join("");
}

function weight(word) {
  let result = 0;
  for (const value of word) {
    if (value !== 0) result += 1;
  }
  return result;
}

function addPaulis(left, right) {
  return left.map((value, index) => value ^ right[index]);
}

function symplecticProduct(left, right) {
  let parity = 0;
  for (let index = 0; index < N; index += 1) {
    const a = left[index];
    const b = right[index];
    if (a !== 0 && b !== 0 && a !== b) parity ^= 1;
  }
  return parity;
}

function binaryRank(words) {
  const rows = words.map((word) => {
    let row = 0n;
    for (let index = 0; index < N; index += 1) {
      if ((word[index] & 1) !== 0) row |= 1n << BigInt(index);
      if ((word[index] & 2) !== 0) row |= 1n << BigInt(N + index);
    }
    return row;
  });
  let rank = 0;
  for (let column = 2 * N - 1; column >= 0; column -= 1) {
    let pivot = rank;
    const mask = 1n << BigInt(column);
    while (pivot < rows.length && (rows[pivot] & mask) === 0n) pivot += 1;
    if (pivot === rows.length) continue;
    [rows[rank], rows[pivot]] = [rows[pivot], rows[rank]];
    for (let row = 0; row < rows.length; row += 1) {
      if (row !== rank && (rows[row] & mask) !== 0n) rows[row] ^= rows[rank];
    }
    rank += 1;
    if (rank === rows.length) break;
  }
  return rank;
}

function enumerateWeightThreeWords() {
  const words = [];
  for (let first = 0; first < N - 2; first += 1) {
    for (let second = first + 1; second < N - 1; second += 1) {
      for (let third = second + 1; third < N; third += 1) {
        for (let a = 1; a <= 3; a += 1) {
          for (let b = 1; b <= 3; b += 1) {
            for (let c = 1; c <= 3; c += 1) {
              const word = Array(N).fill(0);
              word[first] = a;
              word[second] = b;
              word[third] = c;
              words.push(word);
            }
          }
        }
      }
    }
  }
  return words;
}

function sameBinCollision(word, translation) {
  const translated = addPaulis(word, translation);
  if (weight(translated) !== 3) return false;
  let sharedBins = 0;
  for (let index = 0; index < N; index += 1) {
    if (word[index] !== 0 && word[index] === translated[index]) {
      sharedBins += 1;
    }
  }
  // Two distinct weight-three words separated by a weight-four word cannot
  // share two coordinate/Pauli bins.  Keep this as a checked invariant rather
  // than building it into the enumerator.
  assert.ok(sharedBins <= 1, "a collision pair unexpectedly shares two bins");
  return sharedBins === 1;
}

function collisionProfile(words, generators) {
  const histogram = [0, 0, 0, 0];
  const degreeWords = [];
  for (const word of words) {
    let degree = 0;
    for (const generator of generators) {
      if (sameBinCollision(word, generator)) degree += 1;
    }
    assert.ok(degree >= 0 && degree <= 3);
    histogram[degree] += 1;
    degreeWords.push({ degree, word: formatPauli(word) });
  }
  degreeWords.sort((left, right) => {
    if (left.degree !== right.degree) return right.degree - left.degree;
    if (left.word < right.word) return -1;
    if (left.word > right.word) return 1;
    return 0;
  });
  const top = degreeWords.slice(0, 24);
  const top24DegreeSum = top.reduce((sum, entry) => sum + entry.degree, 0);
  const collisionUpperBound = Number(BigInt(top24DegreeSum) / 2n);
  return {
    degreeHistogram: histogram,
    maximumDegree: top[0].degree,
    maximumDegreeWords: degreeWords
      .filter((entry) => entry.degree === top[0].degree)
      .map((entry) => entry.word),
    top24DegreeSum,
    collisionUpperBound,
  };
}

function normalForms() {
  const raw = {
    disjoint: [
      "XXXXIIIIIIIIII",
      "IIIIXXXXIIIIII",
      "IIIIIIIIXXXXII",
    ],
    p0: [
      "XXXXIIIIIIIIII",
      "ZZZZIIIIIIIIII",
      "YYYYIIIIIIIIII",
    ],
    p1: [
      "XIXXXIIIIIIIII",
      "IXXZZIIIIIIIII",
      "XXIYYIIIIIIIII",
    ],
    p2: [
      "XXIIXXIIIIIIII",
      "IIXXXXIIIIIIII",
      "XXXXIIIIIIIIII",
    ],
  };
  return Object.fromEntries(
    Object.entries(raw).map(([name, generators]) => [
      name,
      generators.map(parsePauli),
    ]),
  );
}

function checkNormalForm(name, generators) {
  assert.strictEqual(generators.length, 3);
  for (const generator of generators) assert.strictEqual(weight(generator), 4);
  for (let first = 0; first < 3; first += 1) {
    for (let second = first + 1; second < 3; second += 1) {
      assert.strictEqual(symplecticProduct(generators[first], generators[second]), 0);
    }
  }
  const rank = binaryRank(generators);
  if (name === "disjoint") {
    assert.strictEqual(rank, 3);
    for (let first = 0; first < 3; first += 1) {
      for (let second = first + 1; second < 3; second += 1) {
        let supportIntersection = 0;
        for (let coordinate = 0; coordinate < N; coordinate += 1) {
          if (generators[first][coordinate] && generators[second][coordinate]) {
            supportIntersection += 1;
          }
        }
        assert.strictEqual(supportIntersection, 0);
      }
    }
  } else {
    assert.strictEqual(rank, 2);
    assert.deepStrictEqual(addPaulis(generators[0], generators[1]), generators[2]);
  }
  return rank;
}

function pairSignature(first, second) {
  let intersection = 0;
  let equalLabel = 0;
  for (let coordinate = 0; coordinate < N; coordinate += 1) {
    if (first[coordinate] !== 0 && second[coordinate] !== 0) {
      intersection += 1;
      if (first[coordinate] === second[coordinate]) equalLabel += 1;
    }
  }
  return [intersection, equalLabel];
}

function chooseFourCoordinates(callback) {
  for (let a = 0; a < N - 3; a += 1) {
    for (let b = a + 1; b < N - 2; b += 1) {
      for (let c = b + 1; c < N - 1; c += 1) {
        for (let d = c + 1; d < N; d += 1) callback([a, b, c, d]);
      }
    }
  }
}

function canonicalPair(intersection, equalLabel) {
  const first = Array(N).fill(0);
  const second = Array(N).fill(0);
  for (let coordinate = 0; coordinate < 4; coordinate += 1) first[coordinate] = 1;
  let cursor = 0;
  for (let count = 0; count < equalLabel; count += 1) second[cursor++] = 1;
  for (let count = 0; count < intersection - equalLabel; count += 1) {
    second[cursor++] = 2;
  }
  cursor += 4 - intersection;
  for (let count = 0; count < 4 - intersection; count += 1) {
    second[cursor++] = 1;
  }
  return [first, second];
}

/*
 * Constructively normalize a pair whose first word is XXXX on coordinates
 * 0..3.  Coordinate permutations collect equal-overlap, unequal-overlap,
 * first-only, and second-only positions in that order.  Single-coordinate
 * Clifford permutations then send unequal labels to Z while fixing X, and
 * send each outside label to X.  Returning the transformed words explicitly
 * checks the advertised normal-form argument for every enumerated pair.
 */
function normalizeFixedFirstPair(second) {
  const equal = [];
  const unequal = [];
  const firstOnly = [];
  const secondOnly = [];
  const outsideEmpty = [];
  for (let coordinate = 0; coordinate < 4; coordinate += 1) {
    if (second[coordinate] === 1) equal.push(coordinate);
    else if (second[coordinate] !== 0) unequal.push(coordinate);
    else firstOnly.push(coordinate);
  }
  for (let coordinate = 4; coordinate < N; coordinate += 1) {
    if (second[coordinate] !== 0) secondOnly.push(coordinate);
    else outsideEmpty.push(coordinate);
  }
  const permutation = equal.concat(
    unequal,
    firstOnly,
    secondOnly,
    outsideEmpty,
  );
  assert.strictEqual(permutation.length, N);
  const first = Array(N).fill(0);
  const transformedSecond = Array(N).fill(0);
  for (let newCoordinate = 0; newCoordinate < N; newCoordinate += 1) {
    const oldCoordinate = permutation[newCoordinate];
    const firstValue = oldCoordinate < 4 ? 1 : 0;
    let secondValue = second[oldCoordinate];
    if (firstValue === 1 && secondValue !== 0 && secondValue !== 1) {
      // A local Clifford fixing X may exchange Y and Z.
      secondValue = 2;
    } else if (firstValue === 0 && secondValue !== 0) {
      // With I in the first word, any nonidentity label may be sent to X.
      secondValue = 1;
    }
    first[newCoordinate] = firstValue;
    transformedSecond[newCoordinate] = secondValue;
  }
  return [first, transformedSecond];
}

function enumeratePlanePairs() {
  const first = parsePauli("XXXXIIIIIIIIII");
  const counts = {};
  let candidateSecondWords = 0;
  let qualifyingPairCount = 0;
  let normalizationFailures = 0;
  const digest = crypto.createHash("sha256");

  chooseFourCoordinates((support) => {
    for (let a = 1; a <= 3; a += 1) {
      for (let b = 1; b <= 3; b += 1) {
        for (let c = 1; c <= 3; c += 1) {
          for (let d = 1; d <= 3; d += 1) {
            candidateSecondWords += 1;
            const second = Array(N).fill(0);
            second[support[0]] = a;
            second[support[1]] = b;
            second[support[2]] = c;
            second[support[3]] = d;
            if (symplecticProduct(first, second) !== 0) continue;
            if (weight(addPaulis(first, second)) !== 4) continue;
            qualifyingPairCount += 1;
            const [intersection, equalLabel] = pairSignature(first, second);
            const key = `${intersection},${equalLabel}`;
            counts[key] = (counts[key] || 0) + 1;
            const normalized = normalizeFixedFirstPair(second);
            const expected = canonicalPair(intersection, equalLabel);
            if (
              formatPauli(normalized[0]) !== formatPauli(expected[0]) ||
              formatPauli(normalized[1]) !== formatPauli(expected[1])
            ) {
              normalizationFailures += 1;
            }
            digest.update(`${formatPauli(second)}:${key}\n`, "ascii");
          }
        }
      }
    }
  });

  return {
    fixedFirstWord: formatPauli(first),
    candidateSecondWords,
    qualifyingPairCount,
    signatureCounts: Object.fromEntries(
      Object.entries(counts).sort(([left], [right]) =>
        left < right ? -1 : left > right ? 1 : 0,
      ),
    ),
    observedSignatures: Object.keys(counts).sort(),
    normalizationFailures,
    qualifyingPairsSha256: digest.digest("hex"),
  };
}

function verifyCanonicalRepresentatives(forms) {
  const expected = {
    p0: [4, 0],
    p1: [3, 1],
    p2: [2, 2],
  };
  const results = {};
  for (const [name, signature] of Object.entries(expected)) {
    const generators = forms[name];
    const actual = pairSignature(generators[0], generators[1]);
    const normalized = canonicalPair(actual[0], actual[1]);
    results[name] = {
      signature: actual,
      expectedSignature: signature,
      pairCommutes: symplecticProduct(generators[0], generators[1]) === 0,
      thirdIsSum: formatPauli(addPaulis(generators[0], generators[1])) ===
        formatPauli(generators[2]),
      canonicalPair: normalized.map(formatPauli),
      verified:
        actual[0] === signature[0] &&
        actual[1] === signature[1] &&
        symplecticProduct(generators[0], generators[1]) === 0 &&
        formatPauli(addPaulis(generators[0], generators[1])) ===
          formatPauli(generators[2]),
    };
  }
  return results;
}

function buildCertificate() {
  const words = enumerateWeightThreeWords();
  assert.strictEqual(words.length, 9828);
  const forms = normalForms();
  const formResults = {};
  for (const name of REQUIRED_FORM_NAMES) {
    const generators = forms[name];
    const rank = checkNormalForm(name, generators);
    formResults[name] = {
      generators: generators.map(formatPauli),
      binaryRank: rank,
      ...collisionProfile(words, generators),
    };
  }
  return {
    schema: "quantum-14-3-5-cleanroom-p03-v1",
    implementation: {
      language: "JavaScript",
      arithmetic: "exact integers and BigInt",
      dependencies: ["Node.js standard library"],
    },
    weightThreeEnumeration: {
      coordinateSupports: 364,
      nonidentityLabelsPerSupport: 27,
      wordCount: words.length,
    },
    normalForms: formResults,
    rankTwoPlaneEnumeration: enumeratePlanePairs(),
    canonicalRepresentativeChecks: verifyCanonicalRepresentatives(forms),
  };
}

const EXPECTED_COLLISIONS = {
  disjoint: { histogram: [9288, 540, 0, 0], top24: 24, upper: 12 },
  p0: { histogram: [9288, 540, 0, 0], top24: 24, upper: 12 },
  p1: { histogram: [9290, 537, 0, 1], top24: 26, upper: 13 },
  p2: { histogram: [9376, 372, 72, 8], top24: 56, upper: 28 },
};

function validateCertificate(certificate) {
  assert.strictEqual(certificate.weightThreeEnumeration.wordCount, 9828);
  assert.deepStrictEqual(
    Object.keys(certificate.normalForms).sort(),
    REQUIRED_FORM_NAMES.slice().sort(),
    "normal-form set is incomplete or contains an unexpected form",
  );
  for (const name of REQUIRED_FORM_NAMES) {
    const actual = certificate.normalForms[name];
    const expected = EXPECTED_COLLISIONS[name];
    assert.deepStrictEqual(
      actual.degreeHistogram,
      expected.histogram,
      `${name} collision-degree table changed`,
    );
    assert.strictEqual(actual.top24DegreeSum, expected.top24);
    assert.strictEqual(actual.collisionUpperBound, expected.upper);
  }
  const plane = certificate.rankTwoPlaneEnumeration;
  assert.strictEqual(plane.candidateSecondWords, 81081);
  assert.strictEqual(plane.qualifyingPairCount, 3886);
  assert.deepStrictEqual(plane.observedSignatures, ["2,2", "3,1", "4,0"]);
  assert.deepStrictEqual(plane.signatureCounts, {
    "2,2": 2430,
    "3,1": 1440,
    "4,0": 16,
  });
  assert.strictEqual(plane.normalizationFailures, 0);
  for (const name of ["p0", "p1", "p2"]) {
    assert.strictEqual(
      certificate.canonicalRepresentativeChecks[name].verified,
      true,
      `${name} is not a verified representative of its plane orbit`,
    );
  }
  return true;
}

function clone(value) {
  return JSON.parse(JSON.stringify(value));
}

function mustReject(callback, label) {
  let rejected = false;
  try {
    callback();
  } catch (error) {
    rejected = true;
  }
  assert.strictEqual(rejected, true, `mutation was not rejected: ${label}`);
}

function runSelfTests() {
  const certificate = buildCertificate();
  validateCertificate(certificate);

  const omittedForm = clone(certificate);
  delete omittedForm.normalForms.p2;
  mustReject(
    () => validateCertificate(omittedForm),
    "omitted p2 normal form",
  );

  const alteredTable = clone(certificate);
  alteredTable.normalForms.p1.degreeHistogram[0] += 1;
  alteredTable.normalForms.p1.degreeHistogram[1] -= 1;
  mustReject(
    () => validateCertificate(alteredTable),
    "altered p1 collision table",
  );

  const alteredPlane = clone(certificate);
  alteredPlane.rankTwoPlaneEnumeration.observedSignatures.pop();
  mustReject(
    () => validateCertificate(alteredPlane),
    "omitted plane signature",
  );

  return {
    status: "PASS",
    tests: [
      "generated certificate validates",
      "omitted normal form rejected",
      "altered collision table rejected",
      "omitted plane signature rejected",
    ],
  };
}

function main(argv) {
  if (argv.length !== 1 || !["--json", "--self-test"].includes(argv[0])) {
    process.stderr.write(
      "usage: node proof/cleanroom_checker.js --json|--self-test\n",
    );
    return 2;
  }
  if (argv[0] === "--self-test") {
    const result = runSelfTests();
    process.stdout.write(`CLEANROOM SELF-TEST ${result.status}\n`);
    for (const test of result.tests) process.stdout.write(`- ${test}\n`);
    return 0;
  }
  const certificate = buildCertificate();
  validateCertificate(certificate);
  process.stdout.write(`${JSON.stringify(certificate, null, 2)}\n`);
  return 0;
}

module.exports = {
  buildCertificate,
  runSelfTests,
  validateCertificate,
};

if (require.main === module) {
  process.exitCode = main(process.argv.slice(2));
}
