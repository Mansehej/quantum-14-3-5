#!/usr/bin/env node
'use strict';

const {
  analyzeGenerators,
  checkExpectedCode,
  loadPauliFile,
} = require('./verifier-b');

function usage() {
  return [
    'Usage:',
    '  node src/cli.js FILE [--max-weight W]',
    '    [--expect-n N --expect-k K --expect-distance D]',
    '',
    'FILE contains one phase-free I/X/Y/Z generator per line.',
    'All output is deterministic JSON. No external packages are used.',
  ].join('\n');
}

function parseNonnegativeInteger(flag, raw) {
  if (raw === undefined || !/^\d+$/.test(raw)) {
    throw new Error(`${flag} requires a nonnegative integer`);
  }
  return Number(raw);
}

function parseArguments(argv) {
  if (argv.length === 0 || argv.includes('--help')) {
    return { help: true };
  }

  let file = null;
  let maxWeight = 5;
  const expected = {};
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (!argument.startsWith('--')) {
      if (file !== null) {
        throw new Error(`unexpected positional argument: ${argument}`);
      }
      file = argument;
      continue;
    }

    const raw = argv[index + 1];
    if (argument === '--max-weight') {
      maxWeight = parseNonnegativeInteger(argument, raw);
    } else if (argument === '--expect-n') {
      expected.n = parseNonnegativeInteger(argument, raw);
    } else if (argument === '--expect-k') {
      expected.k = parseNonnegativeInteger(argument, raw);
    } else if (argument === '--expect-distance') {
      expected.distance = parseNonnegativeInteger(argument, raw);
    } else {
      throw new Error(`unknown option: ${argument}`);
    }
    index += 1;
  }

  if (file === null) {
    throw new Error('a Pauli fixture FILE is required');
  }
  const expectedKeys = Object.keys(expected);
  if (expectedKeys.length !== 0 && expectedKeys.length !== 3) {
    throw new Error(
      '--expect-n, --expect-k, and --expect-distance must be supplied together',
    );
  }

  return {
    expected: expectedKeys.length === 3 ? expected : null,
    file,
    help: false,
    maxWeight,
  };
}

function main() {
  try {
    const options = parseArguments(process.argv.slice(2));
    if (options.help) {
      process.stdout.write(`${usage()}\n`);
      return;
    }

    const generators = loadPauliFile(options.file);
    const report = analyzeGenerators(generators, {
      maxWeight: options.maxWeight,
    });
    const output = {
      verifier: 'verifier-b-pauli-native-v1',
      input: options.file,
      report,
    };
    if (options.expected !== null) {
      output.expectedCodeCheck = checkExpectedCode(report, options.expected);
    }

    process.stdout.write(`${JSON.stringify(output, null, 2)}\n`);
    const accepted =
      options.expected === null
        ? report.validStabilizer
        : output.expectedCodeCheck.pass;
    if (!accepted) {
      process.exitCode = 1;
    }
  } catch (error) {
    process.stderr.write(`Verifier B error: ${error.message}\n`);
    process.stderr.write(`${usage()}\n`);
    process.exitCode = 2;
  }
}

main();
