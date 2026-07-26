#!/usr/bin/env node
"use strict";

const assert = require("assert");
const childProcess = require("child_process");
const path = require("path");

const checkerPath = path.resolve(__dirname, "..", "cleanroom_checker.js");
const checker = require(checkerPath);

const certificate = checker.buildCertificate();
assert.strictEqual(checker.validateCertificate(certificate), true);

const missingForm = JSON.parse(JSON.stringify(certificate));
delete missingForm.normalForms.p0;
assert.throws(
  () => checker.validateCertificate(missingForm),
  /normal-form set is incomplete/,
);

const changedCollisionTable = JSON.parse(JSON.stringify(certificate));
changedCollisionTable.normalForms.p2.degreeHistogram = [9375, 373, 72, 8];
assert.throws(
  () => checker.validateCertificate(changedCollisionTable),
  /p2 collision-degree table changed/,
);

const jsonRun = childProcess.spawnSync(
  process.execPath,
  [checkerPath, "--json"],
  { encoding: "utf8" },
);
assert.strictEqual(jsonRun.status, 0, jsonRun.stderr);
const subprocessCertificate = JSON.parse(jsonRun.stdout);
assert.deepStrictEqual(subprocessCertificate, certificate);

const selfTestRun = childProcess.spawnSync(
  process.execPath,
  [checkerPath, "--self-test"],
  { encoding: "utf8" },
);
assert.strictEqual(selfTestRun.status, 0, selfTestRun.stderr);
assert.match(selfTestRun.stdout, /^CLEANROOM SELF-TEST PASS\n/);

process.stdout.write("cleanroom.test.js PASS (6 checks)\n");
