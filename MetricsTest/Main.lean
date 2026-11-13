/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofTools.Test.Harness
import MetricsTest.Properties

open InkproofTools.Test MetricsTest

def main : IO UInt32 :=
  runTests Properties.tests
