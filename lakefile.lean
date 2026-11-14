/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-consumer-metrics» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]
  testDriver := "tests"

require «inkproof-core» from git "https://github.com/paulbutcher/inkproof-core" @ "v0.6.1"
require «inkproof-scale» from git "https://github.com/paulbutcher/inkproof-scale" @ "v0.5.2"
require «inkproof-tools» from git "https://github.com/paulbutcher/inkproof-tools" @ "v0.1.0"

@[default_target]
lean_lib Metrics where
  roots := #[`Metrics, `Metrics.Proofs]

-- Compile-time checks live here too: compiling is passing.
lean_lib MetricsTest where
  globs := #[.submodules `MetricsTest]

lean_exe tests where
  root := `MetricsTest.Main
