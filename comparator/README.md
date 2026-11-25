# Comparing the Lean statements and proofs

[Challenge.lean](Challenge.lean) imports the modules that specify the statements. [comparator.json](comparator.json) lists the 170 declarations to compare with the proofs and the three permitted Lean axioms. The five statements still marked OPEN in [the audit](../lean/AUDIT.md) are excluded from the list. Each conditional statement includes its analytic hypotheses.

Use Linux with Git, elan and bubblewrap (`bwrap`) installed and working. From the root of a clean Git checkout, prepare a temporary copy. The tag pins the Lean toolchain and Mathlib dependencies.

```bash
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -x -C "$comparison_dir"
cp -R comparator/Challenge comparator/Challenge.lean comparator/comparator.json comparator/lakefile.toml "$comparison_dir/"
cd "$comparison_dir"
lake exe cache get
```

Run the comparison:

```sh
lake --no-cache comparator --config=comparator.json
```

On acceptance, Lake prints `Lean default kernel accepts the solution` and `Your solution is okay!`. To include Lean's five additional proof checkers, append `--paranoid` to the same command.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
