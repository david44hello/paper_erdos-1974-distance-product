# Erdős’s 1974 distance-product volume problem

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_erdos-1974-distance-product).

## How to verify

Install Git, Python 3 and elan, the Lean toolchain manager. From the `lean/` directory of a Git checkout, run:

```sh
./scripts/check.sh
```

This checks the real-limsup control, builds the proof and regenerates the audit. The final line reads `5 OPEN, 117 PROVED, 40 PROVED GIVEN`. These counts include supporting lemmas. One Lean process used about 7.5 GB of memory with Mathlib already cached.

The volume and stability bounds use named analytic facts about capacity, equilibrium measures or level surfaces. The sharpness lower bound is proved with no named facts, at every positive threshold. For the statements, assumptions and open claims, see [What to read](WHAT_TO_READ.md).

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
