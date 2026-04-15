# WeightedNetKAT

[![Lean Action CI](https://github.com/cornell-pl/wnetkat-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cornell-pl/wnetkat-lean/actions/workflows/lean_action_ci.yml)


## Accessing formalization

One can access the generated documentation online at [https://cornell-pl.github.io/wnetkat-lean/](https://cornell-pl.github.io/wnetkat-lean/).

Refer to [`Papers.lean`](https://cornell-pl.github.io/wnetkat-lean/WeightedNetKAT/Papers.html) for an overview linking all definitions, theorems, and lemmas from the paper to their respective Lean formulation.

## Interacting with formalization

We recommend setting up Lean using [the official guide](https://lean-lang.org/install/). The project was tested and built using the following toolchain:

```
❯ elan --version && lake --version && lean --version
elan 4.2.1 (3d5138e15 2026-03-18)
Lake version 5.0.0-src+714601b (Lean version 4.30.0-rc1)
Lean (version 4.30.0-rc1, arm64-apple-darwin24.6.0, commit 714601baf118066cbf3f282361339c6d06665b2a, Release)
```

Once setup, open the project in your editor and access the files. The initial setup might take a while as Mathlib takes some time to download and cache.


If you wish to build from the command line follow the steps below:

```
❯ lake exe cache get
❯ lake build
```
