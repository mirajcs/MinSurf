# MinSurf

A Lean 4 formalization of the theory of minimal surfaces, built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

> ⚠️ **Status: under active development.** The library is incomplete and its
> definitions and APIs are still changing. Expect breaking changes.

## Overview

The project develops the differential geometry of minimal surfaces in the
manifold setting. So far it contains:

- `MinSurf/FirstVariation.lean` — a `Variation` of a map `f : S → M` (smooth,
  with fixed boundary and compact support) and its **variational vector field**
  `X = ∂F/∂t |_{t = 0}`, a vector field along `f`.

## Building

```bash
lake build
```

## Documentation

API documentation is generated with
[doc-gen4](https://github.com/leanprover/doc-gen4) and published to GitHub Pages:
<https://mirajcs.github.io/MinSurf/>.

To build the docs locally:

```bash
lake build MinSurf:docs
```

The generated site is written to `.lake/build/doc`; open
`.lake/build/doc/MinSurf/FirstVariation.html` to browse it.

## References

- Manfredo P. do Carmo, *Riemannian Geometry*.
- Tobias H. Colding and William P. Minicozzi II, *A Course in Minimal Surfaces*,
  Graduate Studies in Mathematics, American Mathematical Society.
