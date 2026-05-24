import MinSurf.FirstVariation

/-!
# First variation of the area density

This module records the pointwise computation underlying the first variation of area:
the `t`-derivative at `0` of the area density `ν(t)` of a `Variation` equals the surface
divergence of the variation field `F_t`. It is the next conceptual step after
`Variation.deriv_volume` (differentiation under the integral sign): there the `t`-derivative was
moved inside the integral onto `ν(t)`; here we evaluate `d/dt|₀ ν(t)` itself.

The statement is, at a point `x ∈ Σ`,
$$\frac{d}{dt}\Big|_{0}\nu(t) = \operatorname{div}_\Sigma F_t.$$

This is currently a **paper proof only**: the repository does not yet have a pullback connection
along `F` or a definition of `div_Σ`, both of which the formal statement (Steps E–G below) would
require. The writeup is kept here as documentation; see the sketch of the eventual Lean statement
at the end.

## Setup and notation

Let `F : Σ × (-ε, ε) → M` be the variation, `g = ⟪·,·⟫` the Riemannian metric on `M`, and `∇` its
Levi-Civita connection pulled back along `F`. Fix `x ∈ Σ` and local coordinates `(x¹, …, xᵏ)` near
`x`, where `k = dim Σ`. Write

* `F_{xⁱ} = dF(∂_{xⁱ})` — pushforward of the `i`-th coordinate field (a vector field along `F`);
* `F_t = dF(∂_t)` — the variation field;
* `g_{ij}(t) = ⟪F_{xⁱ}, F_{xʲ}⟫` evaluated at `(x, t)` — i.e. `Variation.metricMatrix b x t i j`;
* `ν(t) = √(det(g_{ij}(t)))` — the area density, here normalized so that `√(det g(0)) = 1`.

**Two standing facts.**

**(1) Orthonormal normalization at `x`.** We choose coordinates so that the frame is orthonormal at
`x` at time `0`:
$$g_{ij}(0) = \delta_{ij}.$$
This is legitimate because `df(∂_{xⁱ}) = F_{xⁱ}|₀` span `T_{f(x)} f(Σ)`, so Gram–Schmidt on the
coordinate basis produces such coordinates. It is exactly `Variation.IsOrthonormalFrame b x`
together with `Variation.IsOrthonormalFrame.metricMatrix_apply`. Both sides of the final identity
are coordinate-free (`ν` is intrinsic; `div_Σ` is defined frame-independently), so proving it at `x`
in one convenient frame proves it.

**(2) Mixed derivatives commute.** Since `∇` is torsion-free and `[∂_t, ∂_{xⁱ}] = 0`,
$$\nabla_{F_t} F_{x^i} - \nabla_{F_{x^i}} F_t = dF([\partial_t, \partial_{x^i}]) = 0,
  \qquad\text{i.e.}\qquad \nabla_{F_t} F_{x^i} = \nabla_{F_{x^i}} F_t.$$

## Computation

**Step A — chain rule for `√·`.**
By (1), `det g(0) = 1 > 0`, so by continuity `det g(t) > 0` near `0` and `t ↦ √(det g(t))` is
differentiable there. The chain rule gives
$$\frac{d}{dt}\Big|_{0}\nu(t)
  = \tfrac12 (\det g(0))^{-1/2}\, \frac{d}{dt}\Big|_{0}\det g(t)
  = \tfrac12 \frac{d}{dt}\Big|_{0}\det g(t),$$
since the prefactor `(det g(0))^{-1/2} = 1` **by (1)** (this uses only `det g(0) = 1`, i.e.
`Variation.IsOrthonormalFrame.det_metricMatrix_zero`).

**Step B — Jacobi's formula.**
For a differentiable matrix path `A(t)`, `d/dt det A(t) = tr(adj(A(t)) · A'(t))`. With `A = g`:
$$\frac{d}{dt}\Big|_{0}\det g(t) = \operatorname{tr}\!\big(\operatorname{adj}(g(0))\, g'(0)\big).$$

**Step C — adjugate becomes the inverse, then the identity.**
Since `det g(0) = 1 ≠ 0`, `g(0)` is invertible and `adj(g(0)) = det g(0) · g(0)⁻¹ = g(0)⁻¹ =
(g^{lm}(0))` (the identity `g^{lm}(t) = (1/det g(t)) · adj(g_{ij}(t))`). By orthonormality (1),
`g(0) = I`, hence `g(0)⁻¹ = I`, so
$$\frac{d}{dt}\Big|_{0}\det g(t)
  = \operatorname{tr}\!\big(g(0)^{-1} g'(0)\big)
  = \operatorname{tr}\!\big(I \cdot g'(0)\big)
  = \operatorname{tr}\big(g'(0)\big),$$
and therefore
$$\frac{d}{dt}\Big|_{0}\nu(t) = \tfrac12 \operatorname{tr}\big(g'(0)\big).$$

**Step D — trace = sum of diagonal-component derivatives.**
By definition of trace, `tr(g'(0)) = Σᵢ g'_{ii}(0)`. Here `g'_{ii}(0)` is the `t`-derivative at `0`
of the `(i,i)` entry of the metric matrix. Taking a fixed matrix entry is a fixed coordinate
projection — a bounded linear map — so it commutes with `d/dt`:
$$g'_{ii}(0) = \frac{d}{dt}\Big|_{0} g_{ii}(t)
  = \frac{d}{dt}\Big|_{0} \langle F_{x^i}, F_{x^i}\rangle.$$
Hence
$$\frac{d}{dt}\Big|_{0}\nu(t)
  = \tfrac12 \sum_{i=1}^{k} \frac{d}{dt}\Big|_{0} \langle F_{x^i}, F_{x^i}\rangle.$$
(Dropping the explicit `|₀` is purely notational: every `d/dt` below is at `t = 0`, at the point
`x`.)

**Step E — metric compatibility.**
`∇` is the Levi-Civita connection, hence compatible with `g`. Differentiating in the `∂_t`
direction, with `V = W = F_{xⁱ}`,
$$\frac{d}{dt} \langle F_{x^i}, F_{x^i}\rangle = 2 \langle \nabla_{F_t} F_{x^i}, F_{x^i}\rangle.$$
The `½` cancels the `2`:
$$\frac{d}{dt}\Big|_{0}\nu(t)
  = \sum_{i=1}^{k} \langle \nabla_{F_t} F_{x^i}, F_{x^i}\rangle\Big|_{t=0}.$$

**Step F — commute the derivatives (fact (2)).**
Replacing `∇_{F_t} F_{xⁱ}` by `∇_{F_{xⁱ}} F_t`,
$$\frac{d}{dt}\Big|_{0}\nu(t)
  = \sum_{i=1}^{k} \langle \nabla_{F_{x^i}} F_t, F_{x^i}\rangle\Big|_{t=0}.$$

**Step G — identify with the surface divergence.**
At `t = 0` and the point `x`, fact (1) says the vectors `eᵢ := F_{xⁱ}|₀` form an orthonormal basis
of `T_x Σ` (inside `T_{f(x)} M`). The surface divergence of `F_t` along `Σ` is, in any orthonormal
frame,
$$\operatorname{div}_\Sigma F_t = \sum_{i=1}^{k} \langle \nabla_{e_i} F_t, e_i\rangle.$$
The orthonormal choice (1) is precisely what turns the trace of Step C into this bare sum.
Therefore, at `x`,
$$\frac{d}{dt}\Big|_{0}\nu(t) = \operatorname{div}_\Sigma F_t. \qquad \blacksquare$$

## Where orthonormality (1) is used

1. **Step A** — kills the prefactor `(det g(0))^{-1/2} = 1`. Only needs `det g(0) = 1`
   (`det_metricMatrix_zero`).
2. **Step C** — gives `g(0)⁻¹ = I` so the trace is `tr(g'(0))`. Needs full `g(0) = I`
   (`IsOrthonormalFrame`).
3. **Step G** — makes `{eᵢ}` orthonormal so the sum *is* `div_Σ F_t`. Needs full `g(0) = I`.

## Sketch of the eventual Lean statement

With a pullback connection `∇` along `F` and a `Variation.surfaceDivergence` in hand, the lemma
would read roughly:

```
theorem Variation.deriv_areaDensity
    (F : Variation IS S I M f) (b : Module.Basis ι ℝ ES) (p : S)
    (h : F.IsOrthonormalFrame b p) :
    deriv (fun t => F.areaDensity b p t) 0 = F.surfaceDivergence b p (F.variationField p)
```

Steps A–D are accessible from current Mathlib (derivative of `Real.sqrt`, `Matrix.det` via
`Matrix.deriv_det`/Jacobi, `Matrix.adjugate_eq` and orthonormality). Steps E–G need the connection
and divergence machinery that the repository does not yet provide.
-/
