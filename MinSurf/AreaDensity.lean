import MinSurf.FirstVariation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt

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

## What is formalized below

Steps A–D — the analytic core — are formalized in this file, sorry-free:

* `hasDerivAt_det_of_entries` — **Jacobi's formula at the identity** (Steps B–C): for a matrix path
  whose entries are differentiable at `t₀` with `g t₀ = 1`, the determinant is differentiable with
  derivative `tr g'`. Proved directly from the Leibniz expansion `Matrix.det_apply'` and the finite
  product rule, the key combinatorial fact being that every non-identity permutation contributes a
  zero factor (`perm_eq_one_of_forall_ne`).
* `hasDerivAt_sqrt_det_of_entries` — Steps A + B–C–D combined: under the same hypotheses,
  `d/dt|₀ √(det g) = (tr g') / 2`.
* `Variation.deriv_areaDensity` — the geometric payoff, for an orthonormal frame: given that each
  metric entry `t ↦ g_{ij}(t)` is differentiable at `0`,
  `deriv (fun t => F.areaDensity b p t) 0 = (g') .trace / 2`, where `g'_{ij} = d/dt|₀ g_{ij}(t)`.
  Since `g'_{ii} = d/dt|₀ ⟪F_{xⁱ}, F_{xⁱ}⟫`, this is exactly the right-hand side of Step D.

The differentiability of the metric entries is taken as a hypothesis: establishing it from
smoothness of `F` and of the metric is a separate task. Steps E–G (metric compatibility, commuting
derivatives, and the identification with `div_Σ F_t`) require a pullback connection along `F` and a
`div_Σ` definition that neither this repository nor Mathlib currently provides.
-/

open Matrix Finset in
/-- A permutation fixing every point other than a single `i` is the identity: if `σ k = k` for all
`k ≠ i`, then `σ = 1`. (A permutation cannot move exactly one point.) -/
theorem perm_eq_one_of_forall_ne {ι : Type*} [DecidableEq ι] {σ : Equiv.Perm ι} {i : ι}
    (h : ∀ k, k ≠ i → σ k = k) : σ = 1 := by
  ext x
  by_cases hx : σ x = x
  · simp [hx]
  · have hxi : x = i := by by_contra hc; exact hx (h x hc)
    exfalso
    by_cases hsi : σ x = i
    · exact hx (hxi ▸ hsi)
    · exact hx (σ.injective (h (σ x) hsi))

/-- **Jacobi's formula at the identity** (Steps B–C of the area-density computation).

If each entry path `t ↦ (g t) i j` is differentiable at `t₀` with derivative `g' i j`, and
`g t₀ = 1`, then `t ↦ det (g t)` is differentiable at `t₀` with derivative `tr g'`.

The proof expands `det` by the Leibniz formula `Matrix.det_apply'`, differentiates each
permutation's monomial with the finite product rule, and then uses `g t₀ = 1` to kill every
permutation except the identity: a non-identity permutation moves at least two points, so any
product over all-but-one index still contains an off-diagonal — hence zero — factor of `g t₀ = 1`.
-/
theorem hasDerivAt_det_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ℝ → Matrix ι ι ℝ} {g' : Matrix ι ι ℝ} {t₀ : ℝ}
    (hg : ∀ i j, HasDerivAt (fun t => g t i j) (g' i j) t₀)
    (h1 : g t₀ = 1) :
    HasDerivAt (fun t => (g t).det) g'.trace t₀ := by
  have hsum : HasDerivAt (fun t => (g t).det)
      (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, g t₀ (σ j) j) • g' (σ i) i) t₀ := by
    simp only [Matrix.det_apply']
    exact HasDerivAt.fun_sum fun σ _ =>
      (HasDerivAt.fun_finset_prod fun i _ => hg (σ i) i).const_mul _
  have hval : (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, g t₀ (σ j) j) • g' (σ i) i) = g'.trace := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
    · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq]
      have htr : g'.trace = ∑ i, g' i i := by simp [Matrix.trace, Matrix.diag_apply]
      rw [htr]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_eq_one fun j _ => by rw [h1, Matrix.one_apply_eq], one_smul]
    · intro σ _ hσ
      have hz : (∑ i, (∏ j ∈ Finset.univ.erase i, g t₀ (σ j) j) • g' (σ i) i) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        obtain ⟨k, hki, hk⟩ : ∃ k, k ≠ i ∧ σ k ≠ k := by
          by_contra hc; push Not at hc; exact hσ (perm_eq_one_of_forall_ne hc)
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)
          (by rw [h1]; exact Matrix.one_apply_ne hk), zero_smul]
      rw [hz, mul_zero]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  rwa [hval] at hsum

/-- Steps A + B–C–D combined: for a matrix path with `g 0 = 1` and differentiable entries,
`d/dt|₀ √(det (g t)) = (tr g') / 2`. -/
theorem hasDerivAt_sqrt_det_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ℝ → Matrix ι ι ℝ} {g' : Matrix ι ι ℝ}
    (hg : ∀ i j, HasDerivAt (fun t => g t i j) (g' i j) 0)
    (h1 : g 0 = 1) :
    HasDerivAt (fun t => Real.sqrt (g t).det) (g'.trace / 2) 0 := by
  have hdet : HasDerivAt (fun t => (g t).det) g'.trace 0 := hasDerivAt_det_of_entries hg h1
  have hne : (g 0).det ≠ 0 := by rw [h1, Matrix.det_one]; exact one_ne_zero
  have hsqrt := hdet.sqrt hne
  simpa only [h1, Matrix.det_one, Real.sqrt_one, mul_one] using hsqrt

open Manifold Bundle

variable
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS}
    {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : S → M}
    [IsManifold I 1 M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsManifold I 1 M] in
/-- **First variation of the area density, Steps A–D** (orthonormal frame).

If the metric entries `t ↦ g_{ij}(t)` are differentiable at `0` with derivatives `g'_{ij}`, and the
frame `b` is orthonormal at `p` (so `g_{ij}(0) = δ_{ij}`), then

`d/dt|₀ ν(t) = (tr g') / 2`.

Since `g'_{ii} = d/dt|₀ ⟪F_{xⁱ}, F_{xⁱ}⟫`, the right-hand side is `½ ∑ᵢ d/dt|₀ ⟪F_{xⁱ}, F_{xⁱ}⟫`,
exactly the end of Step D in the module docstring. The remaining identification with `div_Σ F_t`
(Steps E–G) needs connection/divergence machinery not yet in the repository. -/
theorem Variation.deriv_areaDensity
    (F : Variation IS S I M f) (b : Module.Basis ι ℝ ES) (p : S)
    (h : F.IsOrthonormalFrame b p) {g' : Matrix ι ι ℝ}
    (hg : ∀ i j, HasDerivAt (fun t => F.metricMatrix b p t i j) (g' i j) 0) :
    deriv (fun t => F.areaDensity b p t) 0 = g'.trace / 2 := by
  have h' : F.metricMatrix b p 0 = 1 := h
  have hconst : Real.sqrt ((F.metricMatrix b p 0)⁻¹).det = 1 := by
    rw [h', inv_one, Matrix.det_one, Real.sqrt_one]
  have hfun : (fun t => F.areaDensity b p t)
      = fun t => Real.sqrt (F.metricMatrix b p t).det := by
    funext t; simp only [Variation.areaDensity, hconst, mul_one]
  rw [hfun]
  exact (hasDerivAt_sqrt_det_of_entries hg h').deriv
