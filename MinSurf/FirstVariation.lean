import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

open Manifold

/-!
Let `F : Σ × (-ε, ε) → M` be a variation of `Σ` with compact support and fixed boundary.

We model:
* the surface domain `Σ` as a manifold `S` (possibly with boundary, model `IS`);
* the ambient space `M` as a manifold (model `I`);
* the time interval `(-ε, ε)` as all of `ℝ`;
* the surface being varied as a base map `f : S → M`.
-/

-- The ambient manifold data. These are *implicit* so the operations below resolve them from
-- their `Variation` argument (which makes dot notation like `F.inducedMetric` work). The
-- `Variation` structure itself re-declares `IS S I M f` explicitly so the type can be written
-- `Variation IS S I M f`.
variable
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS}
    {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : S → M}

/-- A smooth variation of the map `f : S → M`, with fixed boundary and compact support.

`toFun p t` is the position of the point `p` of the surface at "time" `t`; at `t = 0` it
recovers `f`. -/
structure Variation
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    {HS : Type*} [TopologicalSpace HS] (IS : ModelWithCorners ℝ ES HS)
    (S : Type*) [TopologicalSpace S] [ChartedSpace HS S]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (f : S → M) where
  /-- The underlying map of the variation, `(p, t) ↦ F(p, t)`. -/
  toFun : S → ℝ → M
  /-- `F` is smooth as a map on the product `S × ℝ`. -/
  contMDiff : ContMDiff (IS.prod 𝓘(ℝ, ℝ)) I ⊤ (fun p : S × ℝ => toFun p.1 p.2)
  /-- At time `0` the variation is the original map `f`. -/
  init : ∀ p, toFun p 0 = f p
  /-- The boundary `∂Σ` is fixed throughout the variation. -/
  fixed_boundary : ∀ p ∈ IS.boundary S, ∀ t, toFun p t = f p
  /-- The variation is supported in a compact set: outside some compact `K`, nothing moves. -/
  compact_support : ∃ K : Set S, IsCompact K ∧ ∀ p ∉ K, ∀ t, toFun p t = f p

/-- The variational vector field `X = ∂F/∂t |_{t = 0}` of a variation `F`.

It is a vector field *along* `f`: at each point `p` of the surface it returns the velocity
at `t = 0` of the curve `t ↦ F(p, t)`, an element of the tangent space `T_{f p} M`. -/
noncomputable def Variation.variationField
    (F : Variation IS S I M f) (p : S) : TangentSpace I (f p) :=
  F.init p ▸ mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => F.toFun p t) 0 (1 : ℝ)

open Bundle

-- Endow the ambient manifold `M` with a Riemannian metric `g`: an inner product
-- `⟪·, ·⟫ = inner ℝ · ·` on each tangent space `T_x M`, varying smoothly with `x`.
-- `[IsManifold I 1 M]` ensures the tangent bundle (hence the fibre inner products) is well behaved.
variable [IsManifold I 1 M] [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- The components of the (time-dependent) induced metric on `Σ` along the variation `F`.

Fix local coordinates `xⁱ` on `Σ` near `p`; the coordinate vector fields `∂_{xⁱ}` correspond to
tangent vectors `v, w : T_p Σ`. Pushing them forward by `F(·, t)` gives `F_{xⁱ} = dF_t(∂_{xⁱ})`,
and the induced metric coefficients are

`g_{ij}(t) = g(F_{xⁱ}, F_{xʲ}) = ⟪dF_t(∂_{xⁱ}), dF_t(∂_{xʲ})⟫`.

This is the coordinate-free pairing `(v, w) ↦ ⟪dF_t v, dF_t w⟫`; the `g_{ij}(t)` are its values
on the coordinate basis. -/
noncomputable def Variation.inducedMetric
    (F : Variation IS S I M f) (p : S) (t : ℝ) (v w : TangentSpace IS p) : ℝ :=
  inner ℝ
    (mfderiv IS I (fun q : S => F.toFun q t) p v)
    (mfderiv IS I (fun q : S => F.toFun q t) p w)

-- A coordinate frame on `Σ`: a (finite) basis `b` of the model space `ES ≃ T_p Σ`,
-- whose vectors `b i` play the role of the coordinate fields `∂_{xⁱ}`.
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix `(g_{ij}(t))` of induced-metric coefficients of the variation `F` at time `t`,
expressed in the coordinate frame `b`: `g_{ij}(t) = ⟪dF_t(b i), dF_t(b j)⟫`. -/
noncomputable def Variation.metricMatrix
    (F : Variation IS S I M f) (b : Module.Basis ι ℝ ES) (p : S) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => F.inducedMetric p t (b i) (b j)

/-- The coordinate frame `b` is *orthonormal* for `F` at `p` if the induced metric at time `0` is
the identity matrix, i.e. `g_{ij}(0) = δ_{ij}`. Equivalently, the pushforwards `df(b i) = dF₀(b i)`
form an orthonormal frame of the tangent space `T_{f p} M`. -/
def Variation.IsOrthonormalFrame
    (F : Variation IS S I M f) (b : Module.Basis ι ℝ ES) (p : S) : Prop :=
  F.metricMatrix b p 0 = 1

omit [IsManifold I 1 M] [Fintype ι] in
/-- For an orthonormal frame the time-`0` metric coefficients are the Kronecker delta:
`g_{ij}(0) = δ_{ij}`. -/
theorem Variation.IsOrthonormalFrame.metricMatrix_apply
    {F : Variation IS S I M f} {b : Module.Basis ι ℝ ES} {p : S}
    (h : F.IsOrthonormalFrame b p) (i j : ι) :
    F.metricMatrix b p 0 i j = if i = j then 1 else 0 := by
  rw [h, Matrix.one_apply]

/-- The relative area density of the variation `F` at `p`, in the coordinate frame `b`:

`ν(t) = √(det g_{ij}(t)) · √(det g^{ij}(0))`,

where `g^{ij}(0)` is the inverse metric `(g_{ij}(0))⁻¹` at time `0`. It is the ratio of the area
element of the induced metric at time `t` to that at time `0`, so `ν(0) = 1`. -/
noncomputable def Variation.areaDensity
    (F : Variation IS S I M f) (b : Module.Basis ι ℝ ES) (p : S) (t : ℝ) : ℝ :=
  Real.sqrt (F.metricMatrix b p t).det * Real.sqrt ((F.metricMatrix b p 0)⁻¹).det

open MeasureTheory

-- To integrate over `Σ` we need a measure; `μ` plays the role of the coordinate Lebesgue
-- measure `dx`, against which `√(det g_{ij}(0))` is the reference area element.
variable [MeasurableSpace S]

/-- The volume (area) of the time-`t` surface `F(Σ, t)`, in the coordinate frame `b` and with
respect to the background measure `μ` on `Σ`:

`Vol(F(Σ, t)) = ∫_Σ ν(t) · √(det g_{ij}(0)) dμ`.

Since `ν(t) = √(det g_{ij}(t)) · √(det g^{ij}(0))`, the integrand is the time-`t` area element
`√(det g_{ij}(t))`; at `t = 0` it reduces to `Vol(F(Σ, 0)) = ∫_Σ √(det g_{ij}(0)) dμ`. -/
noncomputable def Variation.volume
    (F : Variation IS S I M f) (b : Module.Basis ι ℝ ES) (μ : Measure S) (t : ℝ) : ℝ :=
  ∫ p, F.areaDensity b p t * Real.sqrt (F.metricMatrix b p 0).det ∂μ

open Filter
open scoped Topology

omit [IsManifold I 1 M] in
/-- **First variation of volume — differentiation under the integral sign.**

Under the standard hypotheses of the Leibniz rule — for a.e. point the area density
`t ↦ ν(t)(p)` is differentiable throughout a neighbourhood `s` of `0`, with a `μ`-integrable
dominating bound on its derivative, and the time-`0` integrand and the derivative integrand are
measurable/integrable — the `t`-derivative of the volume passes inside the integral:

`d/dt|₀ Vol(F(Σ, t)) = ∫_Σ (d/dt|₀ ν(t)) · √(det g_{ij}(0)) dμ`.

The factor `√(det g_{ij}(0))` is constant in `t`, so it survives as the fixed reference area
element while the derivative falls on `ν(t)`. -/
theorem Variation.deriv_volume
    (F : Variation IS S I M f) (b : Module.Basis ι ℝ ES) (μ : Measure S)
    {bound : S → ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 (0 : ℝ))
    (hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun p => F.areaDensity b p t * Real.sqrt (F.metricMatrix b p 0).det) μ)
    (hF_int : Integrable
      (fun p => F.areaDensity b p 0 * Real.sqrt (F.metricMatrix b p 0).det) μ)
    (hF'_meas : AEStronglyMeasurable
      (fun p => deriv (fun t => F.areaDensity b p t) 0 * Real.sqrt (F.metricMatrix b p 0).det) μ)
    (h_diff : ∀ᵐ p ∂μ, ∀ t ∈ s, DifferentiableAt ℝ (fun t => F.areaDensity b p t) t)
    (h_bound : ∀ᵐ p ∂μ, ∀ t ∈ s,
      ‖deriv (fun t => F.areaDensity b p t) t * Real.sqrt (F.metricMatrix b p 0).det‖ ≤ bound p)
    (bound_integrable : Integrable bound μ) :
    deriv (fun t => F.volume b μ t) 0
      = ∫ p, deriv (fun t => F.areaDensity b p t) 0 * Real.sqrt (F.metricMatrix b p 0).det ∂μ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable
    (h_diff.mono fun _ hp t ht => ((hp t ht).hasDerivAt).mul_const _)).2.deriv
