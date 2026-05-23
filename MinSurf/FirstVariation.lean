import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Defs

open Manifold

/-!
Let `F : Σ × (-ε, ε) → M` be a variation of `Σ` with compact support and fixed boundary.

We model:
* the surface domain `Σ` as a manifold `S` (possibly with boundary, model `IS`);
* the ambient space `M` as a manifold (model `I`);
* the time interval `(-ε, ε)` as all of `ℝ`;
* the surface being varied as a base map `f : S → M`.
-/

variable
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    {HS : Type*} [TopologicalSpace HS] (IS : ModelWithCorners ℝ ES HS)
    (S : Type*) [TopologicalSpace S] [ChartedSpace HS S]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (f : S → M)

/-- A smooth variation of the map `f : S → M`, with fixed boundary and compact support.

`toFun p t` is the position of the point `p` of the surface at "time" `t`; at `t = 0` it
recovers `f`. -/
structure Variation where
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
