import Dubon2026.SourceOriginalWeilCoverPathPrimitiveData

/-! DUB-17/18 -> cover Abel converse -> regular loop generation -> arbitrary
path-to-jump comparison. Reuse the actual cover coefficient pullback and native
uniqueness of analytic primitives. The original path-atlas argument is adapted
from the already proved original-curve modules and their documented FLT source.
All coordinate and regularity inputs are supplied by the actual dissection. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders


open CellGeometry RadialDissectionPeriods

theorem cover_eventually_gvec_sub {κ : Type*} [Finite κ] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
      (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ),
      CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ →
      ∀ {y : Place ℂ EE} {C C' : D.ιC},
      y ∈ (D.cell C).carrier → y ∈ (D.cell C').carrier →
      ∀ᶠ x in 𝓝 y, gvec D Ψ x C - gvec D Ψ x C' = gvec D Ψ y C - gvec D Ψ y C' := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ hP y C C' hC hC'
  have key : ∀ i, ∀ᶠ x in 𝓝 y, Ψ i C ((D.cell C).ζ x) - Ψ i C' ((D.cell C').ζ x) =
      Ψ i C ((D.cell C).ζ y) - Ψ i C' ((D.cell C').ζ y) := by
    intro i
    have hsrc : ∀ {E : D.ιC}, y ∈ (D.cell E).carrier →
        y ∈ (D.cell E).ζ.source ∧ (D.cell E).ζ y ∈ V E := by
      rintro E ⟨z, hz, rfl⟩
      have ht := (D.cell E).hKt hz
      exact ⟨(D.cell E).ζ.map_target ht, by rw [(D.cell E).ζ.right_inv ht]; exact hP.2.2.1 E hz⟩
    have hη : y.differentialCoeff (η i) ∈ y.toValuationSubring :=
      (mem_cover_regularDifferentials_iff N n radicand (η i)).mp (hP.2.2.2.2 i) y
    have h1 := cover_hasDerivAt_coordPrimitive N n radicand baseDivisor hRadicand hOrders
      (D.cell C).ζ (hsrc hC).1 (hP.1 C y (hsrc hC).1).1 (hP.1 C y (hsrc hC).1).2
      (hP.2.1 C) (hsrc hC).2 (hP.2.2.2.1 i C) hη
    have h2 := cover_hasDerivAt_coordPrimitive N n radicand baseDivisor hRadicand hOrders
      (D.cell C').ζ (hsrc hC').1 (hP.1 C' y (hsrc hC').1).1 (hP.1 C' y (hsrc hC').1).2
      (hP.2.1 C') (hsrc hC').2 (hP.2.2.2.1 i C') hη
    have h3 := cover_eventually_coordPrimitive_sub_eq N n radicand baseDivisor hRadicand hOrders h1 h2
    have hin := placeChart_source_mem_nhds N n radicand baseDivisor hRadicand hOrders y
    filter_upwards [h3, hin] with x hx hxs
    have hback : PF y (PC y x) = x := (PC y).left_inv hxs
    simp only [Function.comp_apply, hback,
      (place_spec N n radicand baseDivisor hRadicand hOrders y).2.1] at hx
    exact hx
  filter_upwards [Filter.eventually_all.2 key] with x hx
  funext i
  exact hx i

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
