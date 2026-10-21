import Dubon2026.SourceCurveCanonicalDegree
import Dubon2026.SourceOriginalRegularFinite

/-! DUB-17/18 -> regular differential dimension -> the source genus.
The genus uses the actual canonical degree. Its expression at D(j) is
proved independent of all choices; the numerical modular-curve formula
and its equality with regular differential dimension remain open.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The source genus of the literal original modular function field. -/
def originalGenus : ℕ :=
  letI := hasCanonicalDivisor_original N L
  genus L (modularFunctionFieldOver N L)

theorem originalGenus_eq_jCanonical_degree [IsAlgClosed L] :
    originalGenus N L =
      (Divisor.degree (originalCanonicalDivisor N L (D_jOver_ne_zero N L)) + 2).toNat / 2 := by
  haveI : IsCurveOver L (modularFunctionFieldOver N L) := isCurveOver_original N L
  haveI : HasCanonicalDivisor (K := L) (F := modularFunctionFieldOver N L) :=
    hasCanonicalDivisor_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  have hD : canonicalDivisorOf (D_jOver_ne_zero N L) =
      originalCanonicalDivisor N L (D_jOver_ne_zero N L) := by
    ext v
    rw [canonicalDivisorOf_apply, originalCanonicalDivisor_apply]
  change genus L (modularFunctionFieldOver N L) = _
  rw [genus_eq_canonical_degree (D_jOver_ne_zero N L), hD]

theorem degree_originalCanonicalDivisor_eq_j [IsAlgClosed L]
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    Divisor.degree (originalCanonicalDivisor N L hω) =
      Divisor.degree (originalCanonicalDivisor N L (D_jOver_ne_zero N L)) := by
  haveI : IsCurveOver L (modularFunctionFieldOver N L) := isCurveOver_original N L
  haveI : HasCanonicalDivisor (K := L) (F := modularFunctionFieldOver N L) :=
    hasCanonicalDivisor_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  have hD : ∀ {η : Ω[modularFunctionFieldOver N L⁄L]} (hη : η ≠ 0),
      canonicalDivisorOf hη = originalCanonicalDivisor N L hη := by
    intro η hη
    ext v
    rw [canonicalDivisorOf_apply, originalCanonicalDivisor_apply]
  rw [← hD hω, ← hD (D_jOver_ne_zero N L)]
  exact degree_canonicalDivisorOf_eq hω (D_jOver_ne_zero N L)

end
end Dubon2026.SourceFunctionField
