import Dubon2026.SourceOriginalWeilKummerPointDifference
import Dubon2026.SourceCurvePicardDivisionPrincipal

/-! DUB-17/18 -> finite Weil detection -> norm torsion divisor.
The explicit premise is n-division of the actual cover point-difference
class, the single use of Picard divisibility in NYLL's detecting argument.
The quotient and proved norm/order formula then produce the actual function
and norm divisor. This conditional result does not claim that division exists. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "FF" => modularFunctionFieldOver N L
local notation "E" => Polynomial.SplittingField (X ^ n - C f)

theorem originalWeilKummerDivision_principal (σ : E ≃ₐ[FF] E) (w : Place L E)
    (hdiv : ∃ y : Pic0 L E, n • y = Pic0.mk (originalWeilKummerPointDifference N L n f σ w)) :
    ∃ B : Divisor.degZero (K := L) (F := E), ∃ u : E, u ≠ 0 ∧
      ∀ v, v.ord u = (originalWeilKummerPointDifference N L n f σ w).val v + n * B.val v := by
  exact Pic0.exists_principal_of_nsmul_mk n
    (originalWeilKummerPointDifference N L n f σ w) hdiv

theorem originalWeilKummerDivision_norm_orders (σ : E ≃ₐ[FF] E) (w : Place L E)
    (B : Divisor L E) (u : E) (hu : u ≠ 0)
    (hord : ∀ v, v.ord u = (originalWeilKummerPointDifference N L n f σ w).val v + n * B v) :
    ∀ v : Place L FF, v.ord (Algebra.norm FF u) =
      n * Divisor.geometricPushforward FF B v := by
  let A := originalWeilKummerPointDifference N L n f σ w
  intro v
  have hs : Divisor.geometricPushforward FF (A.val + n • B) v = v.ord (Algebra.norm FF u) := by
    rw [Divisor.geometricPushforward_apply,
      v.ord_norm_eq_sum_fiber (original_place_residue_algebraMap_bijective N L v)
        (originalWeilKummerCover_residue_bijective N L n f) hu]
    apply finsum_congr
    intro q
    simpa only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] using (hord q.val).symm
  rw [map_add, map_nsmul, originalWeilKummerPointDifference_pushforward,
    zero_add, Finsupp.smul_apply, nsmul_eq_mul] at hs
  exact hs.symm

theorem exists_originalWeilKummerDivision_norm_data (σ : E ≃ₐ[FF] E) (w : Place L E)
    (hdiv : ∃ y : Pic0 L E, n • y = Pic0.mk (originalWeilKummerPointDifference N L n f σ w)) :
    ∃ B : Divisor.degZero (K := L) (F := E), ∃ u : E, u ≠ 0 ∧
      (∀ v, v.ord u = (originalWeilKummerPointDifference N L n f σ w).val v + n * B.val v) ∧
      Algebra.norm FF u ≠ 0 ∧
      ∀ v : Place L FF, v.ord (Algebra.norm FF u) =
        n * Divisor.geometricPushforward FF B.val v := by
  obtain ⟨B, u, hu, hord⟩ := originalWeilKummerDivision_principal N L n f σ w hdiv
  exact ⟨B, u, hu, hord, Algebra.norm_ne_zero_iff.mpr hu,
    originalWeilKummerDivision_norm_orders N L n f σ w B.val u hu hord⟩

end
end Dubon2026.SourceFunctionField
