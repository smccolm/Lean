import Dubon2026.SourceOriginalIntegralPrincipalDifference
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> Hecke compatibility on finite Tate layers.
Agreement on integral Laurent principal divisors implies agreement on all
principal divisors by the actual primitive fraction formula. A torsion class
has a principal nonzero multiple; the target integer divisor group is
torsion free. This avoids the stronger global Picard-divisibility route. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
local notation "L" => AlgebraicClosure ℚ
variable (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldOver N L
local notation "kk" => IsLocalRing.ResidueField A
local notation "Db" => Divisor kk (modularFunctionFieldCoeff N kk)

theorem original_divisor_hom_eq_on_principal
    (T S : Divisor L FF →+ Db)
    (hint : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
      coeffMap (IsLocalRing.residue A) y ≠ 0 →
        T (originalPrincipalDivisor N L ⟨coeffMap A.subtype y, hy⟩) =
          S (originalPrincipalDivisor N L ⟨coeffMap A.subtype y, hy⟩))
    (D : Divisor L FF) (hD : Divisor.IsPrincipal D) : T D = S D := by
  obtain ⟨f, hf, hDf⟩ := hD
  have hD' : D = originalPrincipalDivisor N L f := by
    ext P
    exact hDf P
  obtain ⟨x, y, hx, hy, hrx, hry, he⟩ := original_principal_divisor_integral_difference A N f hf
  rw [hD', he, map_sub, map_sub, hint x hx hrx, hint y hy hry]

theorem original_divisor_hom_eq_on_torsion
    (T S : Divisor L FF →+ Db)
    (hint : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
      coeffMap (IsLocalRing.residue A) y ≠ 0 →
        T (originalPrincipalDivisor N L ⟨coeffMap A.subtype y, hy⟩) =
          S (originalPrincipalDivisor N L ⟨coeffMap A.subtype y, hy⟩))
    (D : Divisor.degZero (K := L) (F := FF)) (m : ℕ) (hm : m ≠ 0)
    (hD : m • Pic0.mk D = 0) : T D.val = S D.val := by
  have hp : Divisor.IsPrincipal (m • D.val) :=
    (Pic0.mk_mem_torsion_iff D m).mp (Pic0.mem_torsion_iff.mpr hD)
  have he := original_divisor_hom_eq_on_principal A N T S hint (m • D.val) hp
  rw [map_nsmul, map_nsmul] at he
  exact nsmul_right_injective hm he

end
end Dubon2026.SourceFunctionField
