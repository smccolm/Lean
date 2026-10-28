import Dubon2026.SourceGammaOneDiamondPicard
import Dubon2026.SourceGammaOneComplexPicardMap

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond/Picard comparison. The exact arithmetic/complex field square and
the proved unique constant-field extension of places force the place
square. The original divisor conorm and Picard map therefore intertwine
the independently defined arithmetic and complex diamonds.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M : ℕ) [NeZero M] (g : Gamma0 M)
local notation "FQ" => functionFieldOver (Gamma1 M) Qbar

theorem liftPlace_comap_diamond (v : Place Qbar FQ) :
    (liftPlace M v).comapEquiv (diamondFieldAut M g) =
      liftPlace M (v.comapEquiv (arithmeticDiamondAut M g)) := by
  apply liftPlace_unique M
  ext x
  change diamondFieldHom M g (fieldMap M x) ∈ (liftPlace M v).toValuationSubring ↔
    arithmeticDiamondHom M g x ∈ v.toValuationSubring
  rw [← fieldMap_arithmeticDiamondHom, mem_liftPlace_iff]

theorem conorm_diamondDivisor (D : Divisor Qbar FQ) :
    conorm M (fieldDivisorEquiv (arithmeticDiamondAut M g).symm D) =
      fieldDivisorEquiv (diamondFieldAut M g).symm (conorm M D) := by
  change Finsupp.mapDomain (liftPlace M)
    (Finsupp.equivMapDomain (Place.placeEquiv (arithmeticDiamondAut M g).symm).symm D) =
      Finsupp.equivMapDomain (Place.placeEquiv (diamondFieldAut M g).symm).symm
        (Finsupp.mapDomain (liftPlace M) D)
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext v
  exact (liftPlace_comap_diamond M g v).symm

theorem complexPicardMap_diamond (x : Pic0 Qbar FQ) :
    complexPicardMap M (arithmeticDiamondPicard M g x) =
      complexDiamondPicard M g (complexPicardMap M x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [arithmeticDiamondPicard_mk, complexPicardMap_mk, complexPicardMap_mk,
    complexDiamondPicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact conorm_diamondDivisor M g D.val

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
