import Dubon2026.SourceRationalHeckeWordRelations
import Mathlib.RingTheory.Localization.Module

/-! DUB-17/18 -> rational rank-two Hecke descent -> faithful scalar
extension of the actual integral operator algebra. A complex relation
gives rational coordinate relations by the proved actual character
realization. Native fraction-ring linear independence removes the need
for a separate denominator-clearing development.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]

theorem sourceOriginalIntegralHecke_linearIndependent_complex {ι : Type*}
    (T : ι → sourceOriginalIntegralHeckeAlgebra N 2) (hT : LinearIndependent ℤ T) :
    LinearIndependent ℂ (fun i => (T i).val) := by
  classical
  choose a ha using fun i => sourceWeightTwoCuspHeckeWord_exists N (T i)
  have hZ : LinearIndependent ℤ (fun i => (T i).val) :=
    hT.map' (sourceOriginalIntegralHeckeAlgebra N 2).val.toLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  letI : Module ℚ (Module.End ℂ (CuspForm (Gamma0 N) 2)) :=
    Module.compHom _ (algebraMap ℚ ℂ)
  have hQ : LinearIndependent ℚ (fun i => (T i).val) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
  rw [linearIndependent_iff']
  intro s c hc i hi
  let bC := Module.Basis.ofVectorSpace ℚ ℂ
  suffices hcoord : ∀ β, bC.repr (c i) β = 0 by
    have hz : bC.repr (c i) = 0 := Finsupp.ext hcoord
    exact bC.repr.injective (hz.trans (map_zero bC.repr).symm)
  intro β
  have hw : ∑ j ∈ s, c j • sourceWeightTwoCuspHeckeWord N (a j) = 0 := by
    simpa only [ha] using hc
  have hy := sourceHeckeWord_relation_coordinate N s c a hw β
  simp only [ha, Rat.cast_smul_eq_qsmul ℂ] at hy
  exact (linearIndependent_iff'.mp hQ) s (fun j => bC.repr (c j) β) hy i hi

end
end Dubon2026
