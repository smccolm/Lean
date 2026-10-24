import Dubon2026.SourceDihedralCubicNonscalar
import Dubon2026.SourceEllipticCharThreeConjugation
import Dubon2026.SourceEllipticQuadraticFixedCounts

/-! The actual characteristic-three cubic automorphism fixes exactly
nuThree(N) cyclic subgroups. Its quadratic identity, conjugation relation
and prime-torsion nonscalarity are all derived, using the existing actual
elliptic torsion structure. This closes the cubic fixed-point input to
the DUB-17/18 characteristic-three exceptional-fiber census. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer SourceQuadraticCyclicCount
open SourceLevelProjective
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] [CharP K 3]

theorem char_three_translation_fixed_cyclic_count (N : ℕ) (hNK : (N : K) ≠ 0) :
    Nat.card {H : AddSubgroup (EA (-1 : K)).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N ∧
        H.map (charThreeTranslation (K := K)).toAddMonoidHom = H} = nuThree N := by
  haveI : (EA (-1 : K)).IsElliptic := isElliptic_EA_neg_one_of_char_three
  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  have hu₀0 : u₀ ≠ 0 := by rintro rfl; simp at hu₀
  let u : Kˣ := Units.mk0 u₀ hu₀0
  have hu : (u : K) ^ 2 = -1 := hu₀
  let α := stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu (-1))
  apply elliptic_stable_cyclic_card_eq_nuThree (EA (-1 : K)) N hNK
    (charThreeTranslation (K := K)).toAddMonoidHom charThreeTranslation_quadratic
  intro p hp hpN
  have hpK : (p : K) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hpN
    intro h0
    apply hNK
    push_cast
    rw [h0, zero_mul]
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hpK (CharP.cast_eq_zero K 3)
  obtain ⟨e⟩ : Nonempty (ZMod p × ZMod p ≃+
      Submodule.torsionBy ℤ (EA (-1 : K)).toAffine.Point p) := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id] using
      SourceEllipticTorsionStructure.actual_torsion_structure (EA (-1 : K)) hpK
  exact cubic_nonscalar_of_dihedral_relations α (charThreeTranslation (K := K)).toAddMonoidHom
    charThreeTranslation_quadratic (fun T => charThreeTranslation_conjugation u hu T) p hp hp3 e

end
end Dubon2026.SourceEllipticExceptional
