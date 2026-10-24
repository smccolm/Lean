import Dubon2026.SourceEllipticCharThreePermutationData
import Dubon2026.SourceEllipticCharThreePlaceClassification
import Dubon2026.SourceDihedralThreeCensus

/-! The source characteristic-three census on the actual modular
coefficient field. Every geometric and action input is derived. The
finite set has exactly the source positive-j membership condition.
This supplies the weighted order counts needed by the DUB-17/18 wild
differential contribution and characteristic-three genus comparison. -/
namespace Dubon2026.SourceFunctionField
open SourceCurve SourceEllipticExceptional SourceEllipticDivisionField
open SourceEllipticStabilizer SourceLevelProjective
noncomputable section

theorem coeff_char_three_order_census_with_closure
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 3] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jCoeff N K)) :
    (∀ v ∈ S, v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 2 ∨
      v.ord (jCoeff N K) = 3 ∨ v.ord (jCoeff N K) = 6) ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3).card = nuTwo N ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1).card +
      2 * (S.filter fun v => v.ord (jCoeff N K) = 2).card = nuThree N := by
  classical
  let E₀ := EA (-1 : K)
  letI : E₀.IsElliptic := isElliptic_EA_neg_one_of_char_three
  let X := {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}
  have hcard : Nat.card X = dedekindPsi N := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality (F := K) (K := K) E₀ hNK
  haveI : Finite X := Nat.finite_of_card_ne_zero
    (hcard.trans_ne (ne_of_gt (dedekindPsi_pos (NeZero.ne N))))
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  have hu₀0 : u₀ ≠ 0 := by rintro rfl; simp at hu₀
  let u : Kˣ := Units.mk0 u₀ hu₀0
  have hu : (u : K) ^ 2 = -1 := hu₀
  let a := cyclicSubgroupEquiv N (stabilizerPointEquiv E₀ ⟨u, 0, 0, 0⟩
    (quartic_change_fixes u hu (-1)))
  let b := cyclicSubgroupEquiv N (charThreeTranslation (K := K))
  obtain ⟨ha, hb, hab, hfixa, hfixb⟩ := char_three_cyclic_permutation_data N hNK u hu
  obtain ⟨f, hsurj, hrel, hord⟩ := exists_char_three_cyclic_modular_place_classification K Ω N hNK
  let c : X → Place K (modularFunctionFieldCoeff N K) := fun H => (f H).val
  have hc (H T : X) : c H = c T ↔
      (T = H ∨ T = a H ∨ T = b H ∨ T = b (b H) ∨ T = a (b H) ∨ T = a (b (b H))) := by
    change (f H).val = (f T).val ↔ _
    rw [← Subtype.ext_iff, hrel H T]
    exact char_three_cyclic_stabilizer_related_iff_six N (NeZero.ne N) u hu H T
  have himage (v) : v ∈ S ↔ ∃ H, c H = v := by
    constructor
    · intro hv
      obtain ⟨H, hH⟩ := hsurj ⟨v, (hS v).mp hv⟩
      exact ⟨H, congrArg Subtype.val hH⟩
    · rintro ⟨H, rfl⟩
      exact (hS _).mpr (f H).property
  obtain ⟨hsize, hodd, hsmall⟩ := SourceDihedralThree.orbit_census a b ha hb hab c hc S himage
  have hordF (H : X) : (c H).ord (jCoeff N K) =
      ((Finset.univ.filter fun T : X => c T = c H).card : ℤ) := by
    have he : Nat.card {T : X // SourceEllipticStabilizer.cyclicStabilizerRelated E₀ H.val T.val} =
        Nat.card {T : X // c T = c H} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun T =>
        (hrel H T).symm.trans (Subtype.ext_iff.trans eq_comm))
    change (f H).val.ord (jCoeff N K) = _
    rw [hord H, he, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfa : (Finset.univ.filter fun H : X => a H = H).card = nuTwo N := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hfixa
  have hfb : (Finset.univ.filter fun H : X => b H = H).card = nuThree N := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hfixb
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨H, rfl⟩ := (himage v).mp hv
    rw [hordF]
    exact_mod_cast hsize H
  · have he : (S.filter fun v => v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3) =
        S.filter fun v => (Finset.univ.filter fun H : X => c H = v).card = 1 ∨
          (Finset.univ.filter fun H : X => c H = v).card = 3 := by
      apply Finset.filter_congr
      intro v hv
      obtain ⟨H, rfl⟩ := (himage v).mp hv
      rw [hordF]
      norm_cast
    rw [he, hodd, hfa]
  · have he1 : (S.filter fun v => v.ord (jCoeff N K) = 1) =
        S.filter fun v => (Finset.univ.filter fun H : X => c H = v).card = 1 := by
      apply Finset.filter_congr
      intro v hv
      obtain ⟨H, rfl⟩ := (himage v).mp hv
      rw [hordF]
      norm_cast
    have he2 : (S.filter fun v => v.ord (jCoeff N K) = 2) =
        S.filter fun v => (Finset.univ.filter fun H : X => c H = v).card = 2 := by
      apply Finset.filter_congr
      intro v hv
      obtain ⟨H, rfl⟩ := (himage v).mp hv
      rw [hordF]
      norm_cast
    rw [he1, he2, hsmall, hfb]

theorem coeff_char_three_order_census
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    [CharP K 3] (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jCoeff N K)) :
    (∀ v ∈ S, v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 2 ∨
      v.ord (jCoeff N K) = 3 ∨ v.ord (jCoeff N K) = 6) ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3).card = nuTwo N ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1).card +
      2 * (S.filter fun v => v.ord (jCoeff N K) = 2).card = nuThree N := by
  classical
  exact coeff_char_three_order_census_with_closure K (AlgebraicClosure (RatFunc K)) N hNK S hS

end
end Dubon2026.SourceFunctionField
