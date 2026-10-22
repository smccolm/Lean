import Dubon2026.SourceOriginalFiniteRamification
import Dubon2026.SourceStabilizerMeromorphicOrder
import Dubon2026.SourceGamma0StabilizerIntersection

/-! DUB-17/18 -> numerical modular genus -> exact analytic ramification.
Use the already realized j and jN generators to bound the normalized
analytic multiplicity by both full stabilizers. The actual original
uniformizer has a modular quotient, whose invariance gives the converse
divisibility. This avoids reconstructing modular quotients or assuming
any place-dictionary ramification formula.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem originalAnalyticOrder_jN_sub (N : ℕ) [NeZero N] (τ : ℍ) (c : ℂ) :
    originalAnalyticOrder N τ
      (jNOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =
      meromorphicOrderAt (fun z : ℂ =>
        JMultiplicity.jf (levelRaiseMatrix N • ofComplex z) - c) (τ : ℂ) := by
  unfold originalAnalyticOrder
  apply meromorphicOrderAt_congr
  have he : jNOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c =
      jNOver N ℂ + algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) := by
    rw [map_neg, sub_eq_add_neg]
  rw [he]
  filter_upwards [original_realize_add_eventuallyEq N (jNOver N ℂ)
    (algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c)) τ] with z hz
  have hconst : realize N
      ((algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) : modularFunctionFieldOver N ℂ) :
        LaurentSeries ℂ) (ofComplex z) = -c := realize_algebraMap N (-c) (ofComplex z)
  simpa only [realize_jNOver, hconst, Pi.add_apply,
    sub_eq_add_neg, JMultiplicity.jf] using hz

theorem originalAnalyticRamification_dvd_of_order_eq (N : ℕ) [NeZero N] (τ : ℍ)
    (x : modularFunctionFieldOver N ℂ) (m : ℕ)
    (h : originalAnalyticOrder N τ x = ((m : ℤ) : WithTop ℤ)) :
    originalAnalyticRamification N τ ∣ m := by
  have hx : x ≠ 0 := by
    intro he
    rw [he, originalAnalyticOrder_zero] at h
    exact WithTop.top_ne_coe h
  rw [originalAnalyticPlace_order N τ x hx] at h
  have hi : (originalAnalyticRamification N τ : ℤ) * (originalAnalyticPlace N τ).ord x = m :=
    WithTop.coe_injective h
  have hd : (originalAnalyticRamification N τ : ℤ) ∣ (m : ℤ) := ⟨_, hi.symm⟩
  exact_mod_cast hd

theorem originalAnalyticRamification_dvd_scaled_stabilizer_half (N : ℕ) [NeZero N] (τ : ℍ) :
    originalAnalyticRamification N τ ∣
      Nat.card (MulAction.stabilizer SL(2, ℤ) (levelRaiseMatrix N • τ)) / 2 := by
  let c := JMultiplicity.jf (levelRaiseMatrix N • τ)
  apply originalAnalyticRamification_dvd_of_order_eq N τ
    (jNOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c)
  rw [originalAnalyticOrder_jN_sub,
    meromorphicOrderAt_comp_smul (f := fun w => JMultiplicity.jf w - c)
      (levelRaiseMatrix_det_pos N)]
  exact JMultiplicity.main (levelRaiseMatrix N • τ)

theorem original_stabilizer_card_dvd_two_mul_ramification (N : ℕ) [NeZero N] (τ : ℍ) :
    Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) ∣
      2 * originalAnalyticRamification N τ := by
  let P := originalAnalyticPlace N τ
  obtain ⟨k, g, h, hh, hx⟩ := original_field_modular_ratio N P.uniformizer
  have hF : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z : ℍ,
      g (γ • z) / h (γ • z) = g z / h z := by
    intro γ hγ z
    rw [SlashInvariantForm.slash_action_eqn_SL'' g hγ z,
      SlashInvariantForm.slash_action_eqn_SL'' h hγ z]
    exact mul_div_mul_left _ _ (zpow_ne_zero k (denom_ne_zero _ _))
  have he : meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
      ((originalAnalyticRamification N τ : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr (realize_eventuallyEq_of_ratio g h P.uniformizer hh hx τ)]
    change originalAnalyticOrder N τ P.uniformizer = _
    rw [originalAnalyticPlace_order N τ _ P.uniformizer_ne_zero]
    change (((originalAnalyticRamification N τ : ℤ) * P.ord P.uniformizer : ℤ) : WithTop ℤ) = _
    rw [P.ord_uniformizer, mul_one]
  have hd := SubgroupStabilizer.main (CongruenceSubgroup.Gamma0 N)
    (fun z => g z / h z) hF τ (originalAnalyticRamification N τ) he
  exact_mod_cast hd

theorem original_two_mul_ramification_eq_stabilizer_card (N : ℕ) [NeZero N] (τ : ℍ) :
    2 * originalAnalyticRamification N τ =
      Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by
  apply Nat.dvd_antisymm
  · exact StabilizerCharacter.two_mul_dvd_card_stabilizer_gamma0 N τ _
      (originalAnalyticRamification_pos N τ)
      (originalAnalyticRamification_dvd_full_stabilizer_half N τ)
      (originalAnalyticRamification_dvd_scaled_stabilizer_half N τ)
  · exact original_stabilizer_card_dvd_two_mul_ramification N τ

end
end Dubon2026.SourceFunctionField
