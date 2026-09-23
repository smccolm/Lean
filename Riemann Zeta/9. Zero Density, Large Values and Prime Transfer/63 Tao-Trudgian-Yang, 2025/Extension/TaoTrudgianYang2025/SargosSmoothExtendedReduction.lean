import TaoTrudgianYang2025.SargosExtendedSextuplePhase

/-!
The finite source reduction with its genuinely constructed smooth remainder family.
This is a C-infinity, finite-order uniform-constant variant, not the printed
finite-C-k, constant-one A-bar-four witness theorem.
-/

noncomputable section

open GafniTao Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem sargos_smooth_extended_reduction (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (f : ℝ → ℝ) (B : ℝ),
      1 ≤ H → H ≤ M → 0 ≤ B →
      (∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) →
      (∀ j ≤ Q+1, ∀ y ∈ Ioo (1:ℝ) M,
        |iteratedDeriv (j+6) f y| ≤ B/(M:ℝ)^j) →
      (∀ q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3,
        ContDiff ℝ ∞ (sargosPhysicalExtendedRemainder f M Q q) ∧
        (∀ m ∈ sargosSextupleInterior M q,
          sargosPhysicalExtendedRemainder f M Q q m = sargosSextupleRemainder f q m) ∧
        ∀ x ∈ Icc (0:ℝ) M, ∀ j ≤ Q,
          |iteratedDeriv j (sargosPhysicalExtendedRemainder f M Q q) x| ≤
            C*(B*(H:ℝ)^6/60)/(M:ℝ)^j) ∧
      ‖∑ m ∈ Finset.Ioc (0:ℤ) M, fordAdditiveCharacter (f m)‖^12 ≤
        1492992*((M:ℝ)/H)^6*(M:ℝ)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*sargosExtendedSextupleCorrelation f M H Q+
        C*(M:ℝ)^11*(H:ℝ)^ε := by
  obtain ⟨A,hA,hjets⟩ := sargosPhysicalExtendedRemainder_uniform_jets Q
  obtain ⟨D,hD,hbound⟩ := sargos_character_extended_differencing ε hε
  refine ⟨max A D,hA.trans (le_max_left _ _),?_⟩
  intro H M f B hH hHM hB hf hb
  have hM : 1 ≤ M := hH.trans hHM
  constructor
  · intro q
    refine ⟨sargosPhysicalExtendedRemainder_contDiff hM Q q hf,
      fun m hm => sargosPhysicalExtendedRemainder_agrees f hM Q q hm,?_⟩
    intro x hx j hj
    exact (hjets H M f B q hM hB hf hb x hx j hj).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left A D) (by positivity))
        (pow_nonneg (Nat.cast_nonneg _) j))
  · exact (hbound H hH M hHM f Q).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right A D) (by positivity))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

end TaoTrudgianYang2025
