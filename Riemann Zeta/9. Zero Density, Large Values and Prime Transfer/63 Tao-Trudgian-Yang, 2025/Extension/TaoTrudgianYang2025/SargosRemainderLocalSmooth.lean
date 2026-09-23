import TaoTrudgianYang2025.SargosLocalAffineJets

/-! Actual local smoothness of the six-term remainder inside its source support. -/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem sargosTupleRemainder_contDiffAt_of_points {H : ℕ} {f : ℝ → ℝ} {m : ℝ}
    (t : SargosInitialMomentTuple H 3)
    (hp : ∀ i, ContDiffAt ℝ ∞ f (m+((t i:ℤ):ℝ)))
    (hm : ∀ i, ContDiffAt ℝ ∞ f (m-((t i:ℤ):ℝ)))
    (hc : ContDiffAt ℝ ∞ f m) :
    ContDiffAt ℝ ∞ (sargosTupleRemainder f t) m := by
  apply ContDiffAt.sum
  intro i hi
  exact sargosSymmetricRemainder_contDiffAt (hp i) (hm i) hc

theorem sargosSextupleRemainder_contDiffAt_source {H M : ℕ}
    {f : ℝ → ℝ} {m : ℝ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ x ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f x)
    (hm : m ∈ Ioo ((sargosSextupleRadius q:ℝ)+1) ((M:ℝ)-(sargosSextupleRadius q:ℝ))) :
    ContDiffAt ℝ ∞ (sargosSextupleRemainder f q) m := by
  have hr0 : (0:ℝ) ≤ sargosSextupleRadius q := by
    have hr := (sargosSextupleRadius_bounds q).1
    exact_mod_cast (show 0 ≤ sargosSextupleRadius q by omega)
  have hc : ContDiffAt ℝ ∞ f m := hf m ⟨by linarith [hm.1],by linarith [hm.2]⟩
  have ht (t : SargosInitialMomentTuple H 3) (ht : sargosTupleRadius t ≤ sargosSextupleRadius q) :
      ContDiffAt ℝ ∞ (sargosTupleRemainder f t) m := by
    apply sargosTupleRemainder_contDiffAt_of_points t _ _ hc
    · intro i
      have hn := sargos_tuple_coordinate_bounds t i
      have hnr : ((t i:ℤ):ℝ) ≤ (sargosSextupleRadius q:ℝ) := by
        exact_mod_cast (sargos_tuple_coordinate_le_radius t i).trans ht
      exact hf _ ⟨by linarith [hm.1,hn.1],by linarith [hm.2]⟩
    · intro i
      have hn := sargos_tuple_coordinate_bounds t i
      have hnr : ((t i:ℤ):ℝ) ≤ (sargosSextupleRadius q:ℝ) := by
        exact_mod_cast (sargos_tuple_coordinate_le_radius t i).trans ht
      exact hf _ ⟨by linarith [hm.1],by linarith [hm.2,hn.1]⟩
  exact (ht q.1 (le_max_left _ _)).sub (ht q.2 (le_max_right _ _))

end TaoTrudgianYang2025
