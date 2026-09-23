import TaoTrudgianYang2025.SargosRemainderExtension

/-! Return the constructed extension to the source's physical variable. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosPhysicalExtendedRemainder {H : ℕ} (f : ℝ → ℝ) (M Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (x : ℝ) : ℝ :=
  sargosExtendedRemainder f M Q q (x/M)

theorem sargosPhysicalExtendedRemainder_contDiff {H M : ℕ} {f : ℝ → ℝ}
    (hM : 1 ≤ M) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ (sargosPhysicalExtendedRemainder f M Q q) :=
  (sargosExtendedRemainder_contDiff hM Q q hf).comp (by fun_prop)

theorem sargosPhysicalExtendedRemainder_agrees {H M : ℕ} (f : ℝ → ℝ)
    (hM : 1 ≤ M) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    sargosPhysicalExtendedRemainder f M Q q m = sargosSextupleRemainder f q m :=
  sargosExtendedRemainder_agrees f hM Q q hm

theorem iteratedDeriv_sargosPhysicalExtendedRemainder {H M : ℕ} {f : ℝ → ℝ}
    (hM : 1 ≤ M) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (sargosPhysicalExtendedRemainder f M Q q) x =
      iteratedDeriv j (sargosExtendedRemainder f M Q q) (x/M)/(M:ℝ)^j := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have he := congrFun (iteratedDeriv_comp_const_mul
    ((sargosExtendedRemainder_contDiff hM Q q hf).of_le hj) ((M:ℝ)⁻¹)) x
  simpa only [sargosPhysicalExtendedRemainder,div_eq_mul_inv,inv_pow,mul_comm] using he

theorem sargosPhysicalExtendedRemainder_uniform_jets (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (f : ℝ → ℝ) (B : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → 0 ≤ B →
      (∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) →
      (∀ j ≤ Q+1, ∀ y ∈ Ioo (1:ℝ) M,
        |iteratedDeriv (j+6) f y| ≤ B/(M:ℝ)^j) →
      ∀ x ∈ Icc (0:ℝ) M, ∀ j ≤ Q,
        |iteratedDeriv j (sargosPhysicalExtendedRemainder f M Q q) x| ≤
          C*(B*(H:ℝ)^6/60)/(M:ℝ)^j := by
  obtain ⟨C,hC,hjets⟩ := sargosExtendedRemainder_uniform_jets Q
  refine ⟨C,hC,?_⟩
  intro H M f B q hM hB hf hb x hx j hj
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hx' : x/(M:ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg hx.1 hM0.le,(div_le_one hM0).mpr hx.2⟩
  rw [iteratedDeriv_sargosPhysicalExtendedRemainder hM Q q hf,
    abs_div,abs_of_nonneg (pow_nonneg hM0.le j)]
  exact div_le_div_of_nonneg_right (hjets H M f B q hM hB hf hb _ hx' j hj)
    (pow_nonneg hM0.le j)

end TaoTrudgianYang2025
