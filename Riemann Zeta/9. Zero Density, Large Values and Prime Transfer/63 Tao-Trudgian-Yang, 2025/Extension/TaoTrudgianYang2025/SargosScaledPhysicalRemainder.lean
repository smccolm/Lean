import TaoTrudgianYang2025.SargosScaledRemainderExtension

/-! Physical jets of the constructed real-scale extension throughout [-N,N]. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosScaledPhysicalRemainder {H : ℕ} (f : ℝ → ℝ) (M : ℕ) (N : ℝ) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (x : ℝ) : ℝ :=
  sargosScaledExtendedRemainder f M N Q q (x/N)

theorem sargosScaledPhysicalRemainder_contDiff {H M : ℕ} {N : ℝ} {f : ℝ → ℝ}
    (hN : 0 < N) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ (sargosScaledPhysicalRemainder f M N Q q) :=
  (sargosScaledExtendedRemainder_contDiff hN Q q hf).comp (by fun_prop)

theorem sargosScaledPhysicalRemainder_agrees {H M : ℕ} {N : ℝ} (f : ℝ → ℝ)
    (hN : 0 < N) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    sargosScaledPhysicalRemainder f M N Q q m = sargosSextupleRemainder f q m :=
  sargosScaledExtendedRemainder_agrees f hN Q q hm

theorem iteratedDeriv_sargosScaledPhysicalRemainder {H M : ℕ} {N : ℝ} {f : ℝ → ℝ}
    (hN : 0 < N) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (sargosScaledPhysicalRemainder f M N Q q) x =
      iteratedDeriv j (sargosScaledExtendedRemainder f M N Q q) (x/N)/N^j := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have he := congrFun (iteratedDeriv_comp_const_mul
    ((sargosScaledExtendedRemainder_contDiff hN Q q hf).of_le hj) N⁻¹) x
  simpa only [sargosScaledPhysicalRemainder,div_eq_mul_inv,inv_pow,mul_comm] using he

theorem sargosScaledPhysicalRemainder_uniform_jets (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (N : ℝ) (f : ℝ → ℝ) (B : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → (M:ℝ) ≤ N → 0 ≤ B →
      (∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) →
      (∀ j ≤ Q+1, ∀ y ∈ Ioo (1:ℝ) M, |iteratedDeriv (j+6) f y| ≤ B/N^j) →
      ∀ x ∈ Icc (-N) N, ∀ j ≤ Q,
        |iteratedDeriv j (sargosScaledPhysicalRemainder f M N Q q) x| ≤
          C*(B*(H:ℝ)^6/60)/N^j := by
  obtain ⟨C,hC,hjets⟩ := sargosScaledExtendedRemainder_uniform_jets Q
  refine ⟨C,hC,?_⟩
  intro H M N f B q hM hMN hB hf hb x hx j hj
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN : 0 < N := zero_lt_one.trans_le (hM1.trans hMN)
  have hx' : x/N ∈ Icc (-1:ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hN).mpr
      linarith [hx.1]
    · exact (div_le_one hN).mpr hx.2
  rw [iteratedDeriv_sargosScaledPhysicalRemainder hN Q q hf,
    abs_div,abs_of_nonneg (pow_nonneg hN.le j)]
  exact div_le_div_of_nonneg_right (hjets H M N f B q hM hMN hB hf hb _ hx' j hj)
    (pow_nonneg hN.le j)

end TaoTrudgianYang2025
