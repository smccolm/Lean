import TaoTrudgianYang2025.SargosRemainderLocalSmooth

/-! Actual normalization of the source sextuple remainder and all required jets. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosRemainderLeft {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℝ :=
  ((sargosSextupleRadius q:ℝ)+1)/M

def sargosRemainderRight {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℝ :=
  ((M:ℝ)-(sargosSextupleRadius q:ℝ))/M

def sargosRemainderWidth (M : ℕ) : ℝ := 1/(8*(M:ℝ))

def sargosNormalizedRemainder {H : ℕ} (f : ℝ → ℝ) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (x : ℝ) : ℝ :=
  sargosSextupleRemainder f q ((M:ℝ)*x)

theorem mem_sargosRemainder_interval {H M : ℕ} (hM : 1 ≤ M)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (x : ℝ) :
    x ∈ Ioo (sargosRemainderLeft M q) (sargosRemainderRight M q) ↔
      (M:ℝ)*x ∈ Ioo ((sargosSextupleRadius q:ℝ)+1)
        ((M:ℝ)-(sargosSextupleRadius q:ℝ)) := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  simp only [mem_Ioo,sargosRemainderLeft,sargosRemainderRight,
    div_lt_iff₀ hM0,lt_div_iff₀ hM0,mul_comm x (M:ℝ)]

theorem sargosNormalizedRemainder_contDiffAt {H M : ℕ} {f : ℝ → ℝ} {x : ℝ}
    (hM : 1 ≤ M) (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y)
    (hx : x ∈ Ioo (sargosRemainderLeft M q) (sargosRemainderRight M q)) :
    ContDiffAt ℝ ∞ (sargosNormalizedRemainder f M q) x := by
  exact (sargosSextupleRemainder_contDiffAt_source q hf
    ((mem_sargosRemainder_interval hM q x).mp hx)).comp x
    (contDiffAt_const.mul contDiffAt_id)

theorem iteratedDeriv_sargosNormalizedRemainder {H M : ℕ} {f : ℝ → ℝ} {x : ℝ}
    (hM : 1 ≤ M) (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y)
    (hx : x ∈ Ioo (sargosRemainderLeft M q) (sargosRemainderRight M q)) (j : ℕ) :
    iteratedDeriv j (sargosNormalizedRemainder f M q) x =
      (M:ℝ)^j*iteratedDeriv j (sargosSextupleRemainder f q) ((M:ℝ)*x) := by
  have hh : ∀ y ∈ Ioo (sargosRemainderLeft M q) (sargosRemainderRight M q),
      ContDiffAt ℝ ∞ (sargosSextupleRemainder f q) ((M:ℝ)*y+0) := by
    intro y hy
    simpa only [add_zero] using sargosSextupleRemainder_contDiffAt_source q hf
      ((mem_sargosRemainder_interval hM q y).mp hy)
  simpa only [add_zero,sargosNormalizedRemainder] using
    sargos_iteratedDeriv_comp_affine_local hh hx j

theorem abs_iteratedDeriv_sargosNormalizedRemainder_le {H M Q : ℕ}
    {f : ℝ → ℝ} {x B : ℝ}
    (hM : 1 ≤ M) (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y)
    (hB : ∀ j ≤ Q+1, ∀ y ∈ Ioo (1:ℝ) M,
      |iteratedDeriv (j+6) f y| ≤ B/(M:ℝ)^j)
    (hx : x ∈ Ioo (sargosRemainderLeft M q) (sargosRemainderRight M q))
    {j : ℕ} (hj : j ≤ Q+1) :
    |iteratedDeriv j (sargosNormalizedRemainder f M q) x| ≤ B*(H:ℝ)^6/60 := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [iteratedDeriv_sargosNormalizedRemainder hM q hf hx,
    abs_mul,abs_of_nonneg (pow_nonneg hM0.le j)]
  calc
    _ ≤ (M:ℝ)^j*((B/(M:ℝ)^j)*(H:ℝ)^6/60) :=
      mul_le_mul_of_nonneg_left
        (abs_iteratedDeriv_sargosSextupleRemainder_source_interior q hf j (hB j hj)
          ((mem_sargosRemainder_interval hM q x).mp hx))
        (pow_nonneg hM0.le j)
    _ = _ := by field_simp

end TaoTrudgianYang2025
