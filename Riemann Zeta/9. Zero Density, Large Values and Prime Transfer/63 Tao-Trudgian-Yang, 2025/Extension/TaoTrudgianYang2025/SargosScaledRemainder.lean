import TaoTrudgianYang2025.SargosRemainderLocalSmooth

/-! Normalize the actual remainder by the original real phase scale, preserving integer support. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosScaledRemainderLeft {H : ℕ} (N : ℝ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℝ :=
  ((sargosSextupleRadius q:ℝ)+1)/N

def sargosScaledRemainderRight {H : ℕ} (M : ℕ) (N : ℝ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℝ :=
  ((M:ℝ)-(sargosSextupleRadius q:ℝ))/N

def sargosScaledRemainderWidth (N : ℝ) : ℝ := 1/(8*N)

def sargosScaledRemainder {H : ℕ} (f : ℝ → ℝ) (N : ℝ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (x : ℝ) : ℝ :=
  sargosSextupleRemainder f q (N*x)

theorem mem_sargosScaledRemainder_interval {H : ℕ} {N : ℝ} (hN : 0 < N) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (x : ℝ) :
    x ∈ Ioo (sargosScaledRemainderLeft N q) (sargosScaledRemainderRight M N q) ↔
      N*x ∈ Ioo ((sargosSextupleRadius q:ℝ)+1)
        ((M:ℝ)-(sargosSextupleRadius q:ℝ)) := by
  simp only [mem_Ioo,sargosScaledRemainderLeft,sargosScaledRemainderRight,
    div_lt_iff₀ hN,lt_div_iff₀ hN,mul_comm x N]

theorem sargosScaledRemainder_contDiffAt {H M : ℕ} {N : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hN : 0 < N) (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y)
    (hx : x ∈ Ioo (sargosScaledRemainderLeft N q) (sargosScaledRemainderRight M N q)) :
    ContDiffAt ℝ ∞ (sargosScaledRemainder f N q) x :=
  (sargosSextupleRemainder_contDiffAt_source q hf
    ((mem_sargosScaledRemainder_interval hN M q x).mp hx)).comp x
    (contDiffAt_const.mul contDiffAt_id)

theorem iteratedDeriv_sargosScaledRemainder {H M : ℕ} {N : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hN : 0 < N) (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y)
    (hx : x ∈ Ioo (sargosScaledRemainderLeft N q) (sargosScaledRemainderRight M N q)) (j : ℕ) :
    iteratedDeriv j (sargosScaledRemainder f N q) x =
      N^j*iteratedDeriv j (sargosSextupleRemainder f q) (N*x) := by
  have hh : ∀ y ∈ Ioo (sargosScaledRemainderLeft N q) (sargosScaledRemainderRight M N q),
      ContDiffAt ℝ ∞ (sargosSextupleRemainder f q) (N*y+0) := by
    intro y hy
    simpa only [add_zero] using sargosSextupleRemainder_contDiffAt_source q hf
      ((mem_sargosScaledRemainder_interval hN M q y).mp hy)
  simpa only [add_zero,sargosScaledRemainder] using
    sargos_iteratedDeriv_comp_affine_local hh hx j

theorem abs_iteratedDeriv_sargosScaledRemainder_le {H M Q : ℕ}
    {N : ℝ} {f : ℝ → ℝ} {x B : ℝ}
    (hN : 0 < N) (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y)
    (hB : ∀ j ≤ Q+1, ∀ y ∈ Ioo (1:ℝ) M, |iteratedDeriv (j+6) f y| ≤ B/N^j)
    (hx : x ∈ Ioo (sargosScaledRemainderLeft N q) (sargosScaledRemainderRight M N q))
    {j : ℕ} (hj : j ≤ Q+1) :
    |iteratedDeriv j (sargosScaledRemainder f N q) x| ≤ B*(H:ℝ)^6/60 := by
  rw [iteratedDeriv_sargosScaledRemainder hN q hf hx,
    abs_mul,abs_of_nonneg (pow_nonneg hN.le j)]
  calc
    _ ≤ N^j*((B/N^j)*(H:ℝ)^6/60) :=
      mul_le_mul_of_nonneg_left
        (abs_iteratedDeriv_sargosSextupleRemainder_source_interior q hf j (hB j hj)
          ((mem_sargosScaledRemainder_interval hN M q x).mp hx))
        (pow_nonneg hN.le j)
    _ = _ := by field_simp

end TaoTrudgianYang2025
