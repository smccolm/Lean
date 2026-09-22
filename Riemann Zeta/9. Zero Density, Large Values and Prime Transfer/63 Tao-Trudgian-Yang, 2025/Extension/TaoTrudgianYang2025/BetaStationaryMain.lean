import TaoTrudgianYang2025.BetaAmplitudeVariation

/-!
# Literal stationary main terms and canonical prefix sums

The phase includes the negative-curvature factor e(-1/8). Main terms
use the actual physical second derivative. Exact prefix identities
retain the original natural-number summation endpoints.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025

def modelPhaseStationaryCharacter (F : ℝ → ℝ) (T N r : ℝ) : ℂ :=
  𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)-1/8)

def modelPhaseStationaryMainTerm (F : ℝ → ℝ) (T N r : ℝ) : ℂ :=
  (modelPhasePhysicalAmplitude F T N r : ℂ)*modelPhaseStationaryCharacter F T N r

def exponentialSumAtPrefixMax (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) : ℝ :=
  (Finset.range (L+1)).sup' (by simp) (fun j => ‖exponentialSumAt F T N a (a+j)‖)

theorem norm_modelPhaseStationaryCharacter (F : ℝ → ℝ) (T N r : ℝ) :
    ‖modelPhaseStationaryCharacter F T N r‖ = 1 :=
  Circle.norm_coe _

theorem exponentialSumAt_eq_range (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    exponentialSumAt F T N a (a+L) =
      ∑ i ∈ Finset.range (L+1), (𝐞 (T*F (((a : ℝ)+i)/N)) : ℂ) := by
  rw [exponentialSumAt,RiemannZeta.GuthMaynard.sum_Icc_eq_shifted_range _ a (a+L)
    (Nat.le_add_right a L)]
  simp only [Nat.add_sub_cancel_left,oscillatory,Nat.cast_add]

theorem norm_exponentialSumAt_le_prefixMax (F : ℝ → ℝ) (T N : ℝ)
    (a L j : ℕ) (hj : j ≤ L) :
    ‖exponentialSumAt F T N a (a+j)‖ ≤ exponentialSumAtPrefixMax F T N a L := by
  exact Finset.le_sup' (fun k => ‖exponentialSumAt F T N a (a+k)‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem exponentialSumAtPrefixMax_nonneg (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    0 ≤ exponentialSumAtPrefixMax F T N a L :=
  (norm_nonneg _).trans (norm_exponentialSumAt_le_prefixMax F T N a L 0 (Nat.zero_le L))

theorem exponentialSumAtPrefixMax_le {F : ℝ → ℝ} {T N B : ℝ} {a L : ℕ}
    (h : ∀ j ≤ L, ‖exponentialSumAt F T N a (a+j)‖ ≤ B) :
    exponentialSumAtPrefixMax F T N a L ≤ B := by
  apply Finset.sup'_le
  intro j hj
  exact h j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem modelPhaseStationaryCharacter_canonical
    {χ F : ℝ → ℝ} {σ A w T N r : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : 0 < r*N/T) (hχ : χ (r*N/T) = 1) :
    modelPhaseStationaryCharacter F T N r =
      (𝐞 (modelPhaseDualOffset F σ A w T-1/8) : ℂ) *
        starRingEnd ℂ (𝐞 (modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N))) := by
  unfold modelPhaseStationaryCharacter
  rw [modelPhaseStationaryPoint_canonical_phase hA hw hT hN hv hχ]
  rw [show modelPhaseDualOffset F σ A w T -
      modelPhaseDualParameter σ A T *
        canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N)-1/8 =
      (modelPhaseDualOffset F σ A w T-1/8) +
        -(modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N)) by ring]
  rw [AddChar.map_add_eq_mul,AddChar.map_neg_eq_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]

theorem norm_modelPhaseStationaryCharacter_range
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (a L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hχ : ∀ i : ℕ, i ≤ L → χ (((a : ℝ)+i)*N/T) = 1) :
    ‖∑ i ∈ Finset.range (L+1), modelPhaseStationaryCharacter F T N ((a : ℝ)+i)‖ =
      ‖exponentialSumAt (canonicalLegendrePhase χ F σ A w)
        (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a (a+L)‖ := by
  have he : (∑ i ∈ Finset.range (L+1),
      modelPhaseStationaryCharacter F T N ((a : ℝ)+i)) =
      (𝐞 (modelPhaseDualOffset F σ A w T-1/8) : ℂ) *
        starRingEnd ℂ (exponentialSumAt (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a (a+L)) := by
    rw [exponentialSumAt_eq_range,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact modelPhaseStationaryCharacter_canonical hA hw hT hN
      (hv i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
      (hχ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  rw [he,norm_mul,Circle.norm_coe,one_mul]
  exact Complex.norm_conj _

end TaoTrudgianYang2025
