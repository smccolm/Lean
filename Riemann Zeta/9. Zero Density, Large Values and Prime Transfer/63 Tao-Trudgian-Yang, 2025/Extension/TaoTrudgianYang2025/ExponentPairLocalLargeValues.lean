import TaoTrudgianYang2025.ExponentPairGramLogLoss
import TaoTrudgianYang2025.LargeValueExponent

/-! Uniform local large values from actual exponent-pair Gram sums. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem ExponentPair.local_largeValueBound {k l σ τ : ℝ}
    (hpair : ExponentPair k l) (hτ : 0 ≤ τ)
    (hgap : 1+l-k+k*τ < 2*σ) :
    IsLargeValueBound σ τ (2-2*σ) := by
  intro ε hε
  let g := 2*σ-(1+l-k+k*τ)
  have hg : 0 < g := by dsimp [g]; linarith
  have hk : 0 ≤ k := hpair.inTriangle.1
  let η := min 1 (g/(8*(τ+1)))
  let δ := min 1 (min (ε/8) (g/(8*(k+3))))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have he1 : η ≤ 1 := min_le_left _ _
  have hd1 : δ ≤ 1 := min_le_left _ _
  have hde : δ ≤ ε/8 := (min_le_left _ _).trans' (min_le_right _ _)
  have hdg : δ ≤ g/(8*(k+3)) := (min_le_right _ _).trans' (min_le_right _ _)
  have het : η*(τ+1) ≤ g/8 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(τ+1))).mp
      (show η ≤ g/(8*(τ+1)) from min_le_right _ _)
    nlinarith
  have hdk : δ*(k+3) ≤ g/8 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(k+3))).mp hdg
    nlinarith
  have hbudget : η+1+(τ+δ-1)*(k+η)+(l+η) ≤ (σ-δ)*2 := by
    have heδ := mul_le_mul_of_nonneg_left he1 hδ.le
    dsimp [g] at het hdk
    nlinarith
  obtain ⟨C,hC,hfinite⟩ := hpair.sharp_gram_cardinality_bound hη
  have hev : ∀ᶠ N : ℝ in atTop, 4*C ≤ N^η := by
    simpa only [pow_zero,mul_one] using
      eventually_const_log_pow_le_rpow (4*C) (by positivity) 0 hη
  obtain ⟨Na,hNa⟩ := eventually_atTop.mp hev
  obtain ⟨Nd,hNd⟩ := eventually_atTop.mp
    (eventually_exponentPair_gram_diagonal hC hτ (show 0 < ε/2 by linarith))
  let K := max 1 (max Na Nd)
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : Na ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKD : Nd ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,hK,δ,hδ,?_⟩
  intro P hN _ hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have hN1 : 1 ≤ P.N := P.one_lt_N.le
  have hconstant := hNa P.N (hKA.trans hN)
  have hratio : P.T/P.N ≤ P.N^(τ+δ-1) := calc
    _ ≤ P.N^(τ+δ)/P.N := div_le_div_of_nonneg_right hTu hNp.le
    _ = _ := by rw [Real.rpow_sub hNp,Real.rpow_one]
  have hratioPower : (P.T/P.N)^(k+η) ≤ P.N^((τ+δ-1)*(k+η)) := by
    rw [Real.rpow_mul hNp.le]
    exact Real.rpow_le_rpow (by have := P.T_pos; positivity) hratio (by linarith)
  have hVpow : P.N^((σ-δ)*(2 : ℝ)) ≤ P.V^2 := by
    rw [Real.rpow_mul hNp.le,Real.rpow_two]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hVl 2
  have hvalue : 4*C*P.N*(P.T/P.N)^(k+η)*P.N^(l+η) ≤ P.V^2 := calc
    _ ≤ (P.N^η*P.N)*P.N^((τ+δ-1)*(k+η))*P.N^(l+η) := by
      gcongr
    _ = P.N^(η+1+(τ+δ-1)*(k+η)+(l+η)) := by
      rw [show P.N^η*P.N = P.N^(η+1) by rw [Real.rpow_add hNp,Real.rpow_one],
        ← Real.rpow_add hNp,← Real.rpow_add hNp]
    _ ≤ P.N^((σ-δ)*2) := Real.rpow_le_rpow_of_exponent_le hN1 hbudget
    _ ≤ P.V^2 := hVpow
  have hTpower : P.T ≤ P.N^(τ+1) :=
    hTu.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hdiag := (hfinite P hvalue).trans (hNd P.N (hKD.trans hN) P.T P.T_pos hTpower)
  have hr : (P.ordinates.card : ℝ) ≤ P.N^((2+ε/2)-(σ-δ)*2) := by
    rw [Real.rpow_sub hNp]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
    exact (mul_le_mul_of_nonneg_left hVpow (Nat.cast_nonneg _)).trans hdiag
  calc
    _ ≤ P.N^((2+ε/2)-(σ-δ)*2) := hr
    _ ≤ P.N^(2-2*σ+ε) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ ≤ K*P.N^(2-2*σ+ε) := le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hK

end TaoTrudgianYang2025
