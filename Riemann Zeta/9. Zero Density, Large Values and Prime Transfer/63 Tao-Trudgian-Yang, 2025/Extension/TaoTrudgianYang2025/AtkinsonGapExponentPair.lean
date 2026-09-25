import TaoTrudgianYang2025.AtkinsonGapModelEntry
import TaoTrudgianYang2025.ExponentPairAllHeights

/-!
# The analytic exponent-pair estimate for actual Atkinson gap sums

The physical phase, its model jets, the radian convention and every
finite endpoint are consumed here. The reciprocal low-frequency term
is retained. No gap-sum estimate is accepted as an extra hypothesis.
-/

noncomputable section
open Expdb RiemannZeta.GuthMaynard
open scoped FourierTransform BigOperators
namespace TaoTrudgianYang2025

theorem atkinsonGap_oscillatory_identity {M t u : ℝ}
    (hM : 0 < M) (hu : 0 < u) (htu : u < t) (n : ℕ) :
    oscillatory (atkinsonNormalizedGapPhase M t u)
      (atkinsonGapFrequency M t u/(2*Real.pi)) M n =
      unitaryPhase (atkinsonSourcePhase t n-atkinsonSourcePhase u n) := by
  have hf := atkinsonGapFrequency_pos hM hu htu
  have he : (atkinsonGapFrequency M t u/(2*Real.pi))*
      atkinsonNormalizedGapPhase M t u ((n : ℝ)/M) =
      (atkinsonSourcePhase t n-atkinsonSourcePhase u n)/(2*Real.pi) := by
    unfold atkinsonNormalizedGapPhase atkinsonIndexPhaseDifference
    rw [show M*((n : ℝ)/M) = n by field_simp]
    rw [atkinsonIndexRealPhase_natCast,atkinsonIndexRealPhase_natCast]
    field_simp
  rw [oscillatory,he,Real.fourierChar_apply,unitaryPhase]
  congr 1
  push_cast
  field_simp

theorem atkinsonGap_exponentialSum_identity {M t u : ℝ}
    (hM : 0 < M) (hu : 0 < u) (htu : u < t) (a b : ℕ) :
    exponentialSumAt (atkinsonNormalizedGapPhase M t u)
      (atkinsonGapFrequency M t u/(2*Real.pi)) M a b =
      ∑ n ∈ Finset.Icc a b,
        unitaryPhase (atkinsonSourcePhase t n-atkinsonSourcePhase u n) := by
  unfold exponentialSumAt
  exact Finset.sum_congr rfl (fun n _ => atkinsonGap_oscillatory_identity hM hu htu n)

theorem ExponentPair.atkinson_gap_sum_bound {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (M t u : ℝ) (a b : ℕ), 1 ≤ M → 0 < u → u < t → t ≤ 2*u →
        Real.pi*M/(2*u) < η → M ≤ (a : ℝ) → (b : ℝ) ≤ 2*M →
        ‖∑ n ∈ Finset.Icc a b,
          unitaryPhase (atkinsonSourcePhase t n-atkinsonSourcePhase u n)‖ ≤
          C*((atkinsonGapFrequency M t u/(2*Real.pi*M))^(k+ε)*M^(l+ε)+
            2*Real.pi*M/atkinsonGapFrequency M t u) := by
  obtain ⟨δ,hδ,P,_hP,C,hC,hbound⟩ :=
    hpair.allPositiveHeight_bound (by norm_num : (0 : ℝ) < 1/2) hε
  obtain ⟨η,hη,hmodel⟩ := atkinsonNormalizedGapPhase_approximate P hδ
  refine ⟨η,hη,C,hC,?_⟩
  intro M t u a b hM hu htu ht2 hsmall ha hb
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hf := atkinsonGapFrequency_pos hMp hu htu
  have h := hbound (atkinsonGapFrequency M t u/(2*Real.pi)) M
    (atkinsonNormalizedGapPhase M t u) a b (by positivity) hM ha hb
    (hmodel M t u hMp hu htu ht2 hsmall)
  rw [atkinsonGap_exponentialSum_identity hMp hu htu a b] at h
  convert h using 1
  congr 2 <;> field_simp

end TaoTrudgianYang2025
