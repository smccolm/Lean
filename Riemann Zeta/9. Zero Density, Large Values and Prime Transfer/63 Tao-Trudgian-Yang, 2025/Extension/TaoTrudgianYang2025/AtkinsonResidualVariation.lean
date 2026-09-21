import TaoTrudgianYang2025.AtkinsonSaddleSamples

/-!
# Uniform cutoff and Mellin variation along both actual saddles

The two affine cutoff transitions have variation at most one each.
Their product has variation at most two under increasing or decreasing
sampling, independently of the physical transition width.
-/

noncomputable section

open Complex Set

namespace TaoTrudgianYang2025

theorem finiteVariationBound_zetaBandCutoff_sample {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (u : ℕ → ℝ) (N : ℕ)
    (hu : MonotoneOn u (Iic N) ∨ AntitoneOn u (Iic N)) :
    FiniteVariationBound (fun i => (zetaBandCutoff a b c d (u i) : ℂ)) N 2 := by
  let p : ℝ → ℝ := fun x => Real.smoothTransition ((x-a)/(b-a))
  let q : ℝ → ℝ := fun x => Real.smoothTransition ((d-x)/(d-c))
  have hp : Monotone p := fun x y hxy =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)
  have hq : Antitone q := fun x y hxy =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_left hxy d) (sub_pos.mpr hcd).le)
  have hbnd (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
      (hm : Monotone f ∨ Antitone f) :
      FiniteVariationBound (fun i => (f (u i) : ℂ)) N 1 := by
    rcases hm with hm | hm <;> rcases hu with hu | hu
    · exact finiteVariationBound_of_monotone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
    · exact finiteVariationBound_of_antitone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
    · exact finiteVariationBound_of_antitone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
    · exact finiteVariationBound_of_monotone (by norm_num)
        (fun i hi j hj hij => hm (hu hi hj hij)) (fun i _ => hf _)
  have h₁ := hbnd p (fun _ => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩) (Or.inl hp)
  have h₂ := hbnd q (fun _ => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩) (Or.inr hq)
  simpa only [p,q,zetaBandCutoff,Complex.ofReal_mul,mul_one] using h₁.mul h₂

theorem finiteVariationBound_saddleCutoff {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (m N : ℕ) :
    FiniteVariationBound (fun i => (zetaDivisorBandCutoff T G L
      (zetaAtkinsonSaddle T (Real.sqrt ((m+i:ℕ):ℝ))) : ℂ)) N 2 ∧
    FiniteVariationBound (fun i => (zetaDivisorBandCutoff T G L
      (zetaAtkinsonSaddle T (-Real.sqrt ((m+i:ℕ):ℝ))) : ℂ)) N 2 := by
  have he := zetaDivisorBandEdge_strictMono hT hG
  have hp : Monotone (fun i : ℕ => zetaAtkinsonSaddle T (Real.sqrt ((m+i:ℕ):ℝ))) := by
    intro i j hij
    apply zetaAtkinsonSaddle_monotone hT
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)
  have hm : Antitone (fun i : ℕ => zetaAtkinsonSaddle T (-Real.sqrt ((m+i:ℕ):ℝ))) := by
    intro i j hij
    apply zetaAtkinsonSaddle_monotone hT
    apply neg_le_neg
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_left hij m)
  exact ⟨finiteVariationBound_zetaBandCutoff_sample (he (by linarith)) (he (by linarith))
    _ N (Or.inl (hp.monotoneOn (Iic N))),
    finiteVariationBound_zetaBandCutoff_sample (he (by linarith)) (he (by linarith))
    _ N (Or.inr (hm.antitoneOn (Iic N)))⟩

theorem exists_finiteVariationBound_saddleResidual :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → 0 < L →
      ∀ m N : ℕ, 10000*((m+N:ℕ):ℝ) ≤ T →
      FiniteVariationBound (fun i => atkinsonSaddleResidual T G L (Real.sqrt ((m+i:ℕ):ℝ))) N C ∧
      FiniteVariationBound (fun i => atkinsonSaddleResidual T G L (-Real.sqrt ((m+i:ℕ):ℝ))) N C := by
  obtain ⟨C,hC,hM⟩ := exists_finiteVariationBound_saddleMellin
  refine ⟨4*C,by positivity,?_⟩
  intro T G L hT hG hL m N hN
  obtain ⟨hp,hm⟩ := hM T hT m N hN
  obtain ⟨hpc,hmc⟩ := finiteVariationBound_saddleCutoff hT hG hL m N
  constructor
  · convert hp.mul hpc using 1
    ring
  · convert hm.mul hmc using 1
    ring

end TaoTrudgianYang2025
