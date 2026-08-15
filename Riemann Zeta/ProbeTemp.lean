import RiemannZeta.GuthMaynard.DFIErrorTerms

open scoped Real
open Complex

namespace RiemannZeta.GuthMaynard

noncomputable def testYCoeff
    (C D K : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b q qx qy : ℕ) : ℝ :=
  K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (X / a) ^ (-(1 / 4 : ℝ)) *
    (((2 * X / a) - (X / a)) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
          (((b : ℝ) * Y) / Q ^ 2)) ^ k *
        (D * ((14 * Real.pi + 8) / Real.sqrt qy *
          ((Y / b) ^ (-(1 / 4 : ℝ)) *
            ((Y / b) * (C * ((q : ℝ) * Q)⁻¹)))))))

theorem test_y_norm
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D K : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b →
        (_hq : NeZero q) → (q : ℝ) ≤ 2 * Q →
        ∀ (h : ℤ) (xb yb : DFIVoronoiDualBranch) (m n : ℕ),
          0 < m → 0 < n →
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
          ‖dfiEquation24DoubleDualMellinAmplitude qx xb qy yb E m n‖ ≤
            testYCoeff C D K k Q X Y a b q qx qy *
              (m : ℝ) ^ (ε - 1 / 4) *
              (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨C, D, K, hC, hD, hK, hraw⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_bound
      hf hbox hψ hscale w hUQ ε hε k
  refine ⟨C, D, K, hC, hD, hK, ?_⟩
  intro a b q ha hb hq hqQ h xb yb m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  have hr := hraw a b q ha hb hq hqQ h xb yb m n hm hn
  have hfreq := dfiEquation29_frequency_power_normalization
    (R := (((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2))
    (Z := (b : ℝ) * Y) (Q := Q) (ε := ε) w.Q_pos hn k
  dsimp only at hr
  dsimp only [testYCoeff]
  calc
    _ ≤ _ := hr
    _ = _ := by
      rw [show
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt qy *
                (((Y / b) ^ (-(1 / 4 : ℝ)) *
                  ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) =
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
            (D * ((14 * Real.pi + 8) / Real.sqrt qy *
              ((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) * (C * ((q : ℝ) * Q)⁻¹)))))) by ring]
      rw [hfreq]
      ring

end RiemannZeta.GuthMaynard

#check Summable.tsum_add
#check tsum_add
