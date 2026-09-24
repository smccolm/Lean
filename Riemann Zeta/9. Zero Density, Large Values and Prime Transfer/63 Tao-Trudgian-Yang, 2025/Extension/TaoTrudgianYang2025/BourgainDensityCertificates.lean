import TaoTrudgianYang2025.BourgainDensityParameters

/-! Kernel-checked affine certificates for the two improved-density cells. -/

noncomputable section
namespace TaoTrudgianYang2025

def bourgainDensityFiveTerms (σ τ α χ : ℝ) : ℝ :=
  max (max (max (χ+2-2*σ) (α+χ/2+2-2*σ)) (-χ+2*τ+4-8*σ))
    (max (-2*α+τ+12-16*σ) (4*α+2+max 1 (2*τ-2)-4*σ))

theorem bourgainDensity_first_term {σ τ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτ : 2*bourgainDensityCutoff σ/3 ≤ τ) :
    2-2*σ ≤ bourgainDensitySlope σ*τ := by
  have hb := bourgainDensitySlope_bounds hσ hσ₁
  have he := bourgainDensitySlope_mul_cutoff hσ
  nlinarith [mul_nonneg (show 0 ≤ bourgainDensitySlope σ by linarith)
    (sub_nonneg.mpr hτ)]

theorem bourgainDensity_affine_endpoint {σ τ m c : ℝ}
    (hσ : 17/22 ≤ σ) (hm : bourgainDensitySlope σ ≤ m)
    (hτ : τ ≤ bourgainDensityCutoff σ)
    (hend : m*bourgainDensityCutoff σ+c ≤ 3-3*σ) :
    m*τ+c ≤ bourgainDensitySlope σ*τ := by
  have he := bourgainDensitySlope_mul_cutoff hσ
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hτ)]

/-- The k=4 input supplies the genuine side conditions for the Bourgain
consumer whenever it does not already prove the target bound. -/
theorem bourgainDensity_jutila_side_conditions {σ τ ρ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτ : τ ≤ bourgainDensityCutoff σ)
    (hfirst : 2-2*σ ≤ bourgainDensitySlope σ*τ)
    (hJ : ρ ≤ max (2-2*σ) (max (τ+(7-11*σ)/2) (τ+24-32*σ)))
    (hlarge : bourgainDensitySlope σ*τ < ρ) :
    1 < τ ∧ 14*σ-10 ≤ τ ∧ ρ ≤ 1 ∧ ρ ≤ 4-2*τ := by
  have ht : τ ≤ 8*(2*σ-1)/3 := hτ.trans (min_le_right _ _)
  have hr : ρ ≤ 1 ∧ ρ ≤ 4-2*τ := by
    constructor <;> apply hJ.trans <;>
      refine max_le ?_ (max_le ?_ ?_) <;> linarith
  refine ⟨?_,?_,hr.1,hr.2⟩
  · rcases le_max_iff.mp hJ with hd | hj
    · linarith
    · rcases le_max_iff.mp hj with hj | hj <;> linarith
  · rcases le_max_iff.mp hJ with hd | hj
    · linarith
    · rcases le_max_iff.mp hj with hj | hj <;> linarith

/-- Lower-sigma cell, including the crossing sigma=38/49. -/
theorem bourgainDensity_lower_certificate {σ τ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 38/49)
    (hτ : τ ≤ bourgainDensityCutoff σ) (ht : 1 < τ)
    (haffine : (τ+16-20*σ)/3 ≤ bourgainDensitySlope σ*τ) :
    let χ := max (11-16*σ+τ) 0
    let α := τ/3-2*(7*σ-5)/3-χ/6
    0 ≤ χ ∧ 1 < τ-χ ∧ 0 ≤ α ∧
      bourgainDensityFiveTerms σ τ α χ ≤ bourgainDensitySlope σ*τ := by
  let χ := max (11-16*σ+τ) 0
  let α := τ/3-2*(7*σ-5)/3-χ/6
  have hb := bourgainDensitySlope_bounds hσ (show σ ≤ 4/5 by linarith)
  have hcut := bourgainDensityCutoff_lower_branch hσ₁
  have hτ' : τ ≤ 9*(3*σ-2)/2 := by simpa only [hcut] using hτ
  have hχ0 : 0 ≤ χ := le_max_right _ _
  have hχL : 11-16*σ+τ ≤ χ := le_max_left _ _
  have hχU : 5*τ/4-1-σ ≤ χ := by linarith
  have hchi : χ+2-2*σ ≤ bourgainDensitySlope σ*τ := by
    have htop := bourgainDensity_affine_endpoint (m:=1) (c:=13-18*σ)
      hσ (by linarith) hτ (by rw [hcut]; linarith)
    rcases le_total (11-16*σ+τ) 0 with hc | hc
    · dsimp [χ]; rw [max_eq_right hc]; linarith
    · dsimp [χ]; rw [max_eq_left hc]; linarith
  have hmain : (τ+16-20*σ+χ)/3 ≤ bourgainDensitySlope σ*τ := by
    have htop := bourgainDensity_affine_endpoint (m:=2/3) (c:=9-12*σ)
      hσ (by linarith) hτ (by rw [hcut]; linarith)
    rcases le_total (11-16*σ+τ) 0 with hc | hc
    · dsimp [χ]; rw [max_eq_right hc]; linarith
    · dsimp [χ]; rw [max_eq_left hc]; linarith
  have hlast : 4*α+2+max 1 (2*τ-2)-4*σ ≤ bourgainDensitySlope σ*τ := by
    rw [max_eq_left (by linarith : 2*τ-2 ≤ (1:ℝ))]
    have htop := bourgainDensity_affine_endpoint (m:=2/3) (c:=9-12*σ)
      hσ (by linarith) hτ (by rw [hcut]; linarith)
    dsimp [α]
    linarith
  change 0 ≤ χ ∧ 1 < τ-χ ∧ 0 ≤ α ∧ _
  refine ⟨hχ0,?_,?_,?_⟩
  · rcases le_total (11-16*σ+τ) 0 with hc | hc
    · dsimp [χ]; rw [max_eq_right hc]; linarith
    · dsimp [χ]; rw [max_eq_left hc]; linarith
  · rcases le_total (11-16*σ+τ) 0 with hc | hc
    · dsimp [α,χ]; rw [max_eq_right hc]; linarith
    · dsimp [α,χ]; rw [max_eq_left hc]; linarith
  · unfold bourgainDensityFiveTerms
    dsimp [α] at *
    exact max_le (max_le (max_le hchi (by linarith)) (by linarith))
      (max_le (by linarith) hlast)

/-- Upper-sigma cell, including both endpoints and the height 3/2 split. -/
theorem bourgainDensity_upper_certificate {σ τ : ℝ}
    (hσ : 38/49 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτ : τ ≤ bourgainDensityCutoff σ) (ht : 1 < τ)
    (hlo : 14*σ-10 ≤ τ)
    (hfirst : 2-2*σ ≤ bourgainDensitySlope σ*τ)
    (haffine : (τ+16-20*σ)/3 ≤ bourgainDensitySlope σ*τ) :
    let χ := max (5*τ/4-1-σ) 0
    let α := τ/3-2*(7*σ-5)/3-χ/6
    0 ≤ χ ∧ 1 < τ-χ ∧ 0 ≤ α ∧
      bourgainDensityFiveTerms σ τ α χ ≤ bourgainDensitySlope σ*τ := by
  let χ := max (5*τ/4-1-σ) 0
  let α := τ/3-2*(7*σ-5)/3-χ/6
  have hs : 17/22 ≤ σ := by linarith
  have hb := bourgainDensitySlope_bounds hs hσ₁
  have hcut := bourgainDensityCutoff_upper_branch hσ
  have hτ' : τ ≤ 8*(2*σ-1)/3 := by simpa only [hcut] using hτ
  have hχ0 : 0 ≤ χ := le_max_right _ _
  have hχU : 5*τ/4-1-σ ≤ χ := le_max_left _ _
  have hchi : χ+2-2*σ ≤ bourgainDensitySlope σ*τ := by
    have htop := bourgainDensity_affine_endpoint (m:=5/4) (c:=1-3*σ)
      hs (by linarith) hτ (by rw [hcut]; linarith)
    rcases le_total (5*τ/4-1-σ) 0 with hc | hc
    · dsimp [χ]; rw [max_eq_right hc]; linarith
    · dsimp [χ]; rw [max_eq_left hc]; linarith
  have hmain : (τ+16-20*σ+χ)/3 ≤ bourgainDensitySlope σ*τ := by
    have htop := bourgainDensity_affine_endpoint (m:=3/4) (c:=5-7*σ)
      hs (by linarith) hτ (by rw [hcut]; linarith)
    rcases le_total (5*τ/4-1-σ) 0 with hc | hc
    · dsimp [χ]; rw [max_eq_right hc]; linarith
    · dsimp [χ]; rw [max_eq_left hc]; linarith
  have hlast : 4*α+2+max 1 (2*τ-2)-4*σ ≤ bourgainDensitySlope σ*τ := by
    have htop1 := bourgainDensity_affine_endpoint (m:=1/2) (c:=17-22*σ)
      hs (by linarith) hτ (by rw [hcut]; linarith)
    have htop2 := bourgainDensity_affine_endpoint (m:=5/2) (c:=14-22*σ)
      hs (by linarith) hτ (by rw [hcut]; linarith)
    rcases le_total (2*τ-2) 1 with hc | hc
    · rw [max_eq_left hc]; dsimp [α]; linarith
    · rw [max_eq_right hc]; dsimp [α]; linarith
  change 0 ≤ χ ∧ 1 < τ-χ ∧ 0 ≤ α ∧ _
  refine ⟨hχ0,?_,?_,?_⟩
  · rcases le_total (5*τ/4-1-σ) 0 with hc | hc
    · dsimp [χ]; rw [max_eq_right hc]; linarith
    · dsimp [χ]; rw [max_eq_left hc]; linarith
  · rcases le_total (5*τ/4-1-σ) 0 with hc | hc
    · dsimp [α,χ]; rw [max_eq_right hc]; linarith
    · dsimp [α,χ]; rw [max_eq_left hc]; linarith
  · unfold bourgainDensityFiveTerms
    dsimp [α] at *
    exact max_le (max_le (max_le hchi (by linarith)) (by linarith))
      (max_le (by linarith) hlast)

end TaoTrudgianYang2025
