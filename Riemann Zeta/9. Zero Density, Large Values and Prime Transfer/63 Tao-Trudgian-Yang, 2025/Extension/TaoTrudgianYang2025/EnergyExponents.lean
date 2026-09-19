import TaoTrudgianYang2025.AdditiveEnergy
import TaoTrudgianYang2025.LargeValueExponent
import TaoTrudgianYang2025.ZeroDensityExponent

/-!
# Additive-energy exponents

This module installs the non-asymptotic epsilon--delta meanings of `LV*`,
`LV*_ζ`, and `A*`.  The zero energy is computed directly from distinct zeros
with a product of analytic multiplicities; this is exactly the count obtained
by expanding the zeros into an indexed multiset.
-/

open Complex

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- A zero together with one of its analytic-multiplicity copies. -/
abbrev ZeroCopy (σ T : ℝ) :=
  Σ ρ : ↥(paperZeros σ T),
    Fin (analyticVanishingOrder riemannZeta (ρ : ℂ))

/-- Expanding each distinct zero into `analyticVanishingOrder` copies gives
exactly the paper's multiplicity-weighted zero count. -/
theorem zeroCopy_card (σ T : ℝ) :
    Fintype.card (ZeroCopy σ T) = paperZeroCount σ T := by
  simp only [Fintype.card_sigma, Fintype.card_fin, paperZeroCount]
  exact Finset.sum_attach (paperZeros σ T)
    (fun ρ ↦ analyticVanishingOrder riemannZeta ρ)

/-- Unit-tolerance additive energy of zeta zeros in the paper rectangle,
with analytic multiplicity represented by explicit indexed copies. -/
def zeroAdditiveEnergy (σ T : ℝ) : ℕ :=
  approximateAdditiveEnergyOf 1
    (fun z : ZeroCopy σ T ↦ ((z.1 : ℂ).im : ℝ))

theorem paperZeroCount_square_le_zeroAdditiveEnergy (σ T : ℝ) :
    paperZeroCount σ T ^ 2 ≤ zeroAdditiveEnergy σ T := by
  rw [← zeroCopy_card]
  exact square_le_approximateAdditiveEnergyOf (by norm_num)
    (fun z : ZeroCopy σ T ↦ ((z.1 : ℂ).im : ℝ))

theorem zeroAdditiveEnergy_le_paperZeroCount_fourthPower (σ T : ℝ) :
    zeroAdditiveEnergy σ T ≤ paperZeroCount σ T ^ 4 := by
  rw [← zeroCopy_card]
  exact approximateAdditiveEnergyOf_le_fourthPower 1
    (fun z : ZeroCopy σ T ↦ ((z.1 : ℂ).im : ℝ))

/-- A real candidate upper bound for the general energy large-value
exponent. -/
def IsLargeValueEnergyBound (σ τ ρstar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ P : LargeValuePattern,
          C ≤ P.N →
          P.N ^ (τ - δ) ≤ P.T →
          P.T ≤ P.N ^ (τ + δ) →
          P.N ^ (σ - δ) ≤ P.V →
          P.V ≤ P.N ^ (σ + δ) →
          (finsetAdditiveEnergy P.ordinates : ℝ) ≤
            C * P.N ^ (ρstar + ε)

/-- A real candidate upper bound for the zeta energy large-value exponent. -/
def IsZetaLargeValueEnergyBound (σ τ ρstar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ P : ZetaLargeValuePattern,
          C ≤ P.N →
          P.N ^ (τ - δ) ≤ P.T →
          P.T ≤ P.N ^ (τ + δ) →
          P.N ^ (σ - δ) ≤ P.V →
          P.V ≤ P.N ^ (σ + δ) →
          (finsetAdditiveEnergy P.ordinates : ℝ) ≤
            C * P.N ^ (ρstar + ε)

/-- A real candidate for the shifted zero-density energy estimate. -/
def IsZeroDensityEnergyBound (σ Astar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ T : ℝ, C ≤ T →
          (zeroAdditiveEnergy (σ - δ) T : ℝ) ≤
            C * T ^ (Astar * (1 - σ) + ε)

def largeValueEnergyBounds (σ τ : ℝ) : Set ℝ :=
  {ρstar | IsLargeValueEnergyBound σ τ ρstar}

def zetaLargeValueEnergyBounds (σ τ : ℝ) : Set ℝ :=
  {ρstar | IsZetaLargeValueEnergyBound σ τ ρstar}

def zeroDensityEnergyBounds (σ : ℝ) : Set ℝ :=
  {Astar | IsZeroDensityEnergyBound σ Astar}

noncomputable def largeValueEnergyExponent (σ τ : ℝ) : EReal :=
  sInf (((fun ρstar : ℝ ↦ (ρstar : EReal)) ''
    largeValueEnergyBounds σ τ) : Set EReal)

noncomputable def zetaLargeValueEnergyExponent (σ τ : ℝ) : EReal :=
  sInf (((fun ρstar : ℝ ↦ (ρstar : EReal)) ''
    zetaLargeValueEnergyBounds σ τ) : Set EReal)

noncomputable def zeroDensityEnergyExponent (σ : ℝ) : EReal :=
  sInf (((fun Astar : ℝ ↦ (Astar : EReal)) ''
    zeroDensityEnergyBounds σ) : Set EReal)

theorem largeValueEnergyExponent_le_of_bound {σ τ ρstar : ℝ}
    (h : IsLargeValueEnergyBound σ τ ρstar) :
    largeValueEnergyExponent σ τ ≤ (ρstar : EReal) := by
  apply sInf_le
  exact ⟨ρstar, h, rfl⟩

theorem zetaLargeValueEnergyExponent_le_of_bound {σ τ ρstar : ℝ}
    (h : IsZetaLargeValueEnergyBound σ τ ρstar) :
    zetaLargeValueEnergyExponent σ τ ≤ (ρstar : EReal) := by
  apply sInf_le
  exact ⟨ρstar, h, rfl⟩

theorem zeroDensityEnergyExponent_le_of_bound {σ Astar : ℝ}
    (h : IsZeroDensityEnergyBound σ Astar) :
    zeroDensityEnergyExponent σ ≤ (Astar : EReal) := by
  apply sInf_le
  exact ⟨Astar, h, rfl⟩

theorem IsLargeValueEnergyBound.toZeta {σ τ ρstar : ℝ}
    (h : IsLargeValueEnergyBound σ τ ρstar) :
    IsZetaLargeValueEnergyBound σ τ ρstar := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ := h ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTLower hTUpper hVLower hVUpper
  exact hbound P.toLargeValuePattern hN hTLower hTUpper hVLower hVUpper

theorem zetaLargeValueEnergyExponent_le_largeValueEnergyExponent (σ τ : ℝ) :
    zetaLargeValueEnergyExponent σ τ ≤ largeValueEnergyExponent σ τ := by
  apply sInf_le_sInf
  rintro x ⟨ρstar, h, rfl⟩
  exact ⟨ρstar, h.toZeta, rfl⟩

/-- The one-separated cubic energy bound gives the predicate-level form of
`LV*(σ,τ) ≤ 3 LV(σ,τ)`. -/
theorem IsLargeValueBound.toEnergyBound_three_mul
    {σ τ ρ : ℝ} (h : IsLargeValueBound σ τ ρ) :
    IsLargeValueEnergyBound σ τ (3 * ρ) := by
  intro ε hε
  obtain ⟨K, hK, δ, hδ, hcard⟩ := h (ε / 3) (by linarith)
  let C : ℝ := max K (3 * K ^ 3)
  have hKC : K ≤ C := le_max_left _ _
  have hthreeKC : 3 * K ^ 3 ≤ C := le_max_right _ _
  have hC : 1 ≤ C := hK.trans hKC
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTLower hTUpper hVLower hVUpper
  have hKN : K ≤ P.N := hKC.trans hN
  have hcardBound :=
    hcard P hKN hTLower hTUpper hVLower hVUpper
  have henergyNat := finset_additiveEnergy_le_three_mul_cube
    P.ordinates P.ordinates_oneSeparated
  have henergy : (finsetAdditiveEnergy P.ordinates : ℝ) ≤
      3 * (P.ordinates.card : ℝ) ^ 3 := by
    exact_mod_cast henergyNat
  have hNnonneg : 0 ≤ P.N := le_trans (by norm_num) P.one_lt_N.le
  have hpowNonneg : 0 ≤ P.N ^ (ρ + ε / 3) :=
    Real.rpow_nonneg hNnonneg _
  have hpowCube : (P.N ^ (ρ + ε / 3)) ^ 3 =
      P.N ^ (3 * ρ + ε) := by
    calc
      (P.N ^ (ρ + ε / 3)) ^ 3 =
          P.N ^ ((ρ + ε / 3) * (3 : ℝ)) := by
        rw [Real.rpow_mul hNnonneg]
        exact (Real.rpow_natCast (P.N ^ (ρ + ε / 3)) 3).symm
      _ = P.N ^ (3 * ρ + ε) := by
        congr 1
        ring
  calc
    (finsetAdditiveEnergy P.ordinates : ℝ) ≤
        3 * (P.ordinates.card : ℝ) ^ 3 := henergy
    _ ≤ 3 * (K * P.N ^ (ρ + ε / 3)) ^ 3 := by
      gcongr
    _ = (3 * K ^ 3) * P.N ^ (3 * ρ + ε) := by
      rw [mul_pow, hpowCube]
      ring
    _ ≤ C * P.N ^ (3 * ρ + ε) :=
      mul_le_mul_of_nonneg_right hthreeKC
        (Real.rpow_nonneg hNnonneg _)

/-- The diagonal quadratic energy bound gives the predicate-level form of
`2 LV(σ,τ) ≤ LV*(σ,τ)`. -/
theorem IsLargeValueEnergyBound.toLargeValueBound_half
    {σ τ ρstar : ℝ} (h : IsLargeValueEnergyBound σ τ ρstar) :
    IsLargeValueBound σ τ (ρstar / 2) := by
  intro ε hε
  obtain ⟨K, hK, δ, hδ, henergy⟩ := h (2 * ε) (by linarith)
  refine ⟨K, hK, δ, hδ, ?_⟩
  intro P hN hTLower hTUpper hVLower hVUpper
  have henergyBound :=
    henergy P hN hTLower hTUpper hVLower hVUpper
  have hsquareNat := finset_card_square_le_additiveEnergy P.ordinates
  have hsquare : (P.ordinates.card : ℝ) ^ 2 ≤
      (finsetAdditiveEnergy P.ordinates : ℝ) := by
    exact_mod_cast hsquareNat
  have hNnonneg : 0 ≤ P.N := le_trans (by norm_num) P.one_lt_N.le
  have hpowNonneg : 0 ≤ P.N ^ (ρstar / 2 + ε) :=
    Real.rpow_nonneg hNnonneg _
  have hpowSquare : (P.N ^ (ρstar / 2 + ε)) ^ 2 =
      P.N ^ (ρstar + 2 * ε) := by
    calc
      (P.N ^ (ρstar / 2 + ε)) ^ 2 =
          P.N ^ ((ρstar / 2 + ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hNnonneg]
        exact (Real.rpow_natCast (P.N ^ (ρstar / 2 + ε)) 2).symm
      _ = P.N ^ (ρstar + 2 * ε) := by
        congr 1
        ring
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hdominatedSquare : (P.ordinates.card : ℝ) ^ 2 ≤
      (K * P.N ^ (ρstar / 2 + ε)) ^ 2 := by
    calc
      (P.ordinates.card : ℝ) ^ 2 ≤
          (finsetAdditiveEnergy P.ordinates : ℝ) := hsquare
      _ ≤ K * P.N ^ (ρstar + 2 * ε) := henergyBound
      _ ≤ K ^ 2 * P.N ^ (ρstar + 2 * ε) := by
        gcongr
        nlinarith
      _ = (K * P.N ^ (ρstar / 2 + ε)) ^ 2 := by
        rw [mul_pow, hpowSquare]
  have hcardNonneg : 0 ≤ (P.ordinates.card : ℝ) := Nat.cast_nonneg _
  exact (sq_le_sq₀ hcardNonneg
    (mul_nonneg hKnonneg hpowNonneg)).mp hdominatedSquare

/-- Zeta-restricted one-separated patterns satisfy the same cubic energy
conversion as general large-value patterns. -/
theorem IsZetaLargeValueBound.toEnergyBound_three_mul
    {σ τ ρ : ℝ} (h : IsZetaLargeValueBound σ τ ρ) :
    IsZetaLargeValueEnergyBound σ τ (3 * ρ) := by
  intro ε hε
  obtain ⟨K, hK, δ, hδ, hcard⟩ := h (ε / 3) (by linarith)
  let C : ℝ := max K (3 * K ^ 3)
  have hKC : K ≤ C := le_max_left _ _
  have hthreeKC : 3 * K ^ 3 ≤ C := le_max_right _ _
  have hC : 1 ≤ C := hK.trans hKC
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTLower hTUpper hVLower hVUpper
  have hKN : K ≤ P.N := hKC.trans hN
  have hcardBound :=
    hcard P hKN hTLower hTUpper hVLower hVUpper
  have henergyNat := finset_additiveEnergy_le_three_mul_cube
    P.ordinates P.ordinates_oneSeparated
  have henergy : (finsetAdditiveEnergy P.ordinates : ℝ) ≤
      3 * (P.ordinates.card : ℝ) ^ 3 := by
    exact_mod_cast henergyNat
  have hNnonneg : 0 ≤ P.N := le_trans (by norm_num) P.one_lt_N.le
  have hpowNonneg : 0 ≤ P.N ^ (ρ + ε / 3) :=
    Real.rpow_nonneg hNnonneg _
  have hpowCube : (P.N ^ (ρ + ε / 3)) ^ 3 =
      P.N ^ (3 * ρ + ε) := by
    calc
      (P.N ^ (ρ + ε / 3)) ^ 3 =
          P.N ^ ((ρ + ε / 3) * (3 : ℝ)) := by
        rw [Real.rpow_mul hNnonneg]
        exact (Real.rpow_natCast (P.N ^ (ρ + ε / 3)) 3).symm
      _ = P.N ^ (3 * ρ + ε) := by
        congr 1
        ring
  calc
    (finsetAdditiveEnergy P.ordinates : ℝ) ≤
        3 * (P.ordinates.card : ℝ) ^ 3 := henergy
    _ ≤ 3 * (K * P.N ^ (ρ + ε / 3)) ^ 3 := by
      gcongr
    _ = (3 * K ^ 3) * P.N ^ (3 * ρ + ε) := by
      rw [mul_pow, hpowCube]
      ring
    _ ≤ C * P.N ^ (3 * ρ + ε) :=
      mul_le_mul_of_nonneg_right hthreeKC
        (Real.rpow_nonneg hNnonneg _)

/-- The diagonal quadratic contribution converts a zeta energy bound into
the corresponding half-exponent cardinality bound. -/
theorem IsZetaLargeValueEnergyBound.toLargeValueBound_half
    {σ τ ρstar : ℝ} (h : IsZetaLargeValueEnergyBound σ τ ρstar) :
    IsZetaLargeValueBound σ τ (ρstar / 2) := by
  intro ε hε
  obtain ⟨K, hK, δ, hδ, henergy⟩ := h (2 * ε) (by linarith)
  refine ⟨K, hK, δ, hδ, ?_⟩
  intro P hN hTLower hTUpper hVLower hVUpper
  have henergyBound :=
    henergy P hN hTLower hTUpper hVLower hVUpper
  have hsquareNat := finset_card_square_le_additiveEnergy P.ordinates
  have hsquare : (P.ordinates.card : ℝ) ^ 2 ≤
      (finsetAdditiveEnergy P.ordinates : ℝ) := by
    exact_mod_cast hsquareNat
  have hNnonneg : 0 ≤ P.N := le_trans (by norm_num) P.one_lt_N.le
  have hpowNonneg : 0 ≤ P.N ^ (ρstar / 2 + ε) :=
    Real.rpow_nonneg hNnonneg _
  have hpowSquare : (P.N ^ (ρstar / 2 + ε)) ^ 2 =
      P.N ^ (ρstar + 2 * ε) := by
    calc
      (P.N ^ (ρstar / 2 + ε)) ^ 2 =
          P.N ^ ((ρstar / 2 + ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hNnonneg]
        exact (Real.rpow_natCast (P.N ^ (ρstar / 2 + ε)) 2).symm
      _ = P.N ^ (ρstar + 2 * ε) := by
        congr 1
        ring
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hdominatedSquare : (P.ordinates.card : ℝ) ^ 2 ≤
      (K * P.N ^ (ρstar / 2 + ε)) ^ 2 := by
    calc
      (P.ordinates.card : ℝ) ^ 2 ≤
          (finsetAdditiveEnergy P.ordinates : ℝ) := hsquare
      _ ≤ K * P.N ^ (ρstar + 2 * ε) := henergyBound
      _ ≤ K ^ 2 * P.N ^ (ρstar + 2 * ε) := by
        gcongr
        nlinarith
      _ = (K * P.N ^ (ρstar / 2 + ε)) ^ 2 := by
        rw [mul_pow, hpowSquare]
  have hcardNonneg : 0 ≤ (P.ordinates.card : ℝ) := Nat.cast_nonneg _
  exact (sq_le_sq₀ hcardNonneg
    (mul_nonneg hKnonneg hpowNonneg)).mp hdominatedSquare

/-- Multiplication by a positive finite extended real is an order
automorphism, including at both infinities. -/
private noncomputable def erealScaleOrderIso (c : EReal)
    (hc : 0 < c) (htop : c ≠ ⊤) : EReal ≃o EReal :=
  StrictMono.orderIsoOfSurjective (fun x : EReal => x * c) (by
    intro x y hxy
    have hcancel (z : EReal) : z * c / c = z := by
      rw [mul_comm z c, ← EReal.mul_div c z c,
        EReal.mul_div_cancel (ne_bot_of_gt hc) htop hc.ne']
    have hd : x * c / c < y * c / c := by
      simpa only [hcancel] using hxy
    exact (EReal.strictMono_div_right_of_pos hc htop).lt_iff_lt.mp hd) (by
      intro y
      exact ⟨y / c, EReal.div_mul_cancel (ne_bot_of_gt hc) htop hc.ne'⟩)

private theorem sInf_image_mul_two (s : Set EReal) :
    sInf ((fun x : EReal => x * 2) '' s) = sInf s * 2 := by
  let e := erealScaleOrderIso 2 (by norm_num) (EReal.natCast_ne_top 2)
  rw [sInf_image]
  change (⨅ a ∈ s, e a) = e (sInf s)
  exact (e.map_sInf s).symm

private theorem sInf_image_mul_three (s : Set EReal) :
    sInf ((fun x : EReal => x * 3) '' s) = sInf s * 3 := by
  let e := erealScaleOrderIso 3 (by norm_num) (EReal.natCast_ne_top 3)
  rw [sInf_image]
  change (⨅ a ∈ s, e a) = e (sInf s)
  exact (e.map_sInf s).symm

/-- The diagonal energy contribution gives the exponent-level lower
comparison `2 LV(σ,τ) ≤ LV*(σ,τ)`, including infinite infima. -/
theorem two_mul_largeValueExponent_le_largeValueEnergyExponent (σ τ : ℝ) :
    (2 : EReal) * largeValueExponent σ τ ≤
      largeValueEnergyExponent σ τ := by
  let L : Set EReal :=
    (fun ρ : ℝ => (ρ : EReal)) '' largeValueBounds σ τ
  let E : Set EReal :=
    (fun ρstar : ℝ => (ρstar : EReal)) '' largeValueEnergyBounds σ τ
  have hsubset : E ⊆ (fun x : EReal => x * 2) '' L := by
    rintro x ⟨ρstar, hρstar, rfl⟩
    refine ⟨(ρstar / 2 : ℝ),
      ⟨ρstar / 2, hρstar.toLargeValueBound_half, rfl⟩, ?_⟩
    change (↑(ρstar / 2) : EReal) * 2 = (ρstar : EReal)
    calc
      (↑(ρstar / 2) : EReal) * 2 =
          (↑(ρstar / 2) : EReal) * (↑(2 : ℝ) : EReal) := by rfl
      _ = (↑((ρstar / 2) * 2) : EReal) := (EReal.coe_mul _ _).symm
      _ = (ρstar : EReal) := by congr 1; ring
  have hinf : sInf ((fun x : EReal => x * 2) '' L) ≤ sInf E :=
    sInf_le_sInf hsubset
  rw [sInf_image_mul_two] at hinf
  simpa only [largeValueExponent, largeValueEnergyExponent, L, E,
    mul_comm] using hinf

/-- One-separation gives the exponent-level upper comparison
`LV*(σ,τ) ≤ 3 LV(σ,τ)`, including infinite infima. -/
theorem largeValueEnergyExponent_le_three_mul_largeValueExponent (σ τ : ℝ) :
    largeValueEnergyExponent σ τ ≤
      (3 : EReal) * largeValueExponent σ τ := by
  let L : Set EReal :=
    (fun ρ : ℝ => (ρ : EReal)) '' largeValueBounds σ τ
  let E : Set EReal :=
    (fun ρstar : ℝ => (ρstar : EReal)) '' largeValueEnergyBounds σ τ
  have hsubset : (fun x : EReal => x * 3) '' L ⊆ E := by
    rintro x ⟨y, ⟨ρ, hρ, rfl⟩, rfl⟩
    refine ⟨3 * ρ, hρ.toEnergyBound_three_mul, ?_⟩
    change (↑(3 * ρ) : EReal) = (ρ : EReal) * 3
    calc
      (↑(3 * ρ) : EReal) = (↑(ρ * 3) : EReal) := by congr 1; ring
      _ = (ρ : EReal) * (↑(3 : ℝ) : EReal) := EReal.coe_mul _ _
      _ = (ρ : EReal) * 3 := by rfl
  have hinf : sInf E ≤ sInf ((fun x : EReal => x * 3) '' L) :=
    sInf_le_sInf hsubset
  rw [sInf_image_mul_three] at hinf
  simpa only [largeValueExponent, largeValueEnergyExponent, L, E,
    mul_comm] using hinf

/-- Zeta-restricted diagonal energy gives
`2 LV_ζ(σ,τ) ≤ LV*_ζ(σ,τ)`. -/
theorem two_mul_zetaLargeValueExponent_le_zetaLargeValueEnergyExponent
    (σ τ : ℝ) :
    (2 : EReal) * zetaLargeValueExponent σ τ ≤
      zetaLargeValueEnergyExponent σ τ := by
  let L : Set EReal :=
    (fun ρ : ℝ => (ρ : EReal)) '' zetaLargeValueBounds σ τ
  let E : Set EReal :=
    (fun ρstar : ℝ => (ρstar : EReal)) '' zetaLargeValueEnergyBounds σ τ
  have hsubset : E ⊆ (fun x : EReal => x * 2) '' L := by
    rintro x ⟨ρstar, hρstar, rfl⟩
    refine ⟨(ρstar / 2 : ℝ),
      ⟨ρstar / 2, hρstar.toLargeValueBound_half, rfl⟩, ?_⟩
    change (↑(ρstar / 2) : EReal) * 2 = (ρstar : EReal)
    calc
      (↑(ρstar / 2) : EReal) * 2 =
          (↑(ρstar / 2) : EReal) * (↑(2 : ℝ) : EReal) := by rfl
      _ = (↑((ρstar / 2) * 2) : EReal) := (EReal.coe_mul _ _).symm
      _ = (ρstar : EReal) := by congr 1; ring
  have hinf : sInf ((fun x : EReal => x * 2) '' L) ≤ sInf E :=
    sInf_le_sInf hsubset
  rw [sInf_image_mul_two] at hinf
  simpa only [zetaLargeValueExponent, zetaLargeValueEnergyExponent, L, E,
    mul_comm] using hinf

/-- Zeta one-separation gives `LV*_ζ(σ,τ) ≤ 3 LV_ζ(σ,τ)`. -/
theorem zetaLargeValueEnergyExponent_le_three_mul_zetaLargeValueExponent
    (σ τ : ℝ) :
    zetaLargeValueEnergyExponent σ τ ≤
      (3 : EReal) * zetaLargeValueExponent σ τ := by
  let L : Set EReal :=
    (fun ρ : ℝ => (ρ : EReal)) '' zetaLargeValueBounds σ τ
  let E : Set EReal :=
    (fun ρstar : ℝ => (ρstar : EReal)) '' zetaLargeValueEnergyBounds σ τ
  have hsubset : (fun x : EReal => x * 3) '' L ⊆ E := by
    rintro x ⟨y, ⟨ρ, hρ, rfl⟩, rfl⟩
    refine ⟨3 * ρ, hρ.toEnergyBound_three_mul, ?_⟩
    change (↑(3 * ρ) : EReal) = (ρ : EReal) * 3
    calc
      (↑(3 * ρ) : EReal) = (↑(ρ * 3) : EReal) := by congr 1; ring
      _ = (ρ : EReal) * (↑(3 : ℝ) : EReal) := EReal.coe_mul _ _
      _ = (ρ : EReal) * 3 := by rfl
  have hinf : sInf E ≤ sInf ((fun x : EReal => x * 3) '' L) :=
    sInf_le_sInf hsubset
  rw [sInf_image_mul_three] at hinf
  simpa only [zetaLargeValueExponent, zetaLargeValueEnergyExponent, L, E,
    mul_comm] using hinf

end TaoTrudgianYang2025
