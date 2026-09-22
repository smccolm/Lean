import TaoTrudgianYang2025.BourgainComponentMass

/-!
# The full two-term common shift for genuine selected components

Both coefficients retain the physical shift window and logarithmic losses.
The finite family consists of actual localized large-value patterns and
their already constructed component bands, not independent scalar data.
-/

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

set_option maxHeartbeats 800000

noncomputable section

namespace TaoTrudgianYang2025

def bourgainMassCoefficient (N T B C τ α ε d : ℝ) : ℝ :=
  N^(-α)*N^(τ/2) /
    (32*bourgainDifferenceLogLoss N τ*
      (bourgainZetaBandCount B (T+N^(ε/8)+1)
        (N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)*d*
      Real.sqrt (C*(T+N^(ε/8)+1)^(1+ε)))

def bourgainSliceCardCoefficient (N ε s : ℝ) : ℝ :=
  s^2/(8*N^(ε/8)*(2*Nat.ceil (N^(ε/8))+1 : ℕ))

def bourgainSliceSqrtCoefficient (N T B C τ α ε d : ℝ) : ℝ :=
  bourgainMassCoefficient N T B C τ α ε d /
    (4*Real.sqrt (2*N^(ε/8)*(2*Nat.ceil (N^(ε/8))+1 : ℕ)))

/-- The complete finite counterpart of the source's two-term common-shift
comparison, with all its coefficients derived from actual component masses. -/
theorem bourgain_component_family_slice (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (A : Finset ℕ) (hA : A.Nonempty)
    (W : ℕ → Finset ℝ) (j : ℕ → ℕ) (q : ℕ)
    {B C τ α ε δ s d : ℝ}
    (hsub : ∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates)
    (hδ : δ ≤ 1) (hT : L ≤ P.N^(τ+δ))
    (hband : ∀ i ∈ A, BourgainComponentBand P.N L B C τ α ε (W i) (j i) q)
    (hs : 0 < s) (hd : 0 < d)
    (hrel : ∀ i ∈ A, (2 : ℝ)^(j i) ≤ 2*d*((W i).card : ℝ))
    (hcorr : ∀ i ∈ A, s ≤ bourgainZetaBandCorrelation
      (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8)) (L+P.N^(ε/8)+1)
      (P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q)) :
    let H := P.N^(ε/8)
    let U := L+H+1
    let V := P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
    ∃ u ∈ Ioc (-H) H,
      (bourgainIntegerSlice H U V u).Nonempty ∧
      bourgainSliceCardCoefficient P.N ε s*
          ((bourgainIntegerSlice H U V u).card : ℝ)*(∑ i ∈ A, ((W i).card : ℝ))+
        bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
          Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
            (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ)) <
      ∑ i ∈ A, ((W i).card : ℝ)*
        ((bourgainDifferenceLevel (W i) (j i) ∩ bourgainIntegerSlice H U V u).card : ℝ) := by
  let N := P.N
  let H := N^(ε/8)
  let U := L+H+1
  let V := N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
  let μ := volume.real (bourgainZetaBand U V)
  let K := (2*Nat.ceil H+1 : ℕ)
  let D := fun i => bourgainDifferenceLevel (W i) (j i)
  let R := fun i => ((W i).card : ℝ)
  let M := fun i => bourgainZetaBandMass (D i) H U V
  let β := bourgainMassCoefficient N L B C τ α ε d
  let a := bourgainSliceCardCoefficient N ε s
  let b := bourgainSliceSqrtCoefficient N L B C τ α ε d
  let R₁ := ∑ i ∈ A, R i
  let R₃ := ∑ i ∈ A, (R i)^(3/2 : ℝ)
  let Q := ∑ i ∈ A, R i*M i
  have hN : 0 < N := zero_lt_one.trans P.one_lt_N
  have hH : 0 < H := Real.rpow_pos_of_pos hN _
  have hK : (0 : ℝ) < K := by dsimp only [K]; positivity
  have hR (i : ℕ) (hi : i ∈ A) : 0 < R i := by
    dsimp only [R]
    exact_mod_cast (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le
      (hband i hi).2.2.1
  obtain ⟨i₀, hi₀⟩ := hA
  obtain ⟨_, _, _, _, _, _, _, hV, _, hμ, _, hfourth, _⟩ := hband i₀ hi₀
  have hY : 0 < C*U^(1+ε) := (mul_pos (pow_pos hV 4) hμ).trans_le hfourth
  have hZ : 0 < bourgainDifferenceLogLoss N τ :=
    bourgainDifferenceLogLoss_pos P.one_lt_N.le τ
  have hJ : (0 : ℝ) < bourgainZetaBandCount B U
      (N^(-bourgainSharedFloorExponent α τ ε)) := by
    exact_mod_cast bourgainZetaBandCount_pos _ _ _
  have hβ : 0 < β := by
    dsimp only [β, bourgainMassCoefficient]
    exact div_pos (by positivity)
      (mul_pos (by positivity) (Real.sqrt_pos.mpr hY))
  have ha : 0 < a := by
    change 0 < s^2/(8*H*(K : ℝ))
    positivity
  have hb : 0 < b := by
    change 0 < β/(4*Real.sqrt (2*H*(K : ℝ)))
    positivity
  have hR₁ : 0 ≤ R₁ := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hR₃ : 0 ≤ R₃ := Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmass (i : ℕ) (hi : i ∈ A) :
      s^2*μ*R i/(2*H) ≤ R i*M i ∧
      β*Real.sqrt μ*(R i)^(3/2 : ℝ) < R i*M i := by
    apply (hband i hi).weighted_mass_lower hN hs hd
    · apply bourgain_retained_difference_level_count (P.localized L hL i) (hsub i hi)
        (by
          have hh := hR i hi
          dsimp only [R] at hh
          exact_mod_cast hh) hδ hT
    · exact hrel i hi
    · exact hcorr i hi
  have hfirst : s^2*μ/(2*H)*R₁ ≤ Q := by
    calc
      _ = ∑ i ∈ A, s^2*μ*R i/(2*H) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ Q := Finset.sum_le_sum (fun i hi => (hmass i hi).1)
  have hsecond : β*Real.sqrt μ*R₃ < Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty ⟨i₀, hi₀⟩ (fun i hi => (hmass i hi).2)
  have hQ : 0 < Q :=
    (mul_nonneg (mul_nonneg hβ.le (Real.sqrt_nonneg μ)) hR₃).trans_lt hsecond
  have hfirstEq : (a*R₁)*(K : ℝ)*μ = (s^2*μ/(2*H)*R₁)/4 := by
    change (s^2/(8*H*(K : ℝ))*R₁)*(K : ℝ)*μ = _
    field_simp [hH.ne', hK.ne']
    ring
  have hsecondEq :
      (b*R₃)*Real.sqrt (2*H*(K : ℝ)*μ) = (β*Real.sqrt μ*R₃)/4 := by
    change (β/(4*Real.sqrt (2*H*(K : ℝ)))*R₃)*_ = _
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2*H*(K : ℝ)) μ]
    have hroot : Real.sqrt (2*H*(K : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp [hroot]
  have hcomparison : (a*R₁)*(K : ℝ)*μ+
      (b*R₃)*Real.sqrt (2*H*(K : ℝ)*μ) < Q := by
    rw [hfirstEq, hsecondEq]
    linarith
  obtain ⟨u, hu, hnonempty, hshift⟩ := bourgain_full_slice_common_shift A R D
    hH (mul_nonneg ha.le hR₁) (mul_nonneg hb.le hR₃) hcomparison
  refine ⟨u, hu, hnonempty, ?_⟩
  convert hshift using 1
  ring

end TaoTrudgianYang2025
