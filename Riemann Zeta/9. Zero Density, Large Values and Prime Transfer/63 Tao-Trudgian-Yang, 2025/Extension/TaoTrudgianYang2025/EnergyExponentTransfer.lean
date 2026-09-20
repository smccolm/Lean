import TaoTrudgianYang2025.ZeroEnergyAssembly
import TaoTrudgianYang2025.EnergyRegionSupremum
import Mathlib.Data.EReal.Inv
import Mathlib.Order.LiminfLimsup

/-!
# Energy exponent transfer

The analytic transfer consumes uniform energy bounds. This module connects
those bounds to the extended-real exponent supremum and limsup in the paper.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- The feasible-region compactness theorem discharges the uniform bound
at any real upper bound for the general energy exponent. -/
theorem isLargeValueEnergyBound_of_exponent_le
    {σ τ B : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ)
    (h : largeValueEnergyExponent σ τ ≤ (B : EReal)) :
    IsLargeValueEnergyBound σ τ B := by
  by_contra hnot
  obtain ⟨ρ, ρstar, s, hregion, hB⟩ :=
    energyRegion_exists_rhoStar_gt_of_not_bound hσLower hσUpper hτ hnot
  have hmem : (ρstar : EReal) ≤ largeValueEnergyRegionSupremum σ τ :=
    le_sSup ⟨ρstar, ⟨ρ, s, hregion⟩, rfl⟩
  have hle := hmem.trans ((largeValueEnergyRegionSupremum_le_largeValueEnergyExponent σ τ).trans h)
  exact (not_le_of_gt hB) (EReal.coe_le_coe_iff.mp hle)

/-- Zeta-restricted counterpart, with the same endpoint quantifiers. -/
theorem isZetaLargeValueEnergyBound_of_exponent_le
    {σ τ B : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ)
    (h : zetaLargeValueEnergyExponent σ τ ≤ (B : EReal)) :
    IsZetaLargeValueEnergyBound σ τ B := by
  by_contra hnot
  obtain ⟨ρ, ρstar, s, hregion, hB⟩ :=
    zetaEnergyRegion_exists_rhoStar_gt_of_not_bound hσLower hσUpper hτ hnot
  have hmem : (ρstar : EReal) ≤ zetaLargeValueEnergyRegionSupremum σ τ :=
    le_sSup ⟨ρstar, ⟨ρ, s, hregion⟩, rfl⟩
  have hle := hmem.trans ((zetaLargeValueEnergyRegionSupremum_le_zetaLargeValueEnergyExponent σ τ).trans h)
  exact (not_le_of_gt hB) (EReal.coe_le_coe_iff.mp hle)

/-- A genuine one-ordinate pattern at zero, with all coefficients one.
It supplies the lower endpoint of the general energy exponent, rather than
postulating a nonempty feasible region. -/
def singletonLargeValuePattern (N : ℕ) (σ τ : ℝ) (hN : 1 < N) (hσ : σ ≤ 1) :
    LargeValuePattern where
  N := N
  scale := N
  T := (N : ℝ) ^ τ
  V := (N : ℝ) ^ σ
  coeff := fun _ => 1
  indices := Finset.Icc N (2 * N)
  intervalLeft := 0
  intervalRight := (N : ℝ) ^ τ
  ordinates := {0}
  N_eq_scale := rfl
  one_lt_N := by exact_mod_cast hN
  T_pos := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  V_pos := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  mem_indices_iff := by intro n; simp only [Finset.mem_Icc]; norm_cast
  coeff_one_bounded := by intro n _; norm_num
  interval_length := by ring
  ordinates_in_interval := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    exact ⟨le_rfl, Real.rpow_nonneg (Nat.cast_nonneg N) _⟩
  ordinates_oneSeparated := by
    intro t ht u hu htu
    simp only [Finset.mem_singleton] at ht hu
    exact (htu (ht.trans hu.symm)).elim
  large := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    simp only [dirichletPhase_zero, mul_one, Finset.sum_const,
      Nat.card_Icc, nsmul_one, Complex.norm_natCast]
    have hcard : 2 * N + 1 - N = N + 1 := by omega
    rw [hcard, Nat.cast_add, Nat.cast_one]
    have hp : (N : ℝ) ^ σ ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN.le) hσ
    linarith

theorem singletonLargeValuePattern_energy
    (N : ℕ) (σ τ : ℝ) (hN : 1 < N) (hσ : σ ≤ 1) :
    finsetAdditiveEnergy (singletonLargeValuePattern N σ τ hN hσ).ordinates = 1 := by
  change finsetAdditiveEnergy ({0} : Finset ℝ) = 1
  apply le_antisymm
  · simpa using finset_additiveEnergy_le_fourthPower ({0} : Finset ℝ)
  · simpa using finset_card_square_le_additiveEnergy ({0} : Finset ℝ)

/-- Singleton patterns exclude negative general energy bounds whenever
the requested value exponent is at most one. -/
theorem IsLargeValueEnergyBound.nonneg
    {σ τ ρstar : ℝ} (h : IsLargeValueEnergyBound σ τ ρstar) (hσ : σ ≤ 1) :
    0 ≤ ρstar := by
  by_contra hnot
  have hneg : ρstar < 0 := lt_of_not_ge hnot
  let ε := -ρstar / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _hC, δ, hδ, hbound⟩ := h ε hε
  have hNtop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlimit : Filter.Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-ε))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul ((tendsto_rpow_neg_atTop hε).comp hNtop)
  have hsmall := (tendsto_order.mp hlimit).2 (1 : ℝ) (by norm_num)
  have hCN := hNtop.eventually (Filter.eventually_ge_atTop C)
  obtain ⟨N, hsmallN, hCN, hNtwo⟩ :=
    (hsmall.and (hCN.and (Filter.eventually_ge_atTop (2 : ℕ)))).exists
  have hN : 1 < N := by omega
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  let P := singletonLargeValuePattern N σ τ hN hσ
  have henergy := hbound P hCN
    (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : τ - δ ≤ τ))
    (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : τ ≤ τ + δ))
    (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : σ - δ ≤ σ))
    (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : σ ≤ σ + δ))
  have he : (1 : ℝ) ≤ C * (N : ℝ) ^ (ρstar + ε) := by
    simpa only [P, singletonLargeValuePattern_energy, Nat.cast_one] using henergy
  have hexponent : ρstar + ε = -ε := by dsimp [ε]; ring
  rw [hexponent] at he
  exact (not_le_of_gt hsmallN) he

/-- The extended-real general energy exponent is nonnegative, with no
assumed nonemptiness or finiteness of its defining set of bounds. -/
theorem largeValueEnergyExponent_nonneg (σ τ : ℝ) (hσ : σ ≤ 1) :
    0 ≤ largeValueEnergyExponent σ τ := by
  unfold largeValueEnergyExponent
  apply le_sInf
  rintro x ⟨B, hB, rfl⟩
  exact EReal.coe_nonneg.mpr (IsLargeValueEnergyBound.nonneg hB hσ)

/-- The exact extended-real right side of `zeroe-from-large`: the zeta
energy supremum starts at one, while the general term is a genuine limsup. -/
def zeroEnergyTransferEnvelope (σ : ℝ) : EReal :=
  max (sSup ((fun τ : ℝ => zetaLargeValueEnergyExponent σ τ / (τ : EReal)) '' Set.Ici 1))
    (Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop)

/-- The general-energy limsup makes the transfer envelope nonnegative. -/
theorem zeroEnergyTransferEnvelope_nonneg (σ : ℝ) (hσ : σ ≤ 1) :
    0 ≤ zeroEnergyTransferEnvelope σ := by
  have he : ∀ᶠ τ : ℝ in Filter.atTop,
      (0 : EReal) ≤ largeValueEnergyExponent σ τ / (τ : EReal) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact EReal.div_nonneg (largeValueEnergyExponent_nonneg σ τ hσ)
      (EReal.coe_nonneg.mpr hτ)
  have hlim : (0 : EReal) ≤
      Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop := by
    simpa using Filter.limsup_le_limsup he
  exact hlim.trans (le_max_right _ _)

/-- The paper's `zeroe-from-large` inequality on its exact source domain.
The proof consumes the actual Type I/II zero extraction, multiplicity-safe
energy transfer, compact-scale uniformity, and symmetric-rectangle assembly.
No large-value or zero-energy theorem is assumed in this statement. -/
theorem zeroDensityEnergyExponent_le_sup_limsup
    (σ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1) :
    zeroDensityEnergyExponent σ * ((1 - σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueEnergyExponent σ τ / (τ : EReal)) '' Set.Ici 1))
        (Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop) := by
  change zeroDensityEnergyExponent σ * ((1 - σ : ℝ) : EReal) ≤ zeroEnergyTransferEnvelope σ
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hEnvelope
  have hB : 0 < B := EReal.coe_pos.mp
    ((zeroEnergyTransferEnvelope_nonneg σ hσUpper.le).trans_lt hEnvelope)
  have hZeta : ∀ τ : ℝ, 1 ≤ τ → IsZetaLargeValueEnergyBound σ τ (B * τ) := by
    intro τ hτ
    have hτpos : 0 < τ := zero_lt_one.trans_le hτ
    apply isZetaLargeValueEnergyBound_of_exponent_le hσ.le hσUpper.le hτpos.le
    have hsup : zetaLargeValueEnergyExponent σ τ / (τ : EReal) ≤
        sSup ((fun u : ℝ => zetaLargeValueEnergyExponent σ u / (u : EReal)) '' Set.Ici 1) :=
      le_sSup ⟨τ, hτ, rfl⟩
    have hratio : zetaLargeValueEnergyExponent σ τ / (τ : EReal) ≤
        zeroEnergyTransferEnvelope σ := hsup.trans (le_max_left _ _)
    have hp := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτpos)
      (EReal.coe_ne_top τ)).mp (hratio.trans hEnvelope.le)
    simpa only [← EReal.coe_mul, mul_comm τ B] using hp
  have hlimsup :
      Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop <
        (B : EReal) := (le_max_right _ _).trans_lt hEnvelope
  obtain ⟨τ₁, hτ₁⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_limsup_lt hlimsup)
  let τ₀ := max 1 τ₁
  have hτ₀ : 0 < τ₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hGeneral : ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueEnergyBound σ τ (B * τ) := by
    intro τ hτ
    have hτpos : 0 < τ := hτ₀.trans_le hτ
    apply isLargeValueEnergyBound_of_exponent_le hσ.le hσUpper.le hτpos.le
    have hratio := (hτ₁ τ ((le_max_right _ _).trans hτ)).le
    have hp := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτpos)
      (EReal.coe_ne_top τ)).mp hratio
    simpa only [← EReal.coe_mul, mul_comm τ B] using hp
  have hzero := zeroDensityEnergyExponent_le_of_bound
    (isZeroDensityEnergyBound_of_uniform_energy_bounds σ B τ₀ hσ hσUpper hB.le hτ₀ hZeta hGeneral)
  apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr (by linarith : 0 < 1 - σ))
    (EReal.coe_ne_top (1 - σ))).mp
  simpa only [← EReal.coe_div] using hzero

end TaoTrudgianYang2025
