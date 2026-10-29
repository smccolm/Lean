import Dubon2026.SourceIntegralSlashNormalizedMap

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual reduced slash field embedding. A common
power of the actual discriminant brings every finite family of normalized
generators to one even weight. The proved same-weight relation transfer then
preserves every linear relation among these function-field generators.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash,
XHCuspEmbed.thetaHat_lin. All original coefficient and denominator facts are
discharged by the native localization and discriminant proofs. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne IntegralDiamond
open scoped MatrixGroups ModularForm
local notation "Zbar" => integralClosure ℤ ℂ

theorem ofPowerSeries_smul {K : Type*} [Field K] (c : K) (p : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (c • p) = c • HahnSeries.ofPowerSeries ℤ K p := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem normalizedSlashValue_linear_relation (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    {K : Type*} [Field K] [CharP K ℓ] (φ : Zbar →+* K) (hN : (N : K) ≠ 0)
    (β : SL(2, ℤ)) (c : LaurentSeries K →₀ K)
    (hcG : (↑c.support : Set (LaurentSeries K)) ⊆ normalizedGenerators N K)
    (hc0 : (c.sum fun x a => a • x) = 0) :
    (c.sum fun x a => a • normalizedSlashValue N φ hN β x) = 0 := by
  classical
  let s := c.support
  have hmem : ∀ i : s, (i : LaurentSeries K) ∈ normalizedGenerators N K := fun i => hcG i.property
  let r : s → ℕ := fun i => (hmem i).choose
  let f : (i : s) → ModularForm (Gamma1 N) (12 * (r i : ℤ)) :=
    fun i => (hmem i).choose_spec.choose
  let p : s → PowerSeries ℤ := fun i => (hmem i).choose_spec.choose_spec.choose
  have hp : ∀ i, IsIntegralQExp (f i) (p i) ∧
      (i : LaurentSeries K) = intSeriesC K (p i) / intSeriesC K discriminantSeries ^ r i :=
    fun i => (hmem i).choose_spec.choose_spec.choose_spec
  let R := Finset.univ.sup r
  have hrR : ∀ i, r i ≤ R := fun i => Finset.le_sup (f := r) (Finset.mem_univ i)
  let hwt (i : s) : 12 * (r i : ℤ) + 12 * (↑(R - r i) : ℤ) = 12 * (R : ℤ) := by
    rw [Nat.cast_sub (hrR i)]
    ring
  let G : s → ModularForm (Gamma1 N) (12 * (R : ℤ)) :=
    fun i => ((f i).mul (gammaOneDiscriminantPow N (R - r i))).mcast (hwt i)
  let P : s → PowerSeries ℤ := fun i => p i * discriminantSeries ^ (R - r i)
  have hGP : ∀ i, IsIntegralQExp (G i) (P i) := fun i =>
    integralQExp_mul (f i) (gammaOneDiscriminantPow N (R - r i))
      (hp i).1 (integralQExp_gammaOneDiscriminantPow N (R - r i))
  let d := intSeriesC K discriminantSeries
  have hd : d ≠ 0 := intSeriesC_discriminant_ne_zero K
  have hval : ∀ i : s, (i : LaurentSeries K) = intSeriesC K (P i) / d ^ R := by
    intro i
    rw [(hp i).2]
    dsimp only [P]
    rw [intSeriesC_mul, intSeriesC_pow_eq,
      ← pow_mul_pow_sub d (hrR i), mul_div_mul_right _ _ (pow_ne_zero _ hd)]
  have hsum : ∀ F : LaurentSeries K → LaurentSeries K,
      (c.sum fun x a => a • F x) = ∑ i : s, c i • F i := by
    intro F
    rw [Finsupp.sum, ← Finset.sum_attach]
    rfl
  have hrel : ∑ i : s, c i • intSeriesC K (P i) = 0 := by
    rw [hsum] at hc0
    have he : ∑ i : s, c i • (i : LaurentSeries K) =
        (∑ i : s, c i • intSeriesC K (P i)) / d ^ R := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hval i, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_div_assoc]
    rw [he, div_eq_zero_iff] at hc0
    exact hc0.resolve_right (pow_ne_zero _ hd)
  have hcoef : ∀ n : ℕ, ∑ i : s, c i * ((P i).coeff n : K) = 0 := by
    intro n
    have he := congrArg (fun z : LaurentSeries K => z.coeff (n : ℤ)) hrel
    simpa only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul,
      intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      eq_intCast, HahnSeries.coeff_zero] using he
  let eR : Even (12 * (R : ℤ)) := (show Even (12 : ℤ) by decide).mul_right _
  have hT := reducedSlashSeries_linear_relation N ℓ φ hN β eR Finset.univ
    G P hGP (fun i => c i) hcoef
  rw [hsum]
  have hmap : ∀ i : s, normalizedSlashValue N φ hN β i =
      HahnSeries.ofPowerSeries ℤ K (reducedSlashSeries N eR (G i) (hGP i) β φ hN) /
        HahnSeries.ofPowerSeries ℤ K (reducedSlashSeries N (by decide)
          (gammaOneDiscriminant N) (integralQExp_gammaOneDiscriminant N) β φ hN) ^ R :=
    fun i => normalizedSlashValue_eq N φ hN β ℓ (G i) (hGP i) (hval i)
  have he : ∑ i : s, c i • normalizedSlashValue N φ hN β i =
      HahnSeries.ofPowerSeries ℤ K
        (∑ i : s, c i • reducedSlashSeries N eR (G i) (hGP i) β φ hN) /
      HahnSeries.ofPowerSeries ℤ K (reducedSlashSeries N (by decide)
        (gammaOneDiscriminant N) (integralQExp_gammaOneDiscriminant N) β φ hN) ^ R := by
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmap i, ofPowerSeries_smul, ← HahnSeries.C_mul_eq_smul,
      ← HahnSeries.C_mul_eq_smul, mul_div_assoc]
  rw [he, hT, map_zero, zero_div]

end
end Dubon2026.SourceFunctionField.IntegralSlash
