import Dubon2026.SourceIntegralSlashReducedPowers

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual reduced slash field embedding. Normalize
actual integral forms of weight 12r by the r-th power of the original
discriminant. These generators recover the entire original integral-ratio
field, including representatives of arbitrary integer weight. Multiplication
by g^11 and a discriminant power gives a common nonnegative weight; no weight
positivity or alternate function field is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash,
XHCuspEmbed.GenSet and exists_uv. Only the needed Gamma1 specialization is used. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne IntegralDiamond IntermediateField
open scoped MatrixGroups ModularForm

/-- Actual integral modular forms of weight 12r divided by the original discriminant to power r. -/
def normalizedGenerators (N : ℕ) (K : Type*) [Field K] : Set (LaurentSeries K) :=
  {x | ∃ (r : ℕ) (f : ModularForm (Gamma1 N) (12 * (r : ℤ))) (p : PowerSeries ℤ),
    IsIntegralQExp f p ∧ x = intSeriesC K p / intSeriesC K discriminantSeries ^ r}

theorem mem_normalizedGenerators {N : ℕ} {K : Type*} [Field K]
    {k : ℤ} {r : ℕ} (f : ModularForm (Gamma1 N) k) {p : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (hk : k = 12 * (r : ℤ)) :
    intSeriesC K p / intSeriesC K discriminantSeries ^ r ∈ normalizedGenerators N K :=
  ⟨r, f.mcast hk, p, hp, rfl⟩

theorem intSeriesC_pow_eq (K : Type*) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (p ^ n) = intSeriesC K p ^ n := by
  simp only [intSeriesC, map_pow]

theorem one_mem_normalizedGenerators (N : ℕ) (K : Type*) [Field K] :
    (1 : LaurentSeries K) ∈ normalizedGenerators N K := by
  simpa only [intSeriesC, map_one, pow_zero, div_one] using
    mem_normalizedGenerators (K := K) (r := 0) (1 : ModularForm (Gamma1 N) 0)
      (integralQExp_one N) (by simp)

theorem mul_mem_normalizedGenerators {N : ℕ} {K : Type*} [Field K]
    {x y : LaurentSeries K} (hx : x ∈ normalizedGenerators N K)
    (hy : y ∈ normalizedGenerators N K) : x * y ∈ normalizedGenerators N K := by
  obtain ⟨r, f, p, hp, rfl⟩ := hx
  obtain ⟨s, g, q, hq, rfl⟩ := hy
  have h := mem_normalizedGenerators (K := K) (r := r + s) (f.mul g)
    (integralQExp_mul f g hp hq) (by push_cast; ring)
  simpa only [intSeriesC_mul, pow_add, div_mul_div_comm] using h

theorem normalizedGenerators_subset (N : ℕ) [NeZero N] (K : Type*) [Field K] :
    normalizedGenerators N K ⊆ (qExpFunctionFieldC K (Gamma1 N) : Set (LaurentSeries K)) := by
  rintro x ⟨r, f, p, hp, rfl⟩
  have hd : intSeriesC K (discriminantSeries ^ r) ≠ 0 := by
    rw [intSeriesC_pow_eq]
    exact pow_ne_zero _ (intSeriesC_discriminant_ne_zero K)
  have h := div_mem_qExpFunctionFieldC f (gammaOneDiscriminantPow N r) hp
    (integralQExp_gammaOneDiscriminantPow N r) hd
  rwa [intSeriesC_pow_eq] at h

theorem integral_ratio_eq_div_normalizedGenerators (N : ℕ) [NeZero N]
    {K : Type*} [Field K] {k : ℤ} (f g : ModularForm (Gamma1 N) k)
    {p q : PowerSeries ℤ} (hp : IsIntegralQExp f p) (hq : IsIntegralQExp g q)
    (hq0 : intSeriesC K q ≠ 0) :
    ∃ u v : LaurentSeries K, u ∈ normalizedGenerators N K ∧
      v ∈ normalizedGenerators N K ∧ v ≠ 0 ∧
        intSeriesC K p / intSeriesC K q = u / v := by
  let s := k.natAbs
  have h0 : 0 ≤ k + (s : ℤ) := by
    have h := Int.le_natAbs (a := -k)
    rw [Int.natAbs_neg] at h
    dsimp only [s]
    omega
  let r := (k + (s : ℤ)).toNat
  have hr : (r : ℤ) = k + s := Int.toNat_of_nonneg h0
  let uF := (f.mul (g.pow 11)).mul (gammaOneDiscriminantPow N s)
  let vF := (g.pow 12).mul (gammaOneDiscriminantPow N s)
  let pu := p * q ^ 11 * discriminantSeries ^ s
  let pv := q ^ 12 * discriminantSeries ^ s
  have hpu : IsIntegralQExp uF pu :=
    integralQExp_mul (f.mul (g.pow 11)) (gammaOneDiscriminantPow N s)
      (integralQExp_mul f (g.pow 11) hp (integralQExp_pow N g hq 11))
      (integralQExp_gammaOneDiscriminantPow N s)
  have hpv : IsIntegralQExp vF pv :=
    integralQExp_mul (g.pow 12) (gammaOneDiscriminantPow N s)
      (integralQExp_pow N g hq 12) (integralQExp_gammaOneDiscriminantPow N s)
  have hku : k + 11 * k + 12 * (s : ℤ) = 12 * (r : ℤ) := by rw [hr]; ring
  have hkv : 12 * k + 12 * (s : ℤ) = 12 * (r : ℤ) := by rw [hr]; ring
  let d := intSeriesC K discriminantSeries
  let w := intSeriesC K q ^ 11 * d ^ s
  have hd : d ≠ 0 := intSeriesC_discriminant_ne_zero K
  have hw : w ≠ 0 := mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hd)
  have hu : intSeriesC K pu = intSeriesC K p * w := by
    dsimp only [pu, w, d]
    rw [intSeriesC_mul, intSeriesC_mul, intSeriesC_pow_eq, intSeriesC_pow_eq, mul_assoc]
  have hv : intSeriesC K pv = intSeriesC K q * w := by
    dsimp only [pv, w, d]
    rw [intSeriesC_mul, intSeriesC_pow_eq, intSeriesC_pow_eq,
      show (12 : ℕ) = 11 + 1 from rfl, pow_succ', mul_assoc]
  refine ⟨intSeriesC K pu / d ^ r, intSeriesC K pv / d ^ r,
    mem_normalizedGenerators uF hpu hku, mem_normalizedGenerators vF hpv hkv, ?_, ?_⟩
  · rw [hv]
    exact div_ne_zero (mul_ne_zero hq0 hw) (pow_ne_zero _ hd)
  · rw [div_div_div_cancel_right₀ (pow_ne_zero _ hd), hu, hv,
      mul_div_mul_right _ _ hw]

theorem originalField_eq_adjoin_normalizedGenerators (N : ℕ) [NeZero N]
    (K : Type*) [Field K] :
    qExpFunctionFieldC K (Gamma1 N) = IntermediateField.adjoin K (normalizedGenerators N K) := by
  refine le_antisymm ?_ (IntermediateField.adjoin_le_iff.mpr (normalizedGenerators_subset N K))
  change IntermediateField.adjoin K (intFormRatiosC K (Gamma1 N)) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨k, f, g, p, q, hp, hq, hq0, rfl⟩
  obtain ⟨u, v, hu, hv, _, he⟩ := integral_ratio_eq_div_normalizedGenerators N f g hp hq hq0
  rw [he]
  exact div_mem (IntermediateField.subset_adjoin K _ hu) (IntermediateField.subset_adjoin K _ hv)

end
end Dubon2026.SourceFunctionField.IntegralSlash
