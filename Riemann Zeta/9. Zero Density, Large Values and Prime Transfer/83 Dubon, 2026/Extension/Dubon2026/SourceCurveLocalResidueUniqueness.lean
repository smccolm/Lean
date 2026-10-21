import Dubon2026.SourceCurveLocalResidueScalar

/-! DUB-17/18 -> Riemann--Roch -> residue duality -> canonical local residues.
At a rational place every function has a finite principal part. Induction
on a cleared pole proves that integral values and pure-pole coefficients
determine a scalar linear residue map uniquely. This identifies the direct
construction with any canonical map satisfying the same source normalization.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem uniformizer_pow_mul_neg_pow (n : ℕ) :
    v.uniformizer ^ n * v.uniformizer ^ (-(n + 1 : ℤ)) = v.uniformizer⁻¹ := by
  rw [← zpow_natCast, ← zpow_add₀ v.uniformizer_ne_zero]
  have he : (n : ℤ) + -(n + 1 : ℤ) = -1 := by omega
  rw [he, zpow_neg_one]

theorem clear_pole_mem (f : F) :
    v.uniformizer ^ (-v.ord f).toNat * f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  apply v.mem_of_ord_nonneg
  rw [v.ord_mul (pow_ne_zero _ v.uniformizer_ne_zero) hf,
    ← zpow_natCast, v.ord_zpow, v.ord_uniformizer, mul_one]
  omega

theorem linearMap_zero_of_integral_and_poles
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (χ : F →ₗ[K] K)
    (hreg : ∀ f : F, f ∈ v.toValuationSubring → χ f = 0)
    (hpole : ∀ n : ℕ, χ (v.uniformizer ^ (-(n + 1 : ℤ))) = 0) : χ = 0 := by
  have hclear : ∀ (n : ℕ) (f : F),
      v.uniformizer ^ n * f ∈ v.toValuationSubring → χ f = 0 := by
    intro n
    induction n with
    | zero =>
      intro f hf
      exact hreg f (by simpa using hf)
    | succ n ih =>
      intro f hf
      have hfg : v.uniformizer * (v.uniformizer ^ n * f) ∈ v.toValuationSubring := by
        simpa only [pow_succ, mul_assoc, mul_left_comm] using hf
      obtain ⟨c, _, hc⟩ := v.exists_integral_sub_simplePole hres (v.uniformizer ^ n * f) hfg
      have hrem : v.uniformizer ^ n * (f - c • v.uniformizer ^ (-(n + 1 : ℤ))) ∈
          v.toValuationSubring := by
        rw [mul_sub, Algebra.smul_def, mul_left_comm (v.uniformizer ^ n),
          v.uniformizer_pow_mul_neg_pow]
        simpa only [Algebra.smul_def] using hc
      have hh := ih _ hrem
      rw [map_sub, map_smul, hpole, smul_zero, sub_zero] at hh
      exact hh
  ext f
  exact hclear _ f (v.clear_pole_mem f)

theorem localResidueScalar_unique
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (χ : F →ₗ[K] K)
    (hreg : ∀ f : F, f ∈ v.toValuationSubring → χ f = 0)
    (hpole : ∀ n : ℕ, χ (v.uniformizer ^ (-(n + 1 : ℤ))) =
      if n = 0 then 1 else 0) : χ = v.localResidueScalar := by
  apply sub_eq_zero.mp
  apply v.linearMap_zero_of_integral_and_poles hres
  · intro f hf
    simp only [LinearMap.sub_apply, hreg f hf, v.localResidueScalar_of_mem hf, sub_self]
  · intro n
    simp only [LinearMap.sub_apply, hpole n, v.localResidueScalar_neg_pow n, sub_self]

end
end Dubon2026.SourceCurve.Place
