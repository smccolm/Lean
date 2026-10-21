import Dubon2026.SourceCurveLocalPrincipalParts
import Dubon2026.SourceCurveUniformizerResidue

/-! DUB-17/18 -> Riemann--Roch -> residue duality -> canonical local residues.
The coefficient of the simple pole is extracted from the linearly independent
pure-pole classes using a pinned linear left inverse. At a rational place,
its simple-pole value is the actual residue of the cleared pole. The
original field's residue rationality is proved elsewhere, not assumed there.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The scalar coefficient of the simple pole modulo integral functions. -/
def localResidueScalar : F →ₗ[K] K :=
  (Finsupp.lapply 0).comp
    ((Finsupp.linearCombination K v.poleClass).leftInverse.comp v.integralFunctions.mkQ)

theorem localResidueScalar_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.localResidueScalar f = 0 := by
  have hq : v.integralFunctions.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hf
  simp only [localResidueScalar, LinearMap.comp_apply, hq, map_zero]

theorem localResidueScalar_neg_pow (n : ℕ) :
    v.localResidueScalar (v.uniformizer ^ (-(n + 1 : ℤ))) =
      if n = 0 then 1 else 0 := by
  have he : v.integralFunctions.mkQ (v.uniformizer ^ (-(n + 1 : ℤ))) =
      Finsupp.linearCombination K v.poleClass (Finsupp.single n 1) := by
    rw [Finsupp.linearCombination_single, one_smul]
    rfl
  rw [localResidueScalar, LinearMap.comp_apply, LinearMap.comp_apply, he,
    LinearMap.leftInverse_apply_of_inj (linearIndependent_iff_ker.mp v.poleClass_linearIndependent)]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply]

theorem localResidueScalar_uniformizer_inv : v.localResidueScalar v.uniformizer⁻¹ = 1 := by
  simpa using v.localResidueScalar_neg_pow 0

theorem localResidueScalar_higherPole (n : ℕ) (hn : 1 ≤ n) :
    v.localResidueScalar (v.uniformizer ^ (n + 1))⁻¹ = 0 := by
  have h := v.localResidueScalar_neg_pow n
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
    if_neg (show n ≠ 0 by omega)] at h
  exact h

theorem exists_integral_sub_simplePole
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (f : F) (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    ∃ c : K, algebraMap K v.ResidueField c = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ ∧
      f - c • v.uniformizer⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨c, hc⟩ := hres (IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩)
  refine ⟨c, hc, ?_⟩
  let b : v.toValuationSubring := ⟨v.uniformizer * f, hf⟩ - algebraMap K v.toValuationSubring c
  have hb : IsLocalRing.residue _ b = 0 := by
    change IsLocalRing.residue _ (⟨v.uniformizer * f, hf⟩ - algebraMap K v.toValuationSubring c) = 0
    rw [map_sub]
    change IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ - algebraMap K v.ResidueField c = 0
    exact sub_eq_zero.mpr hc.symm
  have hbmem : b ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff b).mp hb
  rw [v.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton] at hbmem
  obtain ⟨u, hu⟩ := hbmem
  have hueq : (u : F) = f - c • v.uniformizer⁻¹ := by
    have h := congrArg (fun x : v.toValuationSubring => (x : F)) hu
    change v.uniformizer * f - algebraMap K F c = v.uniformizer * (u : F) at h
    rw [Algebra.smul_def]
    apply mul_left_cancel₀ v.uniformizer_ne_zero
    rw [mul_sub, mul_left_comm v.uniformizer (algebraMap K F c),
      mul_inv_cancel₀ v.uniformizer_ne_zero, mul_one]
    exact h.symm
  exact hueq ▸ u.2

theorem localResidueScalar_simplePole
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (f : F) (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.localResidueScalar f) =
      IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ := by
  obtain ⟨c, hc, hreg⟩ := v.exists_integral_sub_simplePole hres f hf
  have he := v.localResidueScalar_of_mem hreg
  rw [map_sub, map_smul, v.localResidueScalar_uniformizer_inv, smul_eq_mul, mul_one,
    sub_eq_zero] at he
  rw [he]
  exact hc

end
end Dubon2026.SourceCurve.Place
