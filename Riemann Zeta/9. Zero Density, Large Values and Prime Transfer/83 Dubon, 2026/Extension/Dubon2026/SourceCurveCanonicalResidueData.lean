import Dubon2026.SourceCurveLocalResidueUniqueness

/-! DUB-17/18 -> Riemann--Roch -> residue duality -> canonical local residues.
These data have the literal normalization fields of
Def_AlgebraicCurve_LocalResidue, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The direct principal-part construction supplies the data at rational
places. No global residue theorem is assumed or claimed by this construction.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The actual local residue map and its regular/simple-pole normalization. -/
structure LocalResidueData where
  /-- The residue-field-valued linear map on the actual function field. -/
  res : F →ₗ[K] v.ResidueField
  /-- Integral functions have zero residue. -/
  res_of_mem : ∀ f : F, f ∈ v.toValuationSubring → res f = 0
  /-- A simple pole is evaluated by the actual residue of its cleared value. -/
  res_simplePole : ∀ (f : F) (hf : v.uniformizer * f ∈ v.toValuationSubring),
    res f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩

/-- The source canonical normalization additionally kills higher pure poles. -/
structure CanonicalLocalResidueDataK extends v.LocalResidueData where
  /-- Higher negative pure uniformizer powers have no simple-pole coefficient. -/
  res_higherPoleMonomial : ∀ n : ℕ, 1 ≤ n → res (v.uniformizer ^ (n + 1))⁻¹ = 0

/-- The canonical normalized residue obtained from actual principal parts. -/
def canonicalLocalResidueData
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    v.CanonicalLocalResidueDataK where
  res := (Algebra.linearMap K v.ResidueField).comp v.localResidueScalar
  res_of_mem f hf := by
    change algebraMap K v.ResidueField (v.localResidueScalar f) = 0
    rw [v.localResidueScalar_of_mem hf, map_zero]
  res_simplePole := v.localResidueScalar_simplePole hres
  res_higherPoleMonomial n hn := by
    change algebraMap K v.ResidueField (v.localResidueScalar (v.uniformizer ^ (n + 1))⁻¹) = 0
    rw [v.localResidueScalar_higherPole n hn, map_zero]

theorem canonicalLocalResidueData_res_unique
    (hres : Function.Bijective (algebraMap K v.ResidueField))
    (d : v.CanonicalLocalResidueDataK) :
    d.res = (v.canonicalLocalResidueData hres.surjective).res := by
  let e : K ≃ₐ[K] v.ResidueField := AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hres
  let χ : F →ₗ[K] K := e.symm.toLinearMap.comp d.res
  have hreg : ∀ f : F, f ∈ v.toValuationSubring → χ f = 0 := by
    intro f hf
    change e.symm (d.res f) = 0
    rw [d.res_of_mem f hf, map_zero]
  have hpole : ∀ n : ℕ, χ (v.uniformizer ^ (-(n + 1 : ℤ))) =
      if n = 0 then 1 else 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero, zero_add, zpow_neg_one]
      have hm : v.uniformizer * v.uniformizer⁻¹ ∈ v.toValuationSubring := by
        rw [mul_inv_cancel₀ v.uniformizer_ne_zero]
        exact one_mem _
      change e.symm (d.res v.uniformizer⁻¹) = 1
      rw [d.res_simplePole _ hm]
      have he : (⟨v.uniformizer * v.uniformizer⁻¹, hm⟩ : v.toValuationSubring) = 1 :=
        Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
      rw [he, map_one, map_one]
    · rw [if_neg hn]
      change e.symm (d.res (v.uniformizer ^ (-(n + 1 : ℤ)))) = 0
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
        d.res_higherPoleMonomial n (by omega), map_zero]
  have hχ := v.localResidueScalar_unique hres.surjective χ hreg hpole
  ext f
  have hf := LinearMap.congr_fun hχ f
  have hh := congrArg e hf
  change e (e.symm (d.res f)) = algebraMap K v.ResidueField (v.localResidueScalar f) at hh
  simpa only [AlgEquiv.apply_symm_apply] using hh

end
end Dubon2026.SourceCurve.Place
