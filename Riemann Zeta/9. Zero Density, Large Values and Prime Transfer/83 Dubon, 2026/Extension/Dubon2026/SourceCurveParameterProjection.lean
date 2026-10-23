import Dubon2026.SourceCurveParameterPoleSpan

/-! A finite principal part and integral retraction for a specified
order-one coordinate. The existing quotient construction applies to its
proved pole basis. This is the exact projection needed for the rational
Tate residue calculation in the DUB-17/18 global residue argument. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Lift the finite principal part in the specified coordinate. -/
def parameterPrincipalPartLift (t : F) : (F ⧸ v.integralFunctions) →ₗ[K] F :=
  (Finsupp.linearCombination K (fun n : ℕ => t ^ (-(n + 1 : ℤ)))).comp
    (Finsupp.linearCombination K (v.parameterPoleClass t)).leftInverse

/-- The actual finite principal part in the specified coordinate. -/
def parameterPrincipalPart (t : F) : F →ₗ[K] F :=
  (v.parameterPrincipalPartLift t).comp v.integralFunctions.mkQ

/-- The principal-part lift fixes each pure pole in the specified coordinate. -/
theorem parameterPrincipalPartLift_poleClass {t : F} (ht : v.ord t = 1) (n : ℕ) :
    v.parameterPrincipalPartLift t (v.parameterPoleClass t n) = t ^ (-(n + 1 : ℤ)) := by
  have he : v.parameterPoleClass t n =
      Finsupp.linearCombination K (v.parameterPoleClass t) (Finsupp.single n 1) := by simp
  rw [parameterPrincipalPartLift, LinearMap.comp_apply, he,
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr (v.parameterPoleClass_linearIndependent ht))]
  simp

/-- The parameter principal-part lift is a section of the actual quotient. -/
theorem mkQ_parameterPrincipalPartLift {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (x : F ⧸ v.integralFunctions) :
    v.integralFunctions.mkQ (v.parameterPrincipalPartLift t x) = x := by
  obtain ⟨c, rfl⟩ := (v.parameterPoleClass_linearCombination_bijective ht hres).surjective x
  rw [parameterPrincipalPartLift, LinearMap.comp_apply,
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr (v.parameterPoleClass_linearIndependent ht))]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Submodule.mkQ_apply, parameterPoleClass]

/-- Integral functions have zero parameter principal part. -/
theorem parameterPrincipalPart_of_mem (t : F) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.parameterPrincipalPart t f = 0 := by
  have h : v.integralFunctions.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hf
  simp only [parameterPrincipalPart, LinearMap.comp_apply, h, map_zero]

/-- Remove the finite principal part in the specified coordinate. -/
def parameterProj (t : F) : F →ₗ[K] F := LinearMap.id - v.parameterPrincipalPart t

/-- Removing the parameter principal part leaves an actual integral function. -/
theorem parameterProj_mem {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    v.parameterProj t f ∈ v.integralFunctions := by
  rw [← Submodule.Quotient.mk_eq_zero]
  change v.integralFunctions.mkQ (f - v.parameterPrincipalPartLift t (v.integralFunctions.mkQ f)) = 0
  rw [map_sub, v.mkQ_parameterPrincipalPartLift ht hres, sub_self]

/-- The parameter projection fixes each integral function. -/
theorem parameterProj_of_mem (t : F) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.parameterProj t f = f := by
  simp only [parameterProj, LinearMap.sub_apply, LinearMap.id_apply,
    v.parameterPrincipalPart_of_mem t hf, sub_zero]

/-- The parameter projection as a retraction to the literal integral subspace. -/
def parameterIntegralRetraction {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    F →ₗ[K] v.integralFunctions :=
  (v.parameterProj t).codRestrict _ (v.parameterProj_mem ht hres)

/-- The constructed parameter retraction fixes the actual integral subspace. -/
theorem parameterIntegralRetraction_apply {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (a : v.integralFunctions) :
    v.parameterIntegralRetraction ht hres a = a :=
  Subtype.ext (v.parameterProj_of_mem t a.2)

end Dubon2026.SourceCurve.Place
