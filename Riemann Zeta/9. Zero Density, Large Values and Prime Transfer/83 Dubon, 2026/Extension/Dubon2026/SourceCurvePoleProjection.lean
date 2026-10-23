import Dubon2026.SourceCurvePoleClassSpan

/-! The canonical projection onto integral functions at a rational place.
The existing independent pure-pole classes and the proved spanning theorem
give the actual finite principal part. This projection is the local operator
whose commutator trace must agree with the already constructed residue. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Lift a pure-pole class to its uniquely determined finite sum of negative powers. -/
def principalPartLift : (F ⧸ v.integralFunctions) →ₗ[K] F :=
  (Finsupp.linearCombination K (fun n : ℕ => v.uniformizer ^ (-(n + 1 : ℤ)))).comp
    (Finsupp.linearCombination K v.poleClass).leftInverse

/-- The finite principal part of a function at the place. -/
def principalPart : F →ₗ[K] F := v.principalPartLift.comp v.integralFunctions.mkQ

/-- The principal-part lift sends each pure pole class to that same negative power. -/
theorem principalPartLift_poleClass (n : ℕ) :
    v.principalPartLift (v.poleClass n) = v.uniformizer ^ (-(n + 1 : ℤ)) := by
  have he : v.poleClass n =
      Finsupp.linearCombination K v.poleClass (Finsupp.single n 1) := by simp
  rw [principalPartLift, LinearMap.comp_apply, he,
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr v.poleClass_linearIndependent)]
  simp

/-- At a rational place the principal-part lift is a section of the actual quotient. -/
theorem mkQ_principalPartLift
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (x : F ⧸ v.integralFunctions) :
    v.integralFunctions.mkQ (v.principalPartLift x) = x := by
  obtain ⟨c, rfl⟩ := (v.poleClass_linearCombination_bijective hres).surjective x
  rw [principalPartLift, LinearMap.comp_apply,
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr v.poleClass_linearIndependent)]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Submodule.mkQ_apply, poleClass]

/-- Integral functions have zero principal part. -/
theorem principalPart_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.principalPart f = 0 := by
  have h : v.integralFunctions.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hf
  simp only [principalPart, LinearMap.comp_apply, h, map_zero]

/-- The projection onto integral functions obtained by removing the finite principal part. -/
def tateProj : F →ₗ[K] F := LinearMap.id - v.principalPart

/-- Removing the principal part leaves an actual integral function. -/
theorem tateProj_mem
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    v.tateProj f ∈ v.integralFunctions := by
  rw [← Submodule.Quotient.mk_eq_zero]
  change v.integralFunctions.mkQ (f - v.principalPartLift (v.integralFunctions.mkQ f)) = 0
  rw [map_sub, v.mkQ_principalPartLift hres, sub_self]

/-- The canonical projection fixes every integral function. -/
theorem tateProj_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.tateProj f = f := by
  simp only [tateProj, LinearMap.sub_apply, LinearMap.id_apply, v.principalPart_of_mem hf,
    sub_zero]

/-- Its range is exactly the actual valuation subring as a constant-field subspace. -/
theorem range_tateProj
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    LinearMap.range v.tateProj = v.integralFunctions := by
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    exact v.tateProj_mem hres f
  · intro x hx
    exact ⟨x, v.tateProj_of_mem hx⟩

/-- Applying the projection twice has the same value as applying it once. -/
theorem tateProj_idem
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    v.tateProj (v.tateProj f) = v.tateProj f :=
  v.tateProj_of_mem (v.tateProj_mem hres f)

end Dubon2026.SourceCurve.Place
