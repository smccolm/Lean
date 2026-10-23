import Dubon2026.SourceCurveParameterProjection

/-! The simple-pole coefficient in a specified order-one coordinate.
The parameter projection extracts this coefficient after multiplication
by the parameter. The next trace comparison identifies it with the actual
Tate residue, as needed for the rational-field DUB-17/18 residue theorem. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The actual simple-pole coefficient in the specified coordinate. -/
def parameterResidueScalar (t : F) : F →ₗ[K] K :=
  (Finsupp.lapply 0).comp
    ((Finsupp.linearCombination K (v.parameterPoleClass t)).leftInverse.comp
      v.integralFunctions.mkQ)

/-- The parameter coefficient vanishes on integral functions. -/
theorem parameterResidueScalar_of_mem (t : F) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.parameterResidueScalar t f = 0 := by
  have hq : v.integralFunctions.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hf
  simp only [parameterResidueScalar, LinearMap.comp_apply, hq, map_zero]

/-- A pure negative power has simple-pole coefficient one exactly at exponent minus one. -/
theorem parameterResidueScalar_neg_pow {t : F} (ht : v.ord t = 1) (n : ℕ) :
    v.parameterResidueScalar t (t ^ (-(n + 1 : ℤ))) = if n = 0 then 1 else 0 := by
  have he : v.integralFunctions.mkQ (t ^ (-(n + 1 : ℤ))) =
      Finsupp.linearCombination K (v.parameterPoleClass t) (Finsupp.single n 1) := by
    rw [Finsupp.linearCombination_single, one_smul]
    rfl
  rw [parameterResidueScalar, LinearMap.comp_apply, LinearMap.comp_apply, he,
    LinearMap.leftInverse_apply_of_inj
      (linearIndependent_iff_ker.mp (v.parameterPoleClass_linearIndependent ht))]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply]

/-- The integral projection kills every pure negative power of the parameter. -/
theorem parameterProj_neg_pow {t : F} (ht : v.ord t = 1) (n : ℕ) :
    v.parameterProj t (t ^ (-(n + 1 : ℤ))) = 0 := by
  change t ^ (-(n + 1 : ℤ)) - v.parameterPrincipalPartLift t (v.parameterPoleClass t n) = 0
  rw [v.parameterPrincipalPartLift_poleClass ht, sub_self]

/-- Multiplication by the parameter extracts the simple-pole basis vector. -/
theorem parameterProj_mul_poleClass {t : F} (ht : v.ord t = 1) (n : ℕ) :
    v.parameterProj t (t * v.parameterPrincipalPartLift t (v.parameterPoleClass t n)) =
      if n = 0 then 1 else 0 := by
  rw [v.parameterPrincipalPartLift_poleClass ht]
  cases n with
  | zero =>
      simp only [Nat.cast_zero, zero_add, zpow_neg_one,
        mul_inv_cancel₀ (v.parameter_ne_zero ht), ite_true]
      exact v.parameterProj_of_mem t (one_mem _)
  | succ n =>
      have h : t * t ^ (-((n + 1 : ℕ) + 1 : ℤ)) = t ^ (-(n + 1 : ℤ)) := by
        conv_lhs => lhs; rw [← zpow_one t]
        rw [← zpow_add₀ (v.parameter_ne_zero ht)]
        congr 1
      rw [h, v.parameterProj_neg_pow ht]
      simp

/-- Projecting the parameter times the actual principal part gives its simple-pole coefficient. -/
theorem parameterProj_mul_principalPart {t : F} (ht : v.ord t = 1) (f : F) :
    v.parameterProj t (t * v.parameterPrincipalPart t f) =
      algebraMap K F (v.parameterResidueScalar t f) := by
  let c := (Finsupp.linearCombination K (v.parameterPoleClass t)).leftInverse
    (v.integralFunctions.mkQ f)
  have hc : v.parameterPrincipalPart t f =
      Finsupp.linearCombination K (fun n : ℕ => t ^ (-(n + 1 : ℤ))) c := rfl
  have hr : v.parameterResidueScalar t f = c 0 := rfl
  rw [hc, hr, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, map_sum]
  have hterm (n : ℕ) : v.parameterProj t (t * (c n • t ^ (-(n + 1 : ℤ)))) =
      if n = 0 then algebraMap K F (c n) else 0 := by
    rw [mul_smul_comm, map_smul]
    rw [← v.parameterPrincipalPartLift_poleClass ht, v.parameterProj_mul_poleClass ht]
    split_ifs <;> simp [Algebra.smul_def]
  simp_rw [hterm]
  classical
  simp
  intro hz
  rw [hz, map_zero]

end Dubon2026.SourceCurve.Place
