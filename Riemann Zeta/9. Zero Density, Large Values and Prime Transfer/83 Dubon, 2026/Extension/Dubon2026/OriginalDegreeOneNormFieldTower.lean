import Dubon2026.OriginalFinitePrimeOrbits
import Dubon2026.UnramifiedUnionFiniteFieldCriterion

/-! # Returning a norm field through a degree-one base realization

An actual degree-one field inclusion is an isomorphism. It preserves
Galoisness of the upper extension and has ramification index one at
every finite prime. These are the field hypotheses for the literal
norm descent from the unrestricted arithmetic realization to the
original base in DUB-17's invariant norm-root construction.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [FiniteDimensional K E]

omit [FiniteDimensional K E] in
/-- Every finite prime has ramification index one in an actual
degree-one base realization. -/
theorem originalDegreeOne_ramification_one (hDegree : Module.finrank K E = 1)
    (w : HeightOneSpectrum (𝓞 E)) :
    (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  letI : NoZeroSMulDivisors (𝓞 K) (𝓞 E) := ⟨by
    intro c x h
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left
      apply NumberField.RingOfIntegers.ext
      apply (algebraMap K E).injective
      simpa only [map_zero] using congrArg (fun z : 𝓞 E => (z : E)) h
    · exact Or.inr h⟩
  let v := originalFinitePrimeBelow K E w
  letI := originalFinitePrimeBelow_liesOver K E w
  have hle := Ideal.ramificationIdx_le_finrank (K := K) (L := E) (𝓞 E)
    (p := v.asIdeal) w.asIdeal
  rw [hDegree] at hle
  exact Nat.le_antisymm hle (Nat.one_le_iff_ne_zero.mpr
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot))

omit [NumberField K] [NumberField E] in
/-- A Galois extension over an actual degree-one realization is Galois
over the original base, using the proved inverse algebra map. -/
theorem originalDegreeOne_tower_isGalois (hDegree : Module.finrank K E = 1)
    (L : Type) [Field L] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [IsGalois E L] : IsGalois K L := by
  have hb := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := K) (E := E)).mp hDegree
  let e : K ≃ₐ[K] E := AlgEquiv.ofBijective (Algebra.ofId K E) hb
  apply IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv) (g := RingEquiv.refl L)
  ext x
  change algebraMap K L (e.symm x) = algebraMap E L x
  rw [IsScalarTower.algebraMap_apply K E L]
  change algebraMap E L (e (e.symm x)) = _
  rw [e.apply_symm_apply]

end
end Dubon2026
