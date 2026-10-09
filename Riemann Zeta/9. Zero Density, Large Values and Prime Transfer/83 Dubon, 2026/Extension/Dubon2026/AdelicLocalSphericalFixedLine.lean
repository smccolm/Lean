import Dubon2026.FinitePlaceSphericalFixedHecke
import Dubon2026.AdelicLocalClosedHeckeEigen

/-! # The actual one-dimensional spherical fixed space of the original primitive local factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem nested_submodule_rescaled_spans {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (T : Submodule ℂ S) (y : V) (n : ℂ) (hn : n ≠ 0)
    (u : T) (hu : u.val.val = n⁻¹ • y)
    (hs : ∀ x : T, ∃ c : ℂ, x.val.val = c • y) (x : T) : ∃ c : ℂ, c • u = x := by
  obtain ⟨c, hc⟩ := hs x
  refine ⟨c * n, Subtype.ext (Subtype.ext ?_)⟩
  change (c * n) • u.val.val = x.val.val
  rw [hu, smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  exact hc.symm

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)

/-- The literal original unit generator inside the actual spherical fixed space of its actual local factor. -/
def adelicLocalSphericalUnit :
    finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :=
  ⟨adelicLocalClosedUnitReference F.toCuspForm _, adelicLocalClosedUnitReference_good_fixed F hpN⟩

omit [NeZero p] in
/-- The original spherical unit is nonzero in the original fixed space. -/
theorem adelicLocalSphericalUnit_ne_zero : adelicLocalSphericalUnit F hpN ≠ 0 := by
  intro h
  have hz : adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) = 0 :=
    congrArg Subtype.val h
  have hu := adelicLocalClosedUnitReference_inner F.toCuspForm (primitiveCuspForm_ne_zero F)
    (rationalPrimePlace p (Fact.out : p.Prime))
  rw [hz] at hu
  have hzero := @inner_zero_left ℂ
    (adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    inferInstance inferInstance inferInstance 0
  exact zero_ne_one (hzero.symm.trans hu)

include hpN

omit [NeZero p] in
/-- The original spherical fixed vector retains actual ambient level invariance. -/
theorem adelicLocalSphericalFixedSpace_val_fixed
    (x : finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    x.val.val ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) := by
  have hK := finitePlaceGL2Gamma0_good_eq_one N p (Fact.out : p.Prime) hpN
  intro g
  exact congrArg (fun y : adelicLocalCyclicClosedSpan F.toCuspForm
    (rationalPrimePlace p (Fact.out : p.Prime)) => y.val) (x.property ⟨g.val, hK ▸ g.property⟩)

/-- The actual ambient value of a spherical fixed vector lies on the original generator line. -/
theorem adelicLocalSphericalFixedSpace_val_generator_scalar
    (x : finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    ∃ c : ℂ, x.val.val = c • adelicCyclicHilbertGenerator F.toCuspForm :=
  @adelicLocalCyclic_fixed_generator_scalar N p inferInstance inferInstance
    inferInstance k F hpN x.val.val x.val.property
    (@adelicLocalSphericalFixedSpace_val_fixed N p inferInstance inferInstance k F hpN x)

/-- Every original spherical fixed vector is an exact scalar multiple of the actual normalized original unit vector. -/
theorem adelicLocalSphericalUnit_spans
    (x : finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    ∃ c : ℂ, c • adelicLocalSphericalUnit F hpN = x := by
  have hn : (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F))
  exact @nested_submodule_rescaled_spans (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance (adelicLocalCyclicClosedSpan F.toCuspForm _)
    (finitePlaceSphericalFixedSpace p (adelicLocalCyclicRepresentation F.toCuspForm _))
    (adelicCyclicHilbertGenerator F.toCuspForm) _ hn (adelicLocalSphericalUnit F hpN) rfl
    (adelicLocalSphericalFixedSpace_val_generator_scalar F hpN) x

include hpN

/-- The actual full integral-fixed space of the original primitive local Hilbert factor has dimension exactly one. -/
theorem adelicLocalSphericalFixedSpace_finrank :
    Module.finrank ℂ (finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) = 1 :=
  (finrank_eq_one_iff_of_nonzero' (adelicLocalSphericalUnit F hpN)
    (adelicLocalSphericalUnit_ne_zero F hpN)).mpr (adelicLocalSphericalUnit_spans F hpN)

end
end Dubon2026
