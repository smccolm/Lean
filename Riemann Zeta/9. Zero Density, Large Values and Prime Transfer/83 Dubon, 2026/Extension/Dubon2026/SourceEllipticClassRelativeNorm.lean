import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Tactic

/-! Actual ideal-class norm and extension for the odd quotient point map.
Adapted from TauCetiProject/TauCeti, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba (crediting Chris Birkbeck's AINTLIB).
Reuse pinned native ideal norms and the integral-representative criterion.
The map between actual point groups will use the derived coordinate-ring
Dedekind property and point-class equivalence. Its intermediate ring and
coordinate evaluation remain separate obligations on the DUB-17/18 chain.
Omit general-domain extension functoriality and norm-power identities. -/
namespace Dubon2026.SourceEllipticClassGroup
noncomputable section
open scoped nonZeroDivisors
variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

variable (R) in
/-- The relative ideal norm restricted to nonzero ideals, using that it reflects `⊥`
(`Ideal.relNorm_eq_bot_iff`). -/
noncomputable def idealRelNorm : (Ideal S)⁰ →* (Ideal R)⁰ :=
  ((Ideal.relNorm R).toMonoidHom.comp (Submonoid.subtype (Ideal S)⁰)).codRestrict
      (Ideal R)⁰ fun I =>
    mem_nonZeroDivisors_iff_ne_zero.mpr <|
      Ideal.relNorm_eq_bot_iff.not.mpr <| mem_nonZeroDivisors_iff_ne_zero.mp I.2

@[simp]
theorem coe_idealRelNorm (I : (Ideal S)⁰) :
    (idealRelNorm R I : Ideal R) = Ideal.relNorm R (I : Ideal S) :=
  (rfl)

theorem mk0_relNorm0_eq_of_mk0_eq {I J : (Ideal S)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (idealRelNorm R I) = ClassGroup.mk0 (idealRelNorm R J) := by
  -- `Algebra.intNorm_ne_zero` needs the fraction fields to form a finite extension; the lifted
  -- algebra is deliberately not an instance, so it is supplied here.
  let _ : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  have : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization R (FractionRing R) (FractionRing S) S
  have : IsScalarTower R S (FractionRing S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite.of_isLocalization R S R⁰
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨Algebra.intNorm R S x, Algebra.intNorm R S y,
    Algebra.intNorm_ne_zero.mpr hx, Algebra.intNorm_ne_zero.mpr hy, ?_⟩
  rw [coe_idealRelNorm, coe_idealRelNorm, ← Ideal.relNorm_singleton (R := R) x,
    ← Ideal.relNorm_singleton (R := R) y, ← map_mul, ← map_mul, hxy]

/-- The **relative norm on class groups**, induced by `Ideal.relNorm`.

Every class has an integral representative, since `ClassGroup.mk0` is surjective, and the class of
the norm does not depend on the representative; `ClassGroup.relNorm_mk0` is the resulting
computation. -/
noncomputable def classRelNorm : ClassGroup S →* ClassGroup R :=
  ((Con.ker (ClassGroup.mk0 (R := S))).lift ((ClassGroup.mk0 (R := R)).comp (idealRelNorm R))
      fun _ _ h => mk0_relNorm0_eq_of_mk0_eq h).comp
    (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm.toMonoidHom

/-- The relative norm of the class represented by a nonzero ideal `I` is the class represented by
`I`'s relative norm. This is the computation rule for `classRelNorm`. -/
@[simp]
theorem classRelNorm_mk0 (I : (Ideal S)⁰) :
    classRelNorm (R := R) (ClassGroup.mk0 I) = ClassGroup.mk0 (idealRelNorm R I) := by
  have h : (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm
      (ClassGroup.mk0 (R := S) I) = (I : (Con.ker (ClassGroup.mk0 (R := S))).Quotient) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  rw [classRelNorm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl


end
end Dubon2026.SourceEllipticClassGroup
