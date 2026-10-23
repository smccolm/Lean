import Dubon2026.SourceEllipticClassRelativeNorm

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
variable {A B : Type*} [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B]

/-- Extension of a nonzero integral ideal along the given injective ring map. -/
def extendedIdeal (f : A →+* B) (hf : Function.Injective f) : (Ideal A)⁰ →* (Ideal B)⁰ :=
  { toFun := fun I => ⟨I.1.map f, mem_nonZeroDivisors_iff_ne_zero.mpr <|
      (Ideal.map_eq_bot_iff_of_injective hf).not.mpr (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩
    map_one' := Subtype.ext (by simpa only [OneMemClass.coe_one, Ideal.one_eq_top] using Ideal.map_top f)
    map_mul' := fun I J => Subtype.ext (Ideal.map_mul f I.1 J.1) }

theorem extendedIdeal_coe (f : A →+* B) (hf : Function.Injective f) (I : (Ideal A)⁰) :
    (extendedIdeal f hf I : Ideal B) = (I : Ideal A).map f := rfl

theorem mk0_extendedIdeal_eq_of_mk0_eq (f : A →+* B) (hf : Function.Injective f)
    {I J : (Ideal A)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (extendedIdeal f hf I) = ClassGroup.mk0 (extendedIdeal f hf J) := by
  obtain ⟨x,y,hx,hy,hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨f x, f y,
    (map_ne_zero_iff f hf).mpr hx, (map_ne_zero_iff f hf).mpr hy, ?_⟩
  have h := congrArg (Ideal.map f) hxy
  simpa only [extendedIdeal_coe, Ideal.map_mul, Ideal.map_span, Set.image_singleton] using h

/-- Actual extension on ideal classes, descended through integral representatives. -/
def classExtendedHom (f : A →+* B) (hf : Function.Injective f) : ClassGroup A →* ClassGroup B :=
  ((Con.ker (ClassGroup.mk0 (R := A))).lift
      ((ClassGroup.mk0 (R := B)).comp (extendedIdeal f hf))
      fun _ _ h => mk0_extendedIdeal_eq_of_mk0_eq f hf h).comp
    (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm.toMonoidHom

theorem classExtendedHom_mk0 (f : A →+* B) (hf : Function.Injective f) (I : (Ideal A)⁰) :
    classExtendedHom f hf (ClassGroup.mk0 I) = ClassGroup.mk0 (extendedIdeal f hf I) := by
  have h : (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm
      (ClassGroup.mk0 (R := A) I) = (I : (Con.ker (ClassGroup.mk0 (R := A))).Quotient) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  rw [classExtendedHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Algebra R B] [Module.Finite R B] [Module.IsTorsionFree R B]

/-- Extend into the actual common overring and norm down to the target ring. -/
def extendedClassNorm (f : A →+* B) (hf : Function.Injective f) :
    ClassGroup A →* ClassGroup R := (classRelNorm (R := R)).comp (classExtendedHom f hf)

theorem extendedClassNorm_mk0 (f : A →+* B) (hf : Function.Injective f) (I : (Ideal A)⁰) :
    extendedClassNorm (R := R) f hf (ClassGroup.mk0 I) =
      ClassGroup.mk0 (idealRelNorm R (extendedIdeal f hf I)) := by
  rw [extendedClassNorm, MonoidHom.comp_apply, classExtendedHom_mk0, classRelNorm_mk0]

end
end Dubon2026.SourceEllipticClassGroup
