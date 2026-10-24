import Dubon2026.SourceEllipticPrimeAbscissaHom

/-! The specific point map for the intrinsic prime quotient. It is defined by
the existing literal degree-two map or actual odd ideal norm, followed only
by equality transport of the target curve. Choosing an arbitrary group
homomorphism with the right kernel would not suffice for later field-map
compatibility. This fixes that map on the DUB-17/18 composite quotient chain. -/

namespace Dubon2026.SourceEllipticVelu
universe u
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate SourceEllipticFunctionField
noncomputable section
variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- The specific original point map, transported to the intrinsic prime quotient model. -/
def primeAbscissaHom (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    W.toAffine.Point →+ (primeAbscissaQuotient W p H).toAffine.Point := by
  by_cases hp2 : p = 2
  · subst p
    let hP := primeKernelGenerator_order W 2 H
    let hE := primeAbscissaQuotient_two_eq W hp H hP (primeKernelGenerator_zmultiples W 2 H)
    exact (AddEquiv.cast (M := fun V : WeierstrassCurve F => V.toAffine.Point) hE.symm).toAddMonoidHom.comp
      (veluTwoHom (two_torsion_coordinates W hP).1 (two_torsion_coordinates W hP).2)
  · let hP := primeKernelGenerator_oddOrder W p hp2 H
    let hE := primeAbscissaQuotient_odd_eq W p hp2 H hP (primeKernelGenerator_zmultiples W p H)
    exact (AddEquiv.cast (M := fun V : WeierstrassCurve F => V.toAffine.Point) hE.symm).toAddMonoidHom.comp
      (oddPointNorm W hP)

/-- The specific intrinsic prime quotient point map has exactly the original subgroup as kernel. -/
theorem primeAbscissaHom_ker (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    (primeAbscissaHom W p hp H).ker = H.1 := by
  have hc {A B C : Type u} [AddGroup A] [AddGroup B] [AddGroup C]
      (e : B ≃+ C) (φ : A →+ B) : (e.toAddMonoidHom.comp φ).ker = φ.ker := by
    ext x
    change e (φ x) = 0 ↔ φ x = 0
    rw [← e.map_zero, e.injective.eq_iff]
  by_cases hp2 : p = 2
  · subst p
    simp only [primeAbscissaHom, dite_true]
    rw [hc, veluTwoHom_ker]
    let P := primeKernelGenerator W 2 H
    have hP : addOrderOf P = 2 := primeKernelGenerator_order W 2 H
    have hP0 : P ≠ 0 := by intro hz; rw [hz, addOrderOf_zero] at hP; omega
    have he : Affine.Point.some (coordsOrZero P).1 (coordsOrZero P).2
        (W.toAffine.equation_iff_nonsingular.mp (two_torsion_coordinates W hP).1) = P :=
      some_coordsOrZero hP0
    rw [he]
    exact primeKernelGenerator_zmultiples W 2 H
  · simp only [primeAbscissaHom, dif_neg hp2]
    rw [hc, ker_oddPointNorm, primeKernelGenerator_zmultiples]

/-- The specific intrinsic prime quotient point map is surjective. -/
theorem primeAbscissaHom_surjective (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    Function.Surjective (primeAbscissaHom W p hp H) := by
  by_cases hp2 : p = 2
  · subst p
    simp only [primeAbscissaHom, dite_true]
    let hE := primeAbscissaQuotient_two_eq W hp H
      (primeKernelGenerator_order W 2 H) (primeKernelGenerator_zmultiples W 2 H)
    apply (AddEquiv.cast (M := fun V : WeierstrassCurve F => V.toAffine.Point) hE.symm).surjective.comp
    rw [veluTwoHom_coe]
    exact veluPointMap2_surjective _ _ _
  · simp only [primeAbscissaHom, dif_neg hp2]
    let hE := primeAbscissaQuotient_odd_eq W p hp2 H
      (primeKernelGenerator_oddOrder W p hp2 H) (primeKernelGenerator_zmultiples W p H)
    exact (AddEquiv.cast (M := fun V : WeierstrassCurve F => V.toAffine.Point) hE.symm).surjective.comp
      (oddPointNorm_surjective W _)

end
end Dubon2026.SourceEllipticVelu
