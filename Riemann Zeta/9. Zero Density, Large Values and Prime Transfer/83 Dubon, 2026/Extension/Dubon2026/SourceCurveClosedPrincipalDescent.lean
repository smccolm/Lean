import Dubon2026.SourceCurveRationalExtensionDivisors
import Dubon2026.SourceCurveGaloisPrincipalDegree
import Dubon2026.SourceRationalClosedPrincipalDivisors
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SplittingField.Construction

/-! DUB-17/18 -> original Frobenius/inertia -> actual residue-curve
principal divisors. A native primitive element gives an actual finite
Galois splitting field. The proved rational base, actual conjugate-divisor
norm argument and pullback degree descend degree zero to the given finite
separable rational-field extension. Every residue and finite-divisor input
is discharged; normality of the given extension is not assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.
Only the primitive-element descent is adapted; local checked consumers
supply the geometry and replace the external global instance setup. -/
namespace Dubon2026.SourceCurve
noncomputable section

theorem hasPrincipalDivisors_finite_ratfunc_closed
    (K E : Type*) [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E] :
    HasPrincipalDivisors K E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (RatFunc K) E
  have hint : IsIntegral (RatFunc K) α := Algebra.IsIntegral.isIntegral α
  have hsep : (minpoly (RatFunc K) α).Separable := Algebra.IsSeparable.isSeparable _ α
  let S := (minpoly (RatFunc K) α).SplittingField
  obtain ⟨g⟩ : Nonempty (E →ₐ[RatFunc K] S) := by
    refine IntermediateField.nonempty_algHom_of_adjoin_splits (fun s hs => ?_) hα
    obtain rfl : s = α := by simpa using hs
    exact ⟨hint, Polynomial.SplittingField.splits _⟩
  letI : Algebra E S := g.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) E S :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : IsScalarTower K E S := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap K S x = g (algebraMap K E x)
    rw [IsScalarTower.algebraMap_apply K (RatFunc K) E x, g.commutes,
      ← IsScalarTower.algebraMap_apply K (RatFunc K) S x]
  haveI : IsGalois (RatFunc K) S := IsGalois.of_separable_splitting_field hsep
  haveI : FiniteDimensional E S := FiniteDimensional.right (RatFunc K) E S
  haveI : Algebra.IsSeparable E S :=
    Algebra.isSeparable_tower_top_of_isSeparable (RatFunc K) E S
  haveI : HasPrincipalDivisors K (RatFunc K) := hasPrincipalDivisors_rational_closed K
  refine ⟨fun f _ => ⟨rationalExtensionPrincipalDivisor K E f,
    rationalExtensionPrincipalDivisor_apply K E f, ?_⟩⟩
  let D : Divisor K S := rationalExtensionPrincipalDivisor K S (algebraMap E S f)
  have hD : ∀ w : Place K S, D w = w.ord (algebraMap E S f) := fun _ => rfl
  have hz : Divisor.degree D = 0 :=
    principal_degree_zero_of_galois (F := RatFunc K)
      (rational_extension_place_residue_bijective K (RatFunc K))
      (rational_extension_place_residue_bijective K S) hD
  exact principal_degree_zero_of_extension
    (rational_extension_place_residue_bijective K E)
    (rational_extension_place_residue_bijective K S)
    (rationalExtensionPrincipalDivisor_apply K E f) hD hz

end
end Dubon2026.SourceCurve
