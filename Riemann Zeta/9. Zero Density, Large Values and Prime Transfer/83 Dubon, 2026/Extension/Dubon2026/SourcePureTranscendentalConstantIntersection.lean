import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Tower

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> fixed-field descent of the proved twist-stable cusp image. An element of
a purely transcendental field that is algebraic over the original constants
belongs to those constants. This is the needed separation input for the
full complex automorphism fixed field, not an assumed Galois descent result.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range. -/
namespace Dubon2026.SourceFunctionField.ConstantFixedField
noncomputable section
open IntermediateField

open MvPolynomial Polynomial in

theorem mem_bot_of_isAlgebraic_of_mem_adjoin_algebraicIndependent {F E : Type*} [Field F]
    [Field E] [Algebra F E] {ι : Type*} {x : ι → E} (hx : AlgebraicIndependent F x)
    {c : E} (hmem : c ∈ IntermediateField.adjoin F (Set.range x)) (halg : IsAlgebraic F c) :
    c ∈ (⊥ : IntermediateField F E) := by
  classical

  set K₁ := IntermediateField.adjoin F (Set.range x)
  let φ := hx.aevalEquivField
  set r : FractionRing (MvPolynomial ι F) := φ.symm ⟨c, hmem⟩ with hr_def
  have hφr : φ r = ⟨c, hmem⟩ := φ.apply_symm_apply _

  have h1 : IsAlgebraic F (⟨c, hmem⟩ : ↥K₁) :=
    (isAlgebraic_algHom_iff K₁.val Subtype.val_injective).mp halg
  have hr_alg : IsAlgebraic F r :=
    (isAlgebraic_algHom_iff φ.toAlgHom φ.injective).mp (hφr ▸ h1)

  haveI : IsIntegrallyClosed (MvPolynomial ι F) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hr_int : IsIntegral (MvPolynomial ι F) r :=
    (isAlgebraic_iff_isIntegral.mp hr_alg).tower_top
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr_int

  set m := minpoly F c
  have hc_int : IsIntegral F c := isAlgebraic_iff_isIntegral.mp halg
  have hmc' : (Polynomial.aeval (⟨c, hmem⟩ : ↥K₁)) m = 0 := by
    refine Subtype.val_injective ?_
    rw [ZeroMemClass.coe_zero,
      show ((Polynomial.aeval (⟨c, hmem⟩ : ↥K₁)) m : E)
        = (Polynomial.aeval (K₁.val ⟨c, hmem⟩)) m from
      (Polynomial.aeval_algHom_apply K₁.val (⟨c, hmem⟩ : ↥K₁) m).symm]
    exact minpoly.aeval F c
  have hmr : (Polynomial.aeval r) m = 0 := by
    rw [show r = φ.symm ⟨c, hmem⟩ from rfl,
      show (Polynomial.aeval (φ.symm ⟨c, hmem⟩)) m = φ.symm ((Polynomial.aeval ⟨c, hmem⟩) m) from
        Polynomial.aeval_algHom_apply (f := φ.symm) (⟨c, hmem⟩ : ↥K₁) m,
      hmc', map_zero]
  have hmp : (Polynomial.aeval p) m = 0 := by
    have h2 := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom F (MvPolynomial ι F) (FractionRing (MvPolynomial ι F))) p m
    rw [IsScalarTower.toAlgHom_apply, hp, hmr] at h2
    exact (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ι F)
      (FractionRing (MvPolynomial ι F)))).mp h2.symm

  let ev : MvPolynomial ι F →ₐ[F] F := MvPolynomial.aeval (fun _ ↦ (0 : F))
  have hma : (Polynomial.aeval (ev p)) m = 0 := by
    rw [show (Polynomial.aeval (ev p)) m = ev ((Polynomial.aeval p) m) from
      Polynomial.aeval_algHom_apply ev p m, hmp, map_zero]
  have hma' : m.IsRoot (ev p) := by
    rwa [Polynomial.IsRoot, ← congrFun (Polynomial.coe_aeval_eq_eval (ev p)) m]

  have hm_irr : Irreducible m := minpoly.irreducible hc_int
  have hdeg : m.degree = 1 := Polynomial.degree_eq_one_of_irreducible_of_root hm_irr hma'
  rw [IntermediateField.mem_bot]
  obtain ⟨y, hy⟩ := minpoly.degree_eq_one_iff.mp hdeg
  exact ⟨y, hy⟩

end
end Dubon2026.SourceFunctionField.ConstantFixedField
