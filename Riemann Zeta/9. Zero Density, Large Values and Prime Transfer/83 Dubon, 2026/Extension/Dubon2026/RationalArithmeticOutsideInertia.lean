import Dubon2026.RationalArithmeticFiniteInertiaTrivial
import Dubon2026.UnramifiedUnionFiniteRamification

/-! Original local norm inertia has trivial image in the whole arithmetic
extension outside its original exceptional integer. The finite-stage
ramification and contracted norm-prime results already proved in the
repository supply this directly. This removes determinant inertia
conditions for characters on the original base support, on the Dubon
Theorem 2.6 auxiliary deformation and patching dependency chain. -/

namespace Dubon2026
noncomputable section
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
open IsDedekindDomain
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

private theorem embedded_finite_inertia_eq_one
    {K L F : Type} [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
    [IsGalois K L] [Field F] [NumberField F] [IsGalois ℚ F]
    (e : F →+* L) (p : ℕ) (hp : p.Prime) (hnorm : ‖(p : L)‖ < 1)
    (hram : ((algebraicLocalGlobalPrime e).under (𝓞 ℚ)).ramificationIdx
      (algebraicLocalGlobalPrime e) = 1)
    (σ : Gal(F/ℚ)) (δ : Gal(L/K)) (hδ : δ ∈ algebraicLocalInertia K L)
    (he : ∀ x : F, e (σ x) = δ (e x)) : σ = 1 := by
  let w : HeightOneSpectrum (𝓞 F) :=
    ⟨algebraicLocalGlobalPrime e, algebraicLocalGlobalPrime_isPrime e,
      algebraicLocalGlobalPrime_ne_bot e p hp hnorm⟩
  let v := w.under (𝓞 ℚ)
  letI : w.asIdeal.LiesOver v.asIdeal :=
    inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under (𝓞 ℚ)))
  have hi := algebraicLocalGlobalPrime_inertia e σ δ hδ he
  change σ ∈ w.asIdeal.inertia Gal(F/ℚ) at hi
  rw [numberField_inertia_eq_bot_of_ramificationIdx_one v w hram] at hi
  exact hi

/-- A finite arithmetic subfield has trivial inertia through any actual
compatible local embedding outside the original support. -/
theorem rationalArithmetic_finite_embedded_inertia_eq_one_of_away
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime)
    (hpa : ¬ (p : 𝓞 ℚ) ∣ a)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (e : F →+* rationalPrimeLocalClosure p hp) (σ : Gal(F/ℚ))
    (δ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hδ : δ ∈ rationalPrimeNormInertia p hp)
    (he : ∀ x : F, e (σ x) = δ (e x)) : σ = 1 := by
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : IsGalois ℚ F := F.isGalois
  letI (α : Algebra ℚ F) : @IsGalois ℚ _ F _ α := by
    have he : F.algebra' = α := Subsingleton.elim _ _
    exact Eq.mp (congrArg (fun α : Algebra ℚ F => @IsGalois ℚ _ F _ α) he) F.isGalois
  let w : HeightOneSpectrum (𝓞 F) :=
    ⟨algebraicLocalGlobalPrime e, algebraicLocalGlobalPrime_isPrime e,
      algebraicLocalGlobalPrime_ne_bot e p hp (rationalPrimeOriginalClosureNorm_prime_lt_one p hp)⟩
  have hwa : algebraMap (𝓞 ℚ) (𝓞 F) a ∉ w.asIdeal := by
    intro h
    have hb : a ∈ (algebraicLocalGlobalPrime e).under (𝓞 ℚ) := h
    rw [algebraicLocalGlobalPrime_under e p hp (rationalPrimeOriginalClosureNorm_prime_lt_one p hp)] at hb
    rw [rationalOriginalPrimePlace_eq_span] at hb
    exact hpa (Ideal.mem_span_singleton.mp hb)
  have hram := originalUnramifiedUnion_finite_ramification a ha F.toIntermediateField w hwa
  exact embedded_finite_inertia_eq_one e p hp
    (rationalPrimeOriginalClosureNorm_prime_lt_one p hp) hram σ δ hδ he

/-- Any compatible original arithmetic automorphism is trivial when
the corresponding local automorphism is inertia outside the support.
The embedding may come from a larger arithmetic extension. -/
theorem rationalArithmetic_embedded_inertia_eq_one_of_away
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) (hpa : ¬ (p : 𝓞 ℚ) ∣ a)
    (e : rationalUnramifiedExtension a →+* rationalPrimeLocalClosure p hp)
    (σ : Gal(rationalUnramifiedExtension a/ℚ))
    (δ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hδ : δ ∈ rationalPrimeNormInertia p hp)
    (he : ∀ x, e (σ x) = δ (e x)) : σ = 1 := by
  have ha : a ≠ 0 := by
    intro h
    apply hpa
    rw [h]
    exact dvd_zero _
  apply AlgEquiv.ext
  intro x
  let U := rationalUnramifiedExtension a
  let F := FiniteGaloisIntermediateField.adjoin ℚ ({x} : Set U)
  have hx : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ {x} (Set.mem_singleton x)
  let f := e.comp (algebraMap F U)
  have hcomm (y : F) : f (σ.restrictNormal F y) = δ (f y) :=
    (congrArg e (σ.restrictNormal_commutes F y)).trans (he (algebraMap F U y))
  have hF := rationalArithmetic_finite_embedded_inertia_eq_one_of_away
    a ha p hp hpa F f (σ.restrictNormal F) δ hδ hcomm
  have h := σ.restrictNormal_commutes F (⟨x, hx⟩ : F)
  have hFx := congrArg (fun s : Gal(F/ℚ) => algebraMap F U (s (⟨x, hx⟩ : F))) hF
  have hfix : σ x = x := h.symm.trans hFx
  exact hfix

/-- The actual original arithmetic restriction kills all local norm
inertia outside the base support, on the entire infinite extension. -/
theorem rationalPrimeArithmeticRestriction_inertia_eq_one_of_away
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) (hpa : ¬ (p : 𝓞 ℚ) ∣ a)
    (δ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hδ : δ ∈ rationalPrimeNormInertia p hp) :
    rationalPrimeArithmeticRestriction a p hp δ = 1 := by
  exact rationalArithmetic_embedded_inertia_eq_one_of_away a p hp hpa
    (rationalPrimeArithmeticOriginalEmbedding a p hp)
    (rationalPrimeArithmeticRestriction a p hp δ) δ hδ
    (rationalPrimeArithmeticRestriction_commutes a p hp δ)

end
end Dubon2026
