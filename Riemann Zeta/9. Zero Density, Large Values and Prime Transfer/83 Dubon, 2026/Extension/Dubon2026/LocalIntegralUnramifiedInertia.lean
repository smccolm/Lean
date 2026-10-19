import Dubon2026.LocalIntegralPrimeBelow
import Dubon2026.NumberFieldInertiaRamification
import Dubon2026.NumberFieldRamificationUnramified

/-! The original norm inertia acts trivially in an original number-field
factor unramified at the same rational prime. The contracted residue
prime and native ramification-index theorem give the comparison, without
constructing another completion. This discharges DUB-17's finite-factor
inertia input once the original completion supplies the prime norm. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- Actual local inertia has trivial restriction to the original finite
field when its original rational prime is unramified there. -/
theorem algebraicLocal_unramified_finite_inertia_eq_one
    {K L F : Type} [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
    [IsGalois K L] [Field F] [NumberField F] [IsGalois ℚ F]
    (e : F →+* L) (p : ℕ) (hp : p.Prime) (hnorm : ‖(p : L)‖ < 1)
    (hunr : Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (σ : Gal(F/ℚ)) (δ : Gal(L/K)) (hδ : δ ∈ algebraicLocalInertia K L)
    (he : ∀ x : F, e (σ x) = δ (e x)) : σ = 1 := by
  let w : HeightOneSpectrum (𝓞 F) :=
    ⟨algebraicLocalGlobalPrime e, algebraicLocalGlobalPrime_isPrime e,
      algebraicLocalGlobalPrime_ne_bot e p hp hnorm⟩
  let v := rationalOriginalPrimePlace p hp
  letI : w.asIdeal.IsPrime := w.isPrime
  letI : v.asIdeal.IsPrime := v.isPrime
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨(algebraicLocalGlobalPrime_under e p hp hnorm).symm⟩
  have hunr' : Chebotarev.UnramifiedIn ℚ F v.asIdeal := by
    simpa only [v, rationalOriginalPrimePlace_eq_span] using hunr
  letI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
    hunr'.2 w.asIdeal w.isMaximal inferInstance
  have hidx : v.asIdeal.ramificationIdx w.asIdeal = 1 :=
    (numberField_isUnramifiedAt_iff_ramificationIdx_one v w).mp inferInstance
  have hi := algebraicLocalGlobalPrime_inertia e σ δ hδ he
  change σ ∈ w.asIdeal.inertia Gal(F/ℚ) at hi
  rw [numberField_inertia_eq_bot_of_ramificationIdx_one v w hidx] at hi
  exact hi

end
end Dubon2026
