import Dubon2026.FiniteTameImage
import Dubon2026.LocalIntegralPrimeAction

/-! Actual norm inertia and its original finite field restriction supply the
finite tame generator, wild subgroup and Frobenius relation. This realizes the
finite local presentation used by ramified auxiliary deformations for DUB-17;
it does not assume a profinite tame presentation or a supplied wild subgroup. -/

namespace Dubon2026

open IsDedekindDomain
open scoped NumberField

attribute [local instance] algebraicLocalIntegerAction

theorem algebraicLocal_exists_finite_tame_generator
    {K L F : Type} [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
    [IsGalois K L] [Field F] [NumberField F]
    (e : F →+* L) (p : ℕ) (hp : p.Prime) (hnorm : ‖(p : L)‖ < 1)
    (r : Gal(L/K) →* Gal(F/ℚ)) (he : ∀ g x, e (r g x) = g (e x))
    (φ : Gal(L/K))
    (hφ : ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L), φ • x = x ^ p) :
    let I := (algebraicLocalInertia K L).map (QuotientGroup.mk' r.ker)
    let Φ := QuotientGroup.mk' r.ker φ
    ∃ (t : Gal(L/K) ⧸ r.ker) (W : Subgroup (Gal(L/K) ⧸ r.ker)),
      t ∈ I ∧ W.Normal ∧ IsPGroup p W ∧ W ≤ I ∧
      I = W ⊔ Subgroup.zpowers t ∧ Φ * t * Φ⁻¹ * (t ^ p)⁻¹ ∈ W := by
  let w : HeightOneSpectrum (𝓞 F) :=
    ⟨algebraicLocalGlobalPrime e, algebraicLocalGlobalPrime_isPrime e,
      algebraicLocalGlobalPrime_ne_bot e p hp hnorm⟩
  let I := (algebraicLocalInertia K L).map (QuotientGroup.mk' r.ker)
  let f := QuotientGroup.kerLift r
  letI : I.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hI : ∀ g ∈ I, f g ∈ w.asIdeal.inertia Gal(F/ℚ) := by
    rintro _ ⟨g, hg, rfl⟩
    exact algebraicLocalGlobalPrime_inertia e (r g) g hg (he g)
  have hstable : ∀ g : Gal(L/K) ⧸ r.ker, ∀ x ∈ w.asIdeal, f g • x ∈ w.asIdeal := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective r.ker g
    exact algebraicLocalGlobalPrime_stable e (r g) g (he g)
  have hfrob : ∀ x : 𝓞 F,
      f (QuotientGroup.mk' r.ker φ) • x - x ^ p ∈ w.asIdeal :=
    algebraicLocalGlobalPrime_frobenius e (r φ) φ (he φ) p hφ
  exact finite_numberField_exists_tame_generator w p hp
    (algebraicLocalGlobalPrime_prime_mem e p hnorm) f
    (QuotientGroup.kerLift_injective r) I hI hstable (QuotientGroup.mk' r.ker φ) hfrob

end Dubon2026
