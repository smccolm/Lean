import Dubon2026.SourceCurveGaloisPlaceCenter

/-! DUB-17/18 -> reverse genus -> exceptional place fibers.
The native Galois transitivity on primes of the integral closure transports
through the existing exact prime/place correspondence. This gives actual
place transitivity without introducing a separate abstract place action. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [IsGalois F E]

theorem exists_comapEquiv_of_restrict_eq (w w' : Place K E)
    (h : w'.restrict F = w.restrict F) :
    ∃ σ : E ≃ₐ[F] E, w.comapEquiv (σ.restrictScalars K) = w' := by
  let v := w.restrict F
  let P := fiberCenter E (F := F) (w := w) rfl
  let Q := fiberCenter E h
  have hP : P.asIdeal ∈ Ideal.primesOver (maximalIdeal v.toValuationSubring)
      (integralClosureAt E v) := ⟨P.isPrime, fiberCenter_liesOver (F := F) (w := w) rfl⟩
  have hQ : Q.asIdeal ∈ Ideal.primesOver (maximalIdeal v.toValuationSubring)
      (integralClosureAt E v) := ⟨Q.isPrime, fiberCenter_liesOver h⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq
    v.toValuationSubring F E (integralClosureAt E v) hP hQ
  refine ⟨σ, ?_⟩
  have he : (⟨w.comapEquiv (σ.restrictScalars K),
      restrict_comapEquiv_galois w σ⟩ : {u : Place K E // u.restrict F = v}) =
      ⟨w', h⟩ := by
    apply (fiberPrimeEquiv E v).injective
    apply HeightOneSpectrum.ext
    change (fiberCenter E (restrict_comapEquiv_galois w σ)).asIdeal = Q.asIdeal
    rw [fiberCenter_comapEquiv_galois]
    exact hσ
  exact congrArg Subtype.val he

end
end Dubon2026.SourceCurve.Place
