import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Finite original exceptional prime sets under actual integral base change -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]

/-- The actual primes above an original height-one prime form a finite fiber of the genuine contraction map. -/
theorem heightOneUnder_fiber_finite (v : HeightOneSpectrum A) :
    {w : HeightOneSpectrum B | w.under A = v}.Finite := by
  let f : {w : HeightOneSpectrum B // w.under A = v} → v.asIdeal.primesOver B :=
    fun w => ⟨w.val.asIdeal, w.val.isPrime,
      ⟨(congrArg HeightOneSpectrum.asIdeal w.property).symm⟩⟩
  have hfinite : Finite {w : HeightOneSpectrum B // w.under A = v} :=
    Finite.of_injective f (by
      intro w z h
      apply Subtype.ext
      apply HeightOneSpectrum.ext_iff.mpr
      exact congrArg Subtype.val h)
  exact @Set.toFinite _ _ hfinite

/-- Pulling the original finite exceptional set to the actual integral extension gives finitely many original primes. -/
theorem heightOneUnder_preimage_finite
    (S : Set (HeightOneSpectrum A)) (hS : S.Finite) :
    {w : HeightOneSpectrum B | w.under A ∈ S}.Finite := by
  have h := hS.biUnion (fun v _ => heightOneUnder_fiber_finite (B := B) v)
  apply h.subset
  intro w hw
  exact Set.mem_biUnion hw rfl

end
end Dubon2026
