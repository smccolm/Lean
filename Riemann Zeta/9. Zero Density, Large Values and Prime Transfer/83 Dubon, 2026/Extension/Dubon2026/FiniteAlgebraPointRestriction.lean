import Dubon2026.ArtinianAlgebraPointKernelOrbit
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Finiteness.Quotient

/-! # Genuine geometric points extend across finite coordinate subalgebras -/

namespace Dubon2026
noncomputable section

variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
  [Module.Finite K A]

/-- Every genuine point of an actual subalgebra of a finite algebra over the original algebraically closed field extends to the original coordinate algebra. Actual lying-over, quotient fields and original point-kernel comparison supply the extension. -/
theorem finiteAlgebraPointRestriction_surjective (S : Subalgebra K A) :
    Function.Surjective (fun q : A →ₐ[K] K => q.comp S.val) := by
  letI : Module.Finite K S := inferInstance
  letI : IsArtinianRing S := IsArtinianRing.of_finite K S
  letI : Module.Finite S A := Module.Finite.of_restrictScalars_finite K S A
  intro p
  let P := RingHom.ker p.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime p.toRingHom
  letI : P.IsMaximal := inferInstance
  have hker : RingHom.ker (algebraMap S A) ≤ P := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
    exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P hker
  letI : Q.IsMaximal := hQmax
  letI := Ideal.Quotient.field Q
  let e : A ⧸ Q →ₐ[K] K := IsAlgClosed.lift
  let q := e.comp (Ideal.Quotient.mkₐ K Q)
  have hk : RingHom.ker (q.comp S.val).toRingHom = RingHom.ker p.toRingHom := by
    ext s
    change e (Ideal.Quotient.mk Q s.val) = 0 ↔ s ∈ P
    have he : e (Ideal.Quotient.mk Q s.val) = 0 ↔ Ideal.Quotient.mk Q s.val = 0 := by
      rw [← map_zero e]
      exact e.injective.eq_iff
    rw [he, Ideal.Quotient.eq_zero_iff_mem]
    change s ∈ Q.comap (algebraMap S A) ↔ s ∈ P
    rw [hQ]
  obtain ⟨g, hg⟩ := artinianAlgebraPoint_sameKernel_galois p (q.comp S.val) hk.symm
  refine ⟨q, ?_⟩
  apply AlgHom.ext
  intro s
  calc
    q (S.val s) = g (p s) := (AlgHom.congr_fun hg s).symm
    _ = p s := g.commutes (p s)

end
end Dubon2026
