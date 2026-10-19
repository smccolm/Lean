import Dubon2026.AuxiliaryCharacterGroupAlgebra
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.PGroup

/-! The genuine finite commutative coefficient-primary auxiliary group
algebra is local. This permits the constructed common power-series
parameters to act on that algebra, needed to identify the annihilator
ideals for the DUB-17 arithmetic patching system. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- Every maximal ideal of the actual finite primary group algebra
is the pullback of the coefficient maximal ideal by augmentation. -/
theorem finitePrimaryGroupAlgebra_maximalIdeal_eq
    (O D : Type*) [CommRing O] [IsLocalRing O] [CommGroup D] [Finite D]
    (q : ℕ) (hq : q.Prime) [CharP (ResidueField O) q]
    (hD : IsPGroup q D) (J : Ideal (MonoidAlgebra O D)) [J.IsMaximal] :
    J = Ideal.comap (coefficientGroupAlgebraAugmentation O D).toRingHom (maximalIdeal O) := by
  letI := Fintype.ofFinite D
  letI : Fact q.Prime := ⟨hq⟩
  letI : Module.Finite O (MonoidAlgebra O D) := Module.Finite.of_basis (MonoidAlgebra.basis D O)
  let ε := coefficientGroupAlgebraAugmentation O D
  let f := Ideal.Quotient.mk J
  have hcomap : Ideal.comap (algebraMap O (MonoidAlgebra O D)) J = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J)
  have hqO : (q : O) ∈ maximalIdeal O := by
    apply (residue_eq_zero_iff _).mp
    rw [map_natCast, CharP.cast_eq_zero]
  have hqJ : (q : MonoidAlgebra O D) ∈ J := by
    have h := hcomap.symm ▸ hqO
    simpa only [Ideal.mem_comap, map_natCast] using h
  letI : CharP (MonoidAlgebra O D ⧸ J) q :=
    (CharP.charP_iff_prime_eq_zero hq).mpr (by
      rw [← map_natCast f]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hqJ)
  have hgen : ∀ d : D, f (MonoidAlgebra.of O D d) = 1 := by
    intro d
    obtain ⟨k, hk⟩ := hD d
    have hp : (f (MonoidAlgebra.of O D d) - 1) ^ (q ^ k) = 0 := by
      rw [sub_pow_char_pow, ← map_pow, ← map_pow, hk, map_one, map_one, one_pow, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hp)
  have he : f = (f.comp (algebraMap O (MonoidAlgebra O D))).comp ε.toRingHom := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      change f (algebraMap O (MonoidAlgebra O D) r) =
        f (algebraMap O (MonoidAlgebra O D) (ε (algebraMap O (MonoidAlgebra O D) r)))
      rw [ε.commutes]
      rfl
    · intro d
      change f (MonoidAlgebra.of O D d) =
        f (algebraMap O (MonoidAlgebra O D) (ε (MonoidAlgebra.of O D d)))
      rw [hgen, coefficientGroupAlgebraAugmentation_of, map_one, map_one]
  ext x
  change x ∈ J ↔ ε x ∈ maximalIdeal O
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change f x = 0 ↔ ε x ∈ maximalIdeal O
  rw [he]
  change f (algebraMap O (MonoidAlgebra O D) (ε x)) = 0 ↔ ε x ∈ maximalIdeal O
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact SetLike.ext_iff.mp hcomap (ε x)

/-- The original finite primary group algebra is a local ring;
locality is derived, not supplied as a coefficient hypothesis. -/
theorem finitePrimaryGroupAlgebra_isLocal
    (O D : Type*) [CommRing O] [IsLocalRing O] [CommGroup D] [Finite D]
    (q : ℕ) (hq : q.Prime) [CharP (ResidueField O) q]
    (hD : IsPGroup q D) : IsLocalRing (MonoidAlgebra O D) := by
  let ε := coefficientGroupAlgebraAugmentation O D
  have hsurj : Function.Surjective ε := fun r => ⟨algebraMap O (MonoidAlgebra O D) r, ε.commutes r⟩
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨Ideal.comap ε.toRingHom (maximalIdeal O),
    Ideal.comap_isMaximal_of_surjective ε.toRingHom hsurj, ?_⟩
  intro J hJ
  letI := hJ
  exact finitePrimaryGroupAlgebra_maximalIdeal_eq O D q hq hD J

end
end Dubon2026
