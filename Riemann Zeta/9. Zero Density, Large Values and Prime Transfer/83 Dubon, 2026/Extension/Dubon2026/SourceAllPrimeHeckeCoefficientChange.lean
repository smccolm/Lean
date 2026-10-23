import Dubon2026.SourceAllPrimeHeckeCharacters

/-! DUB-17/18 -> rational rank-two Hecke descent -> rationality of the
actual character operators. The complete coset-transition sum commutes
with coefficient change, in particular the original inclusion Q -> C.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
open scoped MatrixGroups

theorem sourceAllPrimeHeckeHom_coefficient_change
    (R S : Type) [CommRing R] [CommRing S] (N : ℕ) (ell : Nat.Primes)
    (u : R →+ S) (φ : Additive (Gamma0 N) →+ R) :
    sourceAllPrimeHeckeHom S N ell (u.comp φ) =
      u.comp (sourceAllPrimeHeckeHom R N ell φ) := by
  letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
  letI := sourceHeckeUpperFintype N ell.val
  apply AddMonoidHom.ext
  intro γ
  obtain ⟨g, rfl⟩ : ∃ g, Additive.ofMul g = γ := ⟨γ.toMul, rfl⟩
  rw [sourceAllPrimeHeckeHom_apply, AddMonoidHom.comp_apply, sourceAllPrimeHeckeHom_apply]
  simp only [AddMonoidHom.comp_apply, map_sum]

end
end Dubon2026
