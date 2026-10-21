import Dubon2026.SourceHeckeProductTrace

/-! Composition of the two full original prime correspondences modulo a native coboundary.
DUB-17/18 -> residual modular Galois association -> original residual H1
eigensystem -> full integral H1 Hecke commutativity -> comparison of both
orders with the same actual product correspondence.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable {R : Type} [CommRing R] {Q p q : ℕ} [NeZero p] [NeZero q]

private local instance primeCompositionFinite (n : ℕ) [NeZero n] :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q n) := sourceHeckeUpperFintype Q n

private theorem productCorrespondence_congr (m n : ℕ) [NeZero m] [NeZero n]
    (hmn : m = n) (A : Rep R (Gamma0 Q)) (a : Module.End R A) :
    sourceCorrespondenceOne A (heckeUpperSubgroup Q m) sourceIntegralHeckeHom a =
      sourceCorrespondenceOne A (heckeUpperSubgroup Q n) sourceIntegralHeckeHom a := by
  subst n
  rfl

/-- The composition of distinct good-prime correspondences differs from the
original product correspondence by a genuine native coboundary. All coset
factorization and representative-independence conditions are proved. -/
theorem sourceHeckePrimeComposition_sub (hp : p.Prime) (hq : q.Prime)
    (hpQ : Nat.Coprime p Q) (hqQ : Nat.Coprime q Q) (hpq : Nat.Coprime p q)
    (A : Rep R (Gamma0 Q)) (b d : Module.End R A)
    (hb : ∀ u : heckeUpperSubgroup Q p,
      b.comp (A.ρ (sourceHeckeConjugation hp u)) = (A.ρ u.val).comp b)
    (hd : ∀ u : heckeUpperSubgroup Q q,
      d.comp (A.ρ (sourceHeckeConjugation hq u)) = (A.ρ u.val).comp d)
    (c : groupCohomology.cocycles₁ A) :
    sourceCorrespondenceOne A (heckeUpperSubgroup Q p) (sourceHeckeConjugation hp) b
        (sourceCorrespondenceOne A (heckeUpperSubgroup Q q) (sourceHeckeConjugation hq) d c) -
      sourceCorrespondenceOne A (heckeUpperSubgroup Q (p * q)) sourceIntegralHeckeHom (b.comp d) c ∈
        groupCohomology.coboundaries₁ A := by
  obtain ⟨σ, hσ⟩ := sourceHeckeProduct_exists_section hp hq hpQ hqQ hpq
  have h₁ := sourceCorrespondenceOne_coboundary A (heckeUpperSubgroup Q p)
    (sourceHeckeConjugation hp) b hb (sourceHeckeInnerTrace_sub hp hq A d σ hσ hd c)
  have h₂ := sourceHeckeProductTrace_sub hp hq A b d σ hσ hb hd c
  rw [← sourceHeckePrime_innerTrace_eq_product hp hq A b d σ hσ hb] at h₂
  have h₃ := (groupCohomology.coboundaries₁ A).sub_mem h₂ h₁
  rw [map_sub] at h₃
  convert h₃ using 1
  abel

/-- Two distinct good-prime correspondences with commuting coefficient maps
commute on native H1: their cochain commutator is an actual coboundary. -/
theorem sourceHeckePrimeCommutator_mem (hp : p.Prime) (hq : q.Prime)
    (hpQ : Nat.Coprime p Q) (hqQ : Nat.Coprime q Q) (hpq : Nat.Coprime p q)
    (A : Rep R (Gamma0 Q)) (b d : Module.End R A)
    (hb : ∀ u : heckeUpperSubgroup Q p,
      b.comp (A.ρ (sourceHeckeConjugation hp u)) = (A.ρ u.val).comp b)
    (hd : ∀ u : heckeUpperSubgroup Q q,
      d.comp (A.ρ (sourceHeckeConjugation hq u)) = (A.ρ u.val).comp d)
    (hbd : b.comp d = d.comp b) (c : groupCohomology.cocycles₁ A) :
    sourceCorrespondenceOne A (heckeUpperSubgroup Q p) (sourceHeckeConjugation hp) b
        (sourceCorrespondenceOne A (heckeUpperSubgroup Q q) (sourceHeckeConjugation hq) d c) -
      sourceCorrespondenceOne A (heckeUpperSubgroup Q q) (sourceHeckeConjugation hq) d
        (sourceCorrespondenceOne A (heckeUpperSubgroup Q p) (sourceHeckeConjugation hp) b c) ∈
          groupCohomology.coboundaries₁ A := by
  have h₁ := sourceHeckePrimeComposition_sub hp hq hpQ hqQ hpq A b d hb hd c
  have h₂ := sourceHeckePrimeComposition_sub hq hp hqQ hpQ hpq.symm A d b hd hb c
  rw [productCorrespondence_congr (q * p) (p * q) (Nat.mul_comm q p), ← hbd] at h₂
  have h₃ := (groupCohomology.coboundaries₁ A).sub_mem h₁ h₂
  convert h₃ using 1
  abel

end
end Dubon2026
