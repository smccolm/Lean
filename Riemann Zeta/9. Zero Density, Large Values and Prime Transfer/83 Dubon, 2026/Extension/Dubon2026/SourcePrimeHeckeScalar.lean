import Dubon2026.SourcePrimeCoefficientHeckeH1

/-! The original full Hecke correspondence respects its coefficient scalar.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> separating the actual ell^j flag-quotient scalar from the character
Hecke operator. The identity is proved on the original finite coset trace.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable {R : Type} [CommRing R] {Q ell : ℕ} [NeZero ell]
    (hell : ell.Prime) (A : Rep R (Gamma0 Q)) (b : Module.End R A)
    (hb : ∀ u : heckeUpperSubgroup Q ell,
      b.comp (A.ρ (sourceHeckeConjugation hell u)) = (A.ρ u.val).comp b)
    (r : R)
    (hrb : ∀ u : heckeUpperSubgroup Q ell,
      (r • b).comp (A.ρ (sourceHeckeConjugation hell u)) = (A.ρ u.val).comp (r • b))

private local instance scalarHeckeFinite :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

/-- Scaling the actual coefficient morphism scales its full native cocycle
correspondence by the same scalar. -/
theorem sourcePrimeHeckeCocycles_smul (c : groupCohomology.cocycles₁ A) :
    sourcePrimeHeckeCocycles hell A (r • b) hrb c =
      r • sourcePrimeHeckeCocycles hell A b hb c := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
    A.ρ (g • q).out ((r • b)
      (c (sourceHeckeConjugation hell (cosetTransition (heckeUpperSubgroup Q ell) g q))))) =
    r • ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      A.ρ (g • q).out (b
        (c (sourceHeckeConjugation hell (cosetTransition (heckeUpperSubgroup Q ell) g q))))
  simp only [LinearMap.smul_apply, map_smul, Finset.smul_sum]

/-- Scaling the actual coefficient morphism scales the genuine full prime
correspondence on native H1. -/
theorem sourcePrimeHeckeH1_smul (x : groupCohomology.H1 A) :
    sourcePrimeHeckeH1 hell A (r • b) hrb x = r • sourcePrimeHeckeH1 hell A b hb x := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  rw [sourcePrimeHeckeH1_cocycle, sourcePrimeHeckeH1_cocycle,
    sourcePrimeHeckeCocycles_smul, map_smul]

end
end Dubon2026
