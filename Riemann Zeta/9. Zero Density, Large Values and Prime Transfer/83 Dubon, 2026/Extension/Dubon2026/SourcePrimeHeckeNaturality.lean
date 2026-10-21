import Dubon2026.SourcePrimeCoefficientHeckeH1

/-! The actual full H1 Hecke action commutes with equivariant coefficient morphisms.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> native H1 eigenvalue descent through the original coefficient flag.
This supplies the exact operator compatibilities for its inclusion and
one-dimensional quotient; the proof uses the original full coset sum.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable {R : Type} [CommRing R] {Q ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (A B : Rep R (Gamma0 Q)) (f : A ⟶ B) (b : Module.End R A) (d : Module.End R B)
    (hb : ∀ u : heckeUpperSubgroup Q ell,
      b.comp (A.ρ (sourceHeckeConjugation hell u)) = (A.ρ u.val).comp b)
    (hd : ∀ u : heckeUpperSubgroup Q ell,
      d.comp (B.ρ (sourceHeckeConjugation hell u)) = (B.ρ u.val).comp d)
    (hfd : f.hom.toLinearMap.comp b = d.comp f.hom.toLinearMap)

private local instance naturalityPrimeFinite :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

include hfd

/-- The actual coefficient morphism commutes with the original full prime
coset correspondence on every native one-cocycle. -/
theorem sourcePrimeHeckeCocycles_naturality (c : groupCohomology.cocycles₁ A) :
    groupCohomology.mapCocycles₁ (MonoidHom.id _) f (sourcePrimeHeckeCocycles hell A b hb c) =
      sourcePrimeHeckeCocycles hell B d hd (groupCohomology.mapCocycles₁ (MonoidHom.id _) f c) := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change f.hom (sourceCorrespondenceOne A (heckeUpperSubgroup Q ell)
    (sourceHeckeConjugation hell) b c g) =
    sourceCorrespondenceOne B (heckeUpperSubgroup Q ell)
      (sourceHeckeConjugation hell) d (fun h => f.hom (c h)) g
  rw [sourceCorrespondenceOne_apply, sourceCorrespondenceOne_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [f.hom.isIntertwining]
  apply congrArg
  exact LinearMap.congr_fun hfd _

/-- The induced coefficient map on full native H1 commutes with the original
prime Hecke actions; no cohomological compatibility is supplied. -/
theorem sourcePrimeHeckeH1_naturality (x : groupCohomology.H1 A) :
    ((groupCohomology.functor R (Gamma0 Q) 1).map f)
        (sourcePrimeHeckeH1 hell A b hb x) =
      sourcePrimeHeckeH1 hell B d hd (((groupCohomology.functor R (Gamma0 Q) 1).map f) x) := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  change groupCohomology.map (MonoidHom.id _) f 1
    (sourcePrimeHeckeH1 hell A b hb (groupCohomology.H1π A c)) =
      sourcePrimeHeckeH1 hell B d hd
        (groupCohomology.map (MonoidHom.id _) f 1 (groupCohomology.H1π A c))
  rw [sourcePrimeHeckeH1_cocycle, groupCohomology.H1π_comp_map_apply,
    groupCohomology.H1π_comp_map_apply, sourcePrimeHeckeH1_cocycle,
    sourcePrimeHeckeCocycles_naturality hell A B f b d hb hd hfd]

end
end Dubon2026
