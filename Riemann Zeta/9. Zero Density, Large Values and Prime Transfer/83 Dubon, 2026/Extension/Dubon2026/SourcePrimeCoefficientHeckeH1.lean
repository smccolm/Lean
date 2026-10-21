import Dubon2026.SourceHeckePrimeComposition
import Dubon2026.SourceHeckeCohomologyTrace
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! The original prime correspondence on the required coefficient-flag representations.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> descent through the original residual coefficient flag -> its full H1
Hecke actions. The existing native trace and functorial coefficient map supply
the construction; the already proved product correspondence supplies commutativity.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable {R : Type} [CommRing R] {Q p : ℕ} [NeZero p]
    (hp : p.Prime) (A : Rep R (Gamma0 Q)) (b : Module.End R A)
    (hb : ∀ u : heckeUpperSubgroup Q p,
      b.comp (A.ρ (sourceHeckeConjugation hp u)) = (A.ρ u.val).comp b)

private local instance primeCoefficientFinite :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) := sourceHeckeUpperFintype Q p

/-- The genuine prime correspondence coefficient morphism for an original
flag representation and its actual intertwining coefficient map. -/
def sourcePrimeHeckeMorphism :
    Rep.res (sourceHeckeConjugation hp) A ⟶ Rep.res (heckeUpperSubgroup Q p).subtype A :=
  Rep.ofHom { toLinearMap := b, isIntertwining' := hb }

/-- The original full prime correspondence on native cocycles of the coefficient representation. -/
def sourcePrimeHeckeCocycles : Module.End R (groupCohomology.cocycles₁ A) :=
  (sourceHeckeTraceCocycles A (heckeUpperSubgroup Q p)).comp
    (groupCohomology.mapCocycles₁ (sourceHeckeConjugation hp)
      (sourcePrimeHeckeMorphism hp A b hb)).hom

/-- The actual prime correspondence on full native H1 of the coefficient representation. -/
def sourcePrimeHeckeH1 : Module.End R (groupCohomology.H1 A) :=
  (sourceHeckeH1Trace A (heckeUpperSubgroup Q p)).comp
    (groupCohomology.map (sourceHeckeConjugation hp)
      (sourcePrimeHeckeMorphism hp A b hb) 1).hom

/-- The original coefficient-system H1 correspondence is represented by its actual traced cocycle. -/
theorem sourcePrimeHeckeH1_cocycle (c : groupCohomology.cocycles₁ A) :
    sourcePrimeHeckeH1 hp A b hb (groupCohomology.H1π A c) =
      groupCohomology.H1π A (sourcePrimeHeckeCocycles hp A b hb c) := by
  change sourceHeckeH1Trace _ _
    ((groupCohomology.map (sourceHeckeConjugation hp) (sourcePrimeHeckeMorphism hp A b hb) 1)
      (groupCohomology.H1π A c)) = _
  rw [groupCohomology.H1π_comp_map_apply, sourceHeckeH1Trace_cocycle]
  rfl

/-- The original coefficient-system cocycle is exactly the full finite prime trace. -/
theorem sourcePrimeHeckeCocycles_coe (c : groupCohomology.cocycles₁ A) :
    (sourcePrimeHeckeCocycles hp A b hb c : Gamma0 Q → A) =
      sourceCorrespondenceOne A (heckeUpperSubgroup Q p) (sourceHeckeConjugation hp) b c := rfl

/-- The full H1 correspondences at distinct good primes on an original coefficient system commute
whenever their actual coefficient maps commute. All subgroup, coset and
representative-correction conditions are derived. -/
theorem sourcePrimeHeckeH1_commute {q : ℕ} [NeZero q] (hq : q.Prime)
    (hpQ : Nat.Coprime p Q) (hqQ : Nat.Coprime q Q) (hpq : p ≠ q)
    (d : Module.End R A)
    (hd : ∀ u : heckeUpperSubgroup Q q,
      d.comp (A.ρ (sourceHeckeConjugation hq u)) = (A.ρ u.val).comp d)
    (hbd : b.comp d = d.comp b) :
    Commute (sourcePrimeHeckeH1 hp A b hb) (sourcePrimeHeckeH1 hq A d hd) := by
  have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr (by
    intro h
    exact hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  apply LinearMap.ext
  intro x
  change sourcePrimeHeckeH1 hp A b hb (sourcePrimeHeckeH1 hq A d hd x) =
    sourcePrimeHeckeH1 hq A d hd (sourcePrimeHeckeH1 hp A b hb x)
  refine groupCohomology.H1_induction_on x ?_
  intro c
  rw [sourcePrimeHeckeH1_cocycle, sourcePrimeHeckeH1_cocycle,
    sourcePrimeHeckeH1_cocycle, sourcePrimeHeckeH1_cocycle]
  apply (groupCohomology.H1π_eq_iff _ _).mpr
  exact sourceHeckePrimeCommutator_mem hp hq hpQ hqQ hcop A b d hb hd hbd c
end
end Dubon2026
