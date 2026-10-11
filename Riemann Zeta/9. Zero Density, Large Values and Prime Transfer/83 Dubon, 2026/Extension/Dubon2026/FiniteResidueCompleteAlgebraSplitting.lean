import Dubon2026.AdicCompleteResidueSplitting
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Actual splitting in a complete finite local algebra from one original root -/

namespace Dubon2026
noncomputable section

open Polynomial IsLocalRing

/-- For a monic polynomial with separable irreducible residue, one actual root
in a complete finite local algebra gives all the original roots. Normality of
the actual finite residue field supplies the residue roots; the original
complete-ring Hensel construction lifts them individually and counts them. -/
theorem finiteResidue_complete_algebra_polynomial_splits
    {R S : Type} [CommRing R] [CommRing S] [IsDomain S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Finite (ResidueField R)] [IsAdicComplete (maximalIdeal S) S]
    (f : R[X]) (hf : f.Monic) (hi : Irreducible (f.map (residue R)))
    (hs : (f.map (residue R)).Separable)
    (a : S) (ha : aeval a f = 0) :
    (f.map (algebraMap R S)).Splits := by
  haveI : Finite (ResidueField S) := Module.finite_of_finite (ResidueField R)
  have hmap : (f.map (algebraMap R S)).map (residue S) =
      (f.map (residue R)).map (algebraMap (ResidueField R) (ResidueField S)) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
  have har : aeval (residue S a) (f.map (residue R)) = 0 := by
    have he : ((f.map (algebraMap R S)).map (residue S)).eval (residue S a) = 0 := by
      rw [eval_map_apply, eval_map]
      exact congrArg (residue S) ha
    rw [aeval_def, eval₂_eq_eval_map, ← hmap]
    exact he
  have hmin : f.map (residue R) = minpoly (ResidueField R) (residue S a) :=
    minpoly.eq_of_irreducible_of_monic hi har (hf.map _)
  have hsplit := (inferInstance : Normal (ResidueField R) (ResidueField S)).splits
    (residue S a)
  rw [← hmin] at hsplit
  apply adicComplete_polynomial_splits_of_residue (f.map (algebraMap R S)) (hf.map _)
  · rw [hmap]
    exact hs.map
  · rw [hmap]
    exact hsplit

end
end Dubon2026
