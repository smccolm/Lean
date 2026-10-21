import Dubon2026.SourceTrivialIntegralHecke

/-! DUB-17/18 -> residual Galois association -> characteristic-zero
weight-two Hecke lifting -> the actual integral, complex and residual
actions. Coefficient change is built from the pinned native trivial-H1
identification. Its full-Hecke compatibility follows from the already
proved original coset sum.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology CategoryTheory

variable (R : Type) [CommRing R] (Q : ℕ)

/-- The actual integral-to-coefficient map on native trivial H1, induced
by the integer cast on the original subgroup homomorphisms. -/
def sourceTrivialH1IntegerChange :
    H1 (Rep.trivial ℤ (Gamma0 Q) ℤ) →ₗ[ℤ] H1 (Rep.trivial R (Gamma0 Q) R) := by
  let f : H1 (Rep.trivial ℤ (Gamma0 Q) ℤ) →+ H1 (Rep.trivial R (Gamma0 Q) R) :=
    AddMonoidHom.mk'
    (fun x => (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).inv
      ((Int.castAddHom R).comp ((H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).hom x)))
    (by intro x y; dsimp only; rw [map_add, AddMonoidHom.comp_add, map_add])
  exact { toFun := f
          map_add' := f.map_add
          map_smul' := fun n x => by simpa using map_intCast_smul f ℤ ℤ n x }

/-- Evaluation of actual H1 coefficient change is literal integer cast. -/
theorem sourceTrivialH1IntegerChange_hom_apply
    (x : H1 (Rep.trivial ℤ (Gamma0 Q) ℤ)) (a : Additive (Gamma0 Q)) :
    (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom
        (sourceTrivialH1IntegerChange R Q x) a =
      (((H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).hom x a : ℤ) : R) := by
  change (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom
    ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).inv _) a = _
  simp

/-- Integral coefficient change commutes with every full original Hecke
operator over the actual target coefficient ring. -/
theorem sourceTrivialH1IntegerChange_hecke
    (ell : sourceBinaryHeckePrime Q) (x : H1 (Rep.trivial ℤ (Gamma0 Q) ℤ)) :
    sourceTrivialH1IntegerChange R Q (sourceTrivialRingHeckeOperators ℤ Q ell x) =
      sourceTrivialRingHeckeOperators R Q ell (sourceTrivialH1IntegerChange R Q x) := by
  apply (ConcreteCategory.bijective_of_isIso
    (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom).injective
  apply AddMonoidHom.ext
  intro a
  have ha : a = Additive.ofMul a.toMul := rfl
  rw [ha, sourceTrivialH1IntegerChange_hom_apply, sourceTrivialRingHecke_hom_apply,
    sourceTrivialRingHecke_hom_apply]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact (sourceTrivialH1IntegerChange_hom_apply R Q x _).symm

/-- In characteristic zero, actual integral H1 embeds in its coefficient
extension; this supplies faithfulness of the integral Hecke action on C. -/
theorem sourceTrivialH1IntegerChange_injective [CharZero R] :
    Function.Injective (sourceTrivialH1IntegerChange R Q) := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso
    (H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).hom).injective
  apply AddMonoidHom.ext
  intro a
  have he := congrArg (fun z =>
    (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom z a) h
  exact Int.cast_injective
    ((sourceTrivialH1IntegerChange_hom_apply R Q x a).symm.trans
      (he.trans (sourceTrivialH1IntegerChange_hom_apply R Q y a)))

end
end Dubon2026
