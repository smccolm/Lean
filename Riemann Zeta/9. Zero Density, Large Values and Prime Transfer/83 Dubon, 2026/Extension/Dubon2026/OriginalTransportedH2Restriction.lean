import Dubon2026.OriginalTransportedOrbitH2
import Dubon2026.OriginalCoinducedH2Detection

/-! # Literal stabilizer restriction detects a transitive transported H2 class

The existing transported coinduction isomorphism followed by actual
identity evaluation is the original point evaluation. The explicit H2
detection theorem therefore identifies the relevant local maps without
an assumed compatibility of an abstract Shapiro isomorphism. This serves
DUB-17's original global-to-local H2 injection and invariant sum-zero.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))
  [MulAction.IsPretransitive G ι] (i : ι)

/-- Original transported coinduction followed by identity evaluation is literal original point evaluation. -/
theorem originalTransportedCoind_evaluation :
    (Rep.resFunctor (MulAction.stabilizer G i).subtype).map
        (transportedOrbitCoindIso R G ι M T T_one T_mul i).hom ≫
      originalCoinducedEvaluationRepHom (MulAction.stabilizer G i)
        (transportedStabilizerRep R G ι M T T_one T_mul i) =
      transportedStabilizerEvaluation R G ι M T T_one T_mul i := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change transportedPiMap R G ι M T 1 x i = x i
  rw [transportedPiMap_apply R G ι M T 1 x i i (one_smul G i)]
  exact T_one i (x i)

/-- Actual subgroup restriction and original point evaluation detect H2 on a transitive transported product. -/
theorem originalTransportedStabilizerH2_injective :
    Function.Injective (groupCohomology.map (MulAction.stabilizer G i).subtype
      (transportedStabilizerEvaluation R G ι M T T_one T_mul i) 2) := by
  let e := transportedOrbitCoindIso R G ι M T T_one T_mul i
  let B := transportedStabilizerRep R G ι M T T_one T_mul i
  have he : groupCohomology.map (MulAction.stabilizer G i).subtype
        (transportedStabilizerEvaluation R G ι M T T_one T_mul i) 2 =
      (groupCohomology.functor R G 2).map e.hom ≫
        groupCohomology.map (MulAction.stabilizer G i).subtype
          (originalCoinducedEvaluationRepHom (MulAction.stabilizer G i) B) 2 := by
    change groupCohomology.map (MulAction.stabilizer G i).subtype
      (transportedStabilizerEvaluation R G ι M T T_one T_mul i) 2 =
        groupCohomology.map (MonoidHom.id G) e.hom 2 ≫
          groupCohomology.map (MulAction.stabilizer G i).subtype
            (originalCoinducedEvaluationRepHom (MulAction.stabilizer G i) B) 2
    rw [← groupCohomology.map_comp]
    change groupCohomology.map (MulAction.stabilizer G i).subtype
      (transportedStabilizerEvaluation R G ι M T T_one T_mul i) 2 =
      groupCohomology.map (MulAction.stabilizer G i).subtype
        ((Rep.resFunctor (MulAction.stabilizer G i).subtype).map e.hom ≫
          originalCoinducedEvaluationRepHom (MulAction.stabilizer G i) B) 2
    rw [show (Rep.resFunctor (MulAction.stabilizer G i).subtype).map e.hom ≫
      originalCoinducedEvaluationRepHom (MulAction.stabilizer G i) B =
        transportedStabilizerEvaluation R G ι M T T_one T_mul i from
          originalTransportedCoind_evaluation R G ι M T T_one T_mul i]
  intro x y h
  rw [he] at h
  apply ((groupCohomology.functor R G 2).mapIso e).toLinearEquiv.injective
  exact originalCoinducedH2Evaluation_injective (MulAction.stabilizer G i) B h

end
end Dubon2026
