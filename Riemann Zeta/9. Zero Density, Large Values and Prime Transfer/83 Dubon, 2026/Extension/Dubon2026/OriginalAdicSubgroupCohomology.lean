import Dubon2026.LocalFieldSubgroupCohomologyBound
import Dubon2026.OriginalAdicUnitCohomology
import Dubon2026.OriginalAdicLocalFieldStructures

/-! # Subgroup cohomology of actual completion units

The literal completion Galois equivalence transfers the existing local
Hilbert 90 and H2 size bounds to every subgroup of the original
decomposition group. These discharge the local fundamental-coefficient
inputs to DUB-17's local/global norm and inertia comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
  (S : Subgroup (OriginalFiniteDecompositionGroup K L w))

/-- Restriction of original completion units is the same coefficient
after the actual subgroup/Galois reindexing, with identity on values. -/
def originalAdicSubgroupUnitCoefficientIso :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    let e := originalAdicDecompositionGaloisEquiv K L v w
    Rep.res (e.subgroupMap S).toMonoidHom
      (Rep.res (S.map e.toMonoidHom).subtype
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))) ≅
      Rep.res S.subtype (originalAdicUnitRep K L w) := by
  dsimp only
  exact Rep.mkIso {
    __ := LinearEquiv.refl ℤ (Additive (w.adicCompletion L)ˣ)
    isIntertwining' _ := by ext x; rfl }

/-- The actual subgroup completion-unit cohomology comparison. -/
def originalAdicSubgroupUnitCohomologyIso (n : ℕ) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    let e := originalAdicDecompositionGaloisEquiv K L v w
    groupCohomology (Rep.res (S.map e.toMonoidHom).subtype
      (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))) n ≅
      groupCohomology (Rep.res S.subtype (originalAdicUnitRep K L w)) n := by
  dsimp only
  exact originalCohomologyReindex _
    ((originalAdicDecompositionGaloisEquiv K L v w).subgroupMap S) n ≪≫
      (groupCohomology.functor ℤ S n).mapIso
        (originalAdicSubgroupUnitCoefficientIso K L v w S)

include v in
/-- Actual completion-unit H1 vanishes on every decomposition subgroup. -/
theorem originalAdicUnit_subgroup_first_zero :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalAdicUnitRep K L w)) 1) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  haveI := (originalAdicBaseChange_finite_galois K L v w).1
  let e := originalAdicDecompositionGaloisEquiv K L v w
  exact Limits.IsZero.of_iso
    (galoisSubgroupUnit_first_cohomology_zero (S.map e.toMonoidHom))
    (originalAdicSubgroupUnitCohomologyIso K L v w S 1).symm

include v in
/-- Actual completion-unit H2 is finite with order at most the subgroup order. -/
theorem originalAdicUnit_subgroup_second_finite_card_le :
    Finite (groupCohomology (Rep.res S.subtype (originalAdicUnitRep K L w)) 2) ∧
      Nat.card (groupCohomology (Rep.res S.subtype (originalAdicUnitRep K L w)) 2) ≤
        Nat.card S := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  haveI := (originalAdicBaseChange_finite_galois K L v w).1
  haveI := (originalAdicBaseChange_finite_galois K L v w).2
  letI : ValuativeRel (v.adicCompletion K) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := v.adicCompletion K))
  haveI := originalAdic_isNonarchimedeanLocalField K v
  let e := originalAdicDecompositionGaloisEquiv K L v w
  obtain ⟨hf, hc⟩ := localField_subgroup_second_cohomology_finite_card_le
    (v.adicCompletion K) (w.adicCompletion L) (S.map e.toMonoidHom)
  haveI := hf
  let q := (originalAdicSubgroupUnitCohomologyIso K L v w S 2).toLinearEquiv.toEquiv
  refine ⟨Finite.of_equiv _ q, ?_⟩
  rw [← Nat.card_congr q]
  exact hc.trans_eq (Nat.card_congr (e.subgroupMap S).toEquiv).symm

end
end Dubon2026
