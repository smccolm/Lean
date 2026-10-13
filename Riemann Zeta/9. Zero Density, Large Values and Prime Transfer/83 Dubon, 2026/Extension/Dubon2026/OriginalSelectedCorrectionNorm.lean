/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The local correction argument is adapted to original native ideles from
ClassFieldTheory dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdelePowerLocalUnitNormContainment.lean.
-/
import Dubon2026.OriginalSUnitIdeleCorrection
import Dubon2026.OriginalIdeleNormLocalGlobal
import Dubon2026.OriginalIdeleClassNorm
import Dubon2026.OriginalLocalNormSplitPrime
import Dubon2026.OriginalLocalNormUnramifiedUnits

/-! # Original class norms from the selected S-unit corrections

The actual local-power correction map makes every original idele class a
norm when the given extension splits at S and infinity and is unramified
outside S union T. For the simple Kummer extension of a principal local
power, these local properties are the remaining inputs to prove. Combined
with the already proved cyclic norm-index lower bound, this criterion will
force that extension to be trivial and discharge DUB-17's principal
S-union-T localization equality. No norm-index upper bound is assumed.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Actual selected S-unit corrections and the displayed original local
splitting/unramifiedness conditions imply actual class norm surjectivity. -/
theorem originalIdeleClassNorm_surjective_of_selected_corrections
    (n : ℕ) (hDegree : Module.finrank K L ∣ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hSurj : Function.Surjective (originalSUnitLocalPowerMap K n S T hST))
    (hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ S →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hInf : ∀ w : InfinitePlace L, Function.Surjective (originalInfiniteLocalNorm K L w))
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∪ T →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Function.Surjective (originalIdeleClassNorm K L) := by
  intro c
  obtain ⟨u, hu⟩ := hClasses c
  obtain ⟨x, hx⟩ := originalSupportedIdele_sUnit_power_correction K n S T hST hSurj u
  let y : numberFieldSupportedIdeles K S := u / numberFieldSupportedPrincipalIdele K S x
  have hFin (w : HeightOneSpectrum (𝓞 L)) :
      numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) y.val ∈
        (originalFiniteLocalNorm K L w).range := by
    by_cases hs : originalFinitePrimeBelow K L w ∈ S
    · exact originalFiniteLocalNorm_surjective_of_split K L w (hSplit w hs) _
    · by_cases ht : originalFinitePrimeBelow K L w ∈ T
      · obtain ⟨z, hz⟩ := hx ⟨originalFinitePrimeBelow K L w, ht⟩
        change z ^ n = numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) y.val at hz
        rw [← hz]
        obtain ⟨m, hm⟩ := hDegree
        rw [hm, pow_mul]
        exact (originalFiniteLocalNorm K L w).range.pow_mem
          (originalFiniteLocalNorm_degreePower K L w z) m
      · apply originalFiniteLocalNorm_integerUnit_of_unramified K L w
          (hAway w (by simpa only [Finset.mem_union, not_or] using And.intro hs ht))
        have hy := y.property
        simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] at hy
        exact hy _ hs
  obtain ⟨b, hb⟩ := originalIdeleNorm_exists_of_local K L y.val hFin
    (fun w => hInf w _)
  refine ⟨QuotientGroup.mk' (numberFieldPrincipalIdele L).range b, ?_⟩
  rw [originalIdeleClassNorm_mk, hb]
  change QuotientGroup.mk' (numberFieldPrincipalIdele K).range
    (u.val / numberFieldPrincipalIdele K x.val) = c
  have hp : QuotientGroup.mk' (numberFieldPrincipalIdele K).range
      (numberFieldPrincipalIdele K x.val) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x.val, rfl⟩
  rw [map_div, hp, div_one]
  exact hu

end
end Dubon2026
