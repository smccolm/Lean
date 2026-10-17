import Dubon2026.OriginalRelationDevissage
import Dubon2026.OriginalQuotientInducedRelationDecomposition
import Dubon2026.OriginalQuotientInducedRelationExtension
import Dubon2026.OriginalQuotientRelationObstructionSurjectivity

/-! # The actual relation-extension criterion for nontrivial actions

Assemble the three proved inputs to DUB-17's finite relation dévissage
on the literal induced coefficient sequence. The normalized arithmetic
quotient supplies class data and functional surjectivity. Its actual
kernel norm roots and trivial kernel action suffice; the full Galois
group need not act trivially or have prime-power order.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- For the original arithmetic quotient and a finite prime coefficient,
zero of the actual obstruction is equivalent to extension through the
original free cover. Only the specified subgroup must fix the coefficient. -/
theorem originalClassQuotient_nontrivial_relation_extension_iff
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (p : ℕ) [Fact p.Prime] (N : Subgroup Gal(L/K)) [Fintype N]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] (hB : ∀ b : B, p • b = 0)
    (hNB : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (χ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS) :
    originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS) χ = 0 ↔
      ∃ a : Rep.free ℤ Gal(L/K) B ⟶ originalIdeleClassesModOutsideRep K L S hS,
        originalRelationInclusion B ≫ a = χ := by
  constructor
  · intro hz
    let SB := originalSubgroupInducedSequence N B
    let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
      (Rep.indFunctor ℤ N.subtype)
    letI : Finite SB.X₃ := originalSubgroupInducedQuotient_finite N B
    obtain ⟨ιR, ιP, ρR, ρP, hi₁, hi₂, hr₁, hr₂, hk⟩ :=
      originalClassQuotient_induced_relation_decomposition K L S hS hsys N B
    exact originalRelation_extension_of_devissage _ p
      (originalSubgroupInducedSequence_shortExact N B)
      (originalSubgroupInducedQuotient_nsmul_zero N B p hB)
      TI.f TI.g TI.zero (originalInducedRelationSequence_shortExact N B)
      ιR ιP hi₁ hi₂ ρR ρP hr₁ hr₂ hk
      (fun ψ hψ => (originalClassQuotient_induced_relation_extension
        K L S hS hsys p N hnorm B hB hNB ψ).mp hψ)
      (originalClassQuotient_relation_obstruction_surjective K L S hS hsys SB.X₃) χ hz
  · rintro ⟨a, ha⟩
    exact originalRelationExtensionObstruction_zero_of_extension B _ χ a ha

end
end Dubon2026
