import Dubon2026.SourceOriginalResidueSlashFieldEmbedding

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> residue cusp count -> actual cusp-place map on the existing translation
orbits. Select the already constructed original-field cusp homomorphisms with
one common coefficient reduction. Their exact generator values and j images
are proved; no map or compatibility certificate is assumed. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open CongruenceSubgroup GammaOne
open scoped MatrixGroups
local notation "Zbar" => integralClosure ℤ ℂ
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
private local instance : Algebra kk (qExpFunctionFieldC kk (Gamma1 N)) :=
  (qExpFunctionFieldC kk (Gamma1 N)).toSubalgebra.algebra

/-- The constructed original residue cusp homomorphism, using the fixed coefficient reduction. -/
def originalResidueCuspHom (hℓN : ¬ ℓ ∣ N) (φ : Zbar →+* kk) (β : SL(2, ℤ)) :
    qExpFunctionFieldC kk (Gamma1 N) →ₐ[kk] LaurentSeries kk :=
  (exists_originalResidueSlashFieldHom A N ℓ hℓN φ β).choose_spec.choose

theorem originalResidueCuspHom_normalized (hℓN : ¬ ℓ ∣ N) (φ : Zbar →+* kk)
    (hN : (N : kk) ≠ 0) (β : SL(2, ℤ)) (x : LaurentSeries kk)
    (hx : x ∈ normalizedGenerators N kk) :
    originalResidueCuspHom A N ℓ hℓN φ β ⟨x, normalizedGenerators_subset N kk hx⟩ =
      normalizedSlashValue N φ hN β x :=
  (exists_originalResidueSlashFieldHom A N ℓ hℓN φ β).choose_spec.choose_spec x hx

theorem originalResidueCuspHom_j (hℓN : ¬ ℓ ∣ N) (φ : Zbar →+* kk) (β : SL(2, ℤ)) :
    originalResidueCuspHom A N ℓ hℓN φ β
      ⟨jqModC kk, jqModC_mem_integralRatioField kk (Gamma1 N)⟩ = qExpand kk N (jqModC kk) := by
  have hN : (N : kk) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff kk ℓ N).mp h)
  exact (originalResidueCuspHom_normalized A N ℓ hℓN φ hN β _
    (jqModC_mem_normalizedGenerators N kk)).trans (normalizedSlashValue_jqModC N ℓ φ hN β)

end
end Dubon2026.SourceFunctionField.IntegralSlash
