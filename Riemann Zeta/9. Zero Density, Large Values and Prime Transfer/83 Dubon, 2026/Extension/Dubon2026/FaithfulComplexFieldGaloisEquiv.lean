import Dubon2026.FaithfulComplexFieldAction

/-! # Nontrivial original complex stabilizers are the real/complex Galois group

The faithful continuous action injects into the original group of order two.
For a nontrivial stabilizer it is therefore bijective. This exact group
equivalence supplies the coefficient reindexing for DUB-17's archimedean H2.
-/

namespace Dubon2026
noncomputable section
variable (G F : Type) [Group G] [Finite G] [Nontrivial G] [Field F]
  [MulSemiringAction G F] [FaithfulSMul G F]
  (e : F ≃+* ℂ) (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))

/-- The faithful actual complex action fills the real/complex Galois group whenever the original stabilizer is nontrivial. -/
theorem faithfulComplexActionHom_bijective :
    Function.Bijective (faithfulComplexActionHom G F e hc) := by
  letI : Fintype G := Fintype.ofFinite G
  haveI : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
  have ht : Fintype.card Gal(ℂ/ℝ) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      (IsGalois.card_aut_eq_finrank ℝ ℂ).trans Complex.finrank_real_complex
  have hi := faithfulComplexActionHom_injective G F e hc
  have hle := Fintype.card_le_of_injective _ hi
  have hgt : 1 < Fintype.card G := Fintype.one_lt_card
  have he : Fintype.card G = Fintype.card Gal(ℂ/ℝ) := by omega
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, he⟩

/-- The original nontrivial stabilizer is identified with the exact real/complex Galois group. -/
def faithfulComplexActionEquiv : G ≃* Gal(ℂ/ℝ) :=
  MulEquiv.ofBijective (faithfulComplexActionHom G F e hc)
    (faithfulComplexActionHom_bijective G F e hc)

end
end Dubon2026
