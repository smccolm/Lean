import Dubon2026.SourceCuspHeckeSum
import Dubon2026.SourceCuspHeckeColumnMove
import Dubon2026.SourceFiniteCuspBoundary
import Dubon2026.SourceTrivialIntegralHecke

/-! DUB-17/18 -> residual Galois association -> the boundary of the
constructed original complex weight-two eigenclass. The exact two-term
cusp formula is proved for the original native H1 Hecke correspondence.
The required divisible representative is constructed for every cusp;
the final formula has no representative or comparison hypothesis.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup groupCohomology
open scoped MatrixGroups

variable (R : Type) [CommRing R] {N : ℕ} [NeZero N]

/-- The original native H1 Hecke operator acts on every actual cusp value
by the exact two cusp transforms, with multiplicities ell and one. -/
theorem B_native_hecke (x : H1 (Rep.trivial R (Gamma0 N) R))
    (ell : sourceBinaryHeckePrime N) (δ σ₁ σ₂ : SL(2, ℤ))
    (hσ₂ : ((σ₂ 0 0 : ℤ) : ZMod N) * ell.val = δ 0 0 ∧
      ((σ₂ 1 0 : ℤ) : ZMod N) = δ 1 0)
    (hσ₁ : ((σ₁ 0 0 : ℤ) : ZMod N) = δ 0 0 ∧
      ((σ₁ 1 0 : ℤ) : ZMod N) = ell.val * δ 1 0) :
    B ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom
      (sourceTrivialRingHeckeOperators R N ell x)) δ =
      ell.val • B ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom x) σ₂ +
        B ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom x) σ₁ := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  have hnot : ¬ell.val ∣ N := ell.property.1.coprime_iff_not_dvd.mp ell.property.2
  obtain ⟨g, hg, hdvd⟩ := exists_Gamma_mul_dvd ell.property.1 hnot δ
  obtain ⟨hg00, hg01, hg10, hg11⟩ := Gamma_mem.mp hg
  have hg0 : g ∈ Gamma0 N := Gamma0_mem.mpr hg10
  have hcol : colRed N (g * δ) = colRed N δ := by
    rw [colRed_mul_of_mem_Gamma0 hg0, hg00, hg01, hg11]
    apply Prod.ext <;> simp [colRed]
  rw [← B_congr _ hcol]
  have h0 : (((g * δ) 0 0 : ℤ) : ZMod N) = ((δ 0 0 : ℤ) : ZMod N) :=
    congrArg Prod.fst hcol
  have h1 : (((g * δ) 1 0 : ℤ) : ZMod N) = ((δ 1 0 : ℤ) : ZMod N) :=
    congrArg Prod.snd hcol
  change (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom
    (sourceTrivialRingHeckeOperators R N ell x) (Additive.ofMul (uOf N (g * δ))) = _
  rw [sourceTrivialRingHecke_hom_apply]
  exact hecke_sum_uOf (g * δ) ell.property.1 hdvd hnot _ σ₁ σ₂
    (by rw [h0, h1]; exact hσ₂) (by rw [h0, h1]; exact hσ₁)

/-- The finite cusp boundary of the original full native H1 Hecke operator
is its exact unit-coordinate formula at every good prime. -/
theorem bOf_native_hecke (x : H1 (Rep.trivial R (Gamma0 N) R))
    (ell : sourceBinaryHeckePrime N) (p : P N) :
    let u := ZMod.unitOfCoprime ell.val ell.property.2
    bOf ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom
      (sourceTrivialRingHeckeOperators R N ell x)) p =
      ell.val • bOf ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom x)
        (scale u⁻¹ 1 p) +
      bOf ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom x) (scale 1 u p) := by
  let u := ZMod.unitOfCoprime ell.val ell.property.2
  have hu : (u : ZMod N) = ell.val := ZMod.coe_unitOfCoprime _ _
  apply B_native_hecke R x ell (lift p) (lift (scale 1 u p)) (lift (scale u⁻¹ 1 p))
  · constructor
    · change (colRed N (lift (scale u⁻¹ 1 p))).1 * ell.val = (colRed N (lift p)).1
      rw [colRed_lift, colRed_lift, scale_val_fst, ← hu, mul_right_comm, Units.inv_mul,
        one_mul]
    · change (colRed N (lift (scale u⁻¹ 1 p))).2 = (colRed N (lift p)).2
      rw [colRed_lift, colRed_lift, scale_val_snd, Units.val_one, one_mul]
  · constructor
    · change (colRed N (lift (scale 1 u p))).1 = (colRed N (lift p)).1
      rw [colRed_lift, colRed_lift, scale_val_fst, Units.val_one, one_mul]
    · change (colRed N (lift (scale 1 u p))).2 = ell.val * (colRed N (lift p)).2
      rw [colRed_lift, colRed_lift, scale_val_snd, hu]

end
end Dubon2026.SourceCuspBoundary
