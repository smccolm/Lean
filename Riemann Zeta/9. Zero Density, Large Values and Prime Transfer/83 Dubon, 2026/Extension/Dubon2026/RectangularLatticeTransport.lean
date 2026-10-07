import Dubon2026.RectangularProjectiveDomain
import Dubon2026.CuspCosetTrace
import Dubon2026.LatticeCuspResidue
import Dubon2026.PeterssonSlashTransport

/-! # Transport of the actual rectangular completed lattice-cusp integral -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups Pointwise ModularForm

noncomputable section

/-- Every element of the actual real projective subgroup has an integral representative. -/
def integralToRealProjective (H : Subgroup SL(2, ℤ)) : H →* realProjectiveIntegralSubgroup H :=
  (slToRealProjective.comp H.subtype).codRestrict _ (fun g => by
    rw [realProjectiveIntegralSubgroup_eq_map]
    exact ⟨g.val, g.property, rfl⟩)

/-- This map exhausts the real projective subgroup, preserving the actual action. -/
theorem integralToRealProjective_surjective (H : Subgroup SL(2, ℤ)) :
    Function.Surjective (integralToRealProjective H) := by
  intro g
  have hg : (g : PGL(2, ℝ)) ∈ H.map slToRealProjective := by
    simpa only [realProjectiveIntegralSubgroup_eq_map] using g.property
  obtain ⟨δ, hδ, he⟩ := hg
  exact ⟨⟨δ, hδ⟩, Subtype.ext he⟩

/-- The real projective image remains countable. -/
instance realProjectiveIntegralSubgroup_countable (H : Subgroup SL(2, ℤ)) :
    Countable (realProjectiveIntegralSubgroup H) := (integralToRealProjective_surjective H).countable

/-- The actual completed-lattice Petersson integrand is invariant under its faithful real projective subgroup. -/
theorem lattice_petersson_realSubgroup_invariant {H : Subgroup SL(2, ℤ)} {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re)
    (g : realProjectiveIntegralSubgroup H) (z : ℍ) :
    latticeCompletedMellin (g • z) s * petersson k f f (g • z) =
      latticeCompletedMellin z s * petersson k f f z := by
  obtain ⟨δ, rfl⟩ := integralToRealProjective_surjective H g
  change latticeCompletedMellin (δ.val • z) s * petersson k f f (δ.val • z) = _
  rw [latticeCompletedMellin_SL2 hs z δ.val,
    cusp_petersson_integral_invariant f δ.val δ.property z]

/-- The rectangular lattice point at (ab,b) is exactly the original positive diagonal matrix action. -/
theorem rectangularLatticePoint_product_eq_matrix (a b : ℕ) [NeZero a] [NeZero b] (z : ℍ) :
    rectangularLatticePoint (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) z = levelRaiseMatrix a • z := by
  apply UpperHalfPlane.ext
  rw [coe_rectangularLatticePoint, coe_levelRaiseMatrix_smul, Nat.cast_mul,
    mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne b))]

/-- The exact Petersson normalization after inverse diagonal rescaling is derived from the actual slash action. -/
theorem petersson_rectangularCuspForm_rescale {a b : ℕ} [NeZero a] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (z : ℍ) :
    petersson k f f z = (a : ℂ) ^ (k - 2) *
      petersson k (rectangularCuspForm f) (rectangularCuspForm f) (levelRaiseMatrix a • z) := by
  have hcancel : (⇑(rectangularCuspForm f) ∣[k] levelRaiseMatrix a) = ⇑f := by
    rw [rectangularCuspForm_apply, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  have ht := petersson_slash k (rectangularCuspForm f) (rectangularCuspForm f) (levelRaiseMatrix a) z
  rw [hcancel, abs_levelRaiseMatrix_det_val, σ_levelRaiseMatrix, ContinuousAlgEquiv.refl_apply] at ht
  exact ht

/-- The true completed rectangular cusp integral is exactly the mixed-domain integral of the actual rescaled cusp form. -/
theorem rectangularLatticeCuspCompleted_eq_mixedDomain {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) {s : ℂ} (hs : 1 < s.re) :
    rectangularLatticeCuspCompleted f (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) s =
      (a : ℂ) ^ (k - 2) * ∫ z : ℍ in integralSubgroupDomain (rectangularCongruenceSubgroup a b),
        latticeCompletedMellin z s * petersson k (rectangularCuspForm f) (rectangularCuspForm f) z := by
  have hd := (isFundamentalDomain_rectangular_translate a b).setIntegral_eq
    (f := fun z : ℍ => latticeCompletedMellin z s *
      petersson k (rectangularCuspForm f) (rectangularCuspForm f) z)
    (isFundamentalDomain_rectangular_coset a b)
    (lattice_petersson_realSubgroup_invariant (rectangularCuspForm f) hs)
  rw [← hd, integral_matrix_translate, ← integral_const_mul]
  unfold rectangularLatticeCuspCompleted
  apply integral_congr_ae
  filter_upwards with z
  rw [rectangularLatticePoint_product_eq_matrix, petersson_rectangularCuspForm_rescale]
  ring

end
end Dubon2026
