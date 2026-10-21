import Dubon2026.SourceThreeAffinePrimitive
import Dubon2026.SourceTrivialCuspEvaluation
import Dubon2026.SourceCharacterTwistExponent

/-! The exact kernel alternative for the characteristic-three odd twist.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction -> characteristic-three odd twist. If constant inclusion kills
the original class, it vanishes on the actual upper stabilizer. Its nonzero
cusp value then identifies the eigenvalues using the already proved
full-Hecke cusp functional, without repeating an external Hecke sum.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (Q : ℕ) (h3Q : 3 ∣ Q)

/-- A native class killed by constant inclusion vanishes on the actual
subgroup stabilizing zero in the original affine coefficient action. -/
theorem sourceThreeConstantH1_kernel
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F))
    (hz : sourceThreeConstantH1 F Q h3Q (H1π _ z) = 0)
    (g : Gamma0 Q) (hg : (3 : ℤ) ∣ g.val 0 1) : z g = 0 := by
  rw [sourceThreeConstantH1_cocycle, H1π_eq_zero_iff] at hz
  obtain ⟨f, hf⟩ := hz
  have he := congrFun (congrFun hf g) (0 : ZMod 3)
  change f (sourceAffineD 3 Q g *
      (sourceAffineD 3 Q g * 0 - sourceAffineB 3 Q g)) - f 0 = z g at he
  have hb : sourceAffineB 3 Q g = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hg
  rw [hb, mul_zero, sub_self, mul_zero, sub_self] at he
  exact he.symm

include h3Q in
/-- A nonzero original class vanishing on the actual upper stabilizer has
nonzero value on the original unit translation. -/
theorem sourceThreeCocycle_cusp_nonzero
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) (hz : H1π _ z ≠ 0)
    (hvanish : ∀ g : Gamma0 Q, (3 : ℤ) ∣ g.val 0 1 → z g = 0) :
    z (heckeUpperTranslation Q 1) ≠ 0 := by
  intro hT
  have ht (n : ℤ) : z (heckeUpperTranslation Q n) = 0 := by
    let x : Additive (Gamma0 Q) →+ F :=
      (cocycles₁IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom z
    have he := map_zsmul x n (Additive.ofMul (heckeUpperTranslation Q 1))
    change z (heckeUpperTranslation Q 1 ^ n) = n • z (heckeUpperTranslation Q 1) at he
    rw [sourceCuspTranslation_zpow, hT, smul_zero] at he
    exact he
  have hz0 : z = 0 := by
    apply cocycles₁_ext
    intro g
    let n : ℤ := (SourceCupThree.phi Q g).val
    let a := heckeUpperTranslation Q n
    let δ := a⁻¹ * g
    have ha : SourceCupThree.phi Q a = SourceCupThree.phi Q g := by
      simp [a, n, SourceCupThree.phi, sourceAffineB, sourceAffineD, heckeUpperTranslation]
    have hφ : SourceCupThree.phi Q δ = 0 := by
      change SourceCupThree.phi Q (a⁻¹ * g) = 0
      rw [SourceCupThree.phi_mul Q h3Q, SourceCupThree.phi_inv Q h3Q, ha, neg_add_cancel]
    have hD : sourceAffineD 3 Q δ ≠ 0 := by
      intro h
      have he := sourceAffine_ad 3 Q h3Q δ
      rw [h, mul_zero] at he
      exact zero_ne_one he
    have hB : sourceAffineB 3 Q δ = 0 := (mul_eq_zero.mp hφ).resolve_right hD
    have hδ := hvanish δ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hB)
    have he : g = a * δ := by dsimp [δ]; group
    change z g = 0
    rw [he, cocycles₁_map_mul_of_isTrivial, hδ, add_zero]
    exact ht n
  exact hz (by rw [hz0, map_zero])

variable [CharP F 3]

/-- If constant inclusion kills the original nonzero eigenclass, its exact
prime twist already occurs at the original level. -/
theorem sourceThreeCocycle_twist_of_kernel
    (values : sourceBinaryHeckePrime Q → F)
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) (hz : H1π _ z ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell (H1π _ z) =
      values ell • H1π _ z)
    (hker : sourceThreeConstantH1 F Q h3Q (H1π _ z) = 0) :
    ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell (H1π _ z) =
      ((ell.val : F) * values ell) • H1π _ z := by
  have hT := sourceThreeCocycle_cusp_nonzero F Q h3Q z hz
    (sourceThreeConstantH1_kernel F Q h3Q z hker)
  have hEval : sourceTrivialCuspEvaluation F Q (H1π _ z) ≠ 0 := by
    rwa [sourceTrivialCuspEvaluation_cocycle]
  intro ell
  have he := congrArg (sourceTrivialCuspEvaluation F Q) (heig ell)
  rw [sourceTrivialCuspEvaluation_hecke, map_smul, smul_eq_mul] at he
  have hv : (ell.val : F) + 1 = values ell := mul_right_cancel₀ hEval he
  have hp : (ell.val : F) ^ 2 = 1 :=
    sourceCharacter_goodPrime_pow_order F 3 Q h3Q ell
  have hs : (ell.val : F) * values ell = values ell := by
    rw [← hv]
    linear_combination hp
  rw [hs]
  exact heig ell

end
end Dubon2026
