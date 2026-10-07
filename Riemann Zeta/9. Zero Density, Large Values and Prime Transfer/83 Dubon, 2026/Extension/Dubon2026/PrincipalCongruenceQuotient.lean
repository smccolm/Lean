import Dubon2026.SL2Reduction
import Dubon2026.PrincipalCuspOrbit

/-! # The genuine full finite matrix group acts on principal-level cusp forms -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section
attribute [local instance] principalNormal

/-- Strong approximation identifies the actual principal quotient with all of SL₂(Z/NZ). -/
def principalCongruenceEquiv (N : ℕ) [NeZero N] :
    (SL(2, ℤ) ⧸ Gamma N) ≃* SL(2, ZMod N) :=
  QuotientGroup.liftEquiv (Gamma N) (SL2Reduction.SL2_reduction_surjective N) rfl

/-- The quotient equivalence is exactly entrywise reduction on an integral representative. -/
theorem principalCongruenceEquiv_mk (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    principalCongruenceEquiv N (QuotientGroup.mk γ) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ := rfl

/-- The principal cusp representation of the full finite matrix group. -/
def principalFiniteMatrixRepresentation (N : ℕ) [NeZero N] (k : ℤ) :
    Representation ℂ SL(2, ZMod N) (CuspForm ((Gamma N).map (mapGL ℝ)) k) :=
  (principalCuspRepresentation N k).comp (principalCongruenceEquiv N).symm.toMonoidHom

/-- On integral lifts, the finite matrix action is the genuine inverse-slash action. -/
theorem principalFiniteMatrixRepresentation_lift (N : ℕ) [NeZero N] (k : ℤ)
    (γ : SL(2, ℤ)) (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ⇑(principalFiniteMatrixRepresentation N k
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) f) =
      ⇑f ∣[k] mapGL ℝ γ⁻¹ := by
  change ⇑(principalCuspRepresentation N k ((principalCongruenceEquiv N).symm _) f) = _
  rw [← principalCongruenceEquiv_mk, MulEquiv.symm_apply_apply]
  rfl

/-- Transporting scalar rings transports the actual determinant-one matrix group. -/
def sl2RingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply (g i j)
  right_inv g := by ext i j; exact e.apply_symm_apply (g i j)
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

/-- Determinant-one matrices over a product ring are exactly pairs of determinant-one matrices. -/
def sl2ProductEquiv (R S : Type*) [CommRing R] [CommRing S] :
    SL(2, R × S) ≃* (SL(2, R) × SL(2, S)) where
  toFun g := (Matrix.SpecialLinearGroup.map (RingHom.fst R S) g,
    Matrix.SpecialLinearGroup.map (RingHom.snd R S) g)
  invFun g := ⟨fun i j => (g.1 i j, g.2 i j), by
    apply Prod.ext
    · simpa only [Matrix.det_fin_two, Prod.fst_sub, Prod.fst_mul, Prod.fst_one] using g.1.property
    · simpa only [Matrix.det_fin_two, Prod.snd_sub, Prod.snd_mul, Prod.snd_one] using g.2.property⟩
  left_inv g := by ext i j <;> rfl
  right_inv g := by apply Prod.ext <;> ext i j <;> rfl
  map_mul' g h := by
    apply Prod.ext
    · exact (Matrix.SpecialLinearGroup.map (RingHom.fst R S)).map_mul g h
    · exact (Matrix.SpecialLinearGroup.map (RingHom.snd R S)).map_mul g h

/-- Chinese remaindering gives the actual product decomposition of coprime finite SL₂ groups. -/
def sl2ChineseRemainder {M N : ℕ} (h : Nat.Coprime M N) :
    SL(2, ZMod (M * N)) ≃* (SL(2, ZMod M) × SL(2, ZMod N)) :=
  (sl2RingEquiv (ZMod.chineseRemainder h)).trans (sl2ProductEquiv _ _)

end
end Dubon2026
