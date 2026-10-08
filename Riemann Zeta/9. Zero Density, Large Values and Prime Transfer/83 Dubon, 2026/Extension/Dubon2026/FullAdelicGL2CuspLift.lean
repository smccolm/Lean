import Dubon2026.RealGL2Sign

/-! # The original cusp function on both real components and the full finite adelic GL2 group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- Extend the original cusp lift to every real invertible matrix by the actual diagonal rational sign correction. -/
def fullAdelicGL2CuspLift (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : ℂ :=
  positiveAdelicGL2CuspLift N k f (realGL2PositivePart g)
    ((rationalGL2ToFinite (realGL2RationalSign g))⁻¹ * x)

/-- The full construction agrees exactly with the original positive-component adelic lift. -/
theorem fullAdelicGL2CuspLift_positive (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : GL(2, ℝ)⁺) (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    fullAdelicGL2CuspLift N k f g.val x = positiveAdelicGL2CuspLift N k f g x := by
  rw [fullAdelicGL2CuspLift, realGL2PositivePart_of_positive,
    realGL2RationalSign_of_positive, map_one, inv_one, one_mul]

/-- The full original cusp function is invariant under every diagonal rational invertible matrix. -/
theorem fullAdelicGL2CuspLift_rational_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (δ : Matrix.GeneralLinearGroup (Fin 2) ℚ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    fullAdelicGL2CuspLift N k f (rationalGL2ToReal δ * g) (rationalGL2ToFinite δ * x) =
      fullAdelicGL2CuspLift N k f g x := by
  let s := realGL2RationalSign g
  let t := realGL2RationalSign (rationalGL2ToReal δ * g)
  let h := t⁻¹ * δ * s
  have hr : rationalGL2ToReal h =
      (realGL2PositivePart (rationalGL2ToReal δ * g)).val * (realGL2PositivePart g).val⁻¹ := by
    dsimp only [h, realGL2PositivePart, s, t]
    simp only [map_mul, map_inv]
    group
  have hp : h ∈ Matrix.GLPos (Fin 2) ℚ := by
    apply (rationalGL2ToReal_positive_iff h).mp
    rw [hr]
    exact (Matrix.GLPos (Fin 2) ℝ).mul_mem
      (realGL2PositivePart (rationalGL2ToReal δ * g)).property
      ((Matrix.GLPos (Fin 2) ℝ).inv_mem (realGL2PositivePart g).property)
  let d : GL(2, ℚ)⁺ := ⟨h, hp⟩
  have hre : rationalPositiveGL2ToReal d * realGL2PositivePart g =
      realGL2PositivePart (rationalGL2ToReal δ * g) := by
    apply Subtype.ext
    change rationalGL2ToReal h * (realGL2PositivePart g).val = _
    rw [hr, inv_mul_cancel_right]
  have hfe : rationalPositiveGL2ToFinite d * ((rationalGL2ToFinite s)⁻¹ * x) =
      (rationalGL2ToFinite t)⁻¹ * (rationalGL2ToFinite δ * x) := by
    change rationalGL2ToFinite (t⁻¹ * δ * s) * ((rationalGL2ToFinite s)⁻¹ * x) = _
    simp only [map_mul, map_inv]
    group
  have hi := positiveAdelicGL2CuspLift_rational_invariant N f d
    (realGL2PositivePart g) ((rationalGL2ToFinite s)⁻¹ * x)
  rw [hre, hfe] at hi
  exact hi

/-- The full original cusp function retains the genuine finite level invariance. -/
theorem fullAdelicGL2CuspLift_level_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (v : finiteAdeleGL2Gamma0 N) :
    fullAdelicGL2CuspLift N k f g (x * v.val) = fullAdelicGL2CuspLift N k f g x := by
  unfold fullAdelicGL2CuspLift
  rw [← mul_assoc]
  exact positiveAdelicGL2CuspLift_level_invariant N f _ _ v

/-- The original full real-times-finite adelic cusp function is continuous. -/
theorem fullAdelicGL2CuspLift_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Continuous (fun p : Matrix.GeneralLinearGroup (Fin 2) ℝ ×
        Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
      fullAdelicGL2CuspLift N k f p.1 p.2) := by
  let T := Matrix.GeneralLinearGroup (Fin 2) ℝ ×
    Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)
  have hc : Continuous (fun p : T =>
      (realGL2PositivePart p.1, (rationalGL2ToFinite (realGL2RationalSign p.1))⁻¹ * p.2)) :=
    (realGL2PositivePart_continuous.comp continuous_fst).prodMk
      (((realGL2RationalSign_function_continuous rationalGL2ToFinite).comp
        continuous_fst).inv.mul continuous_snd)
  change Continuous ((fun p => positiveAdelicGL2CuspLift N k f p.1 p.2) ∘
    (fun p : T => (realGL2PositivePart p.1,
      (rationalGL2ToFinite (realGL2RationalSign p.1))⁻¹ * p.2)))
  exact (positiveAdelicGL2CuspLift_continuous N f).comp hc

/-- The full adelic function recovers the exact original real lift at finite identity. -/
theorem fullAdelicGL2CuspLift_one (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺) :
    fullAdelicGL2CuspLift N k f g.val 1 = realPositiveUnitaryLift k f g := by
  rw [fullAdelicGL2CuspLift_positive, positiveAdelicGL2CuspLift_one]

/-- The full adelic construction retains the whole original classical cusp form faithfully. -/
theorem fullAdelicGL2CuspLift_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (fun f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k =>
      fullAdelicGL2CuspLift N k f) := by
  intro f h he
  apply positiveAdelicGL2CuspLift_injective N k
  funext g x
  simpa only [fullAdelicGL2CuspLift_positive] using congrFun (congrFun he g.val) x

end
end Dubon2026
