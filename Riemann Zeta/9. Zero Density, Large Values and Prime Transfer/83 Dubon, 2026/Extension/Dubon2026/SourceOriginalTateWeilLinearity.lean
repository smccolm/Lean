import Dubon2026.SourceOriginalTateWeilPairing

/-! DUB-17/18 -> Frobenius determinant -> a p-adic bilinear arithmetic
pairing. Scalar compatibility uses the existing Tate scalar action and
finite additive Weil pairing, without a new inverse-limit framework. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

omit [NeZero N] in
theorem originalTateTorsionCoordinate_padic_smul (k : ℕ) (a : ℤ_[p])
    (x : TateModule p (originalJZero N)) :
    originalTateTorsionCoordinate N p k (a • x) =
      (a.appr k : ℤ) • originalTateTorsionCoordinate N p k x := by
  apply Subtype.ext
  exact TateModule.smul_apply a x k

theorem originalTateWeilPairing_smul_left (a : ℤ_[p]) (x y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p (a • x) y = a • originalTateWeilPairing N p x y := by
  apply Subtype.ext
  funext k
  rw [originalTateWeilPairing_coordinate, TateModule.smul_apply,
    originalTateWeilPairing_coordinate, originalTateTorsionCoordinate_padic_smul]
  have h := congrArg (fun f => f (originalTateTorsionCoordinate N p k y))
    ((originalWeilBilinear N Qbar (p ^ k)).map_zsmul
      (a.appr k : ℤ) (originalTateTorsionCoordinate N p k x))
  have hu := congrArg (rootsOfUnity (p ^ k) Qbar).subtype.toAdditive h
  simp only [AddMonoidHom.zsmul_apply] at hu
  conv_rhs at hu => rw [map_zsmul]
  exact hu

theorem originalTateWeilPairing_smul_right (a : ℤ_[p]) (x y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p x (a • y) = a • originalTateWeilPairing N p x y := by
  apply Subtype.ext
  funext k
  rw [originalTateWeilPairing_coordinate, TateModule.smul_apply,
    originalTateWeilPairing_coordinate, originalTateTorsionCoordinate_padic_smul]
  have h := (originalWeilBilinear N Qbar (p ^ k)
    (originalTateTorsionCoordinate N p k x)).map_zsmul
      (a.appr k : ℤ) (originalTateTorsionCoordinate N p k y)
  have hu := congrArg (rootsOfUnity (p ^ k) Qbar).subtype.toAdditive h
  conv_rhs at hu => rw [map_zsmul]
  exact hu

/-- The actual arithmetic Tate pairing as a p-adic bilinear map. -/
def originalTateWeilBilinear : TateModule p (originalJZero N) →ₗ[ℤ_[p]]
    TateModule p (originalJZero N) →ₗ[ℤ_[p]] TateModule p (Additive Qbarˣ) where
  toFun x := {
    toFun y := originalTateWeilPairing N p x y
    map_add' := originalTateWeilPairing_add_right N p x
    map_smul' a y := originalTateWeilPairing_smul_right N p a x y }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    exact originalTateWeilPairing_add_left N p x x' y
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact originalTateWeilPairing_smul_left N p a x y

end
end Dubon2026.SourceFunctionField
