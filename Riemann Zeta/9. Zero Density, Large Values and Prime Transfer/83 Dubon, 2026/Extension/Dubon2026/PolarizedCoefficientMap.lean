import Dubon2026.PolarizedGaloisGroupLaws

/-! Coefficient change for the source's polarized target. Residual reduction
and coefficient quotients in the CM deformation problem must use this same
group functor and preserve its fixed similitude. These identities supply
that dependency of the potential-automorphy route to DUB-17. -/

namespace Dubon2026
open Matrix

variable {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Fintype ι] [DecidableEq ι]

/-- Matrix coefficient change commutes with the original inverse transpose. -/
theorem polarizedContragredient_map (f : R →+* S) (g : GeneralLinearGroup ι R) :
    GeneralLinearGroup.map f (polarizedContragredient g) =
      polarizedContragredient (GeneralLinearGroup.map f g) := by
  apply Units.ext
  rfl

/-- Coefficient change sends the original scalar matrix to its mapped scalar. -/
theorem polarizedScalar_map (f : R →+* S) (u : Rˣ) :
    GeneralLinearGroup.map f (GeneralLinearGroup.scalar ι u) =
      GeneralLinearGroup.scalar ι (Units.map f u) := by
  apply Units.ext
  ext i j
  by_cases h : i = j <;>
    simp [GeneralLinearGroup.map, GeneralLinearGroup.scalar,
      Matrix.scalar_apply, h]

/-- Coefficient change on the original matrix and multiplier component. -/
def polarizedIdentityCoefficientMap (f : R →+* S) :
    GeneralLinearGroup ι R × Rˣ →* GeneralLinearGroup ι S × Sˣ :=
  (GeneralLinearGroup.map f).prodMap (Units.map f)

/-- The coefficient map intertwines the precise source involution. -/
theorem polarizedSwitch_coefficientMap (f : R →+* S) (x : GeneralLinearGroup ι R × Rˣ) :
    polarizedIdentityCoefficientMap f (polarizedSwitch x) =
      polarizedSwitch (polarizedIdentityCoefficientMap f x) := by
  apply Prod.ext
  · change GeneralLinearGroup.map f
        (GeneralLinearGroup.scalar ι x.2 * polarizedContragredient x.1) = _
    rw [map_mul, polarizedScalar_map, polarizedContragredient_map]
    rfl
  · rfl

/-- Coefficient change intertwines the whole component action. -/
theorem polarizedSwitchAction_coefficientMap (f : R →+* S) (z : Multiplicative (ZMod 2)) :
    (polarizedIdentityCoefficientMap (ι := ι) f).comp (polarizedSwitchAction z).toMonoidHom =
      (polarizedSwitchAction z).toMonoidHom.comp (polarizedIdentityCoefficientMap f) := by
  apply MonoidHom.ext
  intro x
  change polarizedIdentityCoefficientMap f
      ((if z.toAdd = 0 then (1 : MulAut (GeneralLinearGroup ι R × Rˣ))
        else polarizedSwitchAut) x) =
    (if z.toAdd = 0 then (1 : MulAut (GeneralLinearGroup ι S × Sˣ))
      else polarizedSwitchAut) (polarizedIdentityCoefficientMap f x)
  split_ifs
  · rfl
  · exact polarizedSwitch_coefficientMap f x

/-- The actual coefficient functor on the disconnected polarized target. -/
def polarizedCoefficientMap (f : R →+* S) :
    PolarizedGaloisGroup ι R →* PolarizedGaloisGroup ι S :=
  SemidirectProduct.map (polarizedIdentityCoefficientMap f) (MonoidHom.id _)
    (polarizedSwitchAction_coefficientMap f)

/-- Residual reduction preserves the exact connected-component map. -/
theorem polarizedCoefficientMap_component (f : R →+* S) (x : PolarizedGaloisGroup ι R) :
    polarizedComponent (polarizedCoefficientMap f x) = polarizedComponent x := rfl

/-- The source component sign is natural in the coefficient ring. -/
theorem polarizedComponentSign_map (f : R →+* S) (z : Multiplicative (ZMod 2)) :
    Units.map f.toMonoidHom (polarizedComponentSign z) = polarizedComponentSign z := by
  apply Units.ext
  change f (↑(if z.toAdd = 0 then (1 : Rˣ) else -1)) =
    ↑(if z.toAdd = 0 then (1 : Sˣ) else -1)
  split_ifs <;> simp

/-- Residual reduction preserves the source similitude, including its sign. -/
theorem polarizedCoefficientMap_similitude (f : R →+* S) (x : PolarizedGaloisGroup ι R) :
    polarizedSimilitude (polarizedCoefficientMap f x) =
      Units.map f.toMonoidHom (polarizedSimilitude x) := by
  change Units.map f.toMonoidHom x.left.2 * polarizedComponentSign x.right =
    Units.map f.toMonoidHom (x.left.2 * polarizedComponentSign x.right)
  rw [map_mul, polarizedComponentSign_map]

/-- Identity coefficient change is the identity on the same polarized target. -/
theorem polarizedCoefficientMap_id :
    polarizedCoefficientMap (ι := ι) (RingHom.id R) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro x
  rfl

/-- Iterated reduction agrees with reduction along the composite ring map. -/
theorem polarizedCoefficientMap_comp (f : R →+* S) (g : S →+* T) :
    polarizedCoefficientMap (ι := ι) (g.comp f) =
      (polarizedCoefficientMap g).comp (polarizedCoefficientMap f) := by
  apply MonoidHom.ext
  intro x
  rfl

end Dubon2026
