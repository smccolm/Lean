import Dubon2026.FiniteLocalCongruenceSubgroup

/-! # Finite subgroups of the original local congruence image

The arithmetic stabilizer is represented over the local field, whereas
the congruence kernel is defined over its integral ring. This comparison
lifts the actual finite subgroup through the faithful coefficient map
and derives its residue-primary order from the proved integral theorem.
-/

namespace Dubon2026

noncomputable section

open Matrix IsLocalRing

/-- A faithful coefficient map preserves the actual residual-primary finite-subgroup criterion. -/
theorem finiteCongruenceImageSubgroup_isPGroup
    {R L ι : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing L]
    [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : p.Prime) [CharP (ResidueField R) p]
    (φ : R →+* L) (hφ : Function.Injective φ)
    (H : Subgroup (GeneralLinearGroup ι L)) [Finite H]
    (hH : H ≤ (MatrixCongruenceKernel (ι := ι) (maximalIdeal R)).map
      (GeneralLinearGroup.map φ)) : IsPGroup p H := by
  let f := GeneralLinearGroup.map (n := ι) φ
  have hf : Function.Injective f := by
    intro x y h
    apply Units.ext
    ext i j
    exact hφ (congrArg (fun M : GeneralLinearGroup ι L => M.val i j) h)
  let J := H.comap f
  let τ : J →* H :=
    { toFun := fun x => ⟨f x.val, x.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x.val y.val) }
  have hτ : Function.Injective τ := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  letI : Finite J := Finite.of_injective τ hτ
  have hJ : J ≤ MatrixCongruenceKernel (maximalIdeal R) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hH hx
    exact hf hxy ▸ hy
  have hP := finiteLocalCongruenceSubgroup_isPGroup p hp J hJ
  apply hP.of_surjective τ
  intro y
  obtain ⟨x, hx, hxy⟩ := hH y.property
  refine ⟨⟨x, ?_⟩, Subtype.ext hxy⟩
  change f x ∈ H
  rw [hxy]
  exact y.property

end
end Dubon2026
