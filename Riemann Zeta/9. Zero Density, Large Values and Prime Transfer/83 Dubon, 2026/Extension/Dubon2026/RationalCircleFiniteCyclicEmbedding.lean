import Dubon2026.RationalCircleFiniteCharacters

/-! # A faithful rational-circle character of the finite cyclic target

The actual H2 of a normalized class coefficient is finite cyclic.
Embedding that group in the rational circle bounds its H2-functional
space by the character space already counted by pinned finite duality.
This is the target-side input for DUB-17's relation-obstruction surjectivity.
-/
namespace Dubon2026
noncomputable section

/-- Every finite cyclic integral module has an injective literal
rational-circle character, constructed from actual roots of unity. -/
theorem originalFiniteCyclic_exists_injective_circle_character
    (A : Type) [AddCommGroup A] [hA : Module ℤ A] [Finite A] [IsAddCyclic A] :
    ∃ f : A →ₗ[ℤ] AddCircle (1 : ℚ), Function.Injective f := by
  let n := Nat.card A
  letI : NeZero n := ⟨Nat.card_pos.ne'⟩
  let M := Multiplicative (AddCircle (1 : ℚ))
  letI := originalRationalCircleEnoughRoots n
  let U := rootsOfUnity n M
  have hc : Nat.card (Multiplicative A) = Nat.card U :=
    (Nat.card_congr ⟨Multiplicative.toAdd, Multiplicative.ofAdd, fun _ => rfl, fun _ => rfl⟩).trans
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity M n).symm
  let e : Multiplicative A ≃* U := mulEquivOfCyclicCardEq hc
  let φ : Multiplicative A →* M :=
    (toUnits (G := M)).symm.toMonoidHom.comp (U.subtype.comp e.toMonoidHom)
  let ψ : A →+ AddCircle (1 : ℚ) := AddMonoidHom.toMultiplicative.symm φ
  let f : A →ₗ[ℤ] AddCircle (1 : ℚ) := {
    toFun := ψ
    map_add' := ψ.map_add
    map_smul' := fun k x => by
      change ψ (hA.smul k x) = k • ψ x
      rw [int_smul_eq_zsmul hA k x]
      exact ψ.map_zsmul k x }
  refine ⟨f, fun x y hxy => ?_⟩
  have he : e (Multiplicative.ofAdd x) = e (Multiplicative.ofAdd y) := by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Multiplicative.ofAdd hxy
  exact congrArg Multiplicative.toAdd (e.injective he)

end
end Dubon2026
