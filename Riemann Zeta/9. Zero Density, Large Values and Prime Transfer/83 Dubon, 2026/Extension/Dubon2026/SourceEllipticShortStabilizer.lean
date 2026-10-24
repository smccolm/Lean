import Dubon2026.SourceEllipticExceptionalCoordinates
import Dubon2026.SourceEllipticSubgroupSpecializationTransport

/-! DUB-17/18 -> exceptional place census. On the two short exceptional
models, every stabilizer is a pure scaling. Opposite scalings induce the
same subgroup map, by the already proved invariance under point negation.
This reduces the full coordinate-change relation to two or three orbits. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticStabilizer
open SourceEllipticReduction
noncomputable section
variable {K : Type*} [Field K]

theorem short_stabilizer_translation_zero (W : WeierstrassCurve K)
    (h1 : W.a₁ = 0) (h2' : W.a₂ = 0) (h3' : W.a₃ = 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (C : VariableChange K) (hC : C • W = W) :
    C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hs0 := congrArg WeierstrassCurve.a₁ hC
  rw [variableChange_a₁, h1, zero_add] at hs0
  have hs : C.s = 0 := (mul_eq_zero.mp
    ((mul_eq_zero.mp hs0).resolve_left (C.u⁻¹).ne_zero)).resolve_left h2
  have hr0 := congrArg WeierstrassCurve.a₂ hC
  rw [variableChange_a₂, h2', h1, hs] at hr0
  have hr : C.r = 0 := by
    have hz := (mul_eq_zero.mp hr0).resolve_left (pow_ne_zero 2 (C.u⁻¹).ne_zero)
    have hz' : (3 : K) * C.r = 0 := by simpa only [zero_mul, sub_zero, zero_add, zero_pow two_ne_zero] using hz
    exact (mul_eq_zero.mp hz').resolve_left h3
  have ht0 := congrArg WeierstrassCurve.a₃ hC
  rw [variableChange_a₃, h3', h1, hr] at ht0
  have ht : C.t = 0 := by
    have hz := (mul_eq_zero.mp ht0).resolve_left (pow_ne_zero 3 (C.u⁻¹).ne_zero)
    have hz' : (2 : K) * C.t = 0 := by simpa only [zero_mul, zero_add] using hz
    exact (mul_eq_zero.mp hz').resolve_left h2
  exact ⟨hr, hs, ht⟩

theorem variableChange_eq_pure_of_translation_zero (C : VariableChange K)
    (h : C.r = 0 ∧ C.s = 0 ∧ C.t = 0) : C = ⟨C.u, 0, 0, 0⟩ :=
  VariableChange.ext rfl h.1 h.2.1 h.2.2

theorem pure_scaling_one_point [DecidableEq K] (W : WeierstrassCurve K)
    (h : (⟨1, 0, 0, 0⟩ : VariableChange K) • W = W) (P : W.toAffine.Point) :
    stabilizerPointEquiv W ⟨1, 0, 0, 0⟩ h P = P := by
  apply xy_injective
  rw [xy_stabilizerPointEquiv]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp [vcXInv, vcYInv]

theorem pure_scaling_subgroup_map_eq_of_sign [DecidableEq K]
    (W : WeierstrassCurve K) (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (u v : Kˣ) (hu : (⟨u, 0, 0, 0⟩ : VariableChange K) • W = W)
    (hv : (⟨v, 0, 0, 0⟩ : VariableChange K) • W = W)
    (hs : (u : K) = v ∨ (u : K) = -(v : K)) (H : AddSubgroup W.toAffine.Point) :
    H.map (stabilizerPointEquiv W ⟨u, 0, 0, 0⟩ hu).toAddMonoidHom =
      H.map (stabilizerPointEquiv W ⟨v, 0, 0, 0⟩ hv).toAddMonoidHom := by
  apply subgroup_map_eq_of_eq_or_neg
  rcases hs with hs | hs
  · left
    have he : u = v := Units.ext hs
    subst v
    exact fun _ => rfl
  · right
    intro P
    apply xy_injective
    change xy (stabilizerPointEquiv W ⟨u, 0, 0, 0⟩ hu P) =
      xy (-(stabilizerPointEquiv W ⟨v, 0, 0, 0⟩ hv P))
    rw [xy_stabilizerPointEquiv, xy_neg, xy_stabilizerPointEquiv]
    have hi : ((u⁻¹ : Kˣ) : K) = -((v⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hs, inv_neg]
    rcases xy P with _ | ⟨x, y⟩
    · rfl
    · simp only [Option.map_some, vcXInv, vcYInv, sub_zero, zero_mul,
        Affine.negY, h1, h3, hi, Option.some.injEq, Prod.mk.injEq]
      constructor <;> ring

end
end Dubon2026.SourceEllipticExceptional
