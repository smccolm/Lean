import Dubon2026.SourceOriginalHeckeComplexPlaces

/-! DUB-17/18 -> original Tate Hecke comparison -> compatibility with the
actual Qbar-to-complex Picard map. The existing conorm is the finite-support
map on unique original place extensions. Exact restriction and ramification
identities give its compatibility with finite pullback and pushforward.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N M : ℕ) [NeZero N] [NeZero M]
variable (φ : modularFunctionFieldOver N Qbar →ₐ[Qbar] modularFunctionFieldOver M Qbar)
variable (ψ : modularFunctionFieldOver N ℂ →ₐ[ℂ] modularFunctionFieldOver M ℂ)
variable (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
variable (hcomm : ∀ x, fieldMap M (φ x) = ψ (fieldMap N x))
include hcomm

theorem finitePullbackAlong_conorm (D : Divisor Qbar (modularFunctionFieldOver N Qbar)) :
    conorm M (Divisor.finitePullbackAlong φ hφ D) =
      Divisor.finitePullbackAlong ψ hψ (conorm N D) := by
  classical
  ext w
  by_cases hw : ∃ v, w = liftPlace M v
  · obtain ⟨v, rfl⟩ := hw
    rw [conorm_apply_liftPlace, Divisor.finitePullbackAlong_apply,
      Divisor.finitePullbackAlong_apply, restrictAlong_liftPlace N M φ ψ hφ hψ hcomm,
      conorm_apply_liftPlace, ramificationAlong_liftPlace N M φ ψ hφ hψ hcomm]
  · push Not at hw
    rw [conorm_apply_of_forall_ne M _ hw, Divisor.finitePullbackAlong_apply,
      conorm_apply_of_forall_ne N D
        (restrictAlong_ne_liftPlace_of_ne N M φ ψ hψ hcomm hw), zero_mul]

theorem geometricPushforwardAlong_conorm (D : Divisor Qbar (modularFunctionFieldOver M Qbar)) :
    conorm N (Divisor.geometricPushforwardAlong φ hφ D) =
      Divisor.geometricPushforwardAlong ψ hψ (conorm M D) := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, map_add, ih]
    congr 1
    rw [Divisor.geometricPushforwardAlong_single, conorm_single,
      conorm_single, Divisor.geometricPushforwardAlong_single,
      restrictAlong_liftPlace N M φ ψ hφ hψ hcomm]

end
end Dubon2026.SourceFunctionField.OriginalConstantField
