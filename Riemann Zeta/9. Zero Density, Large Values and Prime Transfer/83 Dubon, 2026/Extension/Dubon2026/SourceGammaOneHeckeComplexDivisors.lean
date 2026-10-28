import Dubon2026.SourceCurvePicardCorrespondence
import Dubon2026.SourceGammaOneHeckeComplexPlaces
import Dubon2026.SourceGammaOneHeckeConorm

/-! DUB17/18 -> actual Gamma1 arithmetic Tate/Hecke comparison -> actual
divisor naturality. Exact restriction and ramification of lifted places
make finite pullback and geometric pushforward commute with conorm.
The finite-map and commuting-square premises are explicit here and are
discharged by the actual degeneracy maps in the next consumer. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M d : ℕ) [NeZero M] [NeZero d]
variable (φ : (functionFieldOver (Gamma1 M) Qbar) →ₐ[Qbar] (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar)) (ψ : (functionFieldOver (Gamma1 M) ℂ) →ₐ[ℂ] (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ))
variable (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
variable (hcomm : ∀ x, HeckeConstantField.fieldMap M d (φ x) = ψ (fieldMap M x))
include hcomm

theorem finitePullbackAlong_conorm (D : Divisor Qbar (functionFieldOver (Gamma1 M) Qbar)) :
    HeckeConstantField.conorm M d (Divisor.finitePullbackAlong φ hφ D) =
      Divisor.finitePullbackAlong ψ hψ (conorm M D) := by
  classical
  ext w
  by_cases hw : ∃ v, w = HeckeConstantField.liftPlace M d v
  · obtain ⟨v, rfl⟩ := hw
    rw [HeckeConstantField.conorm_apply_liftPlace, Divisor.finitePullbackAlong_apply,
      Divisor.finitePullbackAlong_apply, restrictAlong_heckeLiftPlace M d φ ψ hφ hψ hcomm,
      conorm_apply_liftPlace, ramificationAlong_heckeLiftPlace M d φ ψ hφ hψ hcomm]
  · push Not at hw
    rw [HeckeConstantField.conorm_apply_of_forall_ne M d _ hw,
      Divisor.finitePullbackAlong_apply, conorm_apply_of_forall_ne M D
        (restrictAlong_ne_liftPlace_of_ne_hecke M d φ ψ hψ hcomm hw), zero_mul]

theorem geometricPushforwardAlong_conorm (D : Divisor Qbar (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar)) :
    conorm M (Divisor.geometricPushforwardAlong φ hφ D) =
      Divisor.geometricPushforwardAlong ψ hψ (HeckeConstantField.conorm M d D) := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, map_add, ih]
    congr 1
    rw [Divisor.geometricPushforwardAlong_single, conorm_single,
      HeckeConstantField.conorm_single, Divisor.geometricPushforwardAlong_single,
      restrictAlong_heckeLiftPlace M d φ ψ hφ hψ hcomm]

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
