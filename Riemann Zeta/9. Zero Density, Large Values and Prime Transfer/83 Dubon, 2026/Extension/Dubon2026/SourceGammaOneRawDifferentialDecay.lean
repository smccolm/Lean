import Dubon2026.SourceGammaOneLocalRegularDifferentialOrder
import Dubon2026.SourceMeromorphicCuspExponentialDecay

/-! DUB17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
actual meromorphic construction -> exponential cusp decay. Assemble native
periodicity, the proved raw cusp germ, and local regularity at the actual
cusp place. Interior poles require no additional holomorphy assumption. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter SourceCurve KaehlerDifferential
open scoped MatrixGroups ModularForm Topology
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
local notation "EE" => functionFieldOver Γ ℂ

private local instance coefficientCommutes : SMulCommClass ℂ EE EE := ⟨fun c x y => by
  change algebraMap ℂ EE c * (x * y) = x * (algebraMap ℂ EE c * y)
  ring⟩
private local instance differentialModule : Module EE Ω[EE⁄ℂ] :=
  @KaehlerDifferential.module' ℂ EE inferInstance inferInstance inferInstance
    EE inferInstance inferInstance (coefficientCommutes (Γ := Γ))

theorem rawDifferential_cusp_exp_decay (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (a : EE) (ha : a ≠ 0)
    {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hr : (a : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (γ : SL(2, ℤ))
    (hreg : 0 ≤ (cuspPlace N hΓ hT γ).ordDifferential
      (a • D ℂ EE (jCoordinateOver Γ ℂ))) :
    ∃ δ : ℝ, 0 < δ ∧
      (rawDifferential g h ∣[(2 : ℤ)] γ) =O[atImInfty]
        fun τ : ℍ => Real.exp (-δ * τ.im) := by
  let f : SlashInvariantForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2 :=
    { toFun := rawDifferential g h
      slash_action_eq' := by
        intro σ hσ
        obtain ⟨σ', hσ', rfl⟩ := hσ
        exact rawDifferential_slash g h σ' hσ' }
  have hp : Function.Periodic
      ((rawDifferential g h ∣[(2 : ℤ)] γ) ∘ ofComplex) N :=
    SlashInvariantFormClass.periodic_comp_ofComplex
      (SlashInvariantForm.translate f (γ : GL (Fin 2) ℝ))
      (CuspAuxiliary.natCast_mem_strictPeriods_conj N hΓ γ)
  obtain ⟨hmj, -⟩ := cusp_raw_j_derivative_order N hT γ
  have hm : MeromorphicAt (cuspFunction N (rawDifferential g h ∣[(2 : ℤ)] γ)) 0 :=
    ((meromorphicAt_cuspRealize N hΓ hT a γ).mul hmj).congr
      (rawDifferential_cusp_germ N hΓ hT g h hh a hr γ).symm
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hO := SourceMeromorphicCuspDecay.exp_decay_of_cusp_order_pos hN hp hm
    (rawDifferential_cusp_order_pos N hΓ hT a ha g h hh hr γ hreg)
  refine ⟨2 * Real.pi / N, div_pos (mul_pos (by norm_num) Real.pi_pos) hN, ?_⟩
  have he : (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / N)) =
      fun τ : ℍ => Real.exp (-(2 * Real.pi / N) * τ.im) := by
    funext τ
    congr 1
    ring
  rw [he] at hO
  exact hO

end
end Dubon2026.SourceFunctionField.GammaOne
