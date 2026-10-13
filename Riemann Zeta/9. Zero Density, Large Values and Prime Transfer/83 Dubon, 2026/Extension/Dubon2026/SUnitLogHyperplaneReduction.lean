import Dubon2026.SUnitFullLogHyperplane
import Dubon2026.SUnitReducedLogLatticeComplete

/-! # The exact original full-to-reduced logarithmic map

Forgetting the distinguished infinite coordinate and dividing the finite
coordinates by the proved nonzero original weights is injective on the
actual sum-zero hyperplane. On original S-units it is the already proved
reduced logarithm. This is the required normalization comparison for
DUB-17's equivariant lattice and Herbrand-quotient argument.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The exact original full-to-reduced logarithmic coordinate map. -/
def sUnitLogHyperplaneReduction : SUnitLogHyperplane K S →ₗ[ℝ] SUnitReducedLogSpace K S where
  toFun z := (fun w => z.val (Sum.inl w.val),
    fun v => z.val (Sum.inr v) / Real.log (Ideal.absNorm v.val.asIdeal : ℝ))
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext v
      exact add_div _ _ _
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext v
      exact mul_div_assoc _ _ _

/-- The missing original infinite coordinate is determined by sum zero, so reduction is injective. -/
theorem sUnitLogHyperplaneReduction_injective :
    Function.Injective (sUnitLogHyperplaneReduction K S) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hoff : ∀ (w : InfinitePlace K), w ≠ Units.dirichletUnitTheorem.w₀ →
      z.val (Sum.inl w) = 0 := fun w hw => congrFun (congrArg Prod.fst hz) ⟨w, hw⟩
  have hfin : ∀ v : S, z.val (Sum.inr v) = 0 := by
    intro v
    have hv := congrFun (congrArg Prod.snd hz) v
    change z.val (Sum.inr v) / Real.log (Ideal.absNorm v.val.asIdeal : ℝ) = 0 at hv
    exact (div_eq_zero_iff.mp hv).resolve_right (sUnit_finiteLogWeight_ne_zero K S v)
  have hsum : ∑ p, z.val p = 0 := z.property
  rw [Fintype.sum_sum_type] at hsum
  have hfinsum : ∑ v : S, z.val (Sum.inr v) = 0 := Finset.sum_eq_zero fun v _ => hfin v
  rw [hfinsum, add_zero,
    Fintype.sum_eq_add_sum_subtype_ne _ (Units.dirichletUnitTheorem.w₀ (K := K))] at hsum
  have hoffsum : ∑ w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀},
      z.val (Sum.inl w.val) = 0 := Finset.sum_eq_zero fun w _ => hoff w.val w.property
  rw [hoffsum, add_zero] at hsum
  apply Subtype.ext
  funext p
  cases p with
  | inl w =>
    by_cases hw : w = Units.dirichletUnitTheorem.w₀
    · subst w
      exact hsum
    · exact hoff w hw
  | inr v => exact hfin v

/-- The original full logarithm reduces exactly to the original reduced logarithm. -/
theorem sUnitLogHyperplaneReduction_fullLog
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitLogHyperplaneReduction K S (sUnitFullLog K S x) = sUnitReducedLog K S x := by
  apply Prod.ext
  · rfl
  · funext v
    change Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.toMul.val.val) /
      Real.log (Ideal.absNorm v.val.asIdeal : ℝ) =
        (sUnitValuationLinearMap (R := 𝓞 K) (K := K) S x v : ℝ)
    rw [sUnit_log_adicAbv_eq_coordinate, mul_div_cancel_right₀ _ (sUnit_finiteLogWeight_ne_zero K S v)]
    rfl

end
end Dubon2026
