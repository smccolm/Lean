import Dubon2026.SourceIntegralSlashLinearRelation

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual normalized-generator chart. Equality of
the original reduced Fourier series for same-weight integral forms gives equality
of their literal cusp reductions. This is the two-term specialization of the
proved finite relation transfer, used after clearing discriminant denominators. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm
local notation "Zbar" => integralClosure ℤ ℂ

theorem reducedSlashSeries_eq_of_intSeriesC_eq (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    {K : Type*} [Field K] [CharP K ℓ] (φ : Zbar →+* K) (hN : (N : K) ≠ 0)
    (β : SL(2, ℤ)) {k : ℤ} (hk : Even k)
    (f g : ModularForm (Gamma1 N) k) {p q : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (hq : IsIntegralQExp g q)
    (he : intSeriesC K p = intSeriesC K q) :
    reducedSlashSeries N hk f hp β φ hN = reducedSlashSeries N hk g hq β φ hN := by
  have hc : ∀ n : ℕ, (p.coeff n : K) = (q.coeff n : K) := by
    intro n
    have h := congrArg (fun z : LaurentSeries K => z.coeff (n : ℤ)) he
    simpa only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, eq_intCast] using h
  have h := reducedSlashSeries_linear_relation N ℓ φ hN β hk Finset.univ
    ![f, g] ![p, q] (fun i => by fin_cases i <;> assumption) ![1, -1]
      (fun n => by simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, one_mul, neg_one_mul, hc n, add_neg_cancel])
  have hz : reducedSlashSeries N hk f hp β φ hN -
      reducedSlashSeries N hk g hq β φ hN = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, one_smul, neg_one_smul, sub_eq_add_neg] using h
  exact sub_eq_zero.mp hz

end
end Dubon2026.SourceFunctionField.IntegralSlash
