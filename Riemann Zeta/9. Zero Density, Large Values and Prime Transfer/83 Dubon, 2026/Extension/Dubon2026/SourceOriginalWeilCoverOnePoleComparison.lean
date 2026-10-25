import Dubon2026.SourceOriginalWeilCoverMeromorphicDimension
import Dubon2026.SourceOriginalWeilCoverDimensionBounds
import Dubon2026.SourceOriginalWeilCoverGermBasisRelation

/-! DUB-17/18 -> auxiliary Abel converse -> actual meromorphic field comparison.
Two actual finite cover divisor-space bases exceed the proved analytic pole
bound. Their nontrivial relation identifies a meromorphic function with one
possible pole as an element of the same splitting field. The existing finite
coordinate degree-dimension maximum supplies all dimension and finiteness inputs.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem exists_cover_function_of_one_pole_bound
    (Q : Place ℂ (EE)) (k : ℕ)
    (q : Place ℂ (EE) → ℂ)
    (hq : ∀ v, MeromorphicAt (fun z => q (placeFamily N n r A hr hrA v z)) 0)
    (hord : ∀ v, ((-(Finsupp.single Q (k : ℤ)) v : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => q (placeFamily N n r A hr hrA v z)) 0) :
    ∃ f : EE, ∀ v,
      (fun z => q (placeFamily N n r A hr hrA v z)) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N n r A hr hrA v f := by
  classical
  obtain ⟨g, hg⟩ := exists_cover_degree_dimension_bound N n r
  let m := 2 * g
  let D₁ : Divisor ℂ (EE) := Finsupp.single Q ((k + m : ℕ) : ℤ)
  let D₂ : Divisor ℂ (EE) := Finsupp.single Q (m : ℤ)
  let DN : Place ℂ (EE) →₀ ℕ := Finsupp.single Q (k + m)
  letI := finite_cover_lSpace N n r Q D₁
  letI := finite_cover_lSpace N n r Q D₂
  let bf : Module.Basis (Fin (ell D₁)) ℂ (LSpace D₁) := Module.finBasis ℂ _
  let be : Module.Basis (Fin (ell D₂)) ℂ (LSpace D₂) := Module.finBasis ℂ _
  let ψ : Fin (ell D₁) ⊕ Fin (ell D₂) → Place ℂ (EE) → ℂ :=
    Sum.elim (fun i P => P.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r P) (bf i))
      (fun j P => q P * P.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r P) (be j))
  have hDN : ∀ v, (DN v : ℤ) = D₁ v := by
    intro v
    by_cases h : Q = v <;> simp [DN, D₁, h]
  have hψ : ∀ i v, MeromorphicAt (fun z => ψ i (placeFamily N n r A hr hrA v z)) 0 := by
    rintro (i | j) v
    · exact meromorphicAt_chartRead N n r A hr hrA v (bf i) (Metric.mem_ball_self (place_spec N n r A hr hrA v).1)
    · exact (hq v).mul (meromorphicAt_chartRead N n r A hr hrA v (be j) (Metric.mem_ball_self (place_spec N n r A hr hrA v).1))
  have ho : ∀ i v, ((-(DN v : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => ψ i (placeFamily N n r A hr hrA v z)) 0 := by
    rintro (i | j) v
    · rw [hDN]
      exact chartRead_lSpace_order_bound N n r A hr hrA D₁ (bf i).2 v
    · have hm := meromorphicAt_chartRead N n r A hr hrA v (be j) (Metric.mem_ball_self (place_spec N n r A hr hrA v).1)
      have hb := add_le_add (hord v) (chartRead_lSpace_order_bound N n r A hr hrA D₂ (be j).2 v)
      rw [← WithTop.coe_add, ← meromorphicOrderAt_mul (hq v) hm] at hb
      have he : -(Finsupp.single Q (k : ℤ)) v + -D₂ v = -D₁ v := by
        by_cases h : Q = v <;> simp [D₁, D₂, h, Nat.cast_add]
        ring
      rw [he] at hb
      rw [hDN]
      exact hb
  have hcard : (DN.sum fun _ k => k) + 1 < Fintype.card (Fin (ell D₁) ⊕ Fin (ell D₂)) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have hsum : (DN.sum fun _ k => k) = k + m :=
      Finsupp.sum_single_index (by rfl)
    rw [hsum]
    exact cover_one_place_dimension_sum_gt N n r Q g k hg
  obtain ⟨c, hc0, hc⟩ := exists_cover_meromorphic_relation N n r A hr hrA DN ψ hψ ho hcard
  apply exists_cover_function_of_basis_germ_relation N n r A hr hrA bf be q c hc0
  intro v
  simpa only [Fintype.sum_sum_type, ψ, Sum.elim_inl, Sum.elim_inr, chartRead] using hc v

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
