import Dubon2026.SourceRationalSeparatingCoordinates
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! A function generating the actual rational field has only simple
zeros and poles. Reuse the existing separating-coordinate degree formula
and rational residue fields, avoiding a separate rational-place
classification in the DUB-17/18 global residue proof. -/

noncomputable section

namespace Dubon2026.SourceCurve

open IntermediateField

private theorem integer_le_univ_sum {ι : Type*} [Fintype ι]
    (f : ι → ℤ) (hf : ∀ i, 0 ≤ f i) (i : ι) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

/-- The positive orders of an actual field generator sum to one. -/
theorem sum_positive_orders_generator (t : F) (ht : Transcendental K t)
    (hgen : K⟮t⟯ = ⊤) :
    (∑ᶠ v : {v : Place K F // 0 < v.ord t}, v.1.ord t) = 1 := by
  obtain ⟨hfinite, hsep⟩ := finite_separable_of_adjoin_eq_top t hgen
  have hd : Module.finrank K⟮t⟯ F = 1 :=
    Module.finrank_of_bijective_algebraMap
      ⟨(algebraMap K⟮t⟯ F).injective, fun x => ⟨⟨x, hgen ▸ mem_top⟩, rfl⟩⟩
  have h := sum_positive_orders_eq_finrank_separating t ht
  have hr (v : Place K F) : Module.finrank K v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (place_residue_bijective_of_finite_coordinate t v)
  simpa only [hr, Nat.cast_one, mul_one, hd] using h

/-- Every place order of an actual field generator is at most one. -/
theorem ord_generator_le_one (t : F) (ht : Transcendental K t)
    (hgen : K⟮t⟯ = ⊤) (v : Place K F) : v.ord t ≤ 1 := by
  classical
  by_cases hv : 0 < v.ord t
  · obtain ⟨hfinite, hsep⟩ := finite_separable_of_adjoin_eq_top t hgen
    have hS : {w : Place K F | 0 < w.ord t}.Finite :=
      (finite_function_support_of_separating_coordinate t ht t).subset fun _ hw => ne_of_gt hw
    letI : Fintype {w : Place K F // 0 < w.ord t} := hS.fintype
    have hsum := sum_positive_orders_generator t ht hgen
    rw [finsum_eq_sum_of_fintype] at hsum
    calc
      v.ord t ≤ ∑ w : {w : Place K F // 0 < w.ord t}, w.1.ord t :=
        integer_le_univ_sum (fun w : {w : Place K F // 0 < w.ord t} => w.1.ord t)
          (fun w => le_of_lt w.2) ⟨v, hv⟩
      _ = 1 := hsum
  · omega

/-- The literal orders of a rational generator belong to minus one, zero and one. -/
theorem ord_generator_cases (t : F) (ht : Transcendental K t)
    (hgen : K⟮t⟯ = ⊤) (v : Place K F) :
    v.ord t = -1 ∨ v.ord t = 0 ∨ v.ord t = 1 := by
  have hu := ord_generator_le_one t ht hgen v
  have hti : Transcendental K t⁻¹ := fun hi => ht (IsAlgebraic.inv_iff.mp hi)
  have hgeni : K⟮t⁻¹⟯ = ⊤ := by rw [adjoin_singleton_inv_eq, hgen]
  have hl := ord_generator_le_one t⁻¹ hti hgeni v
  rw [v.ord_inv] at hl
  omega

end Dubon2026.SourceCurve
