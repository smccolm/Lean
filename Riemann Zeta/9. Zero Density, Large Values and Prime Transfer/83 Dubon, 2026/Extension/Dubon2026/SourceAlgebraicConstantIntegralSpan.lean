import Dubon2026.SourceAlgebraicConstantInterpolation

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier spanning -> integral base change of Fricke fractions. The algebraic
constant-adjoining step expresses an integral element as a complex span of
integral elements over the original constants. Finite extension embeddings
and Lagrange interpolation discharge integrality of the actual coordinates.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsIntegral_mem_span_of_adjoin_simple_constants. No proof limit is raised.
The later consumer is the actual Fricke fraction field; constant-extension
spanning and rational Fourier realization are not assumed. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℂ K]
variable (F : IntermediateField ℚ ℂ) (B S : Set K)

theorem mem_span_RSet_of_adjoin_simple (hBS : B ⊆ S) {c : ℂ} (hc : IsIntegral ↥F c) {x : K}
    (hxK : x ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hxint : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) x) :
    x ∈ Submodule.span ℂ (RSet F B S) := by
  classical
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  haveI : CharZero ↥L₀ := charZero_KFld F L₀
  have hint : IsIntegral ↥L₀ (ι c) := isIntegral_KFld_algebraMap F hc
  set E := IntermediateField.adjoin ↥L₀ {ι c}
  set g := IntermediateField.AdjoinSimple.gen ↥L₀ (ι c)
  set pb := IntermediateField.adjoin.powerBasis hint
  have hpbg : pb.gen = g := IntermediateField.adjoin.powerBasis_gen hint
  have hpbd : pb.dim = (minpoly ↥L₀ (ι c)).natDegree :=
    IntermediateField.adjoin.powerBasis_dim hint
  set x' : ↥E := ⟨x, closure_adjoin_le F hxK⟩
  set y : Fin pb.dim → ↥L₀ := fun i ↦ pb.basis.repr x' i
  have hx' : x' = ∑ i, y i • g ^ (i : ℕ) := by
    conv_lhs => rw [← pb.basis.sum_repr x']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pb.coe_basis, hpbg]

  obtain ⟨P, hPm, hPc, hPx⟩ := (isIntegral_subalgebra_iff _ x).mp hxint
  set d := P.natDegree
  choose pc hpc hpcφ using fun n ↦ exists_lift_of_mem_adjoin F B hBS hc (hPc n)
  have hw : x' ^ d + ∑ n ∈ Finset.range d, pc n * x' ^ n = 0 := by
    apply Subtype.ext
    rw [IntermediateField.coe_add, IntermediateField.coe_pow, AddSubmonoidClass.coe_finsetSum,
      ZeroMemClass.coe_zero]
    have := hPx
    rw [hPm.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at this
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      at this
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, hpc]

  set roots := (minpoly ↥L₀ (ι c)).aroots K
  set s := roots.toFinset
  have hsconst : ∀ r ∈ s, ∃ a : ℂ, IsIntegral ↥F a ∧ ι a = r := fun r hr ↦
    root_minpoly_KFld_eq_algebraMap F hc (Multiset.mem_toFinset.mp hr)
  let φ : ∀ r, r ∈ roots → (↥E →ₐ[↥L₀] K) := fun r hr ↦
    (IntermediateField.algHomAdjoinIntegralEquiv ↥L₀ hint).symm ⟨r, hr⟩
  have hφg : ∀ r hr, φ r hr g = r := fun r hr ↦
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ↥L₀ hint ⟨r, hr⟩
  let zf : K → K := fun r ↦ if hr : r ∈ roots then φ r hr x' else 0

  have hZ1 : ∀ r hr, IsIntegral ↥(TRng F B) (φ r hr x') := by
    intro r hr
    set T := Algebra.adjoin ↥(TRng F B) {r}
    have hrint : IsIntegral ↥(TRng F B) r := by
      obtain ⟨a, ha, rfl⟩ := root_minpoly_KFld_eq_algebraMap F hc hr
      exact isIntegral_TRng_algebraMap F ha
    have hpcT : ∀ n, φ r hr (pc n) ∈ T := by
      intro n
      have := hpcφ n (φ r hr)
      rwa [hφg] at this
    have hT : IsIntegral ↥T (φ r hr x') := by
      rw [isIntegral_subalgebra_iff]
      refine ⟨X ^ d + ∑ n ∈ Finset.range d, C (φ r hr (pc n)) * X ^ n, ?_, ?_, ?_⟩
      · apply Polynomial.monic_X_pow_add
        refine (Polynomial.degree_sum_le _ _).trans_lt ?_
        refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun k hk ↦ ?_
        exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))
      · intro k
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
        refine Subalgebra.add_mem _ ?_ (Subalgebra.sum_mem _ fun n _ ↦ ?_)
        · split_ifs
          · exact Subalgebra.one_mem _
          · exact Subalgebra.zero_mem _
        · rw [Polynomial.coeff_C_mul_X_pow]
          split_ifs
          · exact hpcT n
          · exact Subalgebra.zero_mem _
      · rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [← map_pow]
        simp_rw [← map_pow, ← map_mul]
        rw [← map_sum, ← map_add, hw, map_zero]
    exact isIntegral_of_isIntegral_adjoin_singleton hrint hT

  have hZ2 : ∀ r hr, φ r hr x' = ∑ i, (y i : K) * r ^ (i : ℕ) := by
    intro r hr
    rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow, hφg, AlgHom.commutes]
    rfl

  set Y : K[X] := ∑ i : Fin pb.dim, C (y i : K) * X ^ (i : ℕ)
  have hcard : s.card = pb.dim := by
    rw [hpbd]; exact card_rootFinset_minpoly_KFld F hc
  have hYdeg : Y.degree < s.card := by
    rw [hcard]; exact Polynomial.degree_sum_fin_lt _
  have hYeval : ∀ r ∈ s, Y.eval (id r) = zf r := by
    intro r hr
    have hr' : r ∈ roots := Multiset.mem_toFinset.mp hr
    simp only [zf, dif_pos hr', id, hZ2 r hr', Y, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hY : Y = Lagrange.interpolate s id zf :=
    Lagrange.eq_interpolate_of_eval_eq zf (Set.injOn_id _) hYdeg hYeval
  have hYcoeff : ∀ i : Fin pb.dim, Y.coeff i = (y i : K) := by
    intro i
    simp only [Y, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (fun h ↦ hji (Fin.ext h.symm))]
    · intro h; exact absurd (Finset.mem_univ i) h

  have hZ4 : ∀ i : Fin pb.dim, IsIntegral ↥(TRng F B) (y i : K) := by
    intro i
    rw [← hYcoeff, hY, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    refine IsIntegral.sum _ fun r hr ↦ ?_
    rw [Polynomial.coeff_C_mul]
    refine IsIntegral.mul ?_ (isIntegral_coeff_lagrangeBasis F hsconst hr _)
    have hr' : r ∈ roots := Multiset.mem_toFinset.mp hr
    simp only [zf, dif_pos hr']
    exact hZ1 r hr'

  have hZ5 : ∀ i : Fin pb.dim, (y i : K) ∈ RSet F B S := fun i ↦ ⟨(y i).2, hZ4 i⟩

  have hxsum : x = ∑ i : Fin pb.dim, (y i : K) * ι c ^ (i : ℕ) := by
    have := congrArg (fun e : ↥E ↦ (e : K)) hx'
    change (x' : K) = ((∑ i, y i • g ^ (i : ℕ) : E) : K) at this
    rw [IntermediateField.coe_sum] at this
    rw [show x = (x' : K) from rfl, this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IntermediateField.coe_smul, IntermediateField.coe_pow,
      IntermediateField.AdjoinSimple.coe_gen, IntermediateField.smul_def, smul_eq_mul]
  rw [hxsum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have : (y i : K) * ι c ^ (i : ℕ) = (c ^ (i : ℕ)) • (y i : K) := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hZ5 i))


end
end Dubon2026.SourceFricke.ConstantDescent
