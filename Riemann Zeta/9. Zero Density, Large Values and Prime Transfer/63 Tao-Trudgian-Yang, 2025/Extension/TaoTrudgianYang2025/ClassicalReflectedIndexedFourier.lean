import TaoTrudgianYang2025.ClassicalReflectedRadius

/-!
# Fourier deweighting with index-dependent reflected lengths

The pointwise analytic extraction is applied at each actual dyadic length.
The witnesses are then assembled on the original index type before the
perturbation-energy estimate is applied. No cardinality subset is selected.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem exists_classicalReflected_bounded_varying_length_family
    {ι : Type*} [Fintype ι]
    (M k : ℕ) (N : ι → ℕ) (sigma L H : ℝ) (W : ι → ℝ)
    (hM : 0 < M) (hN : ∀ x, 0 < N x) (hL : 0 < L) (hk : 1 < k)
    (hlarge : ∀ x, L ≤
      ‖dirichletPoly (N x) (normalizedTypeIReflectedCoeff sigma M) (W x)‖)
    (hradius : ∀ x,
      classicalTypeIFourierRadius M (N x) k (-sigma) ((M : ℝ)^sigma*L) ≤ H) :
    ∃ W' : ι → ℝ,
      (∀ x, |W' x-W x| ≤ 2*Real.pi*H) ∧
      (∀ x, (M : ℝ)^sigma*L /
          (4*(N x : ℝ)^sigma*classicalTypeIFourierL1 (-sigma)) ≤
        ‖∑ n ∈ Finset.Ioc (N x) (min (2*N x) M), dirichletPhase n (W' x)‖) ∧
      approximateAdditiveEnergyOf 1 W ≤
        (4*Nat.ceil (1+4*(2*Real.pi*H))+6)*approximateAdditiveEnergyOf 1 W' := by
  classical
  have hpoint : ∀ x, ∃ t : ℝ,
      |t-W x| ≤ 2*Real.pi*H ∧
      (M : ℝ)^sigma*L /
          (4*(N x : ℝ)^sigma*classicalTypeIFourierL1 (-sigma)) ≤
        ‖∑ n ∈ Finset.Ioc (N x) (min (2*N x) M), dirichletPhase n t‖ := by
    intro x
    obtain ⟨U,hshift,hvalue,_henergy⟩ :=
      exists_classicalReflected_explicitBoundedOrdinate_family
        M (N x) k sigma L (fun _ : Unit => W x) hM (hN x) hL hk
        (fun _ => hlarge x)
    refine ⟨U (), (hshift ()).trans ?_, hvalue ()⟩
    exact mul_le_mul_of_nonneg_left (hradius x) (by positivity)
  choose W' hshift hvalue using hpoint
  refine ⟨W',hshift,hvalue,?_⟩
  exact (approximateAdditiveEnergyOf_perturbation_le hshift).trans
    (approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _)

end TaoTrudgianYang2025

