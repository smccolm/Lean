import Dubon2026.NumberFieldAdelicLatticeClosure
import Dubon2026.NumberFieldIntegralMatrixLevel

/-! # Transporting original global lattices to their actual adelic regions

An original rational matrix mapping one attached lattice into another
maps their actual adelic regions into one another, by proved density and
closedness. Evaluating at integral coordinate vectors gives entrywise
integrality of the relative matrix. This supplies DUB-17's remaining
integral level recovery from the recovered rational unitary matrix.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Matrix Topology

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The original principal vector embedding commutes with the original rational matrix action. -/
theorem numberFieldAdelicVectorMap_mulVec (U : Matrix.GeneralLinearGroup ι K) (x : ι → K) :
    (Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)) U).val.mulVec
      (numberFieldAdelicVectorMap K ι x) = numberFieldAdelicVectorMap K ι (U.val.mulVec x) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap K (FiniteAdeleRing (𝓞 K) K)) U.val x i).symm

/-- An original rational matrix mapping attached lattices also maps their exact adelic regions. -/
theorem numberFieldAdelicLattice_transport_region (U : Matrix.GeneralLinearGroup ι K)
    (g h : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (hU : ∀ x ∈ numberFieldAdelicLattice K ι g,
      U.val.mulVec x ∈ numberFieldAdelicLattice K ι h)
    (y : ι → FiniteAdeleRing (𝓞 K) K) (hy : y ∈ numberFieldAdelicLatticeRegion K ι g) :
    (Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)) U).val.mulVec y ∈
      numberFieldAdelicLatticeRegion K ι h := by
  let P := Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)) U
  have hc : Continuous P.val.mulVec := continuous_pi fun i =>
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hr : Set.range (fun x : numberFieldAdelicLattice K ι g =>
      numberFieldAdelicVectorMap K ι x.val) ⊆
      P.val.mulVec ⁻¹' numberFieldAdelicLatticeRegion K ι h := by
    rintro _ ⟨x, rfl⟩
    change P.val.mulVec (numberFieldAdelicVectorMap K ι x.val) ∈
      numberFieldAdelicLatticeRegion K ι h
    rw [numberFieldAdelicVectorMap_mulVec]
    exact (numberFieldAdelicLattice_mem_iff K ι h _).mp (hU x.val x.property)
  have hz := closure_minimal hr ((numberFieldAdelicLatticeRegion_isClosed K ι h).preimage hc)
  rw [numberFieldAdelicLattice_closure] at hz
  exact hz hy

/-- Original lattice transport forces the relative adelic matrix to have integral entries at every original place. -/
theorem numberFieldAdelicLattice_transport_integral (U : Matrix.GeneralLinearGroup ι K)
    (g h : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (hU : ∀ x ∈ numberFieldAdelicLattice K ι g,
      U.val.mulVec x ∈ numberFieldAdelicLattice K ι h) (i j : ι) :
    (h⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)) U * g).val i j ∈
      numberFieldIntegralFiniteAdeles K := by
  let e : ι → FiniteAdeleRing (𝓞 K) K := Pi.single j 1
  have he (k : ι) : e k ∈ numberFieldIntegralFiniteAdeles K := by
    dsimp [e]
    by_cases hk : k = j
    · subst k
      simp only [Pi.single_eq_same]
      exact (numberFieldIntegralFiniteAdeles K).one_mem
    · rw [Pi.single_eq_of_ne hk]
      exact (numberFieldIntegralFiniteAdeles K).zero_mem
  have hregion : g.val.mulVec e ∈ numberFieldAdelicLatticeRegion K ι g := by
    change ∀ k, (g⁻¹).val.mulVec (g.val.mulVec e) k ∈ _
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact he
  have hz := numberFieldAdelicLattice_transport_region K ι U g h hU _ hregion i
  change (h⁻¹).val.mulVec
    ((Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)) U).val.mulVec
      (g.val.mulVec e)) i ∈ _ at hz
  rw [mulVec_mulVec, mulVec_mulVec] at hz
  simpa only [e, mulVec_single_one, Matrix.col_apply] using hz

end
end Dubon2026
