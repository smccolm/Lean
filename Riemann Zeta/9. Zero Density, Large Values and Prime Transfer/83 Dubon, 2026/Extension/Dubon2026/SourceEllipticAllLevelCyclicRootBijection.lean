import Dubon2026.SourceEllipticAlgebraicCyclicRootBijection
import Dubon2026.SourceEllipticCyclicBijectionTransport
import Dubon2026.SourceCyclicCoordinateAlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The original actual cyclic-subgroup quotient map bijects with the exact
integral modular roots at every invertible level and every transcendental j.
The internal algebraic closure of the actual j-field supplies the proved
induction; native models with prescribed j, exact kernel counts, polynomial
splitting and original coordinate changes remove the auxiliary ambient
algebraicity hypothesis. This is the all-level generic correspondence needed
by the DUB-17/18 inertia census, not the remaining exceptional-fiber census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve IntermediateField SourceEllipticCyclicCount
open SourceFunctionField SourceFunctionField.IntegralJCoordinate
open scoped IntermediateField
noncomputable section

/-- At every admissible level, the original actual cyclic quotients biject with the exact modular roots at transcendental j. -/
theorem cyclicQuotientJ_bijOn_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [DecidableEq F]
    [IsAlgClosed F] [Algebra K F]
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : Transcendental K W.j) :
    let hNF : (N : F) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K F)).mpr hNK
    Set.BijOn (cyclicQuotientJ W N hNF) Set.univ
      {y | (relationAtSeed (modularPolynomial N) W.j).IsRoot y} := by
  intro hNF
  let Ω := algebraicClosure K⟮W.j⟯ F
  letI : DecidableEq Ω := Classical.decEq Ω
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K⟮W.j⟯
  letI : IsScalarTower K Ω F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let t : Ω := algebraMap K⟮W.j⟯ Ω (AdjoinSimple.gen K W.j)
  let f : Ω →+* F := (algebraicClosure K⟮W.j⟯ F).val.toRingHom
  have htF : f t = W.j := rfl
  have ht : Transcendental K t := by
    apply (transcendental_algebraMap_iff (algebraMap Ω F).injective).mp
    change Transcendental K (f t)
    rw [htF]
    exact hj
  let T := ofJ t
  have hTj : T.j = t := ofJ_j t
  letI : Algebra.IsAlgebraic K⟮t⟯ Ω := isAlgebraic_mapped_coordinate_field W.j hj
  have halg (z : Ω) (hz : z = t) : Algebra.IsAlgebraic K⟮z⟯ Ω := by
    subst z
    infer_instance
  letI : Algebra.IsAlgebraic K⟮T.j⟯ Ω := halg T.j hTj
  have hNΩ : (N : Ω) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K Ω)).mpr hNK
  have hcore := cyclicQuotientJ_bijOn_transcendental_algebraic N hNK hNΩ T (hTj.symm ▸ ht)
  have hbase := cyclicQuotientJ_bijOn_map f T N hNΩ hcore
  have he : (T.map f).j = W.j := by rw [map_j, hTj, htF]
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq (T.map f) W he
  have hfinal := cyclicQuotientJ_bijOn_variableChange C (T.map f) N hNF hbase
  have htransport (V V' : WeierstrassCurve F) [V.IsElliptic] [V'.IsElliptic]
      (hV : V = V') :
      Set.BijOn (cyclicQuotientJ V N hNF) Set.univ
        {y | (relationAtSeed (modularPolynomial N) V.j).IsRoot y} →
      Set.BijOn (cyclicQuotientJ V' N hNF) Set.univ
        {y | (relationAtSeed (modularPolynomial N) V'.j).IsRoot y} := by
    subst V'
    exact id
  exact htransport _ _ hC hfinal

end
end Dubon2026.SourceEllipticVelu
