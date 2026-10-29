import Dubon2026.SourceMarkedCyclicRootTransitivity
import Dubon2026.SourceEllipticAllLevelCyclicOrbits
import Dubon2026.SourceEllipticFixedCurvePointMap

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> marked-chart
stabilizers. The actual cyclic-quotient bijection and its native equivariance
turn generic modular-root conjugacy into a Galois move between cyclic
subgroups. No cyclic-subgroup transitivity hypothesis is supplied. Generator
normalization up to sign is supplied separately by the diamond construction. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve SourceEllipticVelu IntegralJCoordinate

theorem exists_cyclic_generator_conjugacy
    {K k Ω : Type*} [Field K] [IsAlgClosed K] [Field k] [Field Ω] [DecidableEq Ω]
    [Algebra K k] [Algebra K Ω] [Algebra k Ω] [IsScalarTower K k Ω] [IsAlgClosure k Ω]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (E : WeierstrassCurve k) [E.IsElliptic] (hE : Transcendental K E.j)
    (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P Q : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = N) (hQ : addOrderOf Q = N) :
    ∃ (σ : Ω ≃ₐ[k] Ω) (n : ℤ), Affine.Point.map (W' := E) σ.toAlgHom P = n • Q := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  letI : Normal k Ω := IsAlgClosure.normal k Ω
  have hNΩ : (N : Ω) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap K Ω)).mpr hN
  have hj : Transcendental K (E.baseChange Ω).j := by
    change Transcendental K (E.map (algebraMap k Ω)).j
    rw [WeierstrassCurve.map_j]
    exact (transcendental_algebraMap_iff (algebraMap k Ω).injective).mpr hE
  let HP : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
    ⟨AddSubgroup.zmultiples P, inferInstance, by rw [Nat.card_zmultiples, hP]⟩
  let HQ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
    ⟨AddSubgroup.zmultiples Q, inferInstance, by rw [Nat.card_zmultiples, hQ]⟩
  have hb := cyclicQuotientJ_bijOn_transcendental N hN (E.baseChange Ω) hj
  obtain ⟨σ, hσ⟩ := exists_modular_root_conjugacy N hN E.j hE hgen
    (cyclicQuotientJ (E.baseChange Ω) N hNΩ HP) (cyclicQuotientJ (E.baseChange Ω) N hNΩ HQ)
    (by simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_j] using hb.mapsTo (Set.mem_univ HP))
    (by simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_j] using hb.mapsTo (Set.mem_univ HQ))
  have hs : fixedCurveCyclicKernelMap σ.toRingHom (E.baseChange Ω)
      (E.map_baseChange σ.toAlgHom) N HP = HQ :=
    hb.injOn (Set.mem_univ _) (Set.mem_univ _)
      ((cyclicQuotientJ_galois E σ N hNΩ HP).trans hσ)
  have hsub := congrArg Subtype.val hs
  rw [fixedCurveCyclicKernelMap_coe, fixedCurvePointMap_galois] at hsub
  change (AddSubgroup.zmultiples P).map (Affine.Point.map (W' := E) σ.toAlgHom) =
    AddSubgroup.zmultiples Q at hsub
  have hmem : Affine.Point.map (W' := E) σ.toAlgHom P ∈ AddSubgroup.zmultiples Q := by
    rw [← hsub]
    exact AddSubgroup.mem_map.mpr ⟨P, AddSubgroup.mem_zmultiples P, rfl⟩
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  exact ⟨σ, n, hn.symm⟩

end
end Dubon2026.SourceFunctionField.MarkedChart
