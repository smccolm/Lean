import Dubon2026.AdelicDistinctLocalHecke
import Dubon2026.AdelicHeckeEigenNormalization
import Dubon2026.AdelicPrimitiveIntertwinerLine
import Dubon2026.AdelicBadPlaceFinite

/-! # The actual bad-place level-fixed cyclic space is the original primitive generator line -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Actual local cyclic membership and local level invariance together give the full original finite-level invariance. -/
theorem adelicLocalCyclic_localFixed_mem_level (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicClosedSpan f v)
    (hfix : x ∈ adelicLocalFixedSpace f v) : x ∈ adelicLevelFixedSpace f := by
  apply (mem_adelicLevelFixedSpace f x).mpr
  intro a
  rw [adelicLocalCyclic_level_action f v a x hx]
  exact hfix ⟨GeneralLinearGroup.map (finiteAdelePlace v) a.val,
    (finiteAdeleGL2Gamma0_iff_places N a.val).mp a.property v⟩

omit [NeZero N] in
/-- Every actual bad place is distinct from every genuine good rational prime place of the original level. -/
theorem badAdelicPlace_ne_good_prime (v : HeightOneSpectrum ℤ) (hv : ¬ IsGoodAdelicPlace N v)
    (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) : v ≠ rationalPrimePlace p hp := by
  intro he
  exact hv ⟨p, hp, hpN, he⟩

/-- Every actual local level-fixed vector in the bad-place cyclic Hilbert space is a scalar multiple of the original primitive generator. -/
theorem adelicBadLocalCyclic_fixed_generator_scalar (F : PrimitiveCuspForm N k) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (hv : ¬ IsGoodAdelicPlace N v)
    (x : AdelicCyclicHilbert F.toCuspForm) (hx : x ∈ adelicLocalCyclicClosedSpan F.toCuspForm v)
    (hfix : x ∈ adelicLocalFixedSpace F.toCuspForm v) :
    ∃ c : ℂ, x = c • adelicCyclicHilbertGenerator F.toCuspForm := by
  have hw : x ∈ adelicRotationWeightSpace F.toCuspForm :=
    adelicFiniteCyclicClosedSpan_le_weight F.toCuspForm (primitiveCuspForm_ne_zero F)
      (adelicLocalCyclicClosedSpan_le_finite F.toCuspForm v hx)
  have hl := adelicLocalCyclic_localFixed_mem_level F.toCuspForm v x hx hfix
  obtain ⟨w, _, he, G, hG, _⟩ := adelicFixedLowest_classical_reconstruction F.toCuspForm
    (primitiveCuspForm_ne_zero F) hk x hw hl
  have hgood (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) :
      cuspHeckeLinear N k p G = cuspCoefficients F.toCuspForm p • G := by
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    apply adelicCyclic_classical_Hecke_eigen F.toCuspForm hpN w G hG
    rw [he]
    apply (adelicNormalizedHecke_eigen_iff F.toCuspForm p hpN x).mp
    rw [adelicNormalizedHecke_eq_local F.toCuspForm p hp hpN x hl]
    exact adelicLocalNormalizedHecke_distinct_component F hp hpN v
      (badAdelicPlace_ne_good_prime v hv p hp hpN) x hx
  have hscalar := primitiveCuspForm_good_prime_eigensystem_scalar F G hgood
  have hwfun : w.val = cuspCoefficients G 1 • (adelicCyclicGenerator N F.toCuspForm).val := by
    rw [hG]
    calc
      _ = canonicalAdelicGL2CuspLift N k (cuspCoefficients G 1 • F.toCuspForm) :=
        congrArg (fun H : CuspForm (Gamma0 N) k => canonicalAdelicGL2CuspLift N k H) hscalar
      _ = _ := canonicalAdelicGL2CuspLift_smul N k (cuspCoefficients G 1) F.toCuspForm
  have hwcore : w = cuspCoefficients G 1 • adelicCyclicGenerator N F.toCuspForm := Subtype.ext hwfun
  refine ⟨cuspCoefficients G 1, ?_⟩
  rw [← he, hwcore, map_smul]
  rfl

end
end Dubon2026
