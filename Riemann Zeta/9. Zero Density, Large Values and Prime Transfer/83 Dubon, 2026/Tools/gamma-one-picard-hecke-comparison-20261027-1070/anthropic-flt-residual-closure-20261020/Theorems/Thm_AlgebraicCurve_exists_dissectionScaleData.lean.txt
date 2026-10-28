import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_dissectionScaleData
attribute [-instance] AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
attribute [-simp] AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X
attribute [-simp] ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

open scoped Manifold ContDiff Topology Real
open Set AlgebraicCurve Complex

theorem AlgebraicCurve.exists_dissectionScaleData
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (x : F) (n : ℕ) (Bad : Finset ℂ) (o : ℝ) (hm : ℝ) (jlo : ℤ) (jhi : ℤ) (klo : ℤ) (khi : ℤ)
      (Rw : ℝ) (capAt : ℤ × ℤ → Option ℂ) (margin : ℤ × ℤ → Set ℂ)
      (sheet : ℤ × ℤ → Fin n → OpenPartialHomeomorph (Place ℂ F) ℂ)
      (capζ : ℂ → Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ) (capρ : ℂ → Place ℂ F → ℝ)
      (cape : ℂ → Place ℂ F → ℕ) (cs : ℂ → ℝ)
      (infζ : Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ) (infρ : Place ℂ F → ℝ)
      (infe : Place ℂ F → ℕ) (centre : ℤ × ℤ → ℂ),
      (Transcendental ℂ x) ∧
      (FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F) ∧
      (0 < n) ∧
      (n = Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F) ∧
      (∀ b : ℂ, {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}.Finite) ∧
      (∀ t : ℂ, t ∉ Bad →
        {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = t}.ncard = n) ∧
      ({w : Place ℂ F | x ∉ w.toValuationSubring}.Finite) ∧
      (0 < hm) ∧
      (jlo + 1 < jhi) ∧
      (klo + 1 < khi) ∧
      (1 < Rw) ∧
      (∀ z : ℂ, ‖z‖ ≤ Rw →
        (o + jlo * hm < z.re ∧ z.re < o + (jhi + 1) * hm) ∧ (o + klo * hm < z.im ∧ z.im < o + (khi + 1) * hm)) ∧
      (∀ z : ℂ, ‖z‖ < Rw - 1 →
        (o + (jlo + 1) * hm < z.re ∧ z.re < o + jhi * hm) ∧ (o + (klo + 1) * hm < z.im ∧ z.im < o + khi * hm)) ∧
      (∀ b ∈ Bad, ‖b‖ < Rw - 1) ∧
      (∀ b ∈ Bad, ∀ j : ℤ, b.re - o ≠ j * hm ∧ b.im - o ≠ j * hm) ∧
      (∀ b ∈ Bad, ∀ b' ∈ Bad, b ≠ b' →
        2 ≤ |⌊(b.re - o) / hm⌋ - ⌊(b'.re - o) / hm⌋| ∨ 2 ≤ |⌊(b.im - o) / hm⌋ - ⌊(b'.im - o) / hm⌋|) ∧
      (∀ (p : ℤ × ℤ) (b : ℂ), capAt p = some b ↔
        b ∈ Bad ∧ ⌊(b.re - o) / hm⌋ = p.1 ∧ ⌊(b.im - o) / hm⌋ = p.2) ∧
      (∀ p : ℤ × ℤ, p.1 = jlo ∨ p.1 = jhi ∨ p.2 = klo ∨ p.2 = khi → capAt p = none) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → IsOpen (margin p)) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
        {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
          z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ⊆ margin p) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → ∀ b ∈ Bad, b ∉ margin p) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
        ((∀ i, (sheet p i).target = margin p) ∧
            (∀ i, ∀ P ∈ (sheet p i).source, x ∈ P.toValuationSubring ∧ sheet p i P = Place.evalAt P x) ∧
            (Pairwise fun i j => Disjoint (sheet p i).source (sheet p j).source) ∧
            (∀ P : Place ℂ F, x ∈ P.toValuationSubring → Place.evalAt P x ∈ margin p →
              ∃ i, P ∈ (sheet p i).source))) ∧
      (∀ b ∈ Bad, 4 * hm < cs b) ∧
      (∀ b ∈ Bad, ∀ b' ∈ Bad, b' ≠ b → 2 * cs b ≤ dist b b') ∧
      (∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
        (0 < capρ b w ∧ 0 < cape b w ∧ w ∈ (capζ b w).source ∧ capζ b w w = 0 ∧
            (capζ b w).target = Metric.ball 0 (capρ b w) ∧
            (capζ b w).source ⊆ (extChartAt 𝓘(ℂ, ℂ) w).source ∧
            AnalyticOnNhd ℂ (capζ b w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w '' (capζ b w).source) ∧
            (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) w '' (capζ b w).source, deriv (capζ b w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z ≠ 0) ∧
            (∀ P ∈ (capζ b w).source, (x - algebraMap ℂ F b) ∈ P.toValuationSubring ∧ Place.evalAt P (x - algebraMap ℂ F b) = (capζ b w P) ^ cape b w) ∧
            cape b w = (w.ord (x - algebraMap ℂ F b)).toNat)) ∧
      (∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
        2 * cs b < capρ b w ^ cape b w) ∧
      (∀ b ∈ Bad, ∀ w w' : Place ℂ F,
        x ∈ w.toValuationSubring → Place.evalAt w x = b →
        x ∈ w'.toValuationSubring → Place.evalAt w' x = b → w ≠ w' →
        Disjoint (capζ b w).source (capζ b w').source) ∧
      (∀ b ∈ Bad, ∀ P : Place ℂ F, x ∈ P.toValuationSubring →
        ‖Place.evalAt P x - b‖ < 2 * cs b →
        ∃ w : Place ℂ F, x ∈ w.toValuationSubring ∧ Place.evalAt w x = b ∧ P ∈ (capζ b w).source) ∧
      (∀ w : Place ℂ F, x ∉ w.toValuationSubring → (0 < infρ w ∧ 0 < infe w ∧ w ∈ (infζ w).source ∧ infζ w w = 0 ∧
        (infζ w).target = Metric.ball 0 (infρ w) ∧
        (infζ w).source ⊆ (extChartAt 𝓘(ℂ, ℂ) w).source ∧
        AnalyticOnNhd ℂ (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w '' (infζ w).source) ∧
        (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) w '' (infζ w).source, deriv (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z ≠ 0) ∧
        (∀ P ∈ (infζ w).source, x⁻¹ ∈ P.toValuationSubring ∧ Place.evalAt P x⁻¹ = (infζ w P) ^ infe w) ∧
        infe w = (w.ord x⁻¹).toNat)) ∧
      (∀ w : Place ℂ F, x ∉ w.toValuationSubring → 1 / Rw < infρ w ^ infe w) ∧
      (∀ w w' : Place ℂ F, x ∉ w.toValuationSubring → x ∉ w'.toValuationSubring → w ≠ w' →
        Disjoint (infζ w).source (infζ w').source) ∧
      (∀ P : Place ℂ F, x ∈ P.toValuationSubring → Rw ≤ ‖Place.evalAt P x‖ →
        ∃ w : Place ℂ F, x ∉ w.toValuationSubring ∧ P ∈ (infζ w).source) ∧
      (∀ p : ℤ × ℤ, (o + p.1 * hm < (centre p).re ∧ (centre p).re < o + (p.1 + 1) * hm) ∧
        (o + p.2 * hm < (centre p).im ∧ (centre p).im < o + (p.2 + 1) * hm)) ∧
      (∀ p : ℤ × ℤ, p.1 = jhi → o + p.2 * hm < 0 → 0 < o + (p.2 + 1) * hm → (centre p).im = 0) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → Place.evalAt v x ∉ Bad →
        ‖Place.evalAt v x‖ < Rw - 1 ∧
        (∀ j : ℤ, (Place.evalAt v x).re - o ≠ j * hm ∧ (Place.evalAt v x).im - o ≠ j * hm) ∧
        capAt (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = none ∧
        centre (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = Place.evalAt v x) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∀ v' ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → x ∈ v'.toValuationSubring →
        Place.evalAt v x ∉ Bad → Place.evalAt v' x ∉ Bad → Place.evalAt v x ≠ Place.evalAt v' x →
        (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) ≠
          (⌊((Place.evalAt v' x).re - o) / hm⌋, ⌊((Place.evalAt v' x).im - o) / hm⌋)) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → ‖Place.evalAt v x‖ < Rw - 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_dissectionScaleData.solution
