import Lean
import RiemannZeta.FiniteDirichletPolynomial
import RiemannZeta.CrossNormProduct
import RiemannZeta.CompletedZetaSymmetry
import RiemannZeta.HardyZ
import RiemannZeta.Nonvanishing
import RiemannZeta.GuthMaynard.Asymptotics
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.DirichletPolynomial
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.MeanValue
import RiemannZeta.GuthMaynard.Transfer
import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.BetaDependence
import RiemannZeta.GuthMaynard.DensityReduction

open Lean

def categorizeDeclarations : CoreM Unit := do
  let env ← getEnv
  let mut proved := #[]
  let mut specs := #[]
  let mut hypotheses := #[]
  let mut models := #[]
  
  for (n, cinfo) in env.constants.toList do
    if n.getRoot.toString == "RiemannZeta" then
      let nameStr := n.toString
      if nameStr.endsWith "Hypothesis" then
        hypotheses := hypotheses.push nameStr
      else if nameStr.endsWith "Model" then
        models := models.push nameStr
      else if nameStr.endsWith "Prop" then
        specs := specs.push nameStr
      else if cinfo.isTheorem then
        proved := proved.push nameStr
      else
        pure ()
  
  logInfo m!"=== DEPENDENCY LEDGER ==="
  logInfo m!"[Provisional Models]: {models}"
  logInfo m!"[Temporary Analytic Hypotheses]: {hypotheses}"
  logInfo m!"[Proposition Specifications]: {specs}"
  logInfo m!"[Theorems / Blueprints]: {proved}"

#eval categorizeDeclarations
