from pathlib import Path
import re
p=Path(__file__).parent
log=p/'SourceOriginalPrimitiveTateImageOwnership8133.log'
assert log.with_suffix('.exit').read_text().strip()=='0'
names=re.findall(r'^OWNER \S+: (\S+)$',log.read_text(encoding='utf-16'),re.M)
assert names and len(names)==len(set(names))
out=p/'SourceOriginalPrimitiveTateImageGlobalOwnership8133.lean';assert not out.exists()
s='import Lean.Util.CollectAxioms\nimport Dubon2026.SemanticRegression\n\nopen Lean\n\n'
s+='private def inspectGlobalOwnership : CoreM Unit := do\n  let env <- getEnv\n'
s+='  let names : Array Name := #['+', '.join('`'+n for n in names)+']\n'
s+='  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]\n'
s+="  for name in names do\n    let some idx := env.getModuleIdxFor? name | throwError \"Missing global owner: {name}\"\n    let some (.thmInfo th) := env.find? name | throwError \"Missing global theorem: {name}\"\n    let axioms <- Lean.collectAxioms name\n    unless (axioms.filter fun a => !allowed.contains a).isEmpty do\n      throwError \"Forbidden global dependencies: {name}: {axioms}\"\n    logInfo m!\"GLOBAL {env.allImportedModuleNames[idx.toNat]!}: {name} {hash th.type} {hash th.value}\"\n\n#eval inspectGlobalOwnership\n"
out.write_text(s,encoding='utf-8')
