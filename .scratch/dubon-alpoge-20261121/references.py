from pathlib import Path
import re
import tarfile

archive, = Path("Riemann Zeta").glob("7. Weil*/84 Alpoge*/Sources/lean.tar.gz")
keys = re.compile(rb"\b(?:NewtonThorneSym|SymSat|SymSqQ|SymCubeQ)\b")
with tarfile.open(archive, "r|gz") as tar:
    for m in tar:
        if m.name.endswith(".lean"):
            src = tar.extractfile(m).read()
            if keys.search(src):
                for i, line in enumerate(src.splitlines(), 1):
                    if not line.startswith(b"import ") and keys.search(line):
                        print(m.name, i, line.decode()[:350])
