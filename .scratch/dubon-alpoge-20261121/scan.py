"""Index declaration statements, excluding imports and proofs, from the frozen source."""
from pathlib import Path
import re
import sqlite3
import tarfile

root = Path(__file__).resolve().parent
archive, = Path("Riemann Zeta").glob("7. Weil*/84 Alpoge*/Sources/lean.tar.gz")
declaration = re.compile(r"(?m)^[ \t]*(?:(?:private|noncomputable|protected|public|nonrec|unsafe|opaque)\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([^\s({:\[]+)")
with sqlite3.connect(root / "headers.sqlite") as db, tarfile.open(archive, "r|gz") as tar:
    db.execute("create table if not exists headers(path text, name text, statement text)")
    db.execute("delete from headers")
    files = 0
    for member in tar:
        if not member.isfile() or not member.name.endswith(".lean"):
            continue
        files += 1
        src = tar.extractfile(member).read().decode("utf-8")
        for m in declaration.finditer(src):
            header = re.split(r":=|\n\s*(?:where|deriving)\b|\n\s*\n", src[m.start():m.end()+3500], 1)[0]
            db.execute("insert into headers values (?,?,?)",(member.name,m[1]," ".join(header.split())))
    print(files, db.execute("select count(*) from headers").fetchone()[0], flush=True)
