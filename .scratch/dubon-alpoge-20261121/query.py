import sqlite3, sys
from pathlib import Path

db = sqlite3.connect(Path(__file__).with_name("headers.sqlite"))
for term in sys.argv[1:]:
    where = "name like ?"
    query = f"select count(*) from headers where {where}"
    print(term, db.execute(query, (term,)).fetchone()[0])
    for name, sig in db.execute(f"select name,statement from headers where {where} limit 10", (term,)):
        print(" ", name, sig[:380])
