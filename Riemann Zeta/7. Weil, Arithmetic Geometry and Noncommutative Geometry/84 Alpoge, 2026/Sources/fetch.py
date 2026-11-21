"""Restore the original November 2026 Alpöge release alongside this script."""

import hashlib
from pathlib import Path
import shutil
import subprocess
import tempfile


SOURCES = Path(__file__).resolve().parent
SITE = "https://alpo.ge/"
ARCHIVE_SHA256 = "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"
NOTE_SHA256 = "3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d"


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def restore(name, parts, expected_hash):
    destination = SOURCES / name
    if destination.exists():
        if digest(destination) != expected_hash:
            raise ValueError(f"Existing {destination} differs from the pinned release")
        print(f"Verified {name}: {expected_hash}", flush=True)
        return
    with tempfile.TemporaryDirectory() as work:
        fragment = Path(work) / "fragment"
        combined = tempfile.NamedTemporaryFile(dir=SOURCES, prefix="alpoge-download-", delete=False)
        temporary = Path(combined.name)
        try:
            with combined:
                for part in parts:
                    print(f"Fetching {part}", flush=True)
                    subprocess.run(
                        ["curl", "--fail", "--silent", "--show-error", "--location", "--retry", "3",
                         "--connect-timeout", "15", "--max-time", "300",
                         "--output", str(fragment), SITE + part],
                        check=True,
                    )
                    with fragment.open("rb") as source:
                        shutil.copyfileobj(source, combined, length=1024 * 1024)
            if digest(temporary) != expected_hash:
                raise ValueError(f"Downloaded {name} differs from the pinned release")
            temporary.replace(destination)
            print(f"Verified {name}: {expected_hash}", flush=True)
        finally:
            temporary.unlink(missing_ok=True)


if __name__ == "__main__":
    restore("remark.pdf", ["remark.pdf"], NOTE_SHA256)
    restore("lean.tar.gz", [f"lean.tar.gz.part{n:02}" for n in range(1, 15)], ARCHIVE_SHA256)
