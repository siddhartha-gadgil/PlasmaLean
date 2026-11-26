"""Pack or unpack the generated QA2R sources.

    python3 scripts/qa2r/pack.py pack      # generated/qa2r/<Package>/ -> generated/qa2r/archives/<Package>.tar.zst
    python3 scripts/qa2r/pack.py unpack    # the reverse, then check MANIFEST.sha256

Git stores the archives, the manifest and the receipts; the unpacked sources are ignored. The
archives are deterministic (sorted members, zero times and owners), so packing unchanged sources
reproduces them byte for byte. Needs the `zstd` command.
"""
import hashlib
import io
import subprocess
import sys
import tarfile
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / "generated/qa2r"
ARCHIVES = OUT / "archives"


def manifest():
    return dict(reversed(line.split("  ", 1)) for line in (OUT / "MANIFEST.sha256").read_text().splitlines())


def pack():
    by_package = {}
    for rel in manifest():
        by_package.setdefault(rel.split("/")[0], []).append(rel)
    ARCHIVES.mkdir(exist_ok=True)
    for old in ARCHIVES.glob("*.tar.zst"):
        if old.name[:-8] not in by_package:
            old.unlink()
    total = 0
    for package, files in sorted(by_package.items()):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w", format=tarfile.PAX_FORMAT) as tar:
            for rel in sorted(files):
                data = (OUT / rel).read_bytes()
                info = tarfile.TarInfo(rel)
                info.size, info.mode = len(data), 0o644
                tar.addfile(info, io.BytesIO(data))
        target = ARCHIVES / (package + ".tar.zst")
        if target.is_file() and target.stat().st_size <= 95e6:
            # Verify the previous archive decodes to the exact canonical tar before reusing it.
            with subprocess.Popen(["zstd", "-dcq", "--long=27", str(target)],
                                  stdout=subprocess.PIPE) as previous:
                archived = hashlib.file_digest(previous.stdout, "sha256").digest()
            if previous.returncode == 0 and archived == hashlib.sha256(buffer.getbuffer()).digest():
                total += target.stat().st_size
                continue
        packed = subprocess.run(["zstd", "-19", "--long=27", "-T4", "-q", "-c"], input=buffer.getvalue(),
                                capture_output=True, check=True).stdout
        if not target.exists() or target.read_bytes() != packed:
            target.write_bytes(packed)
        total += len(packed)
        if len(packed) > 95e6:
            sys.exit(f"{target.name} is {len(packed) / 1e6:.0f} MB: above the 100 MB file limit")
    print(f"{len(by_package)} archives, {total / 1e6:.0f} MB")


def unpack():
    listed = manifest()
    for archive in sorted(ARCHIVES.glob("*.tar.zst")):
        data = subprocess.run(["zstd", "-d", "--long=27", "-q", "-c", str(archive)],
                              capture_output=True, check=True).stdout
        with tarfile.open(fileobj=io.BytesIO(data)) as tar:
            for member in tar:
                if member.name not in listed or not member.isfile():
                    sys.exit(f"{archive.name}: unexpected member {member.name}")
                content = tar.extractfile(member).read()
                if hashlib.sha256(content).hexdigest() != listed[member.name]:
                    sys.exit(f"hash mismatch: {member.name}")
                target = OUT / member.name
                if not target.exists() or target.read_bytes() != content:  # keep Lake's traces valid
                    target.parent.mkdir(exist_ok=True)
                    target.write_bytes(content)
    missing = [rel for rel in listed if not (OUT / rel).exists()]
    if missing:
        sys.exit(f"{len(missing)} sources missing after unpacking, e.g. {missing[0]}")
    print(f"{len(listed)} sources unpacked and checked")


if __name__ == "__main__":
    {"pack": pack, "unpack": unpack}[sys.argv[1] if len(sys.argv) == 2 else sys.exit(__doc__)]()
