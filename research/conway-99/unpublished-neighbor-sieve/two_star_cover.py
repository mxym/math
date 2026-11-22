"""Feed first-row representatives and a covering subset to the independent C++ checker."""
from pathlib import Path
import subprocess
import sys

from one_wing_seeds import PAIRS, seed_types


def main():
    cover_file = Path(__file__).with_suffix(".hex")
    selected = int("".join(cover_file.read_text().split()), 16)
    assert selected.bit_count() == 3467 and selected.bit_length() <= 6727
    stream = []
    for support, _, _, rows in seed_types():
        for row in rows:
            member = (selected >> len(stream)) & 1
            endpoints = (i for edge in row for i in PAIRS[edge])
            stream.append(" ".join(map(str, (member, *support, *endpoints))))
    assert len(stream) == 6727
    subprocess.run([sys.argv[1]], input="\n".join(stream), text=True, check=True)


if __name__ == "__main__":
    main()
