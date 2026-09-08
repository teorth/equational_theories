#!/usr/bin/env python3
import os
import sys
import tempfile
from pathlib import Path

sys.path.insert(
    0,
    str(
        Path(__file__).resolve().parents[1]
        / "equational_theories"
        / "Generated"
        / "VampireProven"
        / "src"
    ),
)
from vampire_bin import vampire_executable


def test_env_overrides_path():
    with tempfile.TemporaryDirectory() as d:
        fake = Path(d) / "vampire"
        fake.write_text("")
        fake.chmod(0o755)
        os.environ["VAMPIRE"] = str(fake)
        try:
            assert vampire_executable() == str(fake)
        finally:
            del os.environ["VAMPIRE"]


if __name__ == "__main__":
    test_env_overrides_path()
    print("ok - vampire_bin")
