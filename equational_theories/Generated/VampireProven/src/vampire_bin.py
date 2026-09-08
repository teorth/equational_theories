"""Locate the Vampire executable without a hardcoded Downloads path."""
from __future__ import annotations

import os
import shutil


def vampire_executable() -> str:
    env = os.environ.get("VAMPIRE")
    if env:
        return os.path.expanduser(env)
    found = shutil.which("vampire")
    if found:
        return found
    fallback = os.path.expanduser("~/Downloads/vampire")
    if os.path.isfile(fallback):
        return fallback
    raise FileNotFoundError(
        "vampire not found; set VAMPIRE or put it on PATH"
    )
