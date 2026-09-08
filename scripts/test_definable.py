#!/usr/bin/env python3
import numpy as np
from definable import BOOL, close_and_get_equivs


def test_bool_alias():
    assert BOOL is np.bool_


def test_closure_on_chain():
    mat = np.eye(4, dtype=BOOL)
    mat[1, 2] = True
    mat[2, 3] = True
    closed, _, _ = close_and_get_equivs(mat)
    assert closed[1, 3]


if __name__ == "__main__":
    test_bool_alias()
    test_closure_on_chain()
    print("ok - definable dtype")
