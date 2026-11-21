"""Regression: implication closure must stop once the boolean support is closed."""

import unittest

import numpy as np

from definable import close_and_get_equivs


class CloseAndGetEquivsTest(unittest.TestCase):
    def test_chain_reaches_and_stops(self):
        # Identity plus 1→2→3. Integer squaring never stabilizes because
        # self-loops make the walk count grow on every square.
        rel = np.eye(4, dtype=bool)
        rel[1, 2] = True
        rel[2, 3] = True
        closed, _, _ = close_and_get_equivs(rel)
        self.assertTrue(closed[1, 3])
        self.assertFalse(closed[3, 1])
        self.assertTrue(closed[1, 1])

    def test_closure_preserves_256_parallel_paths(self):
        rel = np.eye(258, dtype=bool)
        rel[0, 1:257] = True
        rel[1:257, 257] = True
        closed, _, _ = close_and_get_equivs(rel)
        self.assertTrue(closed[0, 257])
        self.assertFalse(closed[257, 0])
        self.assertTrue(np.all(np.diag(closed)))

    def test_mutual_implication_is_one_class(self):
        rel = np.eye(3, dtype=bool)
        rel[1, 2] = True
        rel[2, 1] = True
        closed, _, reps = close_and_get_equivs(rel)
        self.assertTrue(closed[1, 2] and closed[2, 1])
        # Index 0 is the unused 1-based pad, so the live representative is 1.
        self.assertEqual(list(reps), [1])


if __name__ == "__main__":
    unittest.main()
