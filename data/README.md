## Vampire data

The vampire json describes results of vampire. It comprises two dictionaries:
methods and values. The methods are from method_id to solver configurations.
Values map a pair of equation ids x, y to a triple describing value, time,
method_id. The pair is concerned with the implication x=>y. The value comes
from the enum below. I.e. 0 means that the implication was refuted, 1 means
that the implication was proven.

````
class Res(Enum):
    """Possible result for single implication."""

    IMPL_FALSE = 0
    IMPL_TRUE = 1
    IMPL_UNKNOWN = 2
````

## Higman-Neumann data

The JSON file `Higman-Neumann.json` lists 213 equation ids, the
corresponding law, the id of a "parent law" which specializes to this
law, and the class: 179 "HN-equivalent" equations whose models are
groups equipped with division, 21 "finite-equivalent" equations whose
finite models have the same property, and 13 "unknown-candidate"
equations for which it is unknown whether they have finite or infinite
non-group models.
