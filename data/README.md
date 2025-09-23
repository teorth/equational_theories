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
