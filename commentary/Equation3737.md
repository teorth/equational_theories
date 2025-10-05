## The half-group (group division) law

Quasigroups satisfying law 3737 are Ward quasigroups ([Ward 1930](https://doi.org/10.2307/1989585)), namely groups equipped with the division operation `x◇y = x y⁻¹`.  To characterize Ward quasigroups with a single law among all magmas, one needs the much longer [Higman–Neumann axiom](https://teorth.github.io/equational_theories/implications/?42323216), of order 8.

In other words, this law is parastrophically equivalent to the [associativity law 4512](https://teorth.github.io/equational_theories/implications/?4512) in the sense that a quasigroup obeys this law if and only if the operation `x◆y` defined by `(x◆y)◇y = x` is associative.  Law 3737 has a long history.

- [Suschkewitsch, in 1928](https://doi.org/10.2307/1989406), considered finite quasigroups such that `(x◇a)◇b = x◇(a∘b)` for some second binary operation `∘`.  This includes the case where `◇` is a group operation (where `∘` is `◇`).  Assuming the [unipotence law 40](https://teorth.github.io/equational_theories/implications/?40), he proves that `◇` is group division, with `∘` being the group operation.  (Law 3737 appears in the form `(R◇C)◇B = R◇Q` for `B=Q◇C` above Postulate J.)

- [Lorenzen, in 1940](https://doi.org/10.1515/crll.1940.182.50), showed that law 3737, together with surjectivity of the map `y↦x◇y` for at least one `x`, implies that `◇` is division in a group.  This is possibly the earliest explicit reference to this law as a group axiom.

- [Higman and Neumann, in 1952](https://mathscinet.ams.org/mathscinet/relay-station?mr=57866), pointed out that law 3737 together with [law 1718](https://teorth.github.io/equational_theories/implications/?1718) `x = (y◇y) ◇ ((x◇x)◇x)` characterizes group division.  There are in fact only two pairs of laws of order up to 4 characterizing group division: laws 3737 and 1718, or laws 3737 and [1731](https://teorth.github.io/equational_theories/implications/?1731) `x = (y◇y) ◇ ((y◇y)◇x)`.

- [Furstenberg, in 1955](https://doi.org/10.2307/2033124) rederives Lorenzen's result, and a variant thereof: law 3737 together with unipotence (law 40) and the fact that every element is a product (`◇` surjective) implies that `◇` is division in a group.  He also gives structure theorems for magmas satisfying solely law 3737, which he dubbed half-groups.

- [Whittaker, in 1955](https://doi.org/10.1080/00029890.1955.11988712) shows that law 3737, together with unipotence (law 40) and the condition `x◇y=x◇x ⇒ y=x`, implies that `◇` is division in a group.

- The structure of half-groups was elucidated by [Whittaker 1959](https://doi.org/10.4153/CJM-1959-060-8).

This law is also called right transivity.  It implies that the squaring map `S: x ↦ x◇x` is idempotent, namely `S(S(x))=S(x)`.
