This law is [Stein's first law](http://arxiv.org/abs/1509.00796), as named by Sade [1].  It implies that the squaring map `S: x ↦ x◇x` is idempotent (`S(S(x))=S(x)`).

In a quasigroup (more generally when left multiplications are injective) this law implies the [idempotence law 3](https://teorth.github.io/equational_theories/implications/?3) `x = x◇x`.

In a quasigroup, this law holds if and only if the left division operation defined by `x◇(x:y)=y` obeys [law 206](https://teorth.github.io/equational_theories/implications/?206) `x = (x:(x:y)):y`, if and only if the right division operation defined by `(x/y)◇y=x` obeys [law 3343](https://teorth.github.io/equational_theories/implications/?3343) `x/y = y/(x/(x/y))`, namely the laws 335, 206, 3343 (and their duals 384, 124, 4130) are parastrophically equivalent.

This law cannot hold in a non-trivial group.

The free magma with one generator `x` for this law is a two-element magma `{x,x◇x}` with a constant law.

[1]: A. Sade. Quasigroupes obéissant à certaines lois. Rev. Fac. Sci. Univ. Istambul, 22:151–184, 1957.
