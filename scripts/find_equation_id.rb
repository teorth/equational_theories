#!/usr/bin/env ruby

=begin
This module maps magma equations from/to their id

It can be used as a script in interactive mode (with the -i switch), as

    ruby find_equation_id.rb -i

or by passing arguments to it from stdin or as arguments: a (space-separated)
list of ids or of equations (in which the operation can be ".", "*", or "◇"),
optionally preceeded by "*" to dualize the equation (and characters "[,]" are
ignored):

    ruby find_equation_id.rb [12, 34] "(w*u)=t*(u*x)" 4567 "*89" "*67" "0=(1*2)*(0*1)"

When used as a module imported in python code, one can use
- eq = Equation.from_id(integer id)
- eq = Equation.from_str(string)
- eq.id()
- all_eqs(integer order)
- eq.dual()

The theory of magma operations and their labeling is explained in
https://teorth.github.io/equational_theories/blueprint/basic-theory-chapter.html
=end
