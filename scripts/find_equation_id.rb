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

require 'optparse'

VAR_NAMES = "xyzwuvrst"

# ExprType: String, Integer, or [ExprType, String, ExprType]
# ShapeType: nil or [ShapeType, ShapeType]

def process_equation(eq)
  puts "Processing: #{eq}"  # placeholder
end

def main()
    # Main Functon to run the program

    options = {}
    parser = OptionParser.new do |opts|
        opts.banner = "usage: find_equation_id.rb [-h] [--interactive] [equations ...]\n\n" +
                "Canonicalize equations and find their numbers.\n\n"

        opts.separator "positional arguments:"
        opts.separator "  equations          The equations to canonicalize (if not in interactive mode)"
        opts.separator ""

        opts.separator "options:"

        opts.on("-i", "--interactive", "Run in interactive mode") do
            options[:interactive] = true
        end

        opts.on("-h", "--help", "show this help message and exit") do
            puts opts
            exit
        end
    end

    parser.parse!
    equations = ARGV

    if options[:interactive]
        puts "Welcome to the interactive equation canonicalizer!"
        puts "Type 'exit' or 'quit' to end the session."

        loop do
            print "Enter an equation: "
            eq = gets&.chomp
            if eq.nil? || %w[exit quit].include?(eq.downcase)
                puts "Goodbye!"
                break
            end
            process_equation(eq)
        end
    else
        # If stdin is piped (not a terminal)
        unless $stdin.tty?
            piped_equations = $stdin.each_line.flat_map { |line| line.split }
            equations = piped_equations + equations
        end

        if equations.any?
            equations.each { |eq| process_equation(eq) }
        else
            puts parser
        end
    end
end

if __FILE__ == $0
  main()
end
