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

class Equation()
=begin
    Equation(lhs_shape, rhs_shape, rhyme) denotes an equation

    lhs_shape and rhs_shape are nested pairs (tuples) of None giving how
    the operation is nested, and rhyme a tuple of int (starting with 0)
    giving the rhyme scheme (variable names, as numbers).  For instance,
    Equation(None, ((None, None), None), (0, 1, 0, 2)) is x=(y*x)*z.
=end

    attr_reader :lhs_shape, :rhs_shape, :rhyme

    def initialize(lhs_shape, rhs_shape, rhyme)
        @lhs_shape = lhs_shape
        @rhs_shape = rhs_shape
        @rhyme = rhyme
    end

    # Class Method
    def self.from_id(eq_id)
        # Construct an equation from its id
        _equation_from_id(eq_id)  
    end
end

# Recursive approach to mapping from equation number to id and vice-versa

# Counting equations of some order, based on https://oeis.org/A103293, refactored to access intermediate results.

def num_eqs(n, memo = {})
    # Sequence https://oeis.org/A376640 of the number of magma equations
    return memo[n] if memo.key?(n)

    result = if n.odd?
        (MathHelpers.catalan(n + 1) * MathHelpers.bell(n + 2)) / 2
    else
        return 2 if n == 0
        ((MathHelpers.catalan(n + 1) - MathHelpers.catalan(n / 2)) * MathHelpers.bell(n + 2)) / 2 + MathHelpers.catalan(n / 2) * bell_same_shape(n)
    end

    memo[n] = result
    result
end

@bell_same_shape_cache = {}
def bell_same_shape(n)
    # Number of rhymes when lhs and rhs have the same (n//2)-operations shape
    return 2 if n == 0
    return @bell_same_shape_cache[n] if @bell_same_shape_cache.key?(n)

    sum_stirling = (0..(n + 2)).sum { |k| stirling_sym(n + 2, k) }
    result = (MathHelpers.bell(n + 2) + sum_stirling - 2 * MathHelpers.bell(1 + n / 2)) / 2

    @bell_same_shape_cache[n] = result
    result
end

@stirling_cache = {}
def stirling_sym(n, k)
    # Number of symmetric k-partitions of range(n), see https://oeis.org/A103293
    key = [n, k]
    return @stirling_cache[key] if @stirling_cache.key?(key)

    if n < 2
        result = (k == n) ? 1 : 0
    else
        result = k * stirling_sym(n - 2, k) + stirling_sym(n - 2, k - 1) + stirling_sym(n - 2, k - 2)
    end

    @stirling_cache[key] = result
    result
end



# Map from equation to id and back

def _equation_from_id(input_eq)
  @cache ||= {}
  return @cache[input_eq] if @cache.key?(input_eq)

  n = 0
  eq_num = input_eq - 1

  # @cache[input_eq] = result
  result
end


# Helper fuctions to supplement built in python methods not available in Ruby
def strip_chars(str, chars)
  pattern = /\A[#{Regexp.escape(chars)}]+|[#{Regexp.escape(chars)}]+\z/
  str.gsub(pattern, '')
end

module MathHelpers
  @factorial_cache = {0 => 1, 1 => 1}
  @binomial_cache = {}
  @catalan_cache = {}
  @bell_cache = {0 => 1}

  def self.factorial(n)
    return @factorial_cache[n] if @factorial_cache.key?(n)
    @factorial_cache[n] = n * factorial(n - 1)
  end

  def self.binomial(n, k)
    return 0 if k > n || k < 0
    return 1 if k == 0 || k == n
    key = [n, k]
    return @binomial_cache[key] if @binomial_cache.key?(key)

    # Pascal's rule: C(n,k) = C(n-1,k-1) + C(n-1,k)
    @binomial_cache[key] = binomial(n - 1, k - 1) + binomial(n - 1, k)
  end

  def self.catalan(n)
    return @catalan_cache[n] if @catalan_cache.key?(n)
    # C_n = (1 / (n+1)) * C(2n, n)
    @catalan_cache[n] = binomial(2 * n, n) / (n + 1)
  end

  def self.bell(n)
    return @bell_cache[n] if @bell_cache.key?(n)
    # B_{n+1} = sum_{k=0}^{n} C(n, k) * B_k
    @bell_cache[n] = (0...n).map { |k| binomial(n - 1, k) * bell(k) }.sum
  end
end

# Code used when module is used as a script

def process_equation(eq_str)
    # Process a given equation, printing its id and canonical form.
    eq_str = strip_chars(eq_str, '[,]')
    dual = false
    if eq_str.start_with?("*")
        dual = true
        eq_str = eq_str[1..-1]
    end

    begin
        input_eq = Integer(eq_str)
    rescue ArgumentError
        input_eq = nil
    end

    if input_eq.is_a?(Integer)
        puts "Processing ID: #{input_eq}"  # placeholder for actual processing
    else
        puts "Processing: #{eq_str}"  # placeholder
    end
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
