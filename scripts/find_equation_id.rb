#!/usr/bin/env ruby

=begin
This code is a port of find_equation_id.py

This module maps magma equations from/to their id

It can be used as a script in interactive mode (with the -i switch), as

    ruby find_equation_id.rb -i

or by passing arguments to it from stdin or as arguments: a (space-separated)
list of ids or of equations (in which the operation can be ".", "*", or "◇"),
optionally preceded by "*" to dualize the equation (and characters "[,]" are
ignored):

    ruby find_equation_id.rb [12, 34] "(w*u)=t*(u*x)" 4567 "*89" "*67" "0=(1*2)*(0*1)"

When this file is required as a module in another Ruby program, one can use
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

class Equation
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
    
    def to_s
      rhyme_enum = @rhyme.each
      lhs_str = self.class._expr_str(@lhs_shape, rhyme_enum, false)
      rhs_str = self.class._expr_str(@rhs_shape, rhyme_enum, false)
      "#{lhs_str} = #{rhs_str}"
    end
    
    def self._expr_str(shape, rhyme_enum, parenthesize)
      if shape.nil?
        i, j = rhyme_enum.next.divmod(VAR_NAMES.length)
        if i == 0
          return VAR_NAMES[j]
        end
        return VAR_NAMES[j] + i.to_s
      end
      left_str = _expr_str(shape[0], rhyme_enum, true)
      right_str = _expr_str(shape[1], rhyme_enum, true)
      if parenthesize
        "(#{left_str} ◇ #{right_str})"
      else
        "#{left_str} ◇ #{right_str}"
      end
    end

    # Class Method
    def self.from_id(eq_id)
        # Construct an equation from its id
        _equation_from_id(eq_id)  
    end
    
    # property
    def id
      _equation_id(self)
    end

    # Class method
    def self.from_str(eq_str)
      # Parse and canonicalize an equation given as a string.
      _equation_from_str(eq_str)
    end
    
    def dual
      # Swap all left and right operands, swap lhs and rhs if needed
      lhs_shape = shape_dual(@lhs_shape)
      rhs_shape = shape_dual(@rhs_shape)
      lhs_order = shape_order(@lhs_shape)
      lhs_rhyme = @rhyme[0..lhs_order].reverse
      rhs_rhyme = @rhyme[(lhs_order + 1)..].reverse
    
      if shape_lt(rhs_shape, lhs_shape)
        lhs_shape, rhs_shape = rhs_shape, lhs_shape
        lhs_rhyme, rhs_rhyme = rhs_rhyme, lhs_rhyme
      end
    
      rhyme = canonicalize_rhyme(lhs_rhyme + rhs_rhyme)
    
      if lhs_shape == rhs_shape
        alt_rhyme = canonicalize_rhyme(rhs_rhyme + lhs_rhyme)
        rhyme = [rhyme, alt_rhyme].min
      end
    
      Equation.new(lhs_shape, rhs_shape, rhyme)
    end
    
end

##### Parsing an equation string

def _tokenize(expr)
  # Convert an expression string into a list of tokens.
  expr = expr.gsub(".", "◇")
             .gsub("*", "◇")
             .gsub("(", " ( ")
             .gsub(")", " ) ")
             .gsub("◇", " ◇ ")
  expr.split.reject(&:empty?)
end

def _parse_expr(tokens)
  # Parse a list of tokens into an expression tree.
  #
  # Return nested triplets (left, "◇", right) with variables as str or int.

  parse_element = lambda do
    raise "Unexpected end of expression" if tokens.empty?

    if tokens[0] == "("
      tokens.shift  # Remove opening parenthesis
      left = parse_element.call
      if tokens.empty? || tokens[0] != "◇"
        raise "Expected '◇' after element in parentheses"
      end
      tokens.shift  # Remove '◇'
      right = parse_element.call
      if tokens.empty? || tokens[0] != ")"
        raise "Missing closing parenthesis"
      end
      tokens.shift  # Remove closing parenthesis
      return [left, "◇", right]
    end

    token = tokens[0]
    if token.match?(/\A[a-zA-Z_]\w*\z/) || token == "0" || token.match?(/\A[1-9]\d*\z/)
      return tokens.shift
    end

    raise "Unexpected token: #{token}"
  end

  result = parse_element.call
  if !tokens.empty?
    if tokens[0] != "◇"
      raise "Unexpected token after main element: #{tokens[0]}"
    end
    tokens.shift  # Remove '◇'
    right = parse_element.call
    unless tokens.empty?
      raise "Unexpected tokens at the end of expression: #{tokens.join(' ')}"
    end
    result = [result, "◇", right]
  end

  result
end


def _deconstruct_tree(tree)
  if tree.is_a?(String)
    return [nil, [tree]]
  end

  left, _op, right = tree
  left_shape, left_rhyme = _deconstruct_tree(left)
  right_shape, right_rhyme = _deconstruct_tree(right)

  [[left_shape, right_shape], left_rhyme + right_rhyme]
end


def _equation_from_str(eq_str)
  begin
    lhs, rhs = eq_str.split('=')
  rescue
    raise ArgumentError, "No '=' or two '=' found in the equation."
  end

  lhs = _parse_expr(_tokenize(lhs))
  rhs = _parse_expr(_tokenize(rhs))

  lhs_shape, lhs_rhyme = _deconstruct_tree(lhs)
  rhs_shape, rhs_rhyme = _deconstruct_tree(rhs)

  if shape_lt(rhs_shape, lhs_shape)
    lhs_shape, rhs_shape = rhs_shape, lhs_shape
    lhs_rhyme, rhs_rhyme = rhs_rhyme, lhs_rhyme
  end

  rhyme = canonicalize_rhyme(lhs_rhyme + rhs_rhyme)

  if lhs_shape == rhs_shape
    rhyme = [rhyme, canonicalize_rhyme(rhs_rhyme + lhs_rhyme)].min
  end

  Equation.new(lhs_shape, rhs_shape, rhyme)
end


#### On shapes
def shape_dual(shape)
  return nil if shape.nil?
  left, right = shape
  [shape_dual(right), shape_dual(left)]
end

def shape_order(shape)
  return 0 if shape.nil?
  1 + shape_order(shape[0]) + shape_order(shape[1])
end

def shape_cmp(shape1, shape2)
  shape1_order = shape_order(shape1)
  shape2_order = shape_order(shape2)
  return -1 if shape1_order < shape2_order
  return 1 if shape1_order > shape2_order
  return 0 if shape1.nil? && shape2.nil?

  left_cmp = shape_cmp(shape1[0], shape2[0])
  return left_cmp unless left_cmp == 0

  shape_cmp(shape1[1], shape2[1])
end

def shape_lt(shape1, shape2)
  shape_cmp(shape1, shape2) < 0
end


##### Generating all rhymes, all shapes, all equational_theories
def canonicalize_rhyme(rhyme)
  variables = {}
  rhyme.map do |x|
    variables[x] = variables.size unless variables.key?(x)
    variables[x]
  end
end

def all_rhymes(n)
  return enum_for(:all_rhymes, n) unless block_given?
  if n == 0
    yield []
    return
  end
  _all_rhymes_help(n, 0) do |rhyme|
    yield [0] + rhyme
  end
end

def _all_rhymes_help(n, max_used, &block)
  return enum_for(:_all_rhymes_help, n, max_used) unless block_given?
  if n == 0
    yield []
    return
  end
  (0..(max_used + 1)).each do |x|
    _all_rhymes_help(n - 1, [max_used, x].max) do |rest|
      yield [x] + rest
    end
  end
end

# Recursive approach to mapping from equation number to id and vice-versa

# Counting equations of some order, based on https://oeis.org/A103293, refactored to access intermediate results.

def num_eqs(n)
  # Sequence https://oeis.org/A376640 of the number of magma equations
  if n.odd?
    (MathHelpers.catalan(n + 1) * MathHelpers.bell(n + 2)) / 2
  else
    return 2 if n == 0
    ((MathHelpers.catalan(n + 1) - MathHelpers.catalan(n / 2)) * MathHelpers.bell(n + 2)) / 2 +
      MathHelpers.catalan(n / 2) * bell_same_shape(n)
  end
end

def bell_same_shape(n)
  # Number of rhymes when lhs and rhs have the same (n//2)-operations shape
  return 2 if n == 0

  sum_stirling = (0..(n + 2)).sum { |k| stirling_sym(n + 2, k) }
  (MathHelpers.bell(n + 2) + sum_stirling - 2 * MathHelpers.bell(1 + n / 2)) / 2
end

def stirling_sym(n, k)
  # Number of symmetric k-partitions of range(n), see https://oeis.org/A103293
  return 1 if n < 2 && k == n
  return 0 if n < 2

  k * stirling_sym(n - 2, k) + stirling_sym(n - 2, k - 1) + stirling_sym(n - 2, k - 2)
end

# Map from shape to id and back

def shape_id(shape)
  # Gives the shape id (zero-based) among shapes of a given order
  _shape_id_help(shape, shape_order(shape))
end

def _shape_id_help(shape, n)
  return 0 if n == 0

  lhs_shape, rhs_shape = shape
  lhs_n = shape_order(lhs_shape)
  rhs_n = n - 1 - lhs_n

  (0...lhs_n).sum { |n1| MathHelpers.catalan(n1) * MathHelpers.catalan(n - n1 - 1) } +
    _shape_id_help(lhs_shape, lhs_n) * MathHelpers.catalan(rhs_n) +
    _shape_id_help(rhs_shape, rhs_n)
end

def shape_from_id(nodes, tree_num)
  if nodes == 0
    raise ArgumentError, "Invalid tree_num for zero nodes" if tree_num != 0
    return nil
  end

  (0...nodes).each do |n1|
    test_num = MathHelpers.catalan(n1) * MathHelpers.catalan(nodes - n1 - 1)
    if tree_num >= test_num
      tree_num -= test_num
      next
    end
    tree_num_1, tree_num_2 = tree_num.divmod(MathHelpers.catalan(nodes - n1 - 1))
    return [shape_from_id(n1, tree_num_1), shape_from_id(nodes - n1 - 1, tree_num_2)]
  end
end

# Map from rhyme to id and back
def _num_rhyme_help(n, max_used)
  # Number of rhymes of n slots whose minimum number is at most max_used + 1
  return 1 if n == 0

  (max_used + 1) * _num_rhyme_help(n - 1, max_used) +
    _num_rhyme_help(n - 1, max_used + 1)
end

def get_rhyme_by_id(n, rhyme_num, max_used = 0)
  # Find a rhyme scheme for n slots by its number (zero-indexed)
  result = [0]
  while n > 0
    base = _num_rhyme_help(n - 1, max_used)
    var1 = [max_used + 1, rhyme_num / base].min
    result << var1
    rhyme_num -= var1 * base
    max_used = [max_used, var1].max
    n -= 1
  end
  result
end

# Map from rhyme tp id and back
# Number of rhymes of n slots whose minimum number is at most max_used + 1
def _num_rhyme_help(n, max_used)
  return 1 if n == 0
  (max_used + 1) * _num_rhyme_help(n - 1, max_used) + _num_rhyme_help(n - 1, max_used + 1)
end

# Gives the rhyme id (zero-based) among rhymes with a given number of variables
def find_rhyme_id(p)
  raise ArgumentError, "Argument of find_rhyme_id should be [0,...] not #{p.inspect}" if p.empty? || p[0] != 0
  _find_rhyme_id_help(p[1..], 0)
end

def _find_rhyme_id_help(p, max_used)
  return 0 if p.empty?
  p[0] * _num_rhyme_help(p.length - 1, max_used) + _find_rhyme_id_help(p[1..], [p[0], max_used].max)
end

# Map from equation to id and back
def _num_eqs_unbalanced(n)
  # Counts magma equations that have strictly fewer operations on the left than on the right
  term = if n.odd?
    MathHelpers.catalan(n + 1)
  else
    MathHelpers.catalan(n + 1) - MathHelpers.catalan(n / 2) ** 2
  end
  (term * MathHelpers.bell(n + 2)) / 2
end

def _num_eqs_balanced(n, l, r)
  # Number of balanced equations before lhs/rhs shapes number l, r
  bell_n2 = MathHelpers.bell(n + 2)
  part1 = bell_n2 * (MathHelpers.catalan(n / 2) * l - l * (l + 1) / 2 + r - l - (r > l ? 1 : 0))
  part2 = bell_same_shape(n) * (l + (r > l ? 1 : 0))
  part1 + part2
end

def _equation_id(input_eq)
  # Equation id from a processed Equation
  lhs_shape = input_eq.lhs_shape
  rhs_shape = input_eq.rhs_shape
  n_lhs = shape_order(lhs_shape)
  n_rhs = shape_order(rhs_shape)
  n = n_lhs + n_rhs

  if n_lhs != n_rhs
    return 1 + (0...n).sum { |i| num_eqs(i) } +
           MathHelpers.bell(n + 2) * shape_id([lhs_shape, rhs_shape]) +
           find_rhyme_id(input_eq.rhyme)
  end

  # For n_lhs == n_rhs the ordering halves the equations.  
  # For different tree shapes get bell(n + 2) rhymes, otherwise bell_same_shape(n).
  m = MathHelpers.catalan(n_lhs) # number of tree shapes on each side
  l = shape_id(lhs_shape)
  r = shape_id(rhs_shape)

  if l != r
    pid = find_rhyme_id(input_eq.rhyme)
  else
    # Slow code here
    pid = 0
    all_rhymes(n + 1).each do |rhyme|
      break if rhyme == input_eq.rhyme
      flipped = rhyme[n_lhs + 1..] + rhyme[0..n_lhs]
      next if (canonicalize_rhyme(flipped) <=> rhyme) == -1
      next if rhyme == flipped && n > 0
      pid += 1
    end
  end

  return 1 + (0...n).sum { |i| num_eqs(i) } +
         _num_eqs_unbalanced(n) + _num_eqs_balanced(n, l, r) +
         pid
end

def _equation_from_id(input_eq)
  n = 0
  eq_num = input_eq - 1
  n = 0
  while eq_num >= (max_eq_num = num_eqs(n))
    eq_num -= max_eq_num
    n += 1
  end
  if eq_num < _num_eqs_unbalanced(n)
    tree_num, rhyme_num = eq_num.divmod(MathHelpers.bell(n + 2))
    lhs_shape, rhs_shape = shape_from_id(n + 1, tree_num)
    rhyme = get_rhyme_by_id(n + 1, rhyme_num)
    return Equation.new(lhs_shape, rhs_shape, rhyme)
  end
  eq_num -= _num_eqs_unbalanced(n)
  m = MathHelpers.catalan(n.div(2))
  part = (2 * m - 1) * MathHelpers.bell(n + 2) + 2 * bell_same_shape(n)
  sqrt_val = Math.sqrt(part**2 - 8 * MathHelpers.bell(n + 2) * eq_num - 1).to_i
  l = (part - sqrt_val - 1).div(2 * MathHelpers.bell(n + 2))
  
  lhs_shape = shape_from_id(n.div(2), l)
  eq_num -= _num_eqs_balanced(n, l, l)
  # error above somewhere
  if eq_num < bell_same_shape(n)
    rhs_shape = lhs_shape
    # Slow code here
    rhyme = nil  # declare outside

    all_rhymes(n + 1).each do |cand_rhyme|
      flipped = cand_rhyme[(n.div(2)) + 1..] + cand_rhyme[0..(n.div(2))]
      canon_flipped = canonicalize_rhyme(flipped)
    
      #puts "DEBUG: Checking rhyme=#{cand_rhyme.inspect}, flipped=#{flipped.inspect}, canon_flipped=#{canon_flipped.inspect}"
    
      if (canon_flipped <=> cand_rhyme) == -1
        #puts "  Skipped: flipped < rhyme"
        next
      end
      if cand_rhyme == flipped && n > 0
        #puts "  Skipped: palindrome and n > 0"
        next
      end
    
      if eq_num == 0
        rhyme = cand_rhyme
        break
      end
      eq_num -= 1
    end
    
    raise "Could not assign a valid rhyme in balanced same-shape case" if rhyme.nil?
  else
    eq_num -= bell_same_shape(n)
    shape_diff, pid = eq_num.divmod(MathHelpers.bell(n + 2))
    rhs_shape = shape_from_id(n.div(2), l + 1 + shape_diff)
    rhyme = get_rhyme_by_id(n + 1, pid)
  end
  #puts "DEBUG: lhs=#{lhs_shape.inspect}, rhs=#{rhs_shape.inspect}, rhyme=#{rhyme.inspect}"
  return Equation.new(lhs_shape, rhs_shape, rhyme)
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
      eq = Equation.from_id(input_eq)
      if dual
        eq = eq.dual
        eq_num = eq.id
        puts "The dual of Equation #{input_eq} is Equation #{eq_num}: #{eq}"
      else
        puts "Equation #{input_eq}: #{eq}"
      end
      #puts "Processing ID: #{input_eq}"  # placeholder for actual processing
    else
      input_eq = Equation.from_str(eq_str)
      if dual
        dual_eq = input_eq.dual
        dual_num = dual_eq.id
        puts "The dual of '#{eq_str}' is Equation #{dual_num}: #{dual_eq}"
      else
        eq_num = input_eq.id
        puts "The equation '#{eq_str}' is Equation #{eq_num}: #{input_eq}"
      end
      # puts "Processing: #{eq_str}"  # placeholder
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
