# Used to generate faster proofs to prove that some equations are not full spectrum for equations
# that don't have models of cardinality 3.

SEARCH_DEPTH = 3
EQUATION = :eq481

def op(table, a, b)
  return nil if a == nil || b == nil
  return table[(a*3) + b]
end
def eq481(x, y, z, table)
  op(table, y, op(table, x, op(table, y, op(table, z, z))))
end
def eq667(x, y, z, table)
  op(table, y, op(table, x, op(table, op(table, x, x), y)))
end
def eq883(x, y, z, table)
  op(table, y, op(table, op(table, x, y), op(table, y, y)))
end
def eq1098(x, y, z, table)
  op(table, y, op(table, op(table, x, op(table, z, y)), z))
end
def eq1483(x, y, z, table)
  op(table, op(table, y, x), op(table, x, op(table, y, z)))
end
def eq1485(x, y, z, table)
  op(table, op(table, y, x), op(table, x, op(table, z, y)))
end
def eq1526(x, y, z, table)
  op(table, op(table, y, y), op(table, y, op(table, x, y)))
end

$table = Array.new(9, nil)
def set(eq, pos=0, shortest=1000)
  hits = []
  raise "Error" if pos >= 9
  3.times { |t|
    $table[pos] = t
    success = false
    3.times { |x| 3.times { |y| 3.times { |z|
      rv = eq.call(x, y, z, $table)
      if rv != nil && rv != x
        success = [x,y,z]
      end
    }}}
    if success != false
      hits.push [$table.dup, success]
    else
      indices = $table.length.times.to_a.filter { |i| $table[i] == nil }[0, SEARCH_DEPTH]
      best = []
      indices.each { |i|
        if best.length != 0
          best.push set(eq, i, best.sort_by(&:length)[0].length)
        else
          best.push set(eq, i, shortest)
        end
      }
      hits += best.sort_by(&:length)[0]
    end
    break if hits.length > shortest
  }
  $table[pos] = nil
  return hits
end

ret = set(method(EQUATION))

def print(array, path=[])
  if array.length == 1
    puts "  "*path.length + ". use #{array[0][1].map(&:to_s).join(', ')}; simp [*]"
    #puts "  "*path.length + ". use #{array[0][1].map(&:to_s).join(', ')}; simp only [Fin.isValue, Fin.reduceEq, zero_ne_one, one_ne_zero, not_false_eq_true, *]"
    return
  end

  indices = 9.times.to_a.filter { |idx| array.filter { |a| a[0][idx] == nil }.length == 0 }
  pick = (indices - path)[0]

  puts "  "*path.length + ". rcases (op_eq3 m #{pick / 3} #{pick % 3}) with _ | _ | _"
  3.times { |i|
    picked = array.filter { |e| e[0][pick] == i }
    print(picked, path + [pick])
  }
end
print(ret)
