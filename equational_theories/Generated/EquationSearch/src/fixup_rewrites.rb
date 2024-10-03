require 'tempfile'

if ARGV.length != 1
  $stderr.puts "Usage: <lean file>"
  exit 1
end

def run(theorem)
  file = Tempfile.new('foo')

  file.puts "import Mathlib.Tactic.NthRewrite"
  file.puts "import equational_theories.AllEquations"
  file.puts theorem
  file.close

  retval = `lake env lean #{file.path}`

  file.unlink
  retval
end

def bruteforce(theorem, run)
  all_x = theorem.gsub("]\n", " x]\n")
  if !run(all_x).include?("error:")
    return all_x
  end

  if theorem !~ /intro ([^\n]+)/
    $stderr.puts "Failed to read vars: #{theorem}"
    exit 1
  end
  variables = $1.split(" ")

  run =~ /(\d+):\d+: error/
  error_line = $1.to_i
  line = error_line-2 # Account for the imports above

  split_theorem = theorem.split("\n")
  target_line = theorem.split("\n")[line-1]
  #$stderr.puts theorem
  #$stderr.puts run
  #$stderr.puts " ---> #{target_line}"

  if target_line.include? "apply"
    return nil
  elsif target_line !~ /nth_rewrite \d+ \[(.+)\]/
    $stderr.puts "Not finding an nth_rewrite or apply"
    exit 1
  end

  eq = $1

  1.upto(4).each { |idx|
    variables.each { |var1|
      new_line = "  nth_rewrite #{idx} [#{eq} #{var1}]"
      split_theorem[line-1] = new_line

      #$stderr.puts "New line: #{new_line}"

      retval = run(split_theorem.join("\n"))
      if retval =~ /(\d+):\d+: error/
        next if $1.to_i == error_line
      end

      processed = process_theorem(split_theorem.join("\n"))
      return processed if processed
    }
  }

  return nil
end

def process_theorem(theorem)
  run = run(theorem)

  if run.include?("error:")
    return bruteforce(theorem, run)
  end

  return theorem
end

File.open(ARGV[0]) { |f|
  cur_theorem = nil
  while f.gets
    if $_ =~ /^theorem ([^ ]+)/
      if cur_theorem
        $stderr.puts "Bruteforcing #{$1}"
        processed_theorem = process_theorem(cur_theorem)
        if !processed_theorem
          $stderr.puts "Failed to find a working theorem"
          #puts cur_theorem
        else
          puts processed_theorem
        end

      end

      cur_theorem = ""
    end

    if cur_theorem
      cur_theorem += $_
    end
  end

  if cur_theorem
    processed_theorem = process_theorem(cur_theorem)
    if !processed_theorem
      $stderr.puts "Failed to find a working theorem"
      #puts cur_theorem
    else
      puts processed_theorem
    end
  end
}
