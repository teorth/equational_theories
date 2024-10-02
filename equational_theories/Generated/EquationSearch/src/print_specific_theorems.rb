# Reads a CSV and prints the theorems for those implications

if ARGV.length < 2
  $stderr.puts "Usage: print_specific_theorems <csv> <lean file> [lean file] ..."
  exit 1
end

needed = File.read(ARGV[0]).split("\n").map { |s| s.split(",").map(&:to_i) }

ARGV[1, ARGV.length-1].each { |arg|
  File.open(arg) { |f|
    print = false
    while f.gets
      if $_ =~ /theorem Equation(\d+)_implies_Equation(\d+)/
        if needed.include? [$1.to_i, $2.to_i]
          needed.delete([$1.to_i, $2.to_i]) # Only print one, even if it's not the shortest
          print = true
        else
          print = false
        end
      end

      puts $_ if print
    end
  }
}

if needed.length > 0
  $stderr.puts "Did not see #{needed.inspect}!"
  exit 1
end
