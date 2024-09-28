if ARGV.length != 1
  $stderr.puts "Usage: print_successful_theorems <bruteforce directory>"
  exit 1
end

dir = ARGV[0]

Dir["#{dir}/Output/errors_*"].each { |s|
  s =~ /errors_(\d+)/
  equation_num = $1.to_i

  code_lines = File.read("#{dir}/bf_#{equation_num}.lean").split("\n")
  error_file = File.read(s)

  error_line_numbers = {}
  error_file.each_line { |l|
    next if l !~ /(\d+):\d+: error/
    error_line_numbers[$1.to_i] = true
  }

  in_theorem = false
  theorem_line_start = nil

  def check_theorem(start_line, end_line, code_lines, error_line_numbers)
    # Boolean search would be faster
    start_line.upto(end_line) { |num|
      if error_line_numbers[num]
        return
      end
    }
   
    print code_lines[start_line - 1, (end_line - start_line) + 1].join("\n") + "\n"
  end

  code_lines.each_with_index { |l, i|
    line_num = i + 1

    if !in_theorem
      if l =~ /^theorem/
        in_theorem = true
        theorem_line_start = line_num
      end
      next
    end

    # Start of a new theorem/def/etc.
    if l =~ /^[^\s]/
      check_theorem(theorem_line_start, line_num - 1, code_lines, error_line_numbers)
      in_theorem = false
    end

    if l =~ /^theorem/
      in_theorem = true
      theorem_line_start = line_num
    end
  }

  if theorem_line_start && in_theorem
    check_theorem(theorem_line_start, code_lines.length + 1, code_lines, error_line_numbers)
  end
}
