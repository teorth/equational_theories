if ARGV.length != 2
  $stderr.puts "Usage: try_less <lean file> <try line file>"
  exit 1
end

try_lines = Set.new File.read(ARGV[1]).split("\n").map(&:to_i)

File.open(ARGV[0]) { |f|
  line_num = 0
  parens = 0
  print = true
  while f.gets
    line_num += 1

    if try_lines.include?(line_num)
      print = false
    elsif print
      puts $_
      next
    end

    if parens < 0
      $stderr.puts "Impossible"
      exit 1
    elsif parens == 0
      print = true
    end
  end
}
