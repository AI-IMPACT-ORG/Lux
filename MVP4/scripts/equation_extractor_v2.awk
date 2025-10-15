BEGIN {
    buffer = ""
    in_math = 0
    prev_line = ""
}

# Check if line is a single non-space character
length($0) == 1 && $0 !~ /^[[:space:]]*$/ {
    if (in_math) {
        buffer = buffer $0
    } else {
        # Start new mathematical expression
        buffer = $0
        in_math = 1
    }
    prev_line = $0
    next
}

# Line is not a single character
{
    if (in_math) {
        # Check if this line should be joined with the math expression
        # If it's very short (like punctuation or closing brackets), join it
        if (length($0) <= 3 && $0 ~ /^[[:punct:][:space:]]*$/) {
            buffer = buffer $0
            prev_line = $0
            next
        } else {
            # Output accumulated mathematical expression
            print buffer
            buffer = ""
            in_math = 0
        }
    }
    # Output the current line
    print $0
    prev_line = $0
}

END {
    if (in_math) {
        print buffer
    }
}
