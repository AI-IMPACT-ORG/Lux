BEGIN {
    buffer = ""
    in_math = 0
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
    next
}

# Line is not a single character
{
    if (in_math) {
        # If this line is very short (<= 3 chars), join it with the math expression
        if (length($0) <= 3) {
            buffer = buffer $0
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
}

END {
    if (in_math) {
        print buffer
    }
}
