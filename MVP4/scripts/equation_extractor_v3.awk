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
        # Check if this line should be joined with the math expression
        # Join short lines that look like they're part of the math expression
        if (length($0) <= 5 && ($0 ~ /^[[:punct:][:space:]]*$/ || $0 ~ /^[a-zA-Z0-9]*$/)) {
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
