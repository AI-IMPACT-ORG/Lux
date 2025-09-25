# Aggressive equation extractor that joins ALL single characters in sequences
# Only stops when hitting a significantly longer line

BEGIN {
    buffer = ""
    in_sequence = 0
}

# Check if line is a single non-space character
length($0) == 1 && $0 !~ /^[[:space:]]*$/ {
    if (in_sequence) {
        buffer = buffer $0
    } else {
        # Start a new sequence
        buffer = $0
        in_sequence = 1
    }
    next
}

# Line is not a single character
{
    if (in_sequence) {
        # If this line is very short (<= 3 chars), join it with the sequence
        if (length($0) <= 3) {
            buffer = buffer $0
            next
        } else {
            # Output the accumulated sequence
            print buffer
            buffer = ""
            in_sequence = 0
        }
    }
    # Output the current line
    print $0
}

END {
    if (in_sequence) {
        print buffer
    }
}
