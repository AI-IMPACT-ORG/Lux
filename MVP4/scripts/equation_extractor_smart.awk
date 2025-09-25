# Smart equation extractor that recognizes character sequences
# Joins sequences of single characters that are bounded by longer lines

BEGIN {
    buffer = ""
    in_sequence = 0
    sequence_count = 0
}

# Check if line is a single non-space character
length($0) == 1 && $0 !~ /^[[:space:]]*$/ {
    if (in_sequence) {
        buffer = buffer $0
        sequence_count++
    } else {
        # Start a new sequence
        buffer = $0
        in_sequence = 1
        sequence_count = 1
    }
    next
}

# Line is not a single character
{
    if (in_sequence) {
        # If we have a sequence of single characters, output them joined
        if (sequence_count > 0) {
            print buffer
            buffer = ""
            in_sequence = 0
            sequence_count = 0
        }
    }
    # Output the current line
    print $0
}

END {
    if (in_sequence && sequence_count > 0) {
        print buffer
    }
}
