# Block-based equation extractor
# Recognizes blocks that start/end with longer lines and have single characters in between

BEGIN {
    buffer = ""
    in_block = 0
    block_started = 0
}

# Check if line is a single non-space character
length($0) == 1 && $0 !~ /^[[:space:]]*$/ {
    if (in_block) {
        buffer = buffer $0
    } else {
        # Start a potential block
        buffer = $0
        in_block = 1
        block_started = 0
    }
    next
}

# Line is not a single character
{
    if (in_block) {
        if (block_started) {
            # This is the end of a block - output the accumulated characters
            print buffer
            buffer = ""
            in_block = 0
            block_started = 0
        } else {
            # This is the start of a block - mark it and continue
            block_started = 1
        }
    }
    # Output the current line
    print $0
}

END {
    if (in_block) {
        print buffer
    }
}
