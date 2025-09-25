#!/bin/csh
# EquationExtractor.csh - Extract human-readable text from mangled ChatGPT output
# This script processes files where mathematical expressions have been broken
# into individual characters/symbols on separate lines

if ($#argv != 1) then
    echo "Usage: $0 <input_file>"
    echo "Example: $0 ChatGPT_renormalisation_logic_reader"
    echo "Output will be saved as <input_file>_cleaned.txt in the same directory"
    exit 1
endif

set input_file = $1
set input_dir = `dirname $input_file`
set input_basename = `basename $input_file`
set output_file = "$input_dir/${input_basename}_cleaned.txt"

if (! -f $input_file) then
    echo "Error: Input file '$input_file' does not exist"
    exit 1
endif

echo "Processing $input_file -> $output_file"

# Strategy: Use awk to process line by line
# Join consecutive single-character lines into mathematical expressions
# Keep longer lines (normal text) as-is

# Get the directory where this script is located
set script_dir = `dirname $0`

# Run the smart awk script
awk -f "$script_dir/equation_extractor_smart_v2.awk" "$input_file" > "$output_file"

echo "Processing complete. Output saved to $output_file"
echo "Review the output and adjust the script if needed for better results."
