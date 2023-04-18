#!/bin/bash

# Iterate over all .rs files in the current directory
for file in test-files/*.rs; do
    # Extract the file name without extension
    name="${file%.*}"

    echo "$name"

    RUSTFLAGS='-A warnings' cargo run "$file" > temp

    diff temp "${name}.expected"

    # Compare the output with the expected content
    if [[ $? -eq 0 ]]; then
        echo "Test passed for $file"
    else
        echo "Test failed for $file"
        exit 1
    fi
done
