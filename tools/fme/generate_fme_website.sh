#!/usr/bin/env bash

# Run as part of CI to integrate Finite Magma Explorer with the website.
mkdir -p home_page
mkdir -p home_page/fme
cp -r tools/fme/dist/* home_page/fme
~/.elan/bin/lake exe extract_implications unknowns > home_page/fme/unknowns.json
COMMIT_HASH=$(git rev-parse --short HEAD)

# Cross-platform compatible `sed` command for in-place editing
if [[ "$OSTYPE" == "darwin"* ]]; then
  # macOS `sed` syntax
  sed -i '' "s/VERSION_UNKNOWN/$COMMIT_HASH/g" home_page/fme/index.html
else
  # Linux `sed` syntax
  sed -i "s/VERSION_UNKNOWN/$COMMIT_HASH/g" home_page/fme/index.html
fi
