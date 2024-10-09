#/bin/sh

# Run as part of CI to integrate Finite Magma Explorer with the website.
mkdir -p home_page
mkdir -p home_page/fme
cp -r tools/fme/dist/* home_page/fme
~/.elan/bin/lake exe extract_implications unknowns > home_page/fme/unknowns.json
COMMIT_HASH=$(git rev-parse --short HEAD)
sed -i "s/VERSION_UNKNOWN/$COMMIT_HASH/g" home_page/fme/index.html
