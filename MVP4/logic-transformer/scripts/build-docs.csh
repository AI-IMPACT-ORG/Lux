#!/bin/csh
set -e
echo "[docs] building Scribble docs..."
for f in lt-docs/*.scrbl
    scribble --htmls --dest lt-docs $f
end
echo "[docs] index:"
ls -1 lt-docs/*.html



