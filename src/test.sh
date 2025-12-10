#!/bin/sh
set -eux

mkdir -p /opt/cache
grep 'riscv64gc-unknown-linux-gnu' ./stage0 | \
sed -n 's/^\(dist\/[0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\}\/[^=]*\)=.*/\1/p' | \
while read distpath; do
    datepart=$(echo "$distpath" | cut -d'/' -f2)
    mkdir -p "/opt/cache/dist/$datepart"
    wget -O "/opt/cache/$distpath" "https://static.rust-lang.org/$distpath"
done
