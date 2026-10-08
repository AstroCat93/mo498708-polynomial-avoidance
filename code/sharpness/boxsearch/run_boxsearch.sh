#!/bin/bash
# Box-formulation search (solution.md, Remark 3.5): validation at p=7 and the full (11,8) / (13,10) checks.
# Usage:  ./run_boxsearch.sh quick   -- box test vs brute force, p=7 vs brute7, and all of (11,8) six times
#                                       (about 2.5 min; one run of (11,8) alone takes about 10 s)
#         ./run_boxsearch.sh p13     -- all of (13,10): Z={1,2,3}, with scaling, 3 chunks in parallel
#                                       (about 3.7 min per chunk on Apple silicon; 11 CPU-min)
#         ./run_boxsearch.sh p13full -- all of (13,10): Z={2,5,11}, without scaling, 6 chunks, 3 in parallel
#                                       (about 13 min per chunk; 80 CPU-min)
# Logs are written to $LOGDIR (default ../../../logs/boxsearch, i.e. the committed logs are overwritten).
# Exception: p13full writes box_p13_Z2511_noscale_s{0..5}.txt (one chunk per file); the committed
# box_p13_Z2511_noscale_c{0,1,2}.txt are the reviewer's own run (two chunks per file) and are not overwritten.
# Every DONE line at p=11 and p=13 must end in found=0.  Set CC to override the compiler.
set -u
cd "$(dirname "$0")"
CC=${CC:-clang}
L="${LOGDIR:-../../../logs/boxsearch}"
mkdir -p "$L"
$CC -O3 -o boxsearch boxsearch.c && $CC -O3 -o brute7 brute7.c && $CC -O3 -o test_hasbox test_hasbox.c || exit 1
case "${1:-quick}" in
quick)
  { ./test_hasbox 7 3000; ./test_hasbox 11 600; ./test_hasbox 13 300; } | tee "$L/test_hasbox.txt"
  # p=7: the SETS of blocking W-assignments found by boxsearch and by brute7 must coincide
  $CC -O3 -DPRINTLIM=1000000 -o boxsearch_all boxsearch.c || exit 1
  TB=$(mktemp); TX=$(mktemp)
  : > "$L/p7_crosscheck.txt"
  for Z in "4 5 6" "1 2 4" "1 3 6" "2 3 5"; do
    ./brute7 $Z | grep FOUND | sort > "$TB"
    ./boxsearch_all 7 $Z 0 1 1 | grep FOUND | sort > "$TX"
    printf "Z=%s brute=%5s box=%5s symmetric_difference=%s\n" "$Z" "$(wc -l < "$TB" | tr -d ' ')" "$(wc -l < "$TX" | tr -d ' ')" \
      "$(comm -3 "$TB" "$TX" | wc -l | tr -d ' ')" | tee -a "$L/p7_crosscheck.txt"
  done
  rm -f "$TB" "$TX"
  : > "$L/box_p11.txt"
  for Z in "1 2 3" "8 9 10" "2 5 7" "3 4 9" "1 5 10"; do
    ./boxsearch 11 $Z | tee -a "$L/box_p11.txt"
  done
  ./boxsearch 11 1 2 3 0 1 1 | tee -a "$L/box_p11.txt"      # same, without the scaling reduction
  ;;
p13)
  for c in 0 1 2; do ( /usr/bin/time -p ./boxsearch 13 1 2 3 $c 3 > "$L/box_p13_Z123_c$c.txt" 2>&1 ) & done
  wait
  grep -h DONE "$L"/box_p13_Z123_c*.txt
  ;;
p13full)
  export L
  printf "0\n1\n2\n3\n4\n5\n" | xargs -P 3 -I{} bash -c '/usr/bin/time -p ./boxsearch 13 2 5 11 {} 6 1 > "$L/box_p13_Z2511_noscale_s{}.txt" 2>&1'
  grep -h DONE "$L"/box_p13_Z2511_noscale_s*.txt
  ;;
*) echo "usage: $0 [quick|p13|p13full]"; exit 1;;
esac
