#!/bin/bash
# Re-runs the exhaustive (11,8) and (13,10) searches of solution.md, Section 3.4, 3 jobs in parallel.
# Logs go to ../../logs/ (overwriting the committed logs; use `git diff logs/` to compare).
# Each individual job takes < 40 min on one core (Apple silicon, clang -O3); total about 2.8 CPU-hours,
# i.e. roughly 1 hour of wall-clock time on 3 cores.  Set CC / CFLAGS to override the compiler settings.
set -u
cd "$(dirname "$0")"
CC=${CC:-clang}
CFLAGS=${CFLAGS:-"-O3 -march=native"}
$CC $CFLAGS -o indep_k3 indep_k3.c && $CC $CFLAGS -o dualk3c dualk3c.c && $CC $CFLAGS -o dualk3d dualk3d.c || exit 1
L=../../logs
JOBS=$(mktemp)
: > $L/finished_jobs.txt
cat > "$JOBS" <<JOBLIST
./indep_k3 11 0 3 > $L/indep_k3_p11_s0.txt 2>&1
./indep_k3 11 1 3 > $L/indep_k3_p11_s1.txt 2>&1
./indep_k3 11 2 3 > $L/indep_k3_p11_s2.txt 2>&1
./dualk3c 11 0 8 9 10 0 1 > $L/dualk3c_p11_t0.txt 2>&1
./dualk3c 11 1 8 9 10 0 1 > $L/dualk3c_p11_t1.txt 2>&1
./dualk3d 13 0 1 3 9 0 6 > $L/dualk3d_p13_t0_s0.txt 2>&1
./dualk3d 13 0 1 3 9 1 6 > $L/dualk3d_p13_t0_s1.txt 2>&1
./dualk3d 13 0 1 3 9 2 6 > $L/dualk3d_p13_t0_s2.txt 2>&1
./dualk3d 13 0 1 3 9 3 6 > $L/dualk3d_p13_t0_s3.txt 2>&1
./dualk3d 13 0 1 3 9 4 6 > $L/dualk3d_p13_t0_s4.txt 2>&1
./dualk3d 13 0 1 3 9 5 6 > $L/dualk3d_p13_t0_s5.txt 2>&1
./dualk3d 13 1 1 3 9 0 1 > $L/dualk3d_p13_t1.txt 2>&1
./dualk3d 13 2 1 3 9 0 1 > $L/dualk3d_p13_t2.txt 2>&1
JOBLIST
tr '\n' '\0' < "$JOBS" | xargs -0 -P 3 -I{} bash -c '/usr/bin/time -p {} ; echo "{}" >> ../../logs/finished_jobs.txt'
rm -f "$JOBS"
echo ALL_SEARCHES_DONE >> $L/finished_jobs.txt
# Summary: every line below must end in found=0
grep -h "^DONE" $L/indep_k3_p11_s*.txt $L/dualk3c_p11_t*.txt $L/dualk3d_p13_*.txt
