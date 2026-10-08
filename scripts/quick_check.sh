#!/bin/bash
# Reproduction checks for solution.md.  Prints PASS/FAIL per check; exit status 0 iff all pass.
#
#   scripts/quick_check.sh            quick checks only (about 40 seconds)
#   scripts/quick_check.sh --medium   also the medium checks (about 17 minutes in total, up to 3 cores)
#
# Output of every check goes to out/quick/<name>.txt; the committed logs in logs/ are not touched.
# Needs: python3 with numpy and sympy, and a C compiler (set CC to override; default clang, else cc).
# The long runs (about 1 hour wall-clock on 3 cores and more) are not run here; see README.md.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/out/quick"
mkdir -p "$OUT"
if [ -z "${CC:-}" ]; then if command -v clang >/dev/null 2>&1; then CC=clang; else CC=cc; fi; fi
export CC
PY=${PYTHON:-python3}
MEDIUM=0; [ "${1:-}" = "--medium" ] && MEDIUM=1
npass=0; nfail=0; failed=""

# check NAME DIR COMMAND MUST_MATCH [MUST_NOT_MATCH]   (patterns are extended regexps)
check() {
  local name="$1" dir="$2" cmd="$3" must="$4" mustnot="${5:-}"
  local log="$OUT/$name.txt" t0 t1 rc
  t0=$(date +%s)
  ( cd "$ROOT/$dir" && eval "$cmd" ) > "$log" 2>&1
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ] && grep -Eq -- "$must" "$log" && { [ -z "$mustnot" ] || ! grep -Eq -- "$mustnot" "$log"; }; then
    printf "PASS  %-26s %5ss\n" "$name" $((t1-t0)); npass=$((npass+1))
  else
    printf "FAIL  %-26s %5ss   (exit %s; see %s)\n" "$name" $((t1-t0)) "$rc" "$log"; nfail=$((nfail+1)); failed="$failed $name"
  fi
}

echo "== Existence (Theorems 1 and 2) =="
check formula        code/existence "$PY verify_formula.py"   "checked 573 mismatches 0" "MISMATCH|False"
check sn             code/existence "$PY verify_sn.py"        " OK$" "BAD"
check Sr             code/existence "$PY verify_Sr.py"        "^ALL OK$" "MISMATCH"
check invariant      code/existence "$PY verify_invariant.py" "^ALL OK$" "FAIL"
check closed_form    code/existence "$PY closed_form.py"      "cases=501 closed!=newton: 0  zero values: 0"
check coef           code/existence "$PY verify_coef.py | awk '{print} \$4!=\$6{bad=1} END{print (bad?\"COEF MISMATCH\":\"COEF ALL EQUAL\")}'" "COEF ALL EQUAL"
check C_direct       code/existence "$PY verify_C_direct.py"  "^ALL OK$" "MISMATCH"

echo "== Sharpness (Propositions 3, 4 and Theorem 5) =="
check poster         code/sharpness "$PY verify_poster.py"    "ALL CONSTRUCTIONS VERIFIED" "False"
check known          code/sharpness "$PY verify_known.py"     "^23 d=p-2: True  d=p-1: True" "False"
check p7_families    code/sharpness "$PY verify_p7.py"        "d=4 family.*True$" "False"
check indep_k3_brute code/sharpness "$CC -O3 -o indep_k3 indep_k3.c && ./indep_k3 5 brute && ./indep_k3 7 brute" \
      "BRUTE p=7 \(u,box\) pairs=85750 with completion=903 mismatches\(dfs vs brute\)=0" "mismatches\(dfs vs brute\)=[1-9]"
check p7_found_block code/sharpness "./indep_k3 7 2>/dev/null | $PY check_found_p7.py" \
      "found families checked: 903  not actually blocking: 0"
check normalisation  code/sharpness "./indep_k3 7 2>/dev/null > found7.txt && $PY check_normalisation_p7.py found7.txt" \
      "random transformed families: 200 all normalised boxes found: 200"
check box_test       code/sharpness/boxsearch "$CC -O3 -o test_hasbox test_hasbox.c && ./test_hasbox 7 3000 && ./test_hasbox 11 600" \
      "p=11 tests=600 agree=600 disagree=0" "disagree=[1-9]"
check box_vs_brute7  code/sharpness/boxsearch "$CC -O3 -o boxsearch boxsearch.c && $CC -O3 -DPRINTLIM=1000000 -o boxsearch_all boxsearch.c && $CC -O3 -o brute7 brute7.c && ./brute7 4 5 6 | grep FOUND | sort > '$OUT/b7.txt' && ./boxsearch_all 7 4 5 6 0 1 1 | grep FOUND | sort > '$OUT/bx.txt' && wc -l '$OUT/b7.txt' '$OUT/bx.txt' && [ \$(wc -l < '$OUT/b7.txt') -eq 573 ] && cmp '$OUT/b7.txt' '$OUT/bx.txt' && echo P7_SETS_IDENTICAL" \
      "^P7_SETS_IDENTICAL$"
check thm5_p11_box   code/sharpness/boxsearch "./boxsearch 11 1 2 3" "^DONE p=11 chunk 0/1 nodes=5069550 boxchecks=5069550 found=0$" "FOUND"

if [ $MEDIUM = 1 ]; then
  echo "== Medium checks =="
  check L            code/existence "$PY verify_L.py"         "^ALL OK$" "MISMATCH"
  check coef_direct  code/existence "LOGDIR='$OUT/coef_direct' ./run_coef_direct.sh" "runs \(mode0 random families=66, mode1 top part=0, mode2 reduced=80\), mismatches vs closed form: 0" "MISMATCH"
  check endtoend     code/sharpness "$PY endtoend_11_8.py"    "families tested 4665 without solution 0 max degree of found f 7"
  check thm5_p13_box code/sharpness/boxsearch "LOGDIR='$OUT/boxsearch' ./run_boxsearch.sh p13" "chunk 2/3 nodes=121938124 boxchecks=121938124 found=0" "found=[1-9]"
  check exist        code/existence "$PY verify_exist.py"     "exhaustive p=5 d=4 min #avoiders over all families = 1" "= 0$"
fi

echo "== $npass passed, $nfail failed =="
[ $nfail -eq 0 ] || { echo "failed:$failed"; exit 1; }
