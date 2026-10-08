# Logs

Outputs of the runs reported in `solution.md`, all made on 2026-10-08 on one machine (macOS, Apple silicon,
Python 3.9.6, numpy 2.0.2, sympy 1.14.0, Apple clang 21). Lines `real/user/sys` are timings in seconds.

| file(s) | produced by (directory) | what |
|---|---|---|
| `verify_formula.txt`, `verify_L.txt`, `verify_sn.txt`, `verify_Sr.txt`, `verify_C_direct.txt`, `verify_coef.txt`, `verify_invariant.txt`, `verify_exist.txt`, `closed_form.txt`, `C_table.txt` | the scripts of the same name in `code/existence/` | Theorems 1 and 2 |
| `coef_direct.txt`, `coef_direct_raw.txt` | `code/existence/run_coef_direct.sh` | $C(p,d)$ by dense expansion, 146 runs |
| `verify_poster.txt`, `verify_known.txt`, `verify_p7.txt`, `endtoend_11_8.txt` | the scripts of the same name in `code/sharpness/` | Propositions 3, 4; sanity test at (11,8) |
| `indep_k3_brute.txt` | `indep_k3 5 brute`, `indep_k3 7 brute` | DFS vs pruning-free enumeration |
| `indep_k3_p7.txt`, `indep_k3_p7_check.txt` | `indep_k3 7`, piped into `check_found_p7.py` | the 903 normalised blocking families at (7,4) |
| `indep_k3_p11_s{0,1,2}.txt`, `indep_k3_p11_sample.txt` | `indep_k3 11 s 3` (and a 1/200 sample run) | Theorem 5 at p=11, normalisation N1 |
| `dualk3c_p11_t{0,1}.txt` | `dualk3c` | Theorem 5 at p=11, normalisation N2 |
| `dualk3d_p13_*.txt` | `dualk3d` | Theorem 5 at p=13, normalisation N2 + symmetry |
| `finished_jobs.txt` | `run_sharpness_searches.sh` | job completion record |
| `python_checks_status.txt` | the batch run of all Python checks | exit codes |
| `boxsearch/test_hasbox.txt`, `boxsearch/p7_crosscheck.txt`, `boxsearch/box_p11.txt`, `boxsearch/box_p13_Z123_c*.txt` | `code/sharpness/boxsearch/run_boxsearch.sh quick` / `p13` | Remark 3.5: validation, Theorem 5 at p=11 and p=13 |
| `boxsearch/box_p13_Z2511_noscale_c*.txt` | the reviewer's own run of `boxsearch 13 2 5 11 c 6 1` (two chunks per file); not re-run | Remark 3.5: Theorem 5 at p=13 without scaling |

Every Theorem 5 search line (`DONE ...`) ends in `found=0`.
