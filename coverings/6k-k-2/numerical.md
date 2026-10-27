# Fourteen numerical consequences

These fourteen rows also appear once in the [combined pair-consequence
table](../qk-k-2/bounds.md), alongside the earlier lifts and 78 direct additions.

Two pair seeds and twelve positive-step lifts of the unrestricted lower bound.
These are lower bounds only. Every intermediate ceiling is shown.

Comparisons retain the 26/27 October 2026 LJCR snapshot and refresh, and
the cvkt claims recorded 17 October and read 27 October. Missing entries
do not establish novelty. The categories are nine LJCR comparisons, two
additional cvkt comparisons and three rows without an external comparison.

| (v,k,t) | Lower | Category | LJCR interval | cvkt interval | Seed and ceilings |
|---|---:|---|---|---|---|
| (36,6,2) | 43 | refreshed LJCR | 42–47 | 42–47 | (36,6,2) ≥ 43 |
| (72,12,2) | 43 | refreshed LJCR | 42–47 | 42–46 | (72,12,2) ≥ 43 |
| (37,7,3) | 228 | refreshed LJCR | 222–286 | 222–281 | (36,6,2) ≥ 43; ⌈1591/7⌉=228 |
| (73,13,3) | 242 | refreshed LJCR | 236–325 | 236–322 | (72,12,2) ≥ 43; ⌈3139/13⌉=242 |
| (38,8,4) | 1083 | refreshed LJCR | 1055–1606 | 1055–1536 | (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083 |
| (74,14,4) | 1280 | refreshed LJCR | 1248–2360 | 1248–2336 | (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280 |
| (39,9,5) | 4693 | refreshed LJCR | 4572–9487 | 4572–8520 | (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693 |
| (75,15,5) | 6400 | refreshed LJCR | 6240–17358 | 6240–17341 | (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400 |
| (40,10,6) | 18772 | refreshed LJCR | 18288–41392 | 18288–39735 | (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693; ⌈187720/10⌉=18772 |
| (76,16,6) | 30400 | retained cvkt | missing | 29640–109375 | (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400; ⌈486400/16⌉=30400 |
| (41,11,7) | 69969 | retained cvkt | missing | 68165–176139 | (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693; ⌈187720/10⌉=18772; ⌈769652/11⌉=69969 |
| (77,17,7) | 137695 | missing | missing | missing | (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400; ⌈486400/16⌉=30400; ⌈2340800/17⌉=137695 |
| (42,12,8) | 244892 | missing | missing | missing | (36,6,2) ≥ 43; ⌈1591/7⌉=228; ⌈8664/8⌉=1083; ⌈42237/9⌉=4693; ⌈187720/10⌉=18772; ⌈769652/11⌉=69969; ⌈2938698/12⌉=244892 |
| (78,18,8) | 596679 | missing | missing | missing | (72,12,2) ≥ 43; ⌈3139/13⌉=242; ⌈17908/14⌉=1280; ⌈96000/15⌉=6400; ⌈486400/16⌉=30400; ⌈2340800/17⌉=137695; ⌈10740210/18⌉=596679 |

All fourteen parameter triples are disjoint from the earlier 78 direct
bounds and the retained 59 order-four lifts. The [proof](proof.md) derives both pair seeds and the lifting recurrence.
Its Lean appendix identifies the ordinary and indexed theorem for every row.
