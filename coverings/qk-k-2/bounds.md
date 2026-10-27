# Lower bounds derived from the pair-covering results

This table combines **151 distinct parameter triples**: the 59 earlier
order-four lifts, 78 direct additions and 14 order-six consequences.
It contains seven pair seeds and 144 higher-strength bounds. It does not
repeat the separate table of seven exact pair values in the [README](README.md).
All entries are lower bounds; the comparison upper bounds are catalogue
metadata, not constructions proved by this table.

[Proposition 6](proof.md#6-all-recorded-higher-strength-consequences) proves the
recurrence. Starting from the displayed pair seed b₀, its final column
retains every successive ceiling
bⱼ₊₁=⌈(v₀+j+1)bⱼ/(k₀+j+1)⌉. For a pair seed the list is empty.
Each target links to its Lean declaration. Six earlier rows use the general
lifting theorem and their linked `ceilings_k` evaluation rather than a
separately named numerical covering theorem.

The dated comparison categories are:

- **LJCR 26 Oct:** 53 improvements over the snapshot retrieved on
  26 October 2026 at 15:58:28 UTC.
- **LJCR 27 Oct:** 59 improvements from the retained 26/27 October 2026
  snapshot and refresh: 50 direct additions and nine order-six rows.
- **cvkt 17 Oct:** seven improvements over claims recorded on
  17 October 2026 and inspected on 27 October: five direct and two order-six.
  Their LJCR comparisons were unavailable.
- **missing:** 32 rows without the corresponding retained external comparison:
  six earlier lifts, 23 direct additions and three order-six rows.

A dash means that comparison was not retained for this row; it is not a
claim about the current catalogue. In particular, cvkt was not compared for
the 59 earlier lifts. [Sources](sources.md#comparison-dates-and-the-combined-table)
gives provenance and distinguishes these observations from historical priority.
No fresh catalogue search was made for this consolidation.

| (v,k,t) | Proved lower | Category | LJCR interval | cvkt interval | Pair seed ≥ | Successive ceilings |
|---|---:|---|---|---|---|---|
| [(36,6,2)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L17) | 43 | LJCR 27 Oct | 42–47 | 42–47 | (36,6,2) ≥ 43 | — |
| [(42,7,2)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L18) | 43 | LJCR 27 Oct | 42–46 | 42–46 | (42,7,2) ≥ 43 | — |
| [(72,12,2)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L31) | 43 | LJCR 27 Oct | 42–47 | 42–46 | (72,12,2) ≥ 43 | — |
| [(78,13,2)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L31) | 43 | LJCR 27 Oct | 42–47 | 42–46 | (78,13,2) ≥ 43 | — |
| [(84,14,2)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L44) | 43 | LJCR 27 Oct | 42–46 | 42–46 | (84,14,2) ≥ 43 | — |
| [(90,15,2)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L57) | 43 | LJCR 27 Oct | 42–46 | 42–46 | (90,15,2) ≥ 43 | — |
| [(96,16,2)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L70) | 43 | LJCR 27 Oct | 42–47 | 42–46 | (96,16,2) ≥ 43 | — |
| [(37,7,3)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L52) | 228 | LJCR 27 Oct | 222–286 | 222–281 | (36,6,2) ≥ 43 | 228 |
| [(37,10,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L104) | 78 | LJCR 26 Oct | 74–85 | — | (36,9,2) ≥ 21 | 78 |
| [(41,11,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L146) | 79 | LJCR 26 Oct | 75–89 | — | (40,10,2) ≥ 21 | 79 |
| [(43,8,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L90) | 232 | LJCR 27 Oct | 226–297 | 226–297 | (42,7,2) ≥ 43 | 232 |
| [(45,12,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L188) | 79 | LJCR 26 Oct | 75–88 | — | (44,11,2) ≥ 21 | 79 |
| [(53,14,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L223) | 80 | LJCR 26 Oct | 76–87 | — | (52,13,2) ≥ 21 | 80 |
| [(56,12,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L110) | 145 | LJCR 27 Oct | 140–181 | 140–175 | (55,11,2) ≥ 31 | 145 |
| [(57,9,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L130) | 361 | LJCR 27 Oct | 355–398 | 355–398 | (56,8,2) ≥ 57 | 361 |
| [(57,15,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L258) | 80 | LJCR 26 Oct | 76–84 | — | (56,14,2) ≥ 21 | 80 |
| [(61,16,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L293) | 81 | LJCR 26 Oct | 77–84 | — | (60,15,2) ≥ 21 | 81 |
| [(66,14,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L150) | 147 | LJCR 27 Oct | 142–171 | 142–170 | (65,13,2) ≥ 31 | 147 |
| [(69,18,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L328) | 81 | LJCR 26 Oct | 77–84 | — | (68,17,2) ≥ 21 | 81 |
| [(71,15,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L170) | 147 | LJCR 27 Oct | 142–170 | 142–168 | (70,14,2) ≥ 31 | 147 |
| [(73,13,3)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L73) | 242 | LJCR 27 Oct | 236–325 | 236–322 | (72,12,2) ≥ 43 | 242 |
| [(73,19,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L363) | 81 | LJCR 26 Oct | 77–85 | — | (72,18,2) ≥ 21 | 81 |
| [(77,20,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L398) | 81 | LJCR 26 Oct | 77–85 | — | (76,19,2) ≥ 21 | 81 |
| [(79,14,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L190) | 243 | LJCR 27 Oct | 237–341 | 237–330 | (78,13,2) ≥ 43 | 243 |
| [(81,17,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L210) | 148 | LJCR 27 Oct | 144–168 | 144–167 | (80,16,2) ≥ 31 | 148 |
| [(85,15,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L230) | 244 | LJCR 27 Oct | 238–325 | 238–325 | (84,14,2) ≥ 43 | 244 |
| [(85,22,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L433) | 82 | LJCR 26 Oct | 78–85 | — | (84,21,2) ≥ 21 | 82 |
| [(86,18,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L250) | 149 | LJCR 27 Oct | 144–163 | 144–163 | (85,17,2) ≥ 31 | 149 |
| [(89,23,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L454) | 82 | LJCR 26 Oct | 79–86 | — | (88,22,2) ≥ 21 | 82 |
| [(91,11,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L270) | 753 | LJCR 27 Oct | 745–825 | 745–811 | (90,10,2) ≥ 91 | 753 |
| [(91,16,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L290) | 245 | LJCR 27 Oct | 239–333 | 239–333 | (90,15,2) ≥ 43 | 245 |
| [(93,24,3)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L468) | 82 | LJCR 26 Oct | 79–87 | — | (92,23,2) ≥ 21 | 82 |
| [(96,20,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L310) | 149 | LJCR 27 Oct | 144–163 | 144–162 | (95,19,2) ≥ 31 | 149 |
| [(97,17,3)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L330) | 246 | LJCR 27 Oct | 240–338 | 240–338 | (96,16,2) ≥ 43 | 246 |
| [(38,8,4)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L94) | 1083 | LJCR 27 Oct | 1055–1606 | 1055–1536 | (36,6,2) ≥ 43 | 228, 1083 |
| [(38,11,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L111) | 270 | LJCR 26 Oct | 256–408 | — | (36,9,2) ≥ 21 | 78, 270 |
| [(42,12,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L153) | 277 | LJCR 26 Oct | 263–435 | — | (40,10,2) ≥ 21 | 79, 277 |
| [(44,9,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L350) | 1135 | LJCR 27 Oct | 1105–1769 | 1105–1764 | (42,7,2) ≥ 43 | 232, 1135 |
| [(46,13,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L195) | 280 | LJCR 26 Oct | 266–465 | — | (44,11,2) ≥ 21 | 79, 280 |
| [(54,15,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L230) | 288 | LJCR 26 Oct | 274–469 | — | (52,13,2) ≥ 21 | 80, 288 |
| [(57,13,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L370) | 636 | LJCR 27 Oct | 615–1015 | 615–1015 | (55,11,2) ≥ 31 | 145, 636 |
| [(58,10,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L390) | 2094 | LJCR 27 Oct | 2059–3807 | 2059–3703 | (56,8,2) ≥ 57 | 361, 2094 |
| [(58,16,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L265) | 290 | LJCR 26 Oct | 276–504 | — | (56,14,2) ≥ 21 | 80, 290 |
| [(62,17,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L300) | 296 | LJCR 26 Oct | 281–511 | — | (60,15,2) ≥ 21 | 81, 296 |
| [(67,15,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L410) | 657 | LJCR 27 Oct | 635–999 | 635–988 | (65,13,2) ≥ 31 | 147, 657 |
| [(70,19,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L335) | 299 | LJCR 26 Oct | 284–530 | — | (68,17,2) ≥ 21 | 81, 299 |
| [(72,16,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L430) | 662 | LJCR 27 Oct | 639–1161 | 639–1112 | (70,14,2) ≥ 31 | 147, 662 |
| [(74,14,4)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L115) | 1280 | LJCR 27 Oct | 1248–2360 | 1248–2336 | (72,12,2) ≥ 43 | 242, 1280 |
| [(74,20,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L370) | 300 | LJCR 26 Oct | 285–508 | — | (72,18,2) ≥ 21 | 81, 300 |
| [(78,21,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L405) | 301 | LJCR 26 Oct | 286–510 | — | (76,19,2) ≥ 21 | 81, 301 |
| [(80,15,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L450) | 1296 | LJCR 27 Oct | 1264–2463 | 1264–2260 | (78,13,2) ≥ 43 | 243, 1296 |
| [(82,18,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L470) | 675 | LJCR 27 Oct | 656–1151 | 656–1150 | (80,16,2) ≥ 31 | 148, 675 |
| [(86,16,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L490) | 1312 | LJCR 27 Oct | 1280–2667 | 1280–2569 | (84,14,2) ≥ 43 | 244, 1312 |
| [(86,23,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L440) | 307 | LJCR 26 Oct | 292–556 | — | (84,21,2) ≥ 21 | 82, 307 |
| [(87,19,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L510) | 683 | LJCR 27 Oct | 660–1285 | 660–1264 | (85,17,2) ≥ 31 | 149, 683 |
| [(90,24,4)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L461) | 308 | LJCR 26 Oct | 297–424 | — | (88,22,2) ≥ 21 | 82, 308 |
| [(92,12,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L530) | 5773 | LJCR 27 Oct | 5712–9881 | 5712–9824 | (90,10,2) ≥ 91 | 753, 5773 |
| [(92,17,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L550) | 1326 | LJCR 27 Oct | 1294–2866 | 1294–2723 | (90,15,2) ≥ 43 | 245, 1326 |
| [(97,21,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L570) | 689 | LJCR 27 Oct | 666–1366 | 666–1365 | (95,19,2) ≥ 31 | 149, 689 |
| [(98,18,4)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L590) | 1340 | LJCR 27 Oct | 1307–2726 | 1307–2685 | (96,16,2) ≥ 43 | 246, 1340 |
| [(39,9,5)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L136) | 4693 | LJCR 27 Oct | 4572–9487 | 4572–8520 | (36,6,2) ≥ 43 | 228, 1083, 4693 |
| [(39,12,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L118) | 878 | LJCR 26 Oct | 832–1804 | — | (36,9,2) ≥ 21 | 78, 270, 878 |
| [(43,13,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L160) | 917 | LJCR 26 Oct | 870–1835 | — | (40,10,2) ≥ 21 | 79, 277, 917 |
| [(45,10,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L610) | 5108 | LJCR 27 Oct | 4973–10442 | 4973–10163 | (42,7,2) ≥ 43 | 232, 1135, 5108 |
| [(47,14,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L202) | 940 | LJCR 26 Oct | 894–2340 | — | (44,11,2) ≥ 21 | 79, 280, 940 |
| [(55,16,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L237) | 990 | LJCR 26 Oct | 945–1977 | — | (52,13,2) ≥ 21 | 80, 288, 990 |
| [(58,14,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L630) | 2635 | LJCR 27 Oct | 2548–5962 | 2548–5860 | (55,11,2) ≥ 31 | 145, 636, 2635 |
| [(59,11,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L650) | 11232 | LJCR 27 Oct | 11044–28287 | 11044–28281 | (56,8,2) ≥ 57 | 361, 2094, 11232 |
| [(59,17,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L272) | 1007 | LJCR 26 Oct | 963–2195 | — | (56,14,2) ≥ 21 | 80, 290, 1007 |
| [(63,18,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L307) | 1036 | LJCR 26 Oct | 984–2284 | — | (60,15,2) ≥ 21 | 81, 296, 1036 |
| [(68,16,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L670) | 2793 | LJCR 27 Oct | 2699–5002 | 2699–4987 | (65,13,2) ≥ 31 | 147, 657, 2793 |
| [(71,20,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L342) | 1062 | LJCR 26 Oct | 1009–2542 | — | (68,17,2) ≥ 21 | 81, 299, 1062 |
| [(73,17,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L690) | 2843 | LJCR 27 Oct | 2745–6138 | 2745–6121 | (70,14,2) ≥ 31 | 147, 662, 2843 |
| [(75,15,5)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L157) | 6400 | LJCR 27 Oct | 6240–17358 | 6240–17341 | (72,12,2) ≥ 43 | 242, 1280, 6400 |
| [(75,21,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L377) | 1072 | LJCR 26 Oct | 1026–2588 | — | (72,18,2) ≥ 21 | 81, 300, 1072 |
| [(79,22,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L412) | 1081 | LJCR 26 Oct | 1037–2780 | — | (76,19,2) ≥ 21 | 81, 301, 1081 |
| [(81,16,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L710) | 6561 | LJCR 27 Oct | 6399–17985 | 6399–17821 | (78,13,2) ≥ 43 | 243, 1296, 6561 |
| [(83,19,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L730) | 2949 | LJCR 27 Oct | 2866–7950 | 2866–7679 | (80,16,2) ≥ 31 | 148, 675, 2949 |
| [(87,17,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L750) | 6715 | LJCR 27 Oct | 6551–19235 | 6551–19113 | (84,14,2) ≥ 43 | 244, 1312, 6715 |
| [(87,24,5)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L447) | 1113 | LJCR 26 Oct | 1059–2497 | — | (84,21,2) ≥ 21 | 82, 307, 1113 |
| [(88,20,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L770) | 3006 | LJCR 27 Oct | 2904–8522 | 2904–8331 | (85,17,2) ≥ 31 | 149, 683, 3006 |
| [(93,13,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L790) | 41300 | cvkt 17 Oct | — | 40863–120686 | (90,10,2) ≥ 91 | 753, 5773, 41300 |
| [(93,18,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L810) | 6851 | LJCR 27 Oct | 6686–20238 | 6686–20206 | (90,15,2) ≥ 43 | 245, 1326, 6851 |
| [(98,22,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L830) | 3070 | LJCR 27 Oct | 2973–9232 | 2973–9162 | (95,19,2) ≥ 31 | 149, 689, 3070 |
| [(99,19,5)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L850) | 6983 | LJCR 27 Oct | 6811–21313 | 6811–20645 | (96,16,2) ≥ 43 | 246, 1340, 6983 |
| [(40,10,6)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L178) | 18772 | LJCR 27 Oct | 18288–41392 | 18288–39735 | (36,6,2) ≥ 43 | 228, 1083, 4693, 18772 |
| [(40,13,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L125) | 2702 | LJCR 26 Oct | 2560–7652 | — | (36,9,2) ≥ 21 | 78, 270, 878, 2702 |
| [(44,14,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L167) | 2882 | LJCR 26 Oct | 2735–8447 | — | (40,10,2) ≥ 21 | 79, 277, 917, 2882 |
| [(46,11,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L870) | 21361 | LJCR 27 Oct | 20797–53443 | 20797–53315 | (42,7,2) ≥ 43 | 232, 1135, 5108, 21361 |
| [(48,15,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L209) | 3008 | LJCR 26 Oct | 2861–9262 | — | (44,11,2) ≥ 21 | 79, 280, 940, 3008 |
| [(56,17,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L244) | 3262 | LJCR 26 Oct | 3113–10635 | — | (52,13,2) ≥ 21 | 80, 288, 990, 3262 |
| [(59,15,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L890) | 10365 | LJCR 27 Oct | 10023–35455 | 10023–34699 | (55,11,2) ≥ 31 | 145, 636, 2635, 10365 |
| [(60,12,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L910) | 56160 | cvkt 17 Oct | — | 55220–164755 | (56,8,2) ≥ 57 | 361, 2094, 11232, 56160 |
| [(60,18,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L279) | 3357 | LJCR 26 Oct | 3210–10567 | — | (56,14,2) ≥ 21 | 80, 290, 1007, 3357 |
| [(64,19,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L314) | 3490 | LJCR 26 Oct | 3315–10691 | — | (60,15,2) ≥ 21 | 81, 296, 1036, 3490 |
| [(69,17,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L930) | 11337 | LJCR 27 Oct | 10955–39130 | 10955–39123 | (65,13,2) ≥ 31 | 147, 657, 2793, 11337 |
| [(72,21,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L349) | 3642 | LJCR 26 Oct | 3460–11530 | — | (68,17,2) ≥ 21 | 81, 299, 1062, 3642 |
| [(74,18,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L950) | 11688 | LJCR 27 Oct | 11285–39225 | 11285–38236 | (70,14,2) ≥ 31 | 147, 662, 2843, 11688 |
| [(76,16,6)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L199) | 30400 | cvkt 17 Oct | — | 29640–109375 | (72,12,2) ≥ 43 | 242, 1280, 6400, 30400 |
| [(76,22,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L384) | 3704 | LJCR 26 Oct | 3545–12734 | — | (72,18,2) ≥ 21 | 81, 300, 1072, 3704 |
| [(80,23,6)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L419) | 3760 | LJCR 26 Oct | 3607–13906 | — | (76,19,2) ≥ 21 | 81, 301, 1081, 3760 |
| [(82,17,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L970) | 31648 | cvkt 17 Oct | — | 30866–118703 | (78,13,2) ≥ 43 | 243, 1296, 6561, 31648 |
| [(84,20,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L990) | 12386 | LJCR 27 Oct | 12038–45366 | 12038–45314 | (80,16,2) ≥ 31 | 148, 675, 2949, 12386 |
| [(88,18,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1010) | 32829 | cvkt 17 Oct | — | 32028–121832 | (84,14,2) ≥ 43 | 244, 1312, 6715, 32829 |
| [(89,21,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1030) | 12740 | LJCR 27 Oct | 12308–47018 | 12308–47017 | (85,17,2) ≥ 31 | 149, 683, 3006, 12740 |
| [(94,14,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1050) | 277300 | missing | — | — | (90,10,2) ≥ 91 | 753, 5773, 41300, 277300 |
| [(94,19,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1070) | 33895 | missing | — | — | (90,15,2) ≥ 43 | 245, 1326, 6851, 33895 |
| [(99,23,6)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1090) | 13215 | LJCR 27 Oct | 12771–53544 | 12797–53059 | (95,19,2) ≥ 31 | 149, 689, 3070, 13215 |
| [(41,11,7)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L220) | 69969 | cvkt 17 Oct | — | 68165–176139 | (36,6,2) ≥ 43 | 228, 1083, 4693, 18772, 69969 |
| [(41,14,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L132) | 7913 | LJCR 26 Oct | 7498–24841 | — | (36,9,2) ≥ 21 | 78, 270, 878, 2702, 7913 |
| [(45,15,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L174) | 8646 | LJCR 26 Oct | 8205–29718 | — | (40,10,2) ≥ 21 | 79, 277, 917, 2882, 8646 |
| [(47,12,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1110) | 83664 | missing | — | — | (42,7,2) ≥ 43 | 232, 1135, 5108, 21361, 83664 |
| [(49,16,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L216) | 9212 | LJCR 26 Oct | 8762–34725 | — | (44,11,2) ≥ 21 | 79, 280, 940, 3008, 9212 |
| [(57,18,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L251) | 10330 | LJCR 26 Oct | 9858–44002 | — | (52,13,2) ≥ 21 | 80, 288, 990, 3262, 10330 |
| [(60,16,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1130) | 38869 | cvkt 17 Oct | — | 37587–161837 | (55,11,2) ≥ 31 | 145, 636, 2635, 10365, 38869 |
| [(61,13,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1150) | 263520 | missing | — | — | (56,8,2) ≥ 57 | 361, 2094, 11232, 56160, 263520 |
| [(61,19,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L286) | 10778 | LJCR 26 Oct | 10306–45286 | — | (56,14,2) ≥ 21 | 80, 290, 1007, 3357, 10778 |
| [(65,20,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L321) | 11343 | LJCR 26 Oct | 10774–48702 | — | (60,15,2) ≥ 21 | 81, 296, 1036, 3490, 11343 |
| [(70,18,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1170) | 44089 | missing | — | — | (65,13,2) ≥ 31 | 147, 657, 2793, 11337, 44089 |
| [(73,22,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L356) | 12085 | LJCR 26 Oct | 11481–59301 | — | (68,17,2) ≥ 21 | 81, 299, 1062, 3642, 12085 |
| [(75,19,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1190) | 46137 | missing | — | — | (70,14,2) ≥ 31 | 147, 662, 2843, 11688, 46137 |
| [(77,17,7)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L241) | 137695 | missing | — | — | (72,12,2) ≥ 43 | 242, 1280, 6400, 30400, 137695 |
| [(77,23,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L391) | 12401 | LJCR 26 Oct | 11869–64273 | — | (72,18,2) ≥ 21 | 81, 300, 1072, 3704, 12401 |
| [(81,24,7)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L426) | 12690 | LJCR 26 Oct | 12059–66600 | — | (76,19,2) ≥ 21 | 81, 301, 1081, 3760, 12690 |
| [(83,18,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1210) | 145933 | missing | — | — | (78,13,2) ≥ 43 | 243, 1296, 6561, 31648, 145933 |
| [(85,21,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1230) | 50134 | missing | — | — | (80,16,2) ≥ 31 | 148, 675, 2949, 12386, 50134 |
| [(89,19,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1250) | 153778 | missing | — | — | (84,14,2) ≥ 43 | 244, 1312, 6715, 32829, 153778 |
| [(90,22,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1270) | 52119 | missing | — | — | (85,17,2) ≥ 31 | 149, 683, 3006, 12740, 52119 |
| [(95,15,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1290) | 1756234 | missing | — | — | (90,10,2) ≥ 91 | 753, 5773, 41300, 277300, 1756234 |
| [(95,20,7)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1310) | 161002 | missing | — | — | (90,15,2) ≥ 43 | 245, 1326, 6851, 33895, 161002 |
| [(42,12,8)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L262) | 244892 | missing | — | — | (36,6,2) ≥ 43 | 228, 1083, 4693, 18772, 69969, 244892 |
| [(42,15,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L139) | 22157 | LJCR 26 Oct | 20995–80910 | — | (36,9,2) ≥ 21 | 78, 270, 878, 2702, 7913, 22157 |
| [(46,16,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L181) | 24858 | LJCR 26 Oct | 23590–96419 | — | (40,10,2) ≥ 21 | 79, 277, 917, 2882, 8646, 24858 |
| [(48,13,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1330) | 308914 | missing | — | — | (42,7,2) ≥ 43 | 232, 1135, 5108, 21361, 83664, 308914 |
| [(50,17,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L26) | 27095 | missing | — | — | (44,11,2) ≥ 21 | 79, 280, 940, 3008, 9212, 27095 |
| [(58,19,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L35) | 31534 | missing | — | — | (52,13,2) ≥ 21 | 80, 288, 990, 3262, 10330, 31534 |
| [(61,17,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1350) | 139472 | missing | — | — | (55,11,2) ≥ 31 | 145, 636, 2635, 10365, 38869, 139472 |
| [(62,14,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1370) | 1167018 | missing | — | — | (56,8,2) ≥ 57 | 361, 2094, 11232, 56160, 263520, 1167018 |
| [(62,20,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L44) | 33412 | missing | — | — | (56,14,2) ≥ 21 | 80, 290, 1007, 3357, 10778, 33412 |
| [(66,21,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L53) | 35650 | missing | — | — | (60,15,2) ≥ 21 | 81, 296, 1036, 3490, 11343, 35650 |
| [(71,19,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1390) | 164754 | missing | — | — | (65,13,2) ≥ 31 | 147, 657, 2793, 11337, 44089, 164754 |
| [(74,23,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L62) | 38883 | missing | — | — | (68,17,2) ≥ 21 | 81, 299, 1062, 3642, 12085, 38883 |
| [(76,20,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1410) | 175321 | missing | — | — | (70,14,2) ≥ 31 | 147, 662, 2843, 11688, 46137, 175321 |
| [(78,18,8)](../../lean/CoveringDesigns/C6k_K_2/Numerical.lean#L283) | 596679 | missing | — | — | (72,12,2) ≥ 43 | 242, 1280, 6400, 30400, 137695, 596679 |
| [(78,24,8)](../../lean/CoveringDesigns/Qk_K_2/Lifts.lean#L71) | 40304 | missing | — | — | (72,18,2) ≥ 21 | 81, 300, 1072, 3704, 12401, 40304 |
| [(84,19,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1430) | 645178 | missing | — | — | (78,13,2) ≥ 43 | 243, 1296, 6561, 31648, 145933, 645178 |
| [(86,22,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1450) | 195979 | missing | — | — | (80,16,2) ≥ 31 | 148, 675, 2949, 12386, 50134, 195979 |
| [(90,20,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1470) | 692001 | missing | — | — | (84,14,2) ≥ 43 | 244, 1312, 6715, 32829, 153778, 692001 |
| [(91,23,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1490) | 206210 | missing | — | — | (85,17,2) ≥ 31 | 149, 683, 3006, 12740, 52119, 206210 |
| [(96,16,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1510) | 10537404 | missing | — | — | (90,10,2) ≥ 91 | 753, 5773, 41300, 277300, 1756234, 10537404 |
| [(96,21,8)](../../lean/CoveringDesigns/PairConsequences/Numerical.lean#L1530) | 736010 | missing | — | — | (90,15,2) ≥ 43 | 245, 1326, 6851, 33895, 161002, 736010 |
