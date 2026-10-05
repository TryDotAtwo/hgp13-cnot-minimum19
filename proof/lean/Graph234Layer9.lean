import Graph234Layer10
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s9_0 : State := ⟨[1,4,67,145], 44601830679428167303742095461371901181624598, 3, 3, 1, 0⟩
theorem s9_0_edges : next config 9 s9_0 = [] := by decide
theorem s9_0_safe : Safe 4 9 s9_0 := by
  apply safe_succ 3 9 s9_0 [] (by decide) s9_0_edges
  simp
def s9_1 : State := ⟨[1,4,67,145], 44601830679428167304950947494010235518124310, 3, 3, 1, 0⟩
theorem s9_1_edges : next config 9 s9_1 = [] := by decide
theorem s9_1_safe : Safe 4 9 s9_1 := by
  apply safe_succ 3 9 s9_1 [] (by decide) s9_1_edges
  simp
def s9_2 : State := ⟨[1,4,104,145], 133806172603038705179297810890432946676764958, 3, 3, 1, 0⟩
theorem s9_2_edges : next config 9 s9_2 = [] := by decide
theorem s9_2_safe : Safe 4 9 s9_2 := by
  apply safe_succ 3 9 s9_2 [] (by decide) s9_2_edges
  simp
def s9_3 : State := ⟨[1,4,104,145], 156105556672101644566979675664651581109899550, 3, 3, 1, 0⟩
theorem s9_3_edges : next config 9 s9_3 = [] := by decide
theorem s9_3_safe : Safe 4 9 s9_3 := by
  apply safe_succ 3 9 s9_3 [] (by decide) s9_3_edges
  simp
def s9_4 : State := ⟨[1,12,67,145], 44601830679428167226370843006035634000433430, 3, 3, 1, 0⟩
theorem s9_4_edges : next config 9 s9_4 = [] := by decide
theorem s9_4_safe : Safe 4 9 s9_4 := by
  apply safe_succ 3 9 s9_4 [] (by decide) s9_4_edges
  simp
def s9_5 : State := ⟨[1,12,67,145], 44601830679428167227579695038673968336933142, 3, 3, 1, 0⟩
theorem s9_5_edges : next config 9 s9_5 = [] := by decide
theorem s9_5_safe : Safe 4 9 s9_5 := by
  apply safe_succ 3 9 s9_5 [] (by decide) s9_5_edges
  simp
def s9_6 : State := ⟨[1,12,125,145], 44601873214744393976609017223235702553252118, 3, 3, 1, 0⟩
theorem s9_6_edges : next config 9 s9_6 = [] := by decide
theorem s9_6_safe : Safe 4 9 s9_6 := by
  apply safe_succ 3 9 s9_6 [] (by decide) s9_6_edges
  simp
def s9_7 : State := ⟨[1,21,67,145], 44601830679428167226370843006035634000433430, 3, 3, 1, 0⟩
theorem s9_7_edges : next config 9 s9_7 = [] := by decide
theorem s9_7_safe : Safe 4 9 s9_7 := by
  apply safe_succ 3 9 s9_7 [] (by decide) s9_7_edges
  simp
def s9_8 : State := ⟨[1,21,67,145], 44601830679428167227579695038673968336933142, 3, 3, 1, 0⟩
theorem s9_8_edges : next config 9 s9_8 = [] := by decide
theorem s9_8_safe : Safe 4 9 s9_8 := by
  apply safe_succ 3 9 s9_8 [] (by decide) s9_8_edges
  simp
def s9_9 : State := ⟨[1,21,67,145], 44601830679428167303742095461371901181624598, 3, 3, 1, 0⟩
theorem s9_9_edges : next config 9 s9_9 = [] := by decide
theorem s9_9_safe : Safe 4 9 s9_9 := by
  apply safe_succ 3 9 s9_9 [] (by decide) s9_9_edges
  simp
def s9_10 : State := ⟨[1,21,67,145], 44601830679428167304950947494010235518124310, 3, 3, 1, 0⟩
theorem s9_10_edges : next config 9 s9_10 = [] := by decide
theorem s9_10_safe : Safe 4 9 s9_10 := by
  apply safe_succ 3 9 s9_10 [] (by decide) s9_10_edges
  simp
def s9_11 : State := ⟨[1,21,125,145], 44601873214744393976609017223235702553252118, 3, 3, 1, 0⟩
theorem s9_11_edges : next config 9 s9_11 = [] := by decide
theorem s9_11_safe : Safe 4 9 s9_11 := by
  apply safe_succ 3 9 s9_11 [] (by decide) s9_11_edges
  simp
def s9_12 : State := ⟨[1,86,67,145], 44601830679428167298906355289425237063700758, 3, 3, 1, 0⟩
theorem s9_12_edges : next config 9 s9_12 = [] := by decide
theorem s9_12_safe : Safe 4 9 s9_12 := by
  apply safe_succ 3 9 s9_12 [] (by decide) s9_12_edges
  simp
def s9_13 : State := ⟨[1,86,67,145], 44601830679428167298906392182913384482803990, 3, 3, 1, 0⟩
theorem s9_13_edges : next config 9 s9_13 = [] := by decide
theorem s9_13_safe : Safe 4 9 s9_13 := by
  apply safe_succ 3 9 s9_13 [] (by decide) s9_13_edges
  simp
def s9_14 : State := ⟨[1,86,67,145], 44601830679428167303742095461371901181624598, 3, 3, 1, 0⟩
theorem s9_14_edges : next config 9 s9_14 = [] := by decide
theorem s9_14_safe : Safe 4 9 s9_14 := by
  apply safe_succ 3 9 s9_14 [] (by decide) s9_14_edges
  simp
def s9_15 : State := ⟨[1,86,67,145], 44601830679428167304950947494010235518124310, 3, 3, 1, 0⟩
theorem s9_15_edges : next config 9 s9_15 = [] := by decide
theorem s9_15_safe : Safe 4 9 s9_15 := by
  apply safe_succ 3 9 s9_15 [] (by decide) s9_15_edges
  simp
def s9_16 : State := ⟨[1,125,104,145], 44601873214744393976609017223235702553252118, 3, 3, 1, 0⟩
theorem s9_16_edges : next config 9 s9_16 = [] := by decide
theorem s9_16_safe : Safe 4 9 s9_16 := by
  apply safe_succ 3 9 s9_16 [] (by decide) s9_16_edges
  simp
def s9_17 : State := ⟨[3,4,108,145], 44601830679773047412959511028192929602797854, 3, 3, 1, 0⟩
theorem s9_17_edges : next config 9 s9_17 = [] := by decide
theorem s9_17_safe : Safe 4 9 s9_17 := by
  apply safe_succ 3 9 s9_17 [] (by decide) s9_17_edges
  simp
def s9_18 : State := ⟨[3,4,121,145], 44601833337904520429132830109023894142910750, 3, 3, 1, 0⟩
theorem s9_18_edges : next config 9 s9_18 = [] := by decide
theorem s9_18_safe : Safe 4 9 s9_18 := by
  apply safe_succ 3 9 s9_18 [] (by decide) s9_18_edges
  simp
def s9_19 : State := ⟨[3,4,125,145], 44601873214744393976609017223235702553248030, 3, 3, 1, 0⟩
theorem s9_19_edges : next config 9 s9_19 = [s10_45, s10_2] := by decide
theorem s9_19_safe : Safe 4 9 s9_19 := by
  apply safe_succ 3 9 s9_19 [s10_45, s10_2] (by decide) s9_19_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_45_safe
  · subst z; exact s10_2_safe
def s9_20 : State := ⟨[3,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546910, 3, 3, 1, 0⟩
theorem s9_20_edges : next config 9 s9_20 = [] := by decide
theorem s9_20_safe : Safe 4 9 s9_20 := by
  apply safe_succ 3 9 s9_20 [] (by decide) s9_20_edges
  simp
def s9_21 : State := ⟨[3,12,104,145], 44601830679448528859301084301409773582225694, 3, 3, 1, 0⟩
theorem s9_21_edges : next config 9 s9_21 = [] := by decide
theorem s9_21_safe : Safe 4 9 s9_21 := by
  apply safe_succ 3 9 s9_21 [] (by decide) s9_21_edges
  simp
def s9_22 : State := ⟨[3,12,113,145], 44601830689812840166767087888046818989379870, 3, 3, 1, 0⟩
theorem s9_22_edges : next config 9 s9_22 = [] := by decide
theorem s9_22_safe : Safe 4 9 s9_22 := by
  apply safe_succ 3 9 s9_22 [] (by decide) s9_22_edges
  simp
def s9_23 : State := ⟨[3,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179230, 3, 3, 1, 0⟩
theorem s9_23_edges : next config 9 s9_23 = [] := by decide
theorem s9_23_safe : Safe 4 9 s9_23 := by
  apply safe_succ 3 9 s9_23 [] (by decide) s9_23_edges
  simp
def s9_24 : State := ⟨[3,21,104,145], 44601830679448528859301084301409773582225694, 3, 3, 1, 0⟩
theorem s9_24_edges : next config 9 s9_24 = [] := by decide
theorem s9_24_safe : Safe 4 9 s9_24 := by
  apply safe_succ 3 9 s9_24 [] (by decide) s9_24_edges
  simp
def s9_25 : State := ⟨[3,21,104,145], 44601830679449796509901312530811270285426974, 3, 3, 1, 0⟩
theorem s9_25_edges : next config 9 s9_25 = [] := by decide
theorem s9_25_safe : Safe 4 9 s9_25 := by
  apply safe_succ 3 9 s9_25 [] (by decide) s9_25_edges
  simp
def s9_26 : State := ⟨[3,21,104,145], 44601830679773047412959511028192929602797854, 3, 3, 1, 0⟩
theorem s9_26_edges : next config 9 s9_26 = [] := by decide
theorem s9_26_safe : Safe 4 9 s9_26 := by
  apply safe_succ 3 9 s9_26 [] (by decide) s9_26_edges
  simp
def s9_27 : State := ⟨[3,21,113,145], 44601830689812840166767087888046818989379870, 3, 3, 1, 0⟩
theorem s9_27_edges : next config 9 s9_27 = [] := by decide
theorem s9_27_safe : Safe 4 9 s9_27 := by
  apply safe_succ 3 9 s9_27 [] (by decide) s9_27_edges
  simp
def s9_28 : State := ⟨[3,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179230, 3, 3, 1, 0⟩
theorem s9_28_edges : next config 9 s9_28 = [] := by decide
theorem s9_28_safe : Safe 4 9 s9_28 := by
  apply safe_succ 3 9 s9_28 [] (by decide) s9_28_edges
  simp
def s9_29 : State := ⟨[3,54,104,145], 44601830679448528859301084319424172095897886, 3, 1, 1, 0⟩
theorem s9_29_edges : next config 9 s9_29 = [] := by decide
theorem s9_29_safe : Safe 4 9 s9_29 := by
  apply safe_succ 3 9 s9_29 [] (by decide) s9_29_edges
  simp
def s9_30 : State := ⟨[3,54,104,145], 44601830679448528859301084328431371346444574, 3, 1, 1, 0⟩
theorem s9_30_edges : next config 9 s9_30 = [] := by decide
theorem s9_30_safe : Safe 4 9 s9_30 := by
  apply safe_succ 3 9 s9_30 [] (by decide) s9_30_edges
  simp
def s9_31 : State := ⟨[3,62,67,145], 44601830679428167221535070570301239404462366, 3, 1, 1, 0⟩
theorem s9_31_edges : next config 9 s9_31 = [] := by decide
theorem s9_31_safe : Safe 4 9 s9_31 := by
  apply safe_succ 3 9 s9_31 [] (by decide) s9_31_edges
  simp
def s9_32 : State := ⟨[3,62,67,145], 44601830679428167221535070579308438655009054, 3, 1, 1, 0⟩
theorem s9_32_edges : next config 9 s9_32 = [] := by decide
theorem s9_32_safe : Safe 4 9 s9_32 := by
  apply safe_succ 3 9 s9_32 [] (by decide) s9_32_edges
  simp
def s9_33 : State := ⟨[3,62,96,145], 44601830679428246449697437260686243271999774, 3, 1, 1, 0⟩
theorem s9_33_edges : next config 9 s9_33 = [] := by decide
theorem s9_33_safe : Safe 4 9 s9_33 := by
  apply safe_succ 3 9 s9_33 [] (by decide) s9_33_edges
  simp
def s9_34 : State := ⟨[3,62,96,145], 44601830679428246449697437269693442522546462, 3, 1, 1, 0⟩
theorem s9_34_edges : next config 9 s9_34 = [] := by decide
theorem s9_34_safe : Safe 4 9 s9_34 := by
  apply safe_succ 3 9 s9_34 [] (by decide) s9_34_edges
  simp
def s9_35 : State := ⟨[3,86,67,145], 44601830679428167298906318395937089644597534, 3, 3, 1, 0⟩
theorem s9_35_edges : next config 9 s9_35 = [] := by decide
theorem s9_35_safe : Safe 4 9 s9_35 := by
  apply safe_succ 3 9 s9_35 [] (by decide) s9_35_edges
  simp
def s9_36 : State := ⟨[3,100,104,145], 44601830679449796509901312530811270285426974, 3, 3, 1, 0⟩
theorem s9_36_edges : next config 9 s9_36 = [] := by decide
theorem s9_36_safe : Safe 4 9 s9_36 := by
  apply safe_succ 3 9 s9_36 [] (by decide) s9_36_edges
  simp
def s9_37 : State := ⟨[3,108,104,145], 44601830679773047412959511028192929602797854, 3, 3, 1, 0⟩
theorem s9_37_edges : next config 9 s9_37 = [] := by decide
theorem s9_37_safe : Safe 4 9 s9_37 := by
  apply safe_succ 3 9 s9_37 [] (by decide) s9_37_edges
  simp
def s9_38 : State := ⟨[17,4,108,145], 44601830679773047412959511028192929602797854, 3, 3, 1, 0⟩
theorem s9_38_edges : next config 9 s9_38 = [] := by decide
theorem s9_38_safe : Safe 4 9 s9_38 := by
  apply safe_succ 3 9 s9_38 [] (by decide) s9_38_edges
  simp
def s9_39 : State := ⟨[17,4,108,145], 44601830679773047412959547921681077021901078, 3, 3, 1, 0⟩
theorem s9_39_edges : next config 9 s9_39 = [] := by decide
theorem s9_39_safe : Safe 4 9 s9_39 := by
  apply safe_succ 3 9 s9_39 [] (by decide) s9_39_edges
  simp
def s9_40 : State := ⟨[17,4,121,145], 44601833337904520429132830109023894142910750, 3, 3, 1, 0⟩
theorem s9_40_edges : next config 9 s9_40 = [] := by decide
theorem s9_40_safe : Safe 4 9 s9_40 := by
  apply safe_succ 3 9 s9_40 [] (by decide) s9_40_edges
  simp
def s9_41 : State := ⟨[17,4,121,145], 44601833337904520429132867002512041562013974, 3, 3, 1, 0⟩
theorem s9_41_edges : next config 9 s9_41 = [] := by decide
theorem s9_41_safe : Safe 4 9 s9_41 := by
  apply safe_succ 3 9 s9_41 [] (by decide) s9_41_edges
  simp
def s9_42 : State := ⟨[17,4,125,145], 44601873214744393976609017223235702553248030, 3, 3, 1, 0⟩
theorem s9_42_edges : next config 9 s9_42 = [s10_20] := by decide
theorem s9_42_safe : Safe 4 9 s9_42 := by
  apply safe_succ 3 9 s9_42 [s10_20] (by decide) s9_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_20_safe
def s9_43 : State := ⟨[17,4,125,145], 44601873214744393976609017223235711143182614, 3, 3, 1, 0⟩
theorem s9_43_edges : next config 9 s9_43 = [] := by decide
theorem s9_43_safe : Safe 4 9 s9_43 := by
  apply safe_succ 3 9 s9_43 [] (by decide) s9_43_edges
  simp
def s9_44 : State := ⟨[17,4,125,145], 44601873214744393976609054116723849972351254, 3, 3, 1, 0⟩
theorem s9_44_edges : next config 9 s9_44 = [] := by decide
theorem s9_44_safe : Safe 4 9 s9_44 := by
  apply safe_succ 3 9 s9_44 [] (by decide) s9_44_edges
  simp
def s9_45 : State := ⟨[17,4,125,145], 44601873214744552432934045751910889641148694, 3, 3, 1, 0⟩
theorem s9_45_edges : next config 9 s9_45 = [] := by decide
theorem s9_45_safe : Safe 4 9 s9_45 := by
  apply safe_succ 3 9 s9_45 [] (by decide) s9_45_edges
  simp
def s9_46 : State := ⟨[17,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546910, 3, 3, 1, 0⟩
theorem s9_46_edges : next config 9 s9_46 = [] := by decide
theorem s9_46_safe : Safe 4 9 s9_46 := by
  apply safe_succ 3 9 s9_46 [] (by decide) s9_46_edges
  simp
def s9_47 : State := ⟨[17,4,249,145], 904625697166532776746648320380418881934351203729176207679457272982822650134, 3, 3, 1, 0⟩
theorem s9_47_edges : next config 9 s9_47 = [] := by decide
theorem s9_47_safe : Safe 4 9 s9_47 := by
  apply safe_succ 3 9 s9_47 [] (by decide) s9_47_edges
  simp
def s9_48 : State := ⟨[17,12,104,145], 44601830679448528859301084301409773582225694, 3, 3, 1, 0⟩
theorem s9_48_edges : next config 9 s9_48 = [] := by decide
theorem s9_48_safe : Safe 4 9 s9_48 := by
  apply safe_succ 3 9 s9_48 [] (by decide) s9_48_edges
  simp
def s9_49 : State := ⟨[17,12,104,145], 44601830679448528859301084301409782172160278, 3, 3, 1, 0⟩
theorem s9_49_edges : next config 9 s9_49 = [] := by decide
theorem s9_49_safe : Safe 4 9 s9_49 := by
  apply safe_succ 3 9 s9_49 [] (by decide) s9_49_edges
  simp
def s9_50 : State := ⟨[17,12,104,145], 44601830679448528859301121194897921001328918, 3, 3, 1, 0⟩
theorem s9_50_edges : next config 9 s9_50 = [] := by decide
theorem s9_50_safe : Safe 4 9 s9_50 := by
  apply safe_succ 3 9 s9_50 [] (by decide) s9_50_edges
  simp
def s9_51 : State := ⟨[17,12,104,145], 44601830679448687315626112830084960670126358, 3, 3, 1, 0⟩
theorem s9_51_edges : next config 9 s9_51 = [] := by decide
theorem s9_51_safe : Safe 4 9 s9_51 := by
  apply safe_succ 3 9 s9_51 [] (by decide) s9_51_edges
  simp
def s9_52 : State := ⟨[17,12,113,145], 44601830689812840166767087888046818989379870, 3, 3, 1, 0⟩
theorem s9_52_edges : next config 9 s9_52 = [] := by decide
theorem s9_52_safe : Safe 4 9 s9_52 := by
  apply safe_succ 3 9 s9_52 [] (by decide) s9_52_edges
  simp
def s9_53 : State := ⟨[17,12,113,145], 44601830689812840166767124781534966408483094, 3, 3, 1, 0⟩
theorem s9_53_edges : next config 9 s9_53 = [] := by decide
theorem s9_53_safe : Safe 4 9 s9_53 := by
  apply safe_succ 3 9 s9_53 [] (by decide) s9_53_edges
  simp
def s9_54 : State := ⟨[17,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179230, 3, 3, 1, 0⟩
theorem s9_54_edges : next config 9 s9_54 = [] := by decide
theorem s9_54_safe : Safe 4 9 s9_54 := by
  apply safe_succ 3 9 s9_54 [] (by decide) s9_54_edges
  simp
def s9_55 : State := ⟨[17,12,241,145], 3533694129556768659166595001530438862334396040200935385767686376335282454, 3, 3, 1, 0⟩
theorem s9_55_edges : next config 9 s9_55 = [] := by decide
theorem s9_55_safe : Safe 4 9 s9_55 := by
  apply safe_succ 3 9 s9_55 [] (by decide) s9_55_edges
  simp
def s9_56 : State := ⟨[17,21,104,145], 44601830679448528859301084301409773582225694, 3, 3, 1, 0⟩
theorem s9_56_edges : next config 9 s9_56 = [] := by decide
theorem s9_56_safe : Safe 4 9 s9_56 := by
  apply safe_succ 3 9 s9_56 [] (by decide) s9_56_edges
  simp
def s9_57 : State := ⟨[17,21,104,145], 44601830679448528859301084301409782172160278, 3, 3, 1, 0⟩
theorem s9_57_edges : next config 9 s9_57 = [] := by decide
theorem s9_57_safe : Safe 4 9 s9_57 := by
  apply safe_succ 3 9 s9_57 [] (by decide) s9_57_edges
  simp
def s9_58 : State := ⟨[17,21,104,145], 44601830679448528859301121194897921001328918, 3, 3, 1, 0⟩
theorem s9_58_edges : next config 9 s9_58 = [] := by decide
theorem s9_58_safe : Safe 4 9 s9_58 := by
  apply safe_succ 3 9 s9_58 [] (by decide) s9_58_edges
  simp
def s9_59 : State := ⟨[17,21,104,145], 44601830679448687315626112830084960670126358, 3, 3, 1, 0⟩
theorem s9_59_edges : next config 9 s9_59 = [] := by decide
theorem s9_59_safe : Safe 4 9 s9_59 := by
  apply safe_succ 3 9 s9_59 [] (by decide) s9_59_edges
  simp
def s9_60 : State := ⟨[17,21,104,145], 44601830679449796509901312530811270285426974, 3, 3, 1, 0⟩
theorem s9_60_edges : next config 9 s9_60 = [] := by decide
theorem s9_60_safe : Safe 4 9 s9_60 := by
  apply safe_succ 3 9 s9_60 [] (by decide) s9_60_edges
  simp
def s9_61 : State := ⟨[17,21,104,145], 44601830679449796509901349424299417704530198, 3, 3, 1, 0⟩
theorem s9_61_edges : next config 9 s9_61 = [] := by decide
theorem s9_61_safe : Safe 4 9 s9_61 := by
  apply safe_succ 3 9 s9_61 [] (by decide) s9_61_edges
  simp
def s9_62 : State := ⟨[17,21,104,145], 44601830679773047412959511028192929602797854, 3, 3, 1, 0⟩
theorem s9_62_edges : next config 9 s9_62 = [] := by decide
theorem s9_62_safe : Safe 4 9 s9_62 := by
  apply safe_succ 3 9 s9_62 [] (by decide) s9_62_edges
  simp
def s9_63 : State := ⟨[17,21,104,145], 44601830679773047412959547921681077021901078, 3, 3, 1, 0⟩
theorem s9_63_edges : next config 9 s9_63 = [] := by decide
theorem s9_63_safe : Safe 4 9 s9_63 := by
  apply safe_succ 3 9 s9_63 [] (by decide) s9_63_edges
  simp
def s9_64 : State := ⟨[17,21,113,145], 44601830689812840166767087888046818989379870, 3, 3, 1, 0⟩
theorem s9_64_edges : next config 9 s9_64 = [] := by decide
theorem s9_64_safe : Safe 4 9 s9_64 := by
  apply safe_succ 3 9 s9_64 [] (by decide) s9_64_edges
  simp
def s9_65 : State := ⟨[17,21,113,145], 44601830689812840166767124781534966408483094, 3, 3, 1, 0⟩
theorem s9_65_edges : next config 9 s9_65 = [] := by decide
theorem s9_65_safe : Safe 4 9 s9_65 := by
  apply safe_succ 3 9 s9_65 [] (by decide) s9_65_edges
  simp
def s9_66 : State := ⟨[17,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179230, 3, 3, 1, 0⟩
theorem s9_66_edges : next config 9 s9_66 = [] := by decide
theorem s9_66_safe : Safe 4 9 s9_66 := by
  apply safe_succ 3 9 s9_66 [] (by decide) s9_66_edges
  simp
def s9_67 : State := ⟨[17,21,241,145], 3533694129556768659166595001530438862334396040200935385767686376335282454, 3, 3, 1, 0⟩
theorem s9_67_edges : next config 9 s9_67 = [] := by decide
theorem s9_67_safe : Safe 4 9 s9_67 := by
  apply safe_succ 3 9 s9_67 [] (by decide) s9_67_edges
  simp
def s9_68 : State := ⟨[17,86,67,145], 44601830679428167298906318395937089644597534, 3, 3, 1, 0⟩
theorem s9_68_edges : next config 9 s9_68 = [] := by decide
theorem s9_68_safe : Safe 4 9 s9_68 := by
  apply safe_succ 3 9 s9_68 [] (by decide) s9_68_edges
  simp
def s9_69 : State := ⟨[17,100,104,145], 44601830679449796509901312530811270285426974, 3, 3, 1, 0⟩
theorem s9_69_edges : next config 9 s9_69 = [] := by decide
theorem s9_69_safe : Safe 4 9 s9_69 := by
  apply safe_succ 3 9 s9_69 [] (by decide) s9_69_edges
  simp
def s9_70 : State := ⟨[17,100,104,145], 44601830679449796509901349424299417704530198, 3, 3, 1, 0⟩
theorem s9_70_edges : next config 9 s9_70 = [] := by decide
theorem s9_70_safe : Safe 4 9 s9_70 := by
  apply safe_succ 3 9 s9_70 [] (by decide) s9_70_edges
  simp
def s9_71 : State := ⟨[17,108,104,145], 44601830679773047412959511028192929602797854, 3, 3, 1, 0⟩
theorem s9_71_edges : next config 9 s9_71 = [] := by decide
theorem s9_71_safe : Safe 4 9 s9_71 := by
  apply safe_succ 3 9 s9_71 [] (by decide) s9_71_edges
  simp
def s9_72 : State := ⟨[17,108,104,145], 44601830679773047412959547921681077021901078, 3, 3, 1, 0⟩
theorem s9_72_edges : next config 9 s9_72 = [] := by decide
theorem s9_72_safe : Safe 4 9 s9_72 := by
  apply safe_succ 3 9 s9_72 [] (by decide) s9_72_edges
  simp
def s9_73 : State := ⟨[21,4,104,145], 44601830679448528859301084301409773582225694, 3, 3, 1, 0⟩
theorem s9_73_edges : next config 9 s9_73 = [s10_42, s10_0] := by decide
theorem s9_73_safe : Safe 4 9 s9_73 := by
  apply safe_succ 3 9 s9_73 [s10_42, s10_0] (by decide) s9_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_42_safe
  · subst z; exact s10_0_safe
def s9_74 : State := ⟨[21,4,104,145], 44601830679448528859301084301409782172160278, 3, 3, 1, 0⟩
theorem s9_74_edges : next config 9 s9_74 = [] := by decide
theorem s9_74_safe : Safe 4 9 s9_74 := by
  apply safe_succ 3 9 s9_74 [] (by decide) s9_74_edges
  simp
def s9_75 : State := ⟨[21,4,104,145], 44601830679448528859301121194897921001328918, 3, 3, 1, 0⟩
theorem s9_75_edges : next config 9 s9_75 = [s10_43, s10_1] := by decide
theorem s9_75_safe : Safe 4 9 s9_75 := by
  apply safe_succ 3 9 s9_75 [s10_43, s10_1] (by decide) s9_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_43_safe
  · subst z; exact s10_1_safe
def s9_76 : State := ⟨[21,4,104,145], 44601830679448687315626112830084960670126358, 3, 3, 1, 0⟩
theorem s9_76_edges : next config 9 s9_76 = [] := by decide
theorem s9_76_safe : Safe 4 9 s9_76 := by
  apply safe_succ 3 9 s9_76 [] (by decide) s9_76_edges
  simp
def s9_77 : State := ⟨[21,4,104,145], 44601830679449796509901312530811270285426974, 3, 3, 1, 0⟩
theorem s9_77_edges : next config 9 s9_77 = [] := by decide
theorem s9_77_safe : Safe 4 9 s9_77 := by
  apply safe_succ 3 9 s9_77 [] (by decide) s9_77_edges
  simp
def s9_78 : State := ⟨[21,4,104,145], 44601830679449796509901349424299417704530198, 3, 3, 1, 0⟩
theorem s9_78_edges : next config 9 s9_78 = [] := by decide
theorem s9_78_safe : Safe 4 9 s9_78 := by
  apply safe_succ 3 9 s9_78 [] (by decide) s9_78_edges
  simp
def s9_79 : State := ⟨[21,4,104,145], 44601830679773047412959511028192929602797854, 3, 3, 1, 0⟩
theorem s9_79_edges : next config 9 s9_79 = [] := by decide
theorem s9_79_safe : Safe 4 9 s9_79 := by
  apply safe_succ 3 9 s9_79 [] (by decide) s9_79_edges
  simp
def s9_80 : State := ⟨[21,4,104,145], 44601830679773047412959547921681077021901078, 3, 3, 1, 0⟩
theorem s9_80_edges : next config 9 s9_80 = [] := by decide
theorem s9_80_safe : Safe 4 9 s9_80 := by
  apply safe_succ 3 9 s9_80 [] (by decide) s9_80_edges
  simp
def s9_81 : State := ⟨[21,4,113,145], 44601830689812840166767087888046818989379870, 3, 3, 1, 0⟩
theorem s9_81_edges : next config 9 s9_81 = [] := by decide
theorem s9_81_safe : Safe 4 9 s9_81 := by
  apply safe_succ 3 9 s9_81 [] (by decide) s9_81_edges
  simp
def s9_82 : State := ⟨[21,4,113,145], 44601830689812840166767124781534966408483094, 3, 3, 1, 0⟩
theorem s9_82_edges : next config 9 s9_82 = [] := by decide
theorem s9_82_safe : Safe 4 9 s9_82 := by
  apply safe_succ 3 9 s9_82 [] (by decide) s9_82_edges
  simp
def s9_83 : State := ⟨[21,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179230, 3, 3, 1, 0⟩
theorem s9_83_edges : next config 9 s9_83 = [] := by decide
theorem s9_83_safe : Safe 4 9 s9_83 := by
  apply safe_succ 3 9 s9_83 [] (by decide) s9_83_edges
  simp
def s9_84 : State := ⟨[21,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376335282454, 3, 3, 1, 0⟩
theorem s9_84_edges : next config 9 s9_84 = [] := by decide
theorem s9_84_safe : Safe 4 9 s9_84 := by
  apply safe_succ 3 9 s9_84 [] (by decide) s9_84_edges
  simp
def s9_85 : State := ⟨[21,12,125,145], 44601873214744393976609017223235702553252126, 3, 1, 1, 0⟩
theorem s9_85_edges : next config 9 s9_85 = [s10_0] := by decide
theorem s9_85_safe : Safe 4 9 s9_85 := by
  apply safe_succ 3 9 s9_85 [s10_0] (by decide) s9_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_0_safe
def s9_86 : State := ⟨[21,12,125,145], 44601873214744393976609054116723849972355350, 3, 1, 1, 0⟩
theorem s9_86_edges : next config 9 s9_86 = [s10_1] := by decide
theorem s9_86_safe : Safe 4 9 s9_86 := by
  apply safe_succ 3 9 s9_86 [s10_1] (by decide) s9_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_1_safe
def s9_87 : State := ⟨[25,4,104,145], 44601830679448528859301084301409773615776030, 3, 3, 1, 0⟩
theorem s9_87_edges : next config 9 s9_87 = [] := by decide
theorem s9_87_safe : Safe 4 9 s9_87 := by
  apply safe_succ 3 9 s9_87 [] (by decide) s9_87_edges
  simp
def s9_88 : State := ⟨[25,4,104,145], 44601830679448528859301121194897921034879254, 3, 3, 1, 0⟩
theorem s9_88_edges : next config 9 s9_88 = [] := by decide
theorem s9_88_safe : Safe 4 9 s9_88 := by
  apply safe_succ 3 9 s9_88 [] (by decide) s9_88_edges
  simp
def s9_89 : State := ⟨[33,4,125,145], 44601873214744393976609017223235711143182614, 3, 3, 1, 0⟩
theorem s9_89_edges : next config 9 s9_89 = [s10_3] := by decide
theorem s9_89_safe : Safe 4 9 s9_89 := by
  apply safe_succ 3 9 s9_89 [s10_3] (by decide) s9_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_3_safe
def s9_90 : State := ⟨[33,12,104,145], 44601830679448528859301084301409782172160278, 3, 3, 1, 0⟩
theorem s9_90_edges : next config 9 s9_90 = [] := by decide
theorem s9_90_safe : Safe 4 9 s9_90 := by
  apply safe_succ 3 9 s9_90 [] (by decide) s9_90_edges
  simp
def s9_91 : State := ⟨[33,21,104,145], 44601830679448528859301084301409782172160278, 3, 3, 1, 0⟩
theorem s9_91_edges : next config 9 s9_91 = [] := by decide
theorem s9_91_safe : Safe 4 9 s9_91 := by
  apply safe_succ 3 9 s9_91 [] (by decide) s9_91_edges
  simp
def s9_92 : State := ⟨[35,4,67,145], 44601830679428246449697580204938450364993822, 3, 3, 1, 0⟩
theorem s9_92_edges : next config 9 s9_92 = [] := by decide
theorem s9_92_safe : Safe 4 9 s9_92 := by
  apply safe_succ 3 9 s9_92 [] (by decide) s9_92_edges
  simp
def s9_93 : State := ⟨[35,4,67,145], 44601830679428246449697580204938450367086878, 3, 3, 1, 0⟩
theorem s9_93_edges : next config 9 s9_93 = [s10_12, s10_4] := by decide
theorem s9_93_safe : Safe 4 9 s9_93 := by
  apply safe_succ 3 9 s9_93 [s10_12, s10_4] (by decide) s9_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_12_safe
  · subst z; exact s10_4_safe
def s9_94 : State := ⟨[35,4,67,145], 44601830679428246449697580204938458954928406, 3, 3, 1, 0⟩
theorem s9_94_edges : next config 9 s9_94 = [] := by decide
theorem s9_94_safe : Safe 4 9 s9_94 := by
  apply safe_succ 3 9 s9_94 [] (by decide) s9_94_edges
  simp
def s9_95 : State := ⟨[35,4,67,145], 44601830679428246449697580204938458957021462, 3, 3, 1, 0⟩
theorem s9_95_edges : next config 9 s9_95 = [s10_13, s10_5] := by decide
theorem s9_95_safe : Safe 4 9 s9_95 := by
  apply safe_succ 3 9 s9_95 [s10_13, s10_5] (by decide) s9_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_13_safe
  · subst z; exact s10_5_safe
def s9_96 : State := ⟨[35,4,104,145], 44601830679448528859301084301409807939866910, 3, 3, 1, 0⟩
theorem s9_96_edges : next config 9 s9_96 = [] := by decide
theorem s9_96_safe : Safe 4 9 s9_96 := by
  apply safe_succ 3 9 s9_96 [] (by decide) s9_96_edges
  simp
def s9_97 : State := ⟨[35,4,104,145], 44601830679448528859301084301409807941959966, 3, 3, 1, 0⟩
theorem s9_97_edges : next config 9 s9_97 = [s10_14] := by decide
theorem s9_97_safe : Safe 4 9 s9_97 := by
  apply safe_succ 3 9 s9_97 [s10_14] (by decide) s9_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_14_safe
def s9_98 : State := ⟨[35,4,104,145], 44601830679448528859301084301409816529801494, 3, 3, 1, 0⟩
theorem s9_98_edges : next config 9 s9_98 = [] := by decide
theorem s9_98_safe : Safe 4 9 s9_98 := by
  apply safe_succ 3 9 s9_98 [] (by decide) s9_98_edges
  simp
def s9_99 : State := ⟨[35,4,104,145], 44601830679448528859301084301409816531894550, 3, 3, 1, 0⟩
theorem s9_99_edges : next config 9 s9_99 = [s10_15] := by decide
theorem s9_99_safe : Safe 4 9 s9_99 := by
  apply safe_succ 3 9 s9_99 [s10_15] (by decide) s9_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_15_safe
def s9_100 : State := ⟨[35,12,67,145], 44601830679428167221535065940600856823140638, 3, 3, 1, 0⟩
theorem s9_100_edges : next config 9 s9_100 = [s10_27] := by decide
theorem s9_100_safe : Safe 4 9 s9_100 := by
  apply safe_succ 3 9 s9_100 [s10_27] (by decide) s9_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_27_safe
def s9_101 : State := ⟨[35,12,96,145], 44601830679428246449697432630985860690678046, 3, 3, 1, 0⟩
theorem s9_101_edges : next config 9 s9_101 = [s10_4] := by decide
theorem s9_101_safe : Safe 4 9 s9_101 := by
  apply safe_succ 3 9 s9_101 [s10_4] (by decide) s9_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_4_safe
def s9_102 : State := ⟨[35,12,96,145], 44601830679428246449697432630985869280612630, 3, 3, 1, 0⟩
theorem s9_102_edges : next config 9 s9_102 = [s10_5] := by decide
theorem s9_102_safe : Safe 4 9 s9_102 := by
  apply safe_succ 3 9 s9_102 [s10_5] (by decide) s9_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_5_safe
def s9_103 : State := ⟨[35,21,67,145], 44601830679428167221535065940600856823140638, 3, 3, 1, 0⟩
theorem s9_103_edges : next config 9 s9_103 = [s10_28] := by decide
theorem s9_103_safe : Safe 4 9 s9_103 := by
  apply safe_succ 3 9 s9_103 [s10_28] (by decide) s9_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_28_safe
def s9_104 : State := ⟨[35,21,96,145], 44601830679428246449697432630985860690678046, 3, 3, 1, 0⟩
theorem s9_104_edges : next config 9 s9_104 = [s10_6] := by decide
theorem s9_104_safe : Safe 4 9 s9_104 := by
  apply safe_succ 3 9 s9_104 [s10_6] (by decide) s9_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_6_safe
def s9_105 : State := ⟨[35,21,96,145], 44601830679428246449697432630985869280612630, 3, 3, 1, 0⟩
theorem s9_105_edges : next config 9 s9_105 = [s10_7] := by decide
theorem s9_105_safe : Safe 4 9 s9_105 := by
  apply safe_succ 3 9 s9_105 [s10_7] (by decide) s9_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_7_safe
def s9_106 : State := ⟨[35,29,67,145], 44601830679428246449697580204938450903957790, 3, 1, 1, 0⟩
theorem s9_106_edges : next config 9 s9_106 = [s10_25, s10_8] := by decide
theorem s9_106_safe : Safe 4 9 s9_106 := by
  apply safe_succ 3 9 s9_106 [s10_25, s10_8] (by decide) s9_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_25_safe
  · subst z; exact s10_8_safe
def s9_107 : State := ⟨[35,29,67,145], 44601830679428246449697580204938459493892374, 3, 1, 1, 0⟩
theorem s9_107_edges : next config 9 s9_107 = [s10_26, s10_9] := by decide
theorem s9_107_safe : Safe 4 9 s9_107 := by
  apply safe_succ 3 9 s9_107 [s10_26, s10_9] (by decide) s9_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_26_safe
  · subst z; exact s10_9_safe
def s9_108 : State := ⟨[35,54,67,145], 44601830679428246449697580222952848876568862, 3, 1, 1, 0⟩
theorem s9_108_edges : next config 9 s9_108 = [s10_10] := by decide
theorem s9_108_safe : Safe 4 9 s9_108 := by
  apply safe_succ 3 9 s9_108 [s10_10] (by decide) s9_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_10_safe
def s9_109 : State := ⟨[35,54,67,145], 44601830679428246449697580222952857466503446, 3, 1, 1, 0⟩
theorem s9_109_edges : next config 9 s9_109 = [s10_11] := by decide
theorem s9_109_safe : Safe 4 9 s9_109 := by
  apply safe_succ 3 9 s9_109 [s10_11] (by decide) s9_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_11_safe
def s9_110 : State := ⟨[35,62,67,145], 44601830679428167221535070552286875787395358, 3, 1, 1, 0⟩
theorem s9_110_edges : next config 9 s9_110 = [s10_30] := by decide
theorem s9_110_safe : Safe 4 9 s9_110 := by
  apply safe_succ 3 9 s9_110 [s10_30] (by decide) s9_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_30_safe
def s9_111 : State := ⟨[35,62,67,145], 44601830679428167221535070570301273760006430, 3, 1, 1, 0⟩
theorem s9_111_edges : next config 9 s9_111 = [s10_31] := by decide
theorem s9_111_safe : Safe 4 9 s9_111 := by
  apply safe_succ 3 9 s9_111 [s10_31] (by decide) s9_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_31_safe
def s9_112 : State := ⟨[35,62,96,145], 44601830679428246449697437242671879654932766, 3, 1, 1, 0⟩
theorem s9_112_edges : next config 9 s9_112 = [s10_8] := by decide
theorem s9_112_safe : Safe 4 9 s9_112 := by
  apply safe_succ 3 9 s9_112 [s10_8] (by decide) s9_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_8_safe
def s9_113 : State := ⟨[35,62,96,145], 44601830679428246449697437242671888244867350, 3, 1, 1, 0⟩
theorem s9_113_edges : next config 9 s9_113 = [s10_9] := by decide
theorem s9_113_safe : Safe 4 9 s9_113 := by
  apply safe_succ 3 9 s9_113 [s10_9] (by decide) s9_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_9_safe
def s9_114 : State := ⟨[35,62,96,145], 44601830679428246449697437260686277627543838, 3, 1, 1, 0⟩
theorem s9_114_edges : next config 9 s9_114 = [s10_10] := by decide
theorem s9_114_safe : Safe 4 9 s9_114 := by
  apply safe_succ 3 9 s9_114 [s10_10] (by decide) s9_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_10_safe
def s9_115 : State := ⟨[35,62,96,145], 44601830679428246449697437260686286217478422, 3, 1, 1, 0⟩
theorem s9_115_edges : next config 9 s9_115 = [s10_11] := by decide
theorem s9_115_safe : Safe 4 9 s9_115 := by
  apply safe_succ 3 9 s9_115 [s10_11] (by decide) s9_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_11_safe
def s9_116 : State := ⟨[35,86,67,145], 44601830679428246527068832660274717548282142, 3, 1, 1, 0⟩
theorem s9_116_edges : next config 9 s9_116 = [] := by decide
theorem s9_116_safe : Safe 4 9 s9_116 := by
  apply safe_succ 3 9 s9_116 [] (by decide) s9_116_edges
  simp
def s9_117 : State := ⟨[35,86,67,145], 44601830679428246527068832660274726138216726, 3, 1, 1, 0⟩
theorem s9_117_edges : next config 9 s9_117 = [] := by decide
theorem s9_117_safe : Safe 4 9 s9_117 := by
  apply safe_succ 3 9 s9_117 [] (by decide) s9_117_edges
  simp
def s9_118 : State := ⟨[43,4,67,145], 44601830679428167221535065940609652916158750, 3, 3, 1, 0⟩
theorem s9_118_edges : next config 9 s9_118 = [s10_32] := by decide
theorem s9_118_safe : Safe 4 9 s9_118 := by
  apply safe_succ 3 9 s9_118 [s10_32] (by decide) s9_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_32_safe
def s9_119 : State := ⟨[43,4,67,145], 44601830679448528859301231875371193709297950, 1, 1, 1, 0⟩
theorem s9_119_edges : next config 9 s9_119 = [] := by decide
theorem s9_119_safe : Safe 4 9 s9_119 := by
  apply safe_succ 3 9 s9_119 [] (by decide) s9_119_edges
  simp
def s9_120 : State := ⟨[43,4,67,145], 44601830679448528859301231875371202299232534, 1, 1, 1, 0⟩
theorem s9_120_edges : next config 9 s9_120 = [] := by decide
theorem s9_120_safe : Safe 4 9 s9_120 := by
  apply safe_succ 3 9 s9_120 [] (by decide) s9_120_edges
  simp
def s9_121 : State := ⟨[43,4,96,145], 44601830679428246449697432630994656783696158, 3, 3, 1, 0⟩
theorem s9_121_edges : next config 9 s9_121 = [s10_14] := by decide
theorem s9_121_safe : Safe 4 9 s9_121 := by
  apply safe_succ 3 9 s9_121 [s10_14] (by decide) s9_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_14_safe
def s9_122 : State := ⟨[43,4,96,145], 44601830679428246449697432630994665373630742, 3, 3, 1, 0⟩
theorem s9_122_edges : next config 9 s9_122 = [s10_15] := by decide
theorem s9_122_safe : Safe 4 9 s9_122 := by
  apply safe_succ 3 9 s9_122 [s10_15] (by decide) s9_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_15_safe
def s9_123 : State := ⟨[43,21,67,145], 44601830679428246449697580204947246460109086, 3, 1, 1, 0⟩
theorem s9_123_edges : next config 9 s9_123 = [s10_21, s10_35, s10_18] := by decide
theorem s9_123_safe : Safe 4 9 s9_123 := by
  apply safe_succ 3 9 s9_123 [s10_21, s10_35, s10_18] (by decide) s9_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s10_21_safe
  · subst z; exact s10_35_safe
  · subst z; exact s10_18_safe
def s9_124 : State := ⟨[43,21,67,145], 44601830679428246449697580204947255050043670, 3, 1, 1, 0⟩
theorem s9_124_edges : next config 9 s9_124 = [s10_22, s10_36, s10_19] := by decide
theorem s9_124_safe : Safe 4 9 s9_124 := by
  apply safe_succ 3 9 s9_124 [s10_22, s10_36, s10_19] (by decide) s9_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s10_22_safe
  · subst z; exact s10_36_safe
  · subst z; exact s10_19_safe
def s9_125 : State := ⟨[43,21,104,145], 44601830679448528859301084301418604034982174, 3, 1, 1, 0⟩
theorem s9_125_edges : next config 9 s9_125 = [s10_16] := by decide
theorem s9_125_safe : Safe 4 9 s9_125 := by
  apply safe_succ 3 9 s9_125 [s10_16] (by decide) s9_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_16_safe
def s9_126 : State := ⟨[43,21,104,145], 44601830679448528859301084301418612624916758, 3, 1, 1, 0⟩
theorem s9_126_edges : next config 9 s9_126 = [s10_17] := by decide
theorem s9_126_safe : Safe 4 9 s9_126 := by
  apply safe_succ 3 9 s9_126 [s10_17] (by decide) s9_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_17_safe
def s9_127 : State := ⟨[43,62,67,145], 44601830679428167221535070552295671343546654, 3, 1, 1, 0⟩
theorem s9_127_edges : next config 9 s9_127 = [s10_39] := by decide
theorem s9_127_safe : Safe 4 9 s9_127 := by
  apply safe_succ 3 9 s9_127 [s10_39] (by decide) s9_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_39_safe
def s9_128 : State := ⟨[49,4,104,145], 44601830679448528859301084301972723533549854, 3, 3, 1, 0⟩
theorem s9_128_edges : next config 9 s9_128 = [] := by decide
theorem s9_128_safe : Safe 4 9 s9_128 := by
  apply safe_succ 3 9 s9_128 [] (by decide) s9_128_edges
  simp
def s9_129 : State := ⟨[49,4,104,145], 44601830679448528859301084301972723535642910, 3, 3, 1, 0⟩
theorem s9_129_edges : next config 9 s9_129 = [] := by decide
theorem s9_129_safe : Safe 4 9 s9_129 := by
  apply safe_succ 3 9 s9_129 [] (by decide) s9_129_edges
  simp
def s9_130 : State := ⟨[49,12,67,145], 44601830679428167221535065941163772416823582, 3, 3, 1, 0⟩
theorem s9_130_edges : next config 9 s9_130 = [] := by decide
theorem s9_130_safe : Safe 4 9 s9_130 := by
  apply safe_succ 3 9 s9_130 [] (by decide) s9_130_edges
  simp
def s9_131 : State := ⟨[49,12,96,145], 44601830679428246449697432631548776284360990, 3, 3, 1, 0⟩
theorem s9_131_edges : next config 9 s9_131 = [] := by decide
theorem s9_131_safe : Safe 4 9 s9_131 := by
  apply safe_succ 3 9 s9_131 [] (by decide) s9_131_edges
  simp
def s9_132 : State := ⟨[49,21,67,145], 44601830679428167221535065941163772416823582, 3, 3, 1, 0⟩
theorem s9_132_edges : next config 9 s9_132 = [] := by decide
theorem s9_132_safe : Safe 4 9 s9_132 := by
  apply safe_succ 3 9 s9_132 [] (by decide) s9_132_edges
  simp
def s9_133 : State := ⟨[54,21,67,145], 44601830679428246449697580222952848876568862, 3, 1, 1, 0⟩
theorem s9_133_edges : next config 9 s9_133 = [s10_23] := by decide
theorem s9_133_safe : Safe 4 9 s9_133 := by
  apply safe_succ 3 9 s9_133 [s10_23] (by decide) s9_133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_23_safe
def s9_134 : State := ⟨[54,21,67,145], 44601830679428246449697580222952857466503446, 3, 1, 1, 0⟩
theorem s9_134_edges : next config 9 s9_134 = [s10_24] := by decide
theorem s9_134_safe : Safe 4 9 s9_134 := by
  apply safe_succ 3 9 s9_134 [s10_24] (by decide) s9_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_24_safe
def s9_135 : State := ⟨[62,21,67,145], 44601830679428167221535070552295671343546654, 3, 1, 1, 0⟩
theorem s9_135_edges : next config 9 s9_135 = [] := by decide
theorem s9_135_safe : Safe 4 9 s9_135 := by
  apply safe_succ 3 9 s9_135 [] (by decide) s9_135_edges
  simp
def s9_136 : State := ⟨[62,21,67,145], 44601830679428167221535070570301239404462366, 3, 1, 1, 0⟩
theorem s9_136_edges : next config 9 s9_136 = [] := by decide
theorem s9_136_safe : Safe 4 9 s9_136 := by
  apply safe_succ 3 9 s9_136 [] (by decide) s9_136_edges
  simp
def s9_137 : State := ⟨[62,21,67,145], 44601830679428167221535070570301273760006430, 3, 1, 1, 0⟩
theorem s9_137_edges : next config 9 s9_137 = [] := by decide
theorem s9_137_safe : Safe 4 9 s9_137 := by
  apply safe_succ 3 9 s9_137 [] (by decide) s9_137_edges
  simp
def s9_138 : State := ⟨[62,29,67,145], 44601830679428167221535070552286875787395358, 3, 1, 1, 0⟩
theorem s9_138_edges : next config 9 s9_138 = [] := by decide
theorem s9_138_safe : Safe 4 9 s9_138 := by
  apply safe_succ 3 9 s9_138 [] (by decide) s9_138_edges
  simp
def s9_139 : State := ⟨[62,53,67,145], 44601830679428167221535070579308438655009054, 3, 1, 1, 0⟩
theorem s9_139_edges : next config 9 s9_139 = [] := by decide
theorem s9_139_safe : Safe 4 9 s9_139 := by
  apply safe_succ 3 9 s9_139 [] (by decide) s9_139_edges
  simp
def s9_140 : State := ⟨[65,4,108,145], 44601830679773047412959547921681077021901078, 3, 3, 1, 0⟩
theorem s9_140_edges : next config 9 s9_140 = [] := by decide
theorem s9_140_safe : Safe 4 9 s9_140 := by
  apply safe_succ 3 9 s9_140 [] (by decide) s9_140_edges
  simp
def s9_141 : State := ⟨[65,4,249,145], 904625697166532776746648320380418881934351203729176207679457272982822650134, 3, 3, 1, 0⟩
theorem s9_141_edges : next config 9 s9_141 = [] := by decide
theorem s9_141_safe : Safe 4 9 s9_141 := by
  apply safe_succ 3 9 s9_141 [] (by decide) s9_141_edges
  simp
def s9_142 : State := ⟨[65,12,104,145], 44601830679448528859301121194897921001328918, 3, 3, 1, 0⟩
theorem s9_142_edges : next config 9 s9_142 = [] := by decide
theorem s9_142_safe : Safe 4 9 s9_142 := by
  apply safe_succ 3 9 s9_142 [] (by decide) s9_142_edges
  simp
def s9_143 : State := ⟨[65,12,241,145], 3533694129556768659166595001530438862334396040200935385767686376335282454, 3, 3, 1, 0⟩
theorem s9_143_edges : next config 9 s9_143 = [] := by decide
theorem s9_143_safe : Safe 4 9 s9_143 := by
  apply safe_succ 3 9 s9_143 [] (by decide) s9_143_edges
  simp
def s9_144 : State := ⟨[65,108,104,145], 44601830679773047412959547921681077021901078, 3, 3, 1, 0⟩
theorem s9_144_edges : next config 9 s9_144 = [] := by decide
theorem s9_144_safe : Safe 4 9 s9_144 := by
  apply safe_succ 3 9 s9_144 [] (by decide) s9_144_edges
  simp
def s9_145 : State := ⟨[82,4,67,145], 44601830679428167303742021674395606343418142, 3, 3, 1, 0⟩
theorem s9_145_edges : next config 9 s9_145 = [] := by decide
theorem s9_145_safe : Safe 4 9 s9_145 := by
  apply safe_succ 3 9 s9_145 [] (by decide) s9_145_edges
  simp
def s9_146 : State := ⟨[82,12,67,145], 44601830679428167226370769219059339162226974, 3, 3, 1, 0⟩
theorem s9_146_edges : next config 9 s9_146 = [] := by decide
theorem s9_146_safe : Safe 4 9 s9_146 := by
  apply safe_succ 3 9 s9_146 [] (by decide) s9_146_edges
  simp
def s9_147 : State := ⟨[82,21,67,145], 44601830679428167226370769219059339162226974, 3, 3, 1, 0⟩
theorem s9_147_edges : next config 9 s9_147 = [] := by decide
theorem s9_147_safe : Safe 4 9 s9_147 := by
  apply safe_succ 3 9 s9_147 [] (by decide) s9_147_edges
  simp
def s9_148 : State := ⟨[82,86,67,145], 44601830679428167303742021674395606343418142, 3, 3, 1, 0⟩
theorem s9_148_edges : next config 9 s9_148 = [] := by decide
theorem s9_148_safe : Safe 4 9 s9_148 := by
  apply safe_succ 3 9 s9_148 [] (by decide) s9_148_edges
  simp
def s9_149 : State := ⟨[86,4,67,145], 44601830679428167298906318395937089644597534, 3, 3, 1, 0⟩
theorem s9_149_edges : next config 9 s9_149 = [] := by decide
theorem s9_149_safe : Safe 4 9 s9_149 := by
  apply safe_succ 3 9 s9_149 [] (by decide) s9_149_edges
  simp
def s9_150 : State := ⟨[86,4,67,145], 44601830679428167303742021674395606343418142, 3, 3, 1, 0⟩
theorem s9_150_edges : next config 9 s9_150 = [] := by decide
theorem s9_150_safe : Safe 4 9 s9_150 := by
  apply safe_succ 3 9 s9_150 [] (by decide) s9_150_edges
  simp
def s9_151 : State := ⟨[96,4,67,145], 44601830679428246449697580204938450364993822, 3, 3, 1, 0⟩
theorem s9_151_edges : next config 9 s9_151 = [s10_33] := by decide
theorem s9_151_safe : Safe 4 9 s9_151 := by
  apply safe_succ 3 9 s9_151 [s10_33] (by decide) s9_151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_33_safe
def s9_152 : State := ⟨[96,4,67,145], 44601830679428246449697580204938450367086878, 3, 3, 1, 0⟩
theorem s9_152_edges : next config 9 s9_152 = [s10_34, s10_27] := by decide
theorem s9_152_safe : Safe 4 9 s9_152 := by
  apply safe_succ 3 9 s9_152 [s10_34, s10_27] (by decide) s9_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_34_safe
  · subst z; exact s10_27_safe
def s9_153 : State := ⟨[96,4,67,145], 44601830679448528859301231875371193709297950, 1, 1, 1, 0⟩
theorem s9_153_edges : next config 9 s9_153 = [] := by decide
theorem s9_153_safe : Safe 4 9 s9_153 := by
  apply safe_succ 3 9 s9_153 [] (by decide) s9_153_edges
  simp
def s9_154 : State := ⟨[96,29,67,145], 44601830679428246449697580204938450903957790, 3, 1, 1, 0⟩
theorem s9_154_edges : next config 9 s9_154 = [s10_37] := by decide
theorem s9_154_safe : Safe 4 9 s9_154 := by
  apply safe_succ 3 9 s9_154 [s10_37] (by decide) s9_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_37_safe
def s9_155 : State := ⟨[96,54,67,145], 44601830679428246449697580222952848876568862, 3, 1, 1, 0⟩
theorem s9_155_edges : next config 9 s9_155 = [s10_38, s10_31] := by decide
theorem s9_155_safe : Safe 4 9 s9_155 := by
  apply safe_succ 3 9 s9_155 [s10_38, s10_31] (by decide) s9_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s10_38_safe
  · subst z; exact s10_31_safe
def s9_156 : State := ⟨[96,86,67,145], 44601830679428246527068832660274717548282142, 3, 1, 1, 0⟩
theorem s9_156_edges : next config 9 s9_156 = [s10_40] := by decide
theorem s9_156_safe : Safe 4 9 s9_156 := by
  apply safe_succ 3 9 s9_156 [s10_40] (by decide) s9_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_40_safe
def s9_157 : State := ⟨[97,12,104,145], 44601830679448687315626112830084960670126358, 3, 3, 1, 0⟩
theorem s9_157_edges : next config 9 s9_157 = [] := by decide
theorem s9_157_safe : Safe 4 9 s9_157 := by
  apply safe_succ 3 9 s9_157 [] (by decide) s9_157_edges
  simp
def s9_158 : State := ⟨[104,4,67,145], 44601830679448528859301231875371193709297950, 1, 1, 1, 0⟩
theorem s9_158_edges : next config 9 s9_158 = [] := by decide
theorem s9_158_safe : Safe 4 9 s9_158 := by
  apply safe_succ 3 9 s9_158 [] (by decide) s9_158_edges
  simp
def s9_159 : State := ⟨[104,4,67,145], 44601830679448528859301231875371202299232534, 1, 1, 1, 0⟩
theorem s9_159_edges : next config 9 s9_159 = [] := by decide
theorem s9_159_safe : Safe 4 9 s9_159 := by
  apply safe_succ 3 9 s9_159 [] (by decide) s9_159_edges
  simp
def s9_160 : State := ⟨[104,4,67,145], 44602511244182370736228158624577261152571678, 3, 2, 1, 0⟩
theorem s9_160_edges : next config 9 s9_160 = [] := by decide
theorem s9_160_safe : Safe 4 9 s9_160 := by
  apply safe_succ 3 9 s9_160 [] (by decide) s9_160_edges
  simp
def s9_161 : State := ⟨[104,4,67,145], 66902575877979152000836950148010759122129182, 3, 2, 1, 0⟩
theorem s9_161_edges : next config 9 s9_161 = [] := by decide
theorem s9_161_safe : Safe 4 9 s9_161 := by
  apply safe_succ 3 9 s9_161 [] (by decide) s9_161_edges
  simp
def s9_162 : State := ⟨[104,12,67,145], 44601830679448528859301231875362397616279838, 3, 1, 1, 0⟩
theorem s9_162_edges : next config 9 s9_162 = [s10_33] := by decide
theorem s9_162_safe : Safe 4 9 s9_162 := by
  apply safe_succ 3 9 s9_162 [s10_33] (by decide) s9_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_33_safe
def s9_163 : State := ⟨[104,21,67,145], 44601830679448449631138717611033600167444766, 3, 1, 1, 0⟩
theorem s9_163_edges : next config 9 s9_163 = [s10_29] := by decide
theorem s9_163_safe : Safe 4 9 s9_163 := by
  apply safe_succ 3 9 s9_163 [s10_29] (by decide) s9_163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_29_safe
def s9_164 : State := ⟨[104,21,67,145], 44601830679448528859301231875362397618372894, 3, 1, 1, 0⟩
theorem s9_164_edges : next config 9 s9_164 = [s10_44, s10_16, s10_41, s10_40, s10_37] := by decide
theorem s9_164_safe : Safe 4 9 s9_164 := by
  apply safe_succ 3 9 s9_164 [s10_44, s10_16, s10_41, s10_40, s10_37] (by decide) s9_164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s10_44_safe
  · subst z; exact s10_16_safe
  · subst z; exact s10_41_safe
  · subst z; exact s10_40_safe
  · subst z; exact s10_37_safe
def s9_165 : State := ⟨[113,4,104,145], 44601830689833122576370739558470766238568734, 3, 3, 1, 0⟩
theorem s9_165_edges : next config 9 s9_165 = [] := by decide
theorem s9_165_safe : Safe 4 9 s9_165 := by
  apply safe_succ 3 9 s9_165 [] (by decide) s9_165_edges
  simp
def s9_166 : State := ⟨[113,4,104,145], 44601830689833122576370739558470766240661790, 3, 3, 1, 0⟩
theorem s9_166_edges : next config 9 s9_166 = [] := by decide
theorem s9_166_safe : Safe 4 9 s9_166 := by
  apply safe_succ 3 9 s9_166 [] (by decide) s9_166_edges
  simp
def s9_167 : State := ⟨[113,4,104,145], 44601830689833122576370776451958913657671958, 3, 3, 1, 0⟩
theorem s9_167_edges : next config 9 s9_167 = [] := by decide
theorem s9_167_safe : Safe 4 9 s9_167 := by
  apply safe_succ 3 9 s9_167 [] (by decide) s9_167_edges
  simp
def s9_168 : State := ⟨[113,4,104,145], 44601830689833122576370776451958913659765014, 3, 3, 1, 0⟩
theorem s9_168_edges : next config 9 s9_168 = [] := by decide
theorem s9_168_safe : Safe 4 9 s9_168 := by
  apply safe_succ 3 9 s9_168 [] (by decide) s9_168_edges
  simp
def s9_169 : State := ⟨[113,12,96,145], 44601830689812840166767087888046818989379870, 3, 3, 1, 0⟩
theorem s9_169_edges : next config 9 s9_169 = [] := by decide
theorem s9_169_safe : Safe 4 9 s9_169 := by
  apply safe_succ 3 9 s9_169 [] (by decide) s9_169_edges
  simp
def s9_170 : State := ⟨[113,12,96,145], 44601830689812840166767124781534966408483094, 3, 3, 1, 0⟩
theorem s9_170_edges : next config 9 s9_170 = [] := by decide
theorem s9_170_safe : Safe 4 9 s9_170 := by
  apply safe_succ 3 9 s9_170 [] (by decide) s9_170_edges
  simp
def s9_171 : State := ⟨[121,4,104,145], 44601833337904520429132830109023894142910750, 3, 3, 1, 0⟩
theorem s9_171_edges : next config 9 s9_171 = [] := by decide
theorem s9_171_safe : Safe 4 9 s9_171 := by
  apply safe_succ 3 9 s9_171 [] (by decide) s9_171_edges
  simp
def s9_172 : State := ⟨[121,4,104,145], 44601833337904520429132867002512041562013974, 3, 3, 1, 0⟩
theorem s9_172_edges : next config 9 s9_172 = [] := by decide
theorem s9_172_safe : Safe 4 9 s9_172 := by
  apply safe_succ 3 9 s9_172 [] (by decide) s9_172_edges
  simp
def s9_173 : State := ⟨[125,12,104,145], 44601873214744393976609017223235702553252126, 3, 1, 1, 0⟩
theorem s9_173_edges : next config 9 s9_173 = [s10_42] := by decide
theorem s9_173_safe : Safe 4 9 s9_173 := by
  apply safe_succ 3 9 s9_173 [s10_42] (by decide) s9_173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_42_safe
def s9_174 : State := ⟨[125,12,104,145], 44601873214744393976609054116723849972355350, 3, 1, 1, 0⟩
theorem s9_174_edges : next config 9 s9_174 = [s10_43] := by decide
theorem s9_174_safe : Safe 4 9 s9_174 := by
  apply safe_succ 3 9 s9_174 [s10_43] (by decide) s9_174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s10_43_safe
def s9_175 : State := ⟨[146,4,104,145], 133804811473571021425443957392003219604050206, 3, 3, 1, 0⟩
theorem s9_175_edges : next config 9 s9_175 = [] := by decide
theorem s9_175_safe : Safe 4 9 s9_175 := by
  apply safe_succ 3 9 s9_175 [] (by decide) s9_175_edges
  simp
def s9_176 : State := ⟨[146,4,104,145], 133804811473571021425443957392003219606143262, 3, 3, 1, 0⟩
theorem s9_176_edges : next config 9 s9_176 = [] := by decide
theorem s9_176_safe : Safe 4 9 s9_176 := by
  apply safe_succ 3 9 s9_176 [] (by decide) s9_176_edges
  simp
def s9_177 : State := ⟨[146,12,67,145], 133804811473550659787677939031194268487323934, 3, 3, 1, 0⟩
theorem s9_177_edges : next config 9 s9_177 = [] := by decide
theorem s9_177_safe : Safe 4 9 s9_177 := by
  apply safe_succ 3 9 s9_177 [] (by decide) s9_177_edges
  simp
def s9_178 : State := ⟨[146,12,96,145], 133804811473550739015840305721579272354861342, 3, 3, 1, 0⟩
theorem s9_178_edges : next config 9 s9_178 = [] := by decide
theorem s9_178_safe : Safe 4 9 s9_178 := by
  apply safe_succ 3 9 s9_178 [] (by decide) s9_178_edges
  simp
def s9_179 : State := ⟨[146,21,67,145], 133804811473550659787677939031194268487323934, 3, 3, 1, 0⟩
theorem s9_179_edges : next config 9 s9_179 = [] := by decide
theorem s9_179_safe : Safe 4 9 s9_179 := by
  apply safe_succ 3 9 s9_179 [] (by decide) s9_179_edges
  simp
end HGP13.SectorGraph234
