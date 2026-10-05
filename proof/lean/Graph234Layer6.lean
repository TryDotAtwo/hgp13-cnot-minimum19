import Graph234Layer7
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s6_0 : State := ⟨[1,4,64,145], 44602511244162009098461845115863096321184030, 3, 3, 1, 0⟩
theorem s6_0_edges : next config 6 s6_0 = [s7_28] := by decide
theorem s6_0_safe : Safe 7 6 s6_0 := by
  apply safe_succ 6 6 s6_0 [s7_28] (by decide) s6_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_28_safe
def s6_1 : State := ⟨[1,4,64,145], 44602511244162009098461845115863104911118614, 3, 3, 1, 0⟩
theorem s6_1_edges : next config 6 s6_1 = [s7_29] := by decide
theorem s6_1_safe : Safe 7 6 s6_1 := by
  apply safe_succ 6 6 s6_1 [s7_29] (by decide) s6_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_29_safe
def s6_2 : State := ⟨[1,4,64,145], 44602511244162009098461882009351243740287254, 3, 3, 1, 0⟩
theorem s6_2_edges : next config 6 s6_2 = [s7_30] := by decide
theorem s6_2_safe : Safe 7 6 s6_2 := by
  apply safe_succ 6 6 s6_2 [s7_30] (by decide) s6_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_30_safe
def s6_3 : State := ⟨[1,4,64,145], 66902575877958790363070636639296594290741534, 3, 3, 1, 0⟩
theorem s6_3_edges : next config 6 s6_3 = [s7_34] := by decide
theorem s6_3_safe : Safe 7 6 s6_3 := by
  apply safe_succ 6 6 s6_3 [s7_34] (by decide) s6_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_34_safe
def s6_4 : State := ⟨[1,4,64,145], 66902575877958790363070636639296602880676118, 3, 3, 1, 0⟩
theorem s6_4_edges : next config 6 s6_4 = [s7_35] := by decide
theorem s6_4_safe : Safe 7 6 s6_4 := by
  apply safe_succ 6 6 s6_4 [s7_35] (by decide) s6_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_35_safe
def s6_5 : State := ⟨[1,4,64,145], 66902575877958790363070673532784741709844758, 3, 3, 1, 0⟩
theorem s6_5_edges : next config 6 s6_5 = [s7_36] := by decide
theorem s6_5_safe : Safe 7 6 s6_5 := by
  apply safe_succ 6 6 s6_5 [s7_36] (by decide) s6_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_36_safe
def s6_6 : State := ⟨[1,4,64,146], 89204682205957097258460208410374682869567774, 3, 3, 1, 0⟩
theorem s6_6_edges : next config 6 s6_6 = [s7_40] := by decide
theorem s6_6_safe : Safe 7 6 s6_6 := by
  apply safe_succ 6 6 s6_6 [s7_40] (by decide) s6_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_40_safe
def s6_7 : State := ⟨[1,4,64,146], 89204682205957097258460245303862830288670998, 3, 3, 1, 0⟩
theorem s6_7_edges : next config 6 s6_7 = [s7_41] := by decide
theorem s6_7_safe : Safe 7 6 s6_7 := by
  apply safe_succ 6 6 s6_7 [s7_41] (by decide) s6_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_41_safe
def s6_8 : State := ⟨[1,4,64,146], 89207404464892464766167915407234137015259414, 3, 3, 1, 0⟩
theorem s6_8_edges : next config 6 s6_8 = [s7_42] := by decide
theorem s6_8_safe : Safe 7 6 s6_8 := by
  apply safe_succ 6 6 s6_8 [s7_42] (by decide) s6_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_42_safe
def s6_9 : State := ⟨[1,4,64,146], 111504066275020036646142073184593317302702366, 3, 3, 1, 0⟩
theorem s6_9_edges : next config 6 s6_9 = [s7_43] := by decide
theorem s6_9_safe : Safe 7 6 s6_9 := by
  apply safe_succ 6 6 s6_9 [s7_43] (by decide) s6_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_43_safe
def s6_10 : State := ⟨[1,4,64,146], 111504066275020036646142110078081464721805590, 3, 3, 1, 0⟩
theorem s6_10_edges : next config 6 s6_10 = [s7_44] := by decide
theorem s6_10_safe : Safe 7 6 s6_10 := by
  apply safe_succ 6 6 s6_10 [s7_44] (by decide) s6_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_44_safe
def s6_11 : State := ⟨[1,4,64,162], 5846006551025023507419431648200451859860575818014, 3, 3, 1, 0⟩
theorem s6_11_edges : next config 6 s6_11 = [s7_45] := by decide
theorem s6_11_safe : Safe 7 6 s6_11 := by
  apply safe_succ 6 6 s6_11 [s7_45] (by decide) s6_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_45_safe
def s6_12 : State := ⟨[1,4,64,162], 5846006551025023507419431648237345348007994921238, 3, 3, 1, 0⟩
theorem s6_12_edges : next config 6 s6_12 = [s7_46] := by decide
theorem s6_12_safe : Safe 7 6 s6_12 := by
  apply safe_succ 6 6 s6_12 [s7_46] (by decide) s6_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_46_safe
def s6_13 : State := ⟨[1,4,64,162], 5846006553747282442786939355907448719314721509654, 3, 3, 1, 0⟩
theorem s6_13_edges : next config 6 s6_13 = [s7_48] := by decide
theorem s6_13_safe : Safe 7 6 s6_13 := by
  apply safe_succ 6 6 s6_13 [s7_48] (by decide) s6_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_48_safe
def s6_14 : State := ⟨[1,4,64,162], 7307508186994796957939362627063236449789435515166, 3, 3, 1, 0⟩
theorem s6_14_edges : next config 6 s6_14 = [s7_49] := by decide
theorem s6_14_safe : Safe 7 6 s6_14 := by
  apply safe_succ 6 6 s6_14 [s7_49] (by decide) s6_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_49_safe
def s6_15 : State := ⟨[1,4,64,162], 7307508186994796957939362627100129937936854618390, 3, 3, 1, 0⟩
theorem s6_15_edges : next config 6 s6_15 = [s7_50] := by decide
theorem s6_15_safe : Safe 7 6 s6_15 := by
  apply safe_succ 6 6 s6_15 [s7_50] (by decide) s6_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_50_safe
def s6_16 : State := ⟨[1,4,64,162], 17538019649672246853048910309930716017108036161814, 3, 3, 1, 0⟩
theorem s6_16_edges : next config 6 s6_16 = [s7_52] := by decide
theorem s6_16_safe : Safe 7 6 s6_16 := by
  apply safe_succ 6 6 s6_16 [s7_52] (by decide) s6_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_52_safe
def s6_17 : State := ⟨[1,4,64,162], 18999521285642020303568841288793500607036895858966, 3, 3, 1, 0⟩
theorem s6_17_edges : next config 6 s6_17 = [s7_53] := by decide
theorem s6_17_safe : Safe 7 6 s6_17 := by
  apply safe_succ 6 6 s6_17 [s7_53] (by decide) s6_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_53_safe
def s6_18 : State := ⟨[1,4,64,163], 11692013100348635180234170979065583938492895924502, 3, 3, 1, 0⟩
theorem s6_18_edges : next config 6 s6_18 = [s7_54] := by decide
theorem s6_18_safe : Safe 7 6 s6_18 := by
  apply safe_succ 6 6 s6_18 [s7_54] (by decide) s6_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_54_safe
def s6_19 : State := ⟨[1,4,64,163], 11692013101709764647917924832919082368211378835742, 3, 3, 1, 0⟩
theorem s6_19_edges : next config 6 s6_19 = [s7_55] := by decide
theorem s6_19_safe : Safe 7 6 s6_19 := by
  apply safe_succ 6 6 s6_19 [s7_55] (by decide) s6_19_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_55_safe
def s6_20 : State := ⟨[1,4,64,163], 13153514736318408630754101957928368528413165687070, 3, 3, 1, 0⟩
theorem s6_20_edges : next config 6 s6_20 = [s7_56] := by decide
theorem s6_20_safe : Safe 7 6 s6_20 := by
  apply safe_succ 6 6 s6_20 [s7_56] (by decide) s6_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_56_safe
def s6_21 : State := ⟨[1,4,64,163], 14615016373649311548957786790644651548077688164630, 3, 3, 1, 0⟩
theorem s6_21_edges : next config 6 s6_21 = [s7_57] := by decide
theorem s6_21_safe : Safe 7 6 s6_21 := by
  apply safe_succ 6 6 s6_21 [s7_57] (by decide) s6_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_57_safe
def s6_22 : State := ⟨[1,4,64,176], 95780971326419139128294233276893524070171066415255838, 3, 3, 1, 0⟩
theorem s6_22_edges : next config 6 s6_22 = [s7_58] := by decide
theorem s6_22_safe : Safe 7 6 s6_22 := by
  apply safe_succ 6 6 s6_22 [s7_58] (by decide) s6_22_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_58_safe
def s6_23 : State := ⟨[1,4,64,176], 95780971326419139128294233276893560963659213834359062, 3, 3, 1, 0⟩
theorem s6_23_edges : next config 6 s6_23 = [s7_59] := by decide
theorem s6_23_safe : Safe 7 6 s6_23 := by
  apply safe_succ 6 6 s6_23 [s7_59] (by decide) s6_23_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_59_safe
def s6_24 : State := ⟨[1,4,64,176], 95782432805755724832681813820190522080542360841818398, 3, 3, 1, 0⟩
theorem s6_24_edges : next config 6 s6_24 = [s7_60] := by decide
theorem s6_24_safe : Safe 7 6 s6_24 := by
  apply safe_succ 6 6 s6_24 [s7_60] (by decide) s6_24_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_60_safe
def s6_25 : State := ⟨[1,4,64,176], 95782432805755724832681813820190558974030508260921622, 3, 3, 1, 0⟩
theorem s6_25_edges : next config 6 s6_25 = [s7_61] := by decide
theorem s6_25_safe : Safe 7 6 s6_25 := by
  apply safe_succ 6 6 s6_25 [s7_61] (by decide) s6_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_61_safe
def s6_26 : State := ⟨[1,4,65,145], 44601830679428167221534955260136380203995414, 3, 3, 1, 0⟩
theorem s6_26_edges : next config 6 s6_26 = [s7_2] := by decide
theorem s6_26_safe : Safe 7 6 s6_26 := by
  apply safe_succ 6 6 s6_26 [s7_2] (by decide) s6_26_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_2_safe
def s6_27 : State := ⟨[1,4,65,145], 44601830679428167221534955260136380206088470, 3, 3, 1, 0⟩
theorem s6_27_edges : next config 6 s6_27 = [s7_230, s7_3] := by decide
theorem s6_27_safe : Safe 7 6 s6_27 := by
  apply safe_succ 6 6 s6_27 [s7_230, s7_3] (by decide) s6_27_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_230_safe
  · subst z; exact s7_3_safe
def s6_28 : State := ⟨[1,4,66,145], 44601830679428167221534992153624527623098646, 3, 3, 1, 0⟩
theorem s6_28_edges : next config 6 s6_28 = [s7_4, s7_22] := by decide
theorem s6_28_safe : Safe 7 6 s6_28 := by
  apply safe_succ 6 6 s6_28 [s7_4, s7_22] (by decide) s6_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_4_safe
  · subst z; exact s7_22_safe
def s6_29 : State := ⟨[1,4,66,145], 44601830679428167221534992153624527625191702, 3, 3, 1, 0⟩
theorem s6_29_edges : next config 6 s6_29 = [s7_231, s7_5, s7_23] := by decide
theorem s6_29_safe : Safe 7 6 s6_29 := by
  apply safe_succ 6 6 s6_29 [s7_231, s7_5, s7_23] (by decide) s6_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_231_safe
  · subst z; exact s7_5_safe
  · subst z; exact s7_23_safe
def s6_30 : State := ⟨[1,4,67,129], 1020847100762815390556144518962985636126, 3, 3, 1, 0⟩
theorem s6_30_edges : next config 6 s6_30 = [s7_6] := by decide
theorem s6_30_safe : Safe 7 6 s6_30 := by
  apply safe_succ 6 6 s6_30 [s7_6] (by decide) s6_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_6_safe
def s6_31 : State := ⟨[1,4,67,130], 1701411834604692317482893733826522059038, 3, 3, 1, 0⟩
theorem s6_31_edges : next config 6 s6_31 = [s7_14, s7_16] := by decide
theorem s6_31_safe : Safe 7 6 s6_31 := by
  apply safe_succ 6 6 s6_31 [s7_14, s7_16] (by decide) s6_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_14_safe
  · subst z; exact s7_16_safe
def s6_32 : State := ⟨[1,4,67,131], 3062541302288446171336392163553594904862, 3, 3, 1, 0⟩
theorem s6_32_edges : next config 6 s6_32 = [s7_18] := by decide
theorem s6_32_safe : Safe 7 6 s6_32 := by
  apply safe_succ 6 6 s6_32 [s7_18] (by decide) s6_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_18_safe
def s6_33 : State := ⟨[1,4,67,132], 5784800237655953879043389023007740596510, 3, 3, 1, 0⟩
theorem s6_33_edges : next config 6 s6_33 = [] := by decide
theorem s6_33_safe : Safe 7 6 s6_33 := by
  apply safe_succ 6 6 s6_33 [] (by decide) s6_33_edges
  simp
def s6_34 : State := ⟨[1,4,67,136], 87452568298681185110253294806632111345950, 3, 3, 1, 0⟩
theorem s6_34_edges : next config 6 s6_34 = [] := by decide
theorem s6_34_safe : Safe 7 6 s6_34 := by
  apply safe_succ 6 6 s6_34 [] (by decide) s6_34_edges
  simp
def s6_35 : State := ⟨[1,4,67,136], 1481249143206845131456235686847154705465630, 3, 3, 1, 0⟩
theorem s6_35_edges : next config 6 s6_35 = [] := by decide
theorem s6_35_safe : Safe 7 6 s6_35 := by
  apply safe_succ 6 6 s6_35 [] (by decide) s6_35_edges
  simp
def s6_36 : State := ⟨[1,4,67,140], 1394136857275084884809611787344622043336990, 3, 3, 1, 0⟩
theorem s6_36_edges : next config 6 s6_36 = [] := by decide
theorem s6_36_safe : Safe 7 6 s6_36 := by
  apply safe_succ 6 6 s6_36 [] (by decide) s6_36_edges
  simp
def s6_37 : State := ⟨[1,4,67,144], 22301085480897544079999347667952460955193630, 3, 3, 1, 0⟩
theorem s6_37_edges : next config 6 s6_37 = [s7_7, s7_15, s7_20] := by decide
theorem s6_37_safe : Safe 7 6 s6_37 := by
  apply safe_succ 6 6 s6_37 [s7_7, s7_15, s7_20] (by decide) s6_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_7_safe
  · subst z; exact s7_15_safe
  · subst z; exact s7_20_safe
def s6_38 : State := ⟨[1,4,67,145], 44601830679428167226370843006035633998332182, 1, 1, 1, 0⟩
theorem s6_38_edges : next config 6 s6_38 = [s7_232] := by decide
theorem s6_38_safe : Safe 7 6 s6_38 := by
  apply safe_succ 6 6 s6_38 [s7_232] (by decide) s6_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_232_safe
def s6_39 : State := ⟨[1,4,67,145], 44601830679428167227579695038673968334831894, 1, 1, 1, 0⟩
theorem s6_39_edges : next config 6 s6_39 = [s7_233] := by decide
theorem s6_39_safe : Safe 7 6 s6_39 := by
  apply safe_succ 6 6 s6_39 [s7_233] (by decide) s6_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_233_safe
def s6_40 : State := ⟨[1,4,67,145], 44602511244162009098462029583303833416700182, 2, 2, 1, 0⟩
theorem s6_40_edges : next config 6 s6_40 = [] := by decide
theorem s6_40_safe : Safe 7 6 s6_40 := by
  apply safe_succ 6 6 s6_40 [] (by decide) s6_40_edges
  simp
def s6_41 : State := ⟨[1,4,67,145], 44602511244162009098462066476791980835803414, 2, 2, 1, 0⟩
theorem s6_41_edges : next config 6 s6_41 = [] := by decide
theorem s6_41_safe : Safe 7 6 s6_41 := by
  apply safe_succ 6 6 s6_41 [] (by decide) s6_41_edges
  simp
def s6_42 : State := ⟨[1,4,67,145], 66902575877958790363070821106737331386257686, 2, 2, 1, 0⟩
theorem s6_42_edges : next config 6 s6_42 = [] := by decide
theorem s6_42_safe : Safe 7 6 s6_42 := by
  apply safe_succ 6 6 s6_42 [] (by decide) s6_42_edges
  simp
def s6_43 : State := ⟨[1,4,67,145], 66902575877958790363070858000225478805360918, 2, 2, 1, 0⟩
theorem s6_43_edges : next config 6 s6_43 = [] := by decide
theorem s6_43_safe : Safe 7 6 s6_43 := by
  apply safe_succ 6 6 s6_43 [] (by decide) s6_43_edges
  simp
def s6_44 : State := ⟨[1,4,67,145], 133806172603018343541531792529623995557937438, 1, 1, 1, 0⟩
theorem s6_44_edges : next config 6 s6_44 = [s7_234] := by decide
theorem s6_44_safe : Safe 7 6 s6_44 := by
  apply safe_succ 6 6 s6_44 [s7_234] (by decide) s6_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_234_safe
def s6_45 : State := ⟨[1,4,67,145], 156105556672081282929213657303842629991072030, 1, 1, 1, 0⟩
theorem s6_45_edges : next config 6 s6_45 = [s7_235] := by decide
theorem s6_45_safe : Safe 7 6 s6_45 := by
  apply safe_succ 6 6 s6_45 [s7_235] (by decide) s6_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_235_safe
def s6_46 : State := ⟨[1,4,67,146], 89204682205957097258460392877815419965083926, 2, 2, 1, 0⟩
theorem s6_46_edges : next config 6 s6_46 = [] := by decide
theorem s6_46_safe : Safe 7 6 s6_46 := by
  apply safe_succ 6 6 s6_46 [] (by decide) s6_46_edges
  simp
def s6_47 : State := ⟨[1,4,67,146], 89204682205957097258460429771303567384187158, 2, 2, 1, 0⟩
theorem s6_47_edges : next config 6 s6_47 = [] := by decide
theorem s6_47_safe : Safe 7 6 s6_47 := by
  apply safe_succ 6 6 s6_47 [] (by decide) s6_47_edges
  simp
def s6_48 : State := ⟨[1,4,67,146], 111504066275020036646142257652034054398218518, 2, 2, 1, 0⟩
theorem s6_48_edges : next config 6 s6_48 = [] := by decide
theorem s6_48_safe : Safe 7 6 s6_48 := by
  apply safe_succ 6 6 s6_48 [] (by decide) s6_48_edges
  simp
def s6_49 : State := ⟨[1,4,67,146], 111504066275020036646142294545522201817321750, 2, 2, 1, 0⟩
theorem s6_49_edges : next config 6 s6_49 = [] := by decide
theorem s6_49_safe : Safe 7 6 s6_49 := by
  apply safe_succ 6 6 s6_49 [] (by decide) s6_49_edges
  simp
def s6_50 : State := ⟨[1,4,67,160], 1461501637671185285124623296345678323755381756190, 3, 3, 1, 0⟩
theorem s6_50_edges : next config 6 s6_50 = [s7_17, s7_21] := by decide
theorem s6_50_safe : Safe 7 6 s6_50 := by
  apply safe_succ 6 6 s6_50 [s7_17, s7_21] (by decide) s6_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_17_safe
  · subst z; exact s7_21_safe
def s6_51 : State := ⟨[1,4,67,162], 5846006551025023507419431648384919300597671334166, 2, 2, 1, 0⟩
theorem s6_51_edges : next config 6 s6_51 = [] := by decide
theorem s6_51_safe : Safe 7 6 s6_51 := by
  apply safe_succ 6 6 s6_51 [] (by decide) s6_51_edges
  simp
def s6_52 : State := ⟨[1,4,67,162], 5846006551025023507419431648421812788745090437398, 2, 2, 1, 0⟩
theorem s6_52_edges : next config 6 s6_52 = [] := by decide
theorem s6_52_safe : Safe 7 6 s6_52 := by
  apply safe_succ 6 6 s6_52 [] (by decide) s6_52_edges
  simp
def s6_53 : State := ⟨[1,4,67,162], 7307508186994796957939362627247703890526531031318, 2, 2, 1, 0⟩
theorem s6_53_edges : next config 6 s6_53 = [] := by decide
theorem s6_53_safe : Safe 7 6 s6_53 := by
  apply safe_succ 6 6 s6_53 [] (by decide) s6_53_edges
  simp
def s6_54 : State := ⟨[1,4,67,162], 7307508186994796957939362627284597378673950134550, 2, 2, 1, 0⟩
theorem s6_54_edges : next config 6 s6_54 = [] := by decide
theorem s6_54_safe : Safe 7 6 s6_54 := by
  apply safe_succ 6 6 s6_54 [] (by decide) s6_54_edges
  simp
def s6_55 : State := ⟨[1,4,67,171], 3004847366355398941129064462236014280576150903259422, 1, 1, 1, 0⟩
theorem s6_55_edges : next config 6 s6_55 = [] := by decide
theorem s6_55_safe : Safe 7 6 s6_55 := by
  apply safe_succ 6 6 s6_55 [] (by decide) s6_55_edges
  simp
def s6_56 : State := ⟨[1,4,67,171], 3006308867990007585111900639361023566736352690110750, 1, 1, 1, 0⟩
theorem s6_56_edges : next config 6 s6_56 = [] := by decide
theorem s6_56_safe : Safe 7 6 s6_56 := by
  apply safe_succ 6 6 s6_56 [] (by decide) s6_56_edges
  simp
def s6_57 : State := ⟨[1,4,67,176], 95780971326419139128294233276893708537611803510771990, 2, 2, 1, 0⟩
theorem s6_57_edges : next config 6 s6_57 = [] := by decide
theorem s6_57_safe : Safe 7 6 s6_57 := by
  apply safe_succ 6 6 s6_57 [] (by decide) s6_57_edges
  simp
def s6_58 : State := ⟨[1,4,67,176], 95780971326419139128294233276893745431099950929875222, 2, 2, 1, 0⟩
theorem s6_58_edges : next config 6 s6_58 = [] := by decide
theorem s6_58_safe : Safe 7 6 s6_58 := by
  apply safe_succ 6 6 s6_58 [] (by decide) s6_58_edges
  simp
def s6_59 : State := ⟨[1,4,67,176], 95782432805755724832681813820190706547983097937334550, 2, 2, 1, 0⟩
theorem s6_59_edges : next config 6 s6_59 = [] := by decide
theorem s6_59_safe : Safe 7 6 s6_59 := by
  apply safe_succ 6 6 s6_59 [] (by decide) s6_59_edges
  simp
def s6_60 : State := ⟨[1,4,67,176], 95782432805755724832681813820190743441471245356437782, 2, 2, 1, 0⟩
theorem s6_60_edges : next config 6 s6_60 = [] := by decide
theorem s6_60_safe : Safe 7 6 s6_60 := by
  apply safe_succ 6 6 s6_60 [] (by decide) s6_60_edges
  simp
def s6_61 : State := ⟨[1,4,67,192], 6277101735386680764176071790128604879731750748563483726110, 3, 3, 1, 0⟩
theorem s6_61_edges : next config 6 s6_61 = [] := by decide
theorem s6_61_safe : Safe 7 6 s6_61 := by
  apply safe_succ 6 6 s6_61 [] (by decide) s6_61_edges
  simp
def s6_62 : State := ⟨[1,4,67,195], 50216813883093446111026597752582269792448238859811725316382, 3, 3, 1, 0⟩
theorem s6_62_edges : next config 6 s6_62 = [] := by decide
theorem s6_62_safe : Safe 7 6 s6_62 := by
  apply safe_succ 6 6 s6_62 [] (by decide) s6_62_edges
  simp
def s6_63 : State := ⟨[1,4,67,210], 1645504557321206042177270268038248049062735287088508619142009110, 2, 2, 1, 0⟩
theorem s6_63_edges : next config 6 s6_63 = [s7_8] := by decide
theorem s6_63_safe : Safe 7 6 s6_63 := by
  apply safe_succ 6 6 s6_63 [s7_8] (by decide) s6_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_8_safe
def s6_64 : State := ⟨[1,4,67,210], 1645529665728147588878024865997410256586863978237638113774080278, 2, 2, 1, 0⟩
theorem s6_64_edges : next config 6 s6_64 = [s7_9] := by decide
theorem s6_64_safe : Safe 7 6 s6_64 := by
  apply safe_succ 6 6 s6_64 [s7_9] (by decide) s6_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_9_safe
def s6_65 : State := ⟨[1,4,67,210], 27973577474460502716656777188955856128786509137225786432719749398, 2, 2, 1, 0⟩
theorem s6_65_edges : next config 6 s6_65 = [s7_11] := by decide
theorem s6_65_safe : Safe 7 6 s6_65 := by
  apply safe_succ 6 6 s6_65 [s7_11] (by decide) s6_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_11_safe
def s6_66 : State := ⟨[1,4,67,210], 27973602582867444263357531786915018336310637828374915927351820566, 2, 2, 1, 0⟩
theorem s6_66_edges : next config 6 s6_66 = [s7_12] := by decide
theorem s6_66_safe : Safe 7 6 s6_66 := by
  apply safe_succ 6 6 s6_66 [s7_12] (by decide) s6_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_12_safe
def s6_67 : State := ⟨[1,4,68,145], 44601830679428167221535213514553412139811094, 3, 3, 1, 0⟩
theorem s6_67_edges : next config 6 s6_67 = [] := by decide
theorem s6_67_safe : Safe 7 6 s6_67 := by
  apply safe_succ 6 6 s6_67 [] (by decide) s6_67_edges
  simp
def s6_68 : State := ⟨[1,4,80,145], 44601830679428167222743844186262861959598358, 3, 3, 1, 0⟩
theorem s6_68_edges : next config 6 s6_68 = [s7_24] := by decide
theorem s6_68_safe : Safe 7 6 s6_68 := by
  apply safe_succ 6 6 s6_68 [s7_24] (by decide) s6_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_24_safe
def s6_69 : State := ⟨[1,4,80,145], 44601830679428167222743844186262861961691414, 3, 3, 1, 0⟩
theorem s6_69_edges : next config 6 s6_69 = [s7_236, s7_25] := by decide
theorem s6_69_safe : Safe 7 6 s6_69 := by
  apply safe_succ 6 6 s6_69 [s7_236, s7_25] (by decide) s6_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_236_safe
  · subst z; exact s7_25_safe
def s6_70 : State := ⟨[1,4,81,145], 44601830679428167223952770005877491134304534, 3, 3, 1, 0⟩
theorem s6_70_edges : next config 6 s6_70 = [] := by decide
theorem s6_70_safe : Safe 7 6 s6_70 := by
  apply safe_succ 6 6 s6_70 [] (by decide) s6_70_edges
  simp
def s6_71 : State := ⟨[1,4,81,145], 44601830679428167223952770005877491136397590, 3, 3, 1, 0⟩
theorem s6_71_edges : next config 6 s6_71 = [s7_237] := by decide
theorem s6_71_safe : Safe 7 6 s6_71 := by
  apply safe_succ 6 6 s6_71 [s7_237] (by decide) s6_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_237_safe
def s6_72 : State := ⟨[1,4,82,145], 44602511244162009103297622181297907858215190, 2, 2, 1, 0⟩
theorem s6_72_edges : next config 6 s6_72 = [] := by decide
theorem s6_72_safe : Safe 7 6 s6_72 := by
  apply safe_succ 6 6 s6_72 [] (by decide) s6_72_edges
  simp
def s6_73 : State := ⟨[1,4,82,145], 44602511244162009104506474213936242194714902, 2, 2, 1, 0⟩
theorem s6_73_edges : next config 6 s6_73 = [] := by decide
theorem s6_73_safe : Safe 7 6 s6_73 := by
  apply safe_succ 6 6 s6_73 [] (by decide) s6_73_edges
  simp
def s6_74 : State := ⟨[1,4,82,145], 44602511244162009180668874636634175039406358, 2, 2, 1, 0⟩
theorem s6_74_edges : next config 6 s6_74 = [] := by decide
theorem s6_74_safe : Safe 7 6 s6_74 := by
  apply safe_succ 6 6 s6_74 [] (by decide) s6_74_edges
  simp
def s6_75 : State := ⟨[1,4,82,145], 44602511244162009181877726669272509375906070, 2, 2, 1, 0⟩
theorem s6_75_edges : next config 6 s6_75 = [] := by decide
theorem s6_75_safe : Safe 7 6 s6_75 := by
  apply safe_succ 6 6 s6_75 [] (by decide) s6_75_edges
  simp
def s6_76 : State := ⟨[1,4,82,145], 66902575877958790367906413704731405827772694, 2, 2, 1, 0⟩
theorem s6_76_edges : next config 6 s6_76 = [] := by decide
theorem s6_76_safe : Safe 7 6 s6_76 := by
  apply safe_succ 6 6 s6_76 [] (by decide) s6_76_edges
  simp
def s6_77 : State := ⟨[1,4,82,145], 66902575877958790369115265737369740164272406, 2, 2, 1, 0⟩
theorem s6_77_edges : next config 6 s6_77 = [] := by decide
theorem s6_77_safe : Safe 7 6 s6_77 := by
  apply safe_succ 6 6 s6_77 [] (by decide) s6_77_edges
  simp
def s6_78 : State := ⟨[1,4,82,145], 66902575877958790445277666160067673008963862, 2, 2, 1, 0⟩
theorem s6_78_edges : next config 6 s6_78 = [] := by decide
theorem s6_78_safe : Safe 7 6 s6_78 := by
  apply safe_succ 6 6 s6_78 [] (by decide) s6_78_edges
  simp
def s6_79 : State := ⟨[1,4,82,145], 66902575877958790446486518192706007345463574, 2, 2, 1, 0⟩
theorem s6_79_edges : next config 6 s6_79 = [] := by decide
theorem s6_79_safe : Safe 7 6 s6_79 := by
  apply safe_succ 6 6 s6_79 [] (by decide) s6_79_edges
  simp
def s6_80 : State := ⟨[1,4,86,145], 44601830679428167303741947887419311503114518, 1, 1, 1, 0⟩
theorem s6_80_edges : next config 6 s6_80 = [] := by decide
theorem s6_80_safe : Safe 7 6 s6_80 := by
  apply safe_succ 6 6 s6_80 [] (by decide) s6_80_edges
  simp
def s6_81 : State := ⟨[1,4,86,145], 44601830679428167304950799920057645839614230, 1, 1, 1, 0⟩
theorem s6_81_edges : next config 6 s6_81 = [] := by decide
theorem s6_81_safe : Safe 7 6 s6_81 := by
  apply safe_succ 6 6 s6_81 [] (by decide) s6_81_edges
  simp
def s6_82 : State := ⟨[1,4,96,129], 1020847100842043552922834903966853173534, 3, 3, 1, 0⟩
theorem s6_82_edges : next config 6 s6_82 = [s7_65, s7_28] := by decide
theorem s6_82_safe : Safe 7 6 s6_82 := by
  apply safe_succ 6 6 s6_82 [s7_65, s7_28] (by decide) s6_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_65_safe
  · subst z; exact s7_28_safe
def s6_83 : State := ⟨[1,4,96,129], 1020847100842043552922834903975443108118, 3, 3, 1, 0⟩
theorem s6_83_edges : next config 6 s6_83 = [s7_66, s7_29] := by decide
theorem s6_83_safe : Safe 7 6 s6_83 := by
  apply safe_succ 6 6 s6_83 [s7_66, s7_29] (by decide) s6_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_66_safe
  · subst z; exact s7_29_safe
def s6_84 : State := ⟨[1,4,96,129], 1020847100842043552959728392114272276758, 3, 3, 1, 0⟩
theorem s6_84_edges : next config 6 s6_84 = [s7_67, s7_30] := by decide
theorem s6_84_safe : Safe 7 6 s6_84 := by
  apply safe_succ 6 6 s6_84 [s7_67, s7_30] (by decide) s6_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_67_safe
  · subst z; exact s7_30_safe
def s6_85 : State := ⟨[1,4,96,129], 1020847101000499877951363579153941074198, 3, 3, 1, 0⟩
theorem s6_85_edges : next config 6 s6_85 = [s7_68, s7_31] := by decide
theorem s6_85_safe : Safe 7 6 s6_85 := by
  apply safe_succ 6 6 s6_85 [s7_68, s7_31] (by decide) s6_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_68_safe
  · subst z; exact s7_31_safe
def s6_86 : State := ⟨[1,4,96,129], 1020847102109694153151064305463556374814, 3, 3, 1, 0⟩
theorem s6_86_edges : next config 6 s6_86 = [s7_69, s7_32] := by decide
theorem s6_86_safe : Safe 7 6 s6_86 := by
  apply safe_succ 6 6 s6_86 [s7_69, s7_32] (by decide) s6_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_69_safe
  · subst z; exact s7_32_safe
def s6_87 : State := ⟨[1,4,96,129], 1020847102109694153187957793610975478038, 3, 3, 1, 0⟩
theorem s6_87_edges : next config 6 s6_87 = [s7_70, s7_33] := by decide
theorem s6_87_safe : Safe 7 6 s6_87 := by
  apply safe_succ 6 6 s6_87 [s7_70, s7_33] (by decide) s6_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_70_safe
  · subst z; exact s7_33_safe
def s6_88 : State := ⟨[1,4,96,130], 1701411834683920479849584118830389596446, 3, 3, 1, 0⟩
theorem s6_88_edges : next config 6 s6_88 = [s7_73, s7_40, s7_45] := by decide
theorem s6_88_safe : Safe 7 6 s6_88 := by
  apply safe_succ 6 6 s6_88 [s7_73, s7_40, s7_45] (by decide) s6_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_73_safe
  · subst z; exact s7_40_safe
  · subst z; exact s7_45_safe
def s6_89 : State := ⟨[1,4,96,130], 1701411834683920479849584118838979531030, 3, 3, 1, 0⟩
theorem s6_89_edges : next config 6 s6_89 = [s7_74] := by decide
theorem s6_89_safe : Safe 7 6 s6_89 := by
  apply safe_succ 6 6 s6_89 [s7_74] (by decide) s6_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_74_safe
def s6_90 : State := ⟨[1,4,96,130], 1701411834683920479886477606977808699670, 3, 3, 1, 0⟩
theorem s6_90_edges : next config 6 s6_90 = [s7_75, s7_41, s7_46] := by decide
theorem s6_90_safe : Safe 7 6 s6_90 := by
  apply safe_succ 6 6 s6_90 [s7_75, s7_41, s7_46] (by decide) s6_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_75_safe
  · subst z; exact s7_41_safe
  · subst z; exact s7_46_safe
def s6_91 : State := ⟨[1,4,96,130], 1701411834842376804878112794017477497110, 3, 3, 1, 0⟩
theorem s6_91_edges : next config 6 s6_91 = [s7_76, s7_47] := by decide
theorem s6_91_safe : Safe 7 6 s6_91 := by
  apply safe_succ 6 6 s6_91 [s7_76, s7_47] (by decide) s6_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_76_safe
  · subst z; exact s7_47_safe
def s6_92 : State := ⟨[1,4,96,130], 1701411835951571080077813520327092797726, 3, 3, 1, 0⟩
theorem s6_92_edges : next config 6 s6_92 = [s7_77] := by decide
theorem s6_92_safe : Safe 7 6 s6_92 := by
  apply safe_succ 6 6 s6_92 [s7_77] (by decide) s6_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_77_safe
def s6_93 : State := ⟨[1,4,96,130], 1701411835951571080114707008474511900950, 3, 3, 1, 0⟩
theorem s6_93_edges : next config 6 s6_93 = [s7_78] := by decide
theorem s6_93_safe : Safe 7 6 s6_93 := by
  apply safe_succ 6 6 s6_93 [s7_78] (by decide) s6_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_78_safe
def s6_94 : State := ⟨[1,4,96,130], 4423670770051428187556580978284535288086, 3, 3, 1, 0⟩
theorem s6_94_edges : next config 6 s6_94 = [s7_81, s7_42, s7_48] := by decide
theorem s6_94_safe : Safe 7 6 s6_94 := by
  apply safe_succ 6 6 s6_94 [s7_81, s7_42, s7_48] (by decide) s6_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_81_safe
  · subst z; exact s7_42_safe
  · subst z; exact s7_48_safe
def s6_95 : State := ⟨[1,4,96,130], 4423670771319078787784810379781238489366, 3, 3, 1, 0⟩
theorem s6_95_edges : next config 6 s6_95 = [s7_82] := by decide
theorem s6_95_safe : Safe 7 6 s6_95 := by
  apply safe_succ 6 6 s6_95 [s7_82] (by decide) s6_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_82_safe
def s6_96 : State := ⟨[1,4,96,131], 3062541302367674333703082548557462442270, 3, 3, 1, 0⟩
theorem s6_96_edges : next config 6 s6_96 = [s7_84, s7_55] := by decide
theorem s6_96_safe : Safe 7 6 s6_96 := by
  apply safe_succ 6 6 s6_96 [s7_84, s7_55] (by decide) s6_96_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_84_safe
  · subst z; exact s7_55_safe
def s6_97 : State := ⟨[1,4,96,131], 3062541303635324933931311950054165643550, 3, 3, 1, 0⟩
theorem s6_97_edges : next config 6 s6_97 = [s7_85] := by decide
theorem s6_97_safe : Safe 7 6 s6_97 := by
  apply safe_succ 6 6 s6_97 [s7_85] (by decide) s6_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_85_safe
def s6_98 : State := ⟨[1,4,96,132], 5784800237735182041410079408011608133918, 3, 3, 1, 0⟩
theorem s6_98_edges : next config 6 s6_98 = [s7_87] := by decide
theorem s6_98_safe : Safe 7 6 s6_98 := by
  apply safe_succ 6 6 s6_98 [s7_87] (by decide) s6_98_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_87_safe
def s6_99 : State := ⟨[1,4,96,132], 5784800237735182041410079408020198068502, 3, 3, 1, 0⟩
theorem s6_99_edges : next config 6 s6_99 = [s7_88] := by decide
theorem s6_99_safe : Safe 7 6 s6_99 := by
  apply safe_succ 6 6 s6_99 [s7_88] (by decide) s6_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_88_safe
def s6_100 : State := ⟨[1,4,96,132], 5784800237735182041446972896159027237142, 3, 3, 1, 0⟩
theorem s6_100_edges : next config 6 s6_100 = [s7_89] := by decide
theorem s6_100_safe : Safe 7 6 s6_100 := by
  apply safe_succ 6 6 s6_100 [s7_89] (by decide) s6_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_89_safe
def s6_101 : State := ⟨[1,4,96,132], 5784800237893638366438608083198696034582, 3, 3, 1, 0⟩
theorem s6_101_edges : next config 6 s6_101 = [s7_90] := by decide
theorem s6_101_safe : Safe 7 6 s6_101 := by
  apply safe_succ 6 6 s6_101 [s7_90] (by decide) s6_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_90_safe
def s6_102 : State := ⟨[1,4,96,132], 5784800239002832641638308809508311335198, 3, 3, 1, 0⟩
theorem s6_102_edges : next config 6 s6_102 = [s7_91] := by decide
theorem s6_102_safe : Safe 7 6 s6_102 := by
  apply safe_succ 6 6 s6_102 [s7_91] (by decide) s6_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_91_safe
def s6_103 : State := ⟨[1,4,96,132], 5784800239002832641675202297655730438422, 3, 3, 1, 0⟩
theorem s6_103_edges : next config 6 s6_103 = [s7_92] := by decide
theorem s6_103_safe : Safe 7 6 s6_103 := by
  apply safe_succ 6 6 s6_103 [s7_92] (by decide) s6_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_92_safe
def s6_104 : State := ⟨[1,4,96,136], 87452568298760413272619985191635978883358, 3, 3, 1, 0⟩
theorem s6_104_edges : next config 6 s6_104 = [s7_95] := by decide
theorem s6_104_safe : Safe 7 6 s6_104 := by
  apply safe_succ 6 6 s6_104 [s7_95] (by decide) s6_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_95_safe
def s6_105 : State := ⟨[1,4,96,136], 87452568298760413272619985191644568817942, 3, 3, 1, 0⟩
theorem s6_105_edges : next config 6 s6_105 = [s7_96] := by decide
theorem s6_105_safe : Safe 7 6 s6_105 := by
  apply safe_succ 6 6 s6_105 [s7_96] (by decide) s6_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_96_safe
def s6_106 : State := ⟨[1,4,96,136], 87452568298760413272656878679783397986582, 3, 3, 1, 0⟩
theorem s6_106_edges : next config 6 s6_106 = [s7_97] := by decide
theorem s6_106_safe : Safe 7 6 s6_106 := by
  apply safe_succ 6 6 s6_106 [s7_97] (by decide) s6_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_97_safe
def s6_107 : State := ⟨[1,4,96,136], 87452568298918869597648513866823066784022, 3, 3, 1, 0⟩
theorem s6_107_edges : next config 6 s6_107 = [s7_98] := by decide
theorem s6_107_safe : Safe 7 6 s6_107 := by
  apply safe_succ 6 6 s6_107 [s7_98] (by decide) s6_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_98_safe
def s6_108 : State := ⟨[1,4,96,136], 87452568300028063872848214593132682084638, 3, 3, 1, 0⟩
theorem s6_108_edges : next config 6 s6_108 = [s7_99] := by decide
theorem s6_108_safe : Safe 7 6 s6_108 := by
  apply safe_succ 6 6 s6_108 [s7_99] (by decide) s6_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_99_safe
def s6_109 : State := ⟨[1,4,96,136], 87452568300028063872885108081280101187862, 3, 3, 1, 0⟩
theorem s6_109_edges : next config 6 s6_109 = [s7_100] := by decide
theorem s6_109_safe : Safe 7 6 s6_109 := by
  apply safe_succ 6 6 s6_109 [s7_100] (by decide) s6_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_100_safe
def s6_110 : State := ⟨[1,4,96,136], 1481249143206924359618602377232158573003038, 3, 3, 1, 0⟩
theorem s6_110_edges : next config 6 s6_110 = [s7_103] := by decide
theorem s6_110_safe : Safe 7 6 s6_110 := by
  apply safe_succ 6 6 s6_110 [s7_103] (by decide) s6_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_103_safe
def s6_111 : State := ⟨[1,4,96,136], 1481249143206924359618602377232167162937622, 3, 3, 1, 0⟩
theorem s6_111_edges : next config 6 s6_111 = [s7_104] := by decide
theorem s6_111_safe : Safe 7 6 s6_111 := by
  apply safe_succ 6 6 s6_111 [s7_104] (by decide) s6_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_104_safe
def s6_112 : State := ⟨[1,4,96,136], 1481249143206924359618639270720305992106262, 3, 3, 1, 0⟩
theorem s6_112_edges : next config 6 s6_112 = [s7_105] := by decide
theorem s6_112_safe : Safe 7 6 s6_112 := by
  apply safe_succ 6 6 s6_112 [s7_105] (by decide) s6_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_105_safe
def s6_113 : State := ⟨[1,4,96,136], 1481249143207082815943630905907345660903702, 3, 3, 1, 0⟩
theorem s6_113_edges : next config 6 s6_113 = [s7_106] := by decide
theorem s6_113_safe : Safe 7 6 s6_113 := by
  apply safe_succ 6 6 s6_113 [s7_106] (by decide) s6_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_106_safe
def s6_114 : State := ⟨[1,4,96,140], 1394136857275164112971978477729625910874398, 3, 3, 1, 0⟩
theorem s6_114_edges : next config 6 s6_114 = [s7_107] := by decide
theorem s6_114_safe : Safe 7 6 s6_114 := by
  apply safe_succ 6 6 s6_114 [s7_107] (by decide) s6_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_107_safe
def s6_115 : State := ⟨[1,4,96,140], 1394136857275164112971978477729634500808982, 3, 3, 1, 0⟩
theorem s6_115_edges : next config 6 s6_115 = [s7_108] := by decide
theorem s6_115_safe : Safe 7 6 s6_115 := by
  apply safe_succ 6 6 s6_115 [s7_108] (by decide) s6_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_108_safe
def s6_116 : State := ⟨[1,4,96,140], 1394136857275164112972015371217773329977622, 3, 3, 1, 0⟩
theorem s6_116_edges : next config 6 s6_116 = [s7_109] := by decide
theorem s6_116_safe : Safe 7 6 s6_116 := by
  apply safe_succ 6 6 s6_116 [s7_109] (by decide) s6_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_109_safe
def s6_117 : State := ⟨[1,4,96,140], 1394136857275322569297007006404812998775062, 3, 3, 1, 0⟩
theorem s6_117_edges : next config 6 s6_117 = [s7_110] := by decide
theorem s6_117_safe : Safe 7 6 s6_117 := by
  apply safe_succ 6 6 s6_117 [s7_110] (by decide) s6_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_110_safe
def s6_118 : State := ⟨[1,4,96,144], 22301085480897623308161714358337464822731038, 3, 3, 1, 0⟩
theorem s6_118_edges : next config 6 s6_118 = [s7_111, s7_34, s7_43, s7_58] := by decide
theorem s6_118_safe : Safe 7 6 s6_118 := by
  apply safe_succ 6 6 s6_118 [s7_111, s7_34, s7_43, s7_58] (by decide) s6_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_111_safe
  · subst z; exact s7_34_safe
  · subst z; exact s7_43_safe
  · subst z; exact s7_58_safe
def s6_119 : State := ⟨[1,4,96,144], 22301085480897623308161714358337473412665622, 3, 3, 1, 0⟩
theorem s6_119_edges : next config 6 s6_119 = [s7_112, s7_35] := by decide
theorem s6_119_safe : Safe 7 6 s6_119 := by
  apply safe_succ 6 6 s6_119 [s7_112, s7_35] (by decide) s6_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_112_safe
  · subst z; exact s7_35_safe
def s6_120 : State := ⟨[1,4,96,144], 22301085480897623308161751251825612241834262, 3, 3, 1, 0⟩
theorem s6_120_edges : next config 6 s6_120 = [s7_113, s7_36, s7_44, s7_59] := by decide
theorem s6_120_safe : Safe 7 6 s6_120 := by
  apply safe_succ 6 6 s6_120 [s7_113, s7_36, s7_44, s7_59] (by decide) s6_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_113_safe
  · subst z; exact s7_36_safe
  · subst z; exact s7_44_safe
  · subst z; exact s7_59_safe
def s6_121 : State := ⟨[1,4,96,144], 22301085480897781764486742887012651910631702, 3, 3, 1, 0⟩
theorem s6_121_edges : next config 6 s6_121 = [s7_114, s7_37] := by decide
theorem s6_121_safe : Safe 7 6 s6_121 := by
  apply safe_succ 6 6 s6_121 [s7_114, s7_37] (by decide) s6_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_114_safe
  · subst z; exact s7_37_safe
def s6_122 : State := ⟨[1,4,96,144], 22301085480898890958761942587738961525932318, 3, 3, 1, 0⟩
theorem s6_122_edges : next config 6 s6_122 = [s7_115, s7_38] := by decide
theorem s6_122_safe : Safe 7 6 s6_122 := by
  apply safe_succ 6 6 s6_122 [s7_115, s7_38] (by decide) s6_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_115_safe
  · subst z; exact s7_38_safe
def s6_123 : State := ⟨[1,4,96,144], 22301085480898890958761979481227108945035542, 3, 3, 1, 0⟩
theorem s6_123_edges : next config 6 s6_123 = [s7_116, s7_39] := by decide
theorem s6_123_safe : Safe 7 6 s6_123 := by
  apply safe_succ 6 6 s6_123 [s7_116, s7_39] (by decide) s6_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_116_safe
  · subst z; exact s7_39_safe
def s6_124 : State := ⟨[1,4,96,145], 44601830679428246449697432630985826328842518, 3, 3, 1, 0⟩
theorem s6_124_edges : next config 6 s6_124 = [s7_839, s7_317, s7_598, s7_62, s7_224, s7_119, s7_218] := by decide
theorem s6_124_safe : Safe 7 6 s6_124 := by
  apply safe_succ 6 6 s6_124 [s7_839, s7_317, s7_598, s7_62, s7_224, s7_119, s7_218] (by decide) s6_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_839_safe
  · subst z; exact s7_317_safe
  · subst z; exact s7_598_safe
  · subst z; exact s7_62_safe
  · subst z; exact s7_224_safe
  · subst z; exact s7_119_safe
  · subst z; exact s7_218_safe
def s6_125 : State := ⟨[1,4,96,145], 44601830679428246449697432630985826330935574, 3, 3, 1, 0⟩
theorem s6_125_edges : next config 6 s6_125 = [s7_840, s7_318, s7_365, s7_599, s7_302, s7_238, s7_63, s7_64, s7_225, s7_120, s7_219] := by decide
theorem s6_125_safe : Safe 7 6 s6_125 := by
  apply safe_succ 6 6 s6_125 [s7_840, s7_318, s7_365, s7_599, s7_302, s7_238, s7_63, s7_64, s7_225, s7_120, s7_219] (by decide) s6_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s7_840_safe
  · subst z; exact s7_318_safe
  · subst z; exact s7_365_safe
  · subst z; exact s7_599_safe
  · subst z; exact s7_302_safe
  · subst z; exact s7_238_safe
  · subst z; exact s7_63_safe
  · subst z; exact s7_64_safe
  · subst z; exact s7_225_safe
  · subst z; exact s7_120_safe
  · subst z; exact s7_219_safe
def s6_126 : State := ⟨[1,4,96,145], 44601830679428246449697727778891005681664278, 3, 3, 1, 0⟩
theorem s6_126_edges : next config 6 s6_126 = [s7_121] := by decide
theorem s6_126_safe : Safe 7 6 s6_126 := by
  apply safe_succ 6 6 s6_126 [s7_121] (by decide) s6_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_121_safe
def s6_127 : State := ⟨[1,4,96,145], 44601830679429514100297660860387323032043798, 3, 3, 1, 0⟩
theorem s6_127_edges : next config 6 s6_127 = [s7_319, s7_122] := by decide
theorem s6_127_safe : Safe 7 6 s6_127 := by
  apply safe_succ 6 6 s6_127 [s7_319, s7_122] (by decide) s6_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_319_safe
  · subst z; exact s7_122_safe
def s6_128 : State := ⟨[1,4,96,145], 133806172603018422769694159220008999425474846, 1, 1, 1, 0⟩
theorem s6_128_edges : next config 6 s6_128 = [s7_239, s7_124] := by decide
theorem s6_128_safe : Safe 7 6 s6_128 := by
  apply safe_succ 6 6 s6_128 [s7_239, s7_124] (by decide) s6_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_239_safe
  · subst z; exact s7_124_safe
def s6_129 : State := ⟨[1,4,96,145], 156105556672081362157376023994227633858609438, 1, 1, 1, 0⟩
theorem s6_129_edges : next config 6 s6_129 = [s7_240, s7_125] := by decide
theorem s6_129_safe : Safe 7 6 s6_129 := by
  apply safe_succ 6 6 s6_129 [s7_240, s7_125] (by decide) s6_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_240_safe
  · subst z; exact s7_125_safe
def s6_130 : State := ⟨[1,4,96,160], 1461501637671185285203851458712368708759249293598, 3, 3, 1, 0⟩
theorem s6_130_edges : next config 6 s6_130 = [s7_126, s7_49, s7_60] := by decide
theorem s6_130_safe : Safe 7 6 s6_130 := by
  apply safe_succ 6 6 s6_130 [s7_126, s7_49, s7_60] (by decide) s6_130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_126_safe
  · subst z; exact s7_49_safe
  · subst z; exact s7_60_safe
def s6_131 : State := ⟨[1,4,96,160], 1461501637671185285203851458712368708767839228182, 3, 3, 1, 0⟩
theorem s6_131_edges : next config 6 s6_131 = [s7_127] := by decide
theorem s6_131_safe : Safe 7 6 s6_131 := by
  apply safe_succ 6 6 s6_131 [s7_127] (by decide) s6_131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_127_safe
def s6_132 : State := ⟨[1,4,96,160], 1461501637671185285203851458749262196906668396822, 3, 3, 1, 0⟩
theorem s6_132_edges : next config 6 s6_132 = [s7_128, s7_50, s7_61] := by decide
theorem s6_132_safe : Safe 7 6 s6_132 := by
  apply safe_succ 6 6 s6_132 [s7_128, s7_50, s7_61] (by decide) s6_132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_128_safe
  · subst z; exact s7_50_safe
  · subst z; exact s7_61_safe
def s6_133 : State := ⟨[1,4,96,160], 1461501637671185285362307783740897383946337194262, 3, 3, 1, 0⟩
theorem s6_133_edges : next config 6 s6_133 = [s7_129, s7_51] := by decide
theorem s6_133_safe : Safe 7 6 s6_133 := by
  apply safe_succ 6 6 s6_133 [s7_129, s7_51] (by decide) s6_133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_129_safe
  · subst z; exact s7_51_safe
def s6_134 : State := ⟨[1,4,96,160], 1461501637671185286471502058940598110255952494878, 3, 3, 1, 0⟩
theorem s6_134_edges : next config 6 s6_134 = [s7_130] := by decide
theorem s6_134_safe : Safe 7 6 s6_134 := by
  apply safe_succ 6 6 s6_134 [s7_130] (by decide) s6_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_130_safe
def s6_135 : State := ⟨[1,4,96,160], 1461501637671185286471502058977491598403371598102, 3, 3, 1, 0⟩
theorem s6_135_edges : next config 6 s6_135 = [s7_131] := by decide
theorem s6_135_safe : Safe 7 6 s6_135 := by
  apply safe_succ 6 6 s6_135 [s7_131] (by decide) s6_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_131_safe
def s6_136 : State := ⟨[1,4,96,160], 4384504912332991121611221124144934748071114379542, 3, 3, 1, 0⟩
theorem s6_136_edges : next config 6 s6_136 = [s7_134] := by decide
theorem s6_136_safe : Safe 7 6 s6_136 := by
  apply safe_succ 6 6 s6_136 [s7_134] (by decide) s6_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_134_safe
def s6_137 : State := ⟨[1,4,96,161], 2923003275002088203407536291428651728423771771158, 3, 3, 1, 0⟩
theorem s6_137_edges : next config 6 s6_137 = [s7_135, s7_57] := by decide
theorem s6_137_safe : Safe 7 6 s6_137 := by
  apply safe_succ 6 6 s6_137 [s7_135, s7_57] (by decide) s6_137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_135_safe
  · subst z; exact s7_57_safe
def s6_138 : State := ⟨[1,4,96,162], 25108406947392729606368181200329325475124137975310257819926, 2, 2, 1, 0⟩
theorem s6_138_edges : next config 6 s6_138 = [s7_136] := by decide
theorem s6_138_safe : Safe 7 6 s6_138 := by
  apply safe_succ 6 6 s6_138 [s7_136] (by decide) s6_138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_136_safe
def s6_139 : State := ⟨[1,4,96,162], 31385508682779410368842841155853238037372994990047219486998, 2, 2, 1, 0⟩
theorem s6_139_edges : next config 6 s6_139 = [s7_137] := by decide
theorem s6_139_safe : Safe 7 6 s6_139 := by
  apply safe_succ 6 6 s6_139 [s7_137] (by decide) s6_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_137_safe
def s6_140 : State := ⟨[1,4,96,163], 11692013102390329381839029922360095920668459208982, 2, 2, 1, 0⟩
theorem s6_140_edges : next config 6 s6_140 = [s7_138] := by decide
theorem s6_140_safe : Safe 7 6 s6_140 := by
  apply safe_succ 6 6 s6_140 [s7_138] (by decide) s6_140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_138_safe
def s6_141 : State := ⟨[1,4,96,163], 11692013103070894115680906849286845135531995631894, 2, 2, 1, 0⟩
theorem s6_141_edges : next config 6 s6_141 = [s7_139] := by decide
theorem s6_141_safe : Safe 7 6 s6_141 := by
  apply safe_succ 6 6 s6_141 [s7_139] (by decide) s6_141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_139_safe
def s6_142 : State := ⟨[1,4,96,163], 14615016374329876282878891880085665100526178603286, 2, 2, 1, 0⟩
theorem s6_142_edges : next config 6 s6_142 = [s7_140] := by decide
theorem s6_142_safe : Safe 7 6 s6_142 := by
  apply safe_succ 6 6 s6_142 [s7_140] (by decide) s6_142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_140_safe
def s6_143 : State := ⟨[1,4,96,163], 16076518010980214467240699785875198905318574723350, 2, 2, 1, 0⟩
theorem s6_143_edges : next config 6 s6_143 = [s7_141] := by decide
theorem s6_143_safe : Safe 7 6 s6_143 := by
  apply safe_succ 6 6 s6_143 [s7_141] (by decide) s6_143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_141_safe
def s6_144 : State := ⟨[1,4,96,163], 17538019649672246853128138472444980354701580112150, 2, 2, 1, 0⟩
theorem s6_144_edges : next config 6 s6_144 = [s7_142] := by decide
theorem s6_144_safe : Safe 7 6 s6_144 := by
  apply safe_succ 6 6 s6_144 [s7_142] (by decide) s6_144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_142_safe
def s6_145 : State := ⟨[1,4,96,163], 18999521285642020303648069451307764944630439809302, 2, 2, 1, 0⟩
theorem s6_145_edges : next config 6 s6_145 = [s7_143] := by decide
theorem s6_145_safe : Safe 7 6 s6_145 := by
  apply safe_succ 6 6 s6_145 [s7_143] (by decide) s6_145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_143_safe
def s6_146 : State := ⟨[1,4,96,170], 4495579036431558788229218465915136152580478891786518, 1, 1, 1, 0⟩
theorem s6_146_edges : next config 6 s6_146 = [s7_144] := by decide
theorem s6_146_safe : Safe 7 6 s6_146 := by
  apply safe_succ 6 6 s6_146 [s7_144] (by decide) s6_146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_144_safe
def s6_147 : State := ⟨[1,4,96,170], 4497040538067528561679738396893998937170407751483670, 1, 1, 1, 0⟩
theorem s6_147_edges : next config 6 s6_147 = [s7_145] := by decide
theorem s6_147_safe : Safe 7 6 s6_147 := by
  apply safe_succ 6 6 s6_147 [s7_145] (by decide) s6_147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_145_safe
def s6_148 : State := ⟨[1,4,96,171], 2999001359804714199988645197213662340452803967779606, 1, 1, 1, 0⟩
theorem s6_148_edges : next config 6 s6_148 = [s7_146] := by decide
theorem s6_148_safe : Safe 7 6 s6_148 := by
  apply safe_succ 6 6 s6_148 [s7_146] (by decide) s6_148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_146_safe
def s6_149 : State := ⟨[1,4,96,171], 3000462861440683973439165128192525125042732827476758, 1, 1, 1, 0⟩
theorem s6_149_edges : next config 6 s6_149 = [s7_147] := by decide
theorem s6_149_safe : Safe 7 6 s6_149 := by
  apply safe_succ 6 6 s6_149 [s7_147] (by decide) s6_149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_147_safe
def s6_150 : State := ⟨[1,4,96,171], 3004847366354037811661459936544527472531436287885590, 1, 1, 1, 0⟩
theorem s6_150_edges : next config 6 s6_150 = [s7_148] := by decide
theorem s6_150_safe : Safe 7 6 s6_150 := by
  apply safe_succ 6 6 s6_150 [s7_148] (by decide) s6_150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_148_safe
def s6_151 : State := ⟨[1,4,96,171], 3004847366355398941129143690398380970961154770796830, 1, 1, 1, 0⟩
theorem s6_151_edges : next config 6 s6_151 = [s7_149] := by decide
theorem s6_151_safe : Safe 7 6 s6_151 := by
  apply safe_succ 6 6 s6_151 [s7_149] (by decide) s6_151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_149_safe
def s6_152 : State := ⟨[1,4,96,171], 3006308867990007585111979867523390257121356557648158, 1, 1, 1, 0⟩
theorem s6_152_edges : next config 6 s6_152 = [s7_150] := by decide
theorem s6_152_safe : Safe 7 6 s6_152 := by
  apply safe_succ 6 6 s6_152 [s7_150] (by decide) s6_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_150_safe
def s6_153 : State := ⟨[1,4,96,171], 3007770369627338488030183552356106540141021080125718, 1, 1, 1, 0⟩
theorem s6_153_edges : next config 6 s6_153 = [s7_151] := by decide
theorem s6_153_safe : Safe 7 6 s6_153 := by
  apply safe_succ 6 6 s6_153 [s7_151] (by decide) s6_153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_151_safe
def s6_154 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042098441133567351263518, 3, 3, 1, 0⟩
theorem s6_154_edges : next config 6 s6_154 = [s7_152] := by decide
theorem s6_154_safe : Safe 7 6 s6_154 := by
  apply safe_succ 6 6 s6_154 [s7_152] (by decide) s6_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_152_safe
def s6_155 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042098441133575941198102, 3, 3, 1, 0⟩
theorem s6_155_edges : next config 6 s6_155 = [s7_153] := by decide
theorem s6_155_safe : Safe 7 6 s6_155 := by
  apply safe_succ 6 6 s6_155 [s7_153] (by decide) s6_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_153_safe
def s6_156 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042135334621714770366742, 3, 3, 1, 0⟩
theorem s6_156_edges : next config 6 s6_156 = [s7_154] := by decide
theorem s6_156_safe : Safe 7 6 s6_156 := by
  apply safe_succ 6 6 s6_156 [s7_154] (by decide) s6_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_154_safe
def s6_157 : State := ⟨[1,4,96,192], 6277101735386680764176071790366289367126969808754439164182, 3, 3, 1, 0⟩
theorem s6_157_edges : next config 6 s6_157 = [s7_155] := by decide
theorem s6_157_safe : Safe 7 6 s6_157 := by
  apply safe_succ 6 6 s6_157 [s7_155] (by decide) s6_157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_155_safe
def s6_158 : State := ⟨[1,4,96,192], 6277101735386680764176071791475483642326670535064054464798, 3, 3, 1, 0⟩
theorem s6_158_edges : next config 6 s6_158 = [s7_156] := by decide
theorem s6_158_safe : Safe 7 6 s6_158 := by
  apply safe_succ 6 6 s6_158 [s7_156] (by decide) s6_158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_156_safe
def s6_159 : State := ⟨[1,4,96,192], 6277101735386680764176071791475483642363564023211473568022, 3, 3, 1, 0⟩
theorem s6_159_edges : next config 6 s6_159 = [s7_157] := by decide
theorem s6_159_safe : Safe 7 6 s6_159 := by
  apply safe_succ 6 6 s6_159 [s7_157] (by decide) s6_159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_157_safe
def s6_160 : State := ⟨[1,4,96,192], 18831305206160042291847650636623165874303152022495420289302, 3, 3, 1, 0⟩
theorem s6_160_edges : next config 6 s6_160 = [s7_160] := by decide
theorem s6_160_safe : Safe 7 6 s6_160 := by
  apply safe_succ 6 6 s6_160 [s7_160] (by decide) s6_160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_160_safe
def s6_161 : State := ⟨[1,4,96,192], 18831305206160042291847650637890816474531381423992123490582, 3, 3, 1, 0⟩
theorem s6_161_edges : next config 6 s6_161 = [s7_161] := by decide
theorem s6_161_safe : Safe 7 6 s6_161 := by
  apply safe_succ 6 6 s6_161 [s7_161] (by decide) s6_161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_161_safe
def s6_162 : State := ⟨[1,4,96,193], 12554203470773361528011861213415499458237690066178804879638, 3, 3, 1, 0⟩
theorem s6_162_edges : next config 6 s6_162 = [s7_163] := by decide
theorem s6_162_safe : Safe 7 6 s6_162 := by
  apply safe_succ 6 6 s6_162 [s7_163] (by decide) s6_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_163_safe
def s6_163 : State := ⟨[1,4,96,193], 12554203470773361528011861214683150058465919467675508080918, 3, 3, 1, 0⟩
theorem s6_163_edges : next config 6 s6_163 = [s7_164] := by decide
theorem s6_163_safe : Safe 7 6 s6_163 := by
  apply safe_succ 6 6 s6_163 [s7_164] (by decide) s6_163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_164_safe
def s6_164 : State := ⟨[1,4,96,194], 25108406947392729606368181200329325475124137975310257819926, 2, 2, 1, 0⟩
theorem s6_164_edges : next config 6 s6_164 = [s7_166] := by decide
theorem s6_164_safe : Safe 7 6 s6_164 := by
  apply safe_succ 6 6 s6_164 [s7_166] (by decide) s6_164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_166_safe
def s6_165 : State := ⟨[1,4,96,194], 25108406948854231242337954650849256453986922565239117517078, 2, 2, 1, 0⟩
theorem s6_165_edges : next config 6 s6_165 = [s7_167] := by decide
theorem s6_165_safe : Safe 7 6 s6_165 := by
  apply safe_succ 6 6 s6_165 [s7_167] (by decide) s6_165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_167_safe
def s6_166 : State := ⟨[1,4,96,210], 1645504557321206042244173864763307681469358588308292139762127126, 2, 2, 1, 0⟩
theorem s6_166_edges : next config 6 s6_166 = [s7_168] := by decide
theorem s6_166_safe : Safe 7 6 s6_166 := by
  apply safe_succ 6 6 s6_166 [s7_168] (by decide) s6_166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_168_safe
def s6_167 : State := ⟨[1,4,96,210], 1645504557321206042266473248832370620857040453082510774195261718, 2, 2, 1, 0⟩
theorem s6_167_edges : next config 6 s6_167 = [s7_170] := by decide
theorem s6_167_safe : Safe 7 6 s6_167 := by
  apply safe_succ 6 6 s6_167 [s7_170] (by decide) s6_167_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_170_safe
def s6_168 : State := ⟨[1,4,96,210], 1645529665728147588878026227126878019568880124639476549876257046, 2, 2, 1, 0⟩
theorem s6_168_edges : next config 6 s6_168 = [s7_172] := by decide
theorem s6_168_safe : Safe 7 6 s6_168 := by
  apply safe_succ 6 6 s6_168 [s7_172] (by decide) s6_168_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_172_safe
def s6_169 : State := ⟨[1,4,96,210], 1645535942829882975558788701786833543481442373496491286837924118, 2, 2, 1, 0⟩
theorem s6_169_edges : next config 6 s6_169 = [s7_174] := by decide
theorem s6_169_safe : Safe 7 6 s6_169 := by
  apply safe_succ 6 6 s6_169 [s7_174] (by decide) s6_169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_174_safe
def s6_170 : State := ⟨[1,4,96,210], 2056880696651507552716012563677585754536581546400312294008492310, 2, 2, 1, 0⟩
theorem s6_170_edges : next config 6 s6_170 = [s7_176] := by decide
theorem s6_170_safe : Safe 7 6 s6_170 := by
  apply safe_succ 6 6 s6_170 [s7_176] (by decide) s6_170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_176_safe
def s6_171 : State := ⟨[1,4,96,210], 2056886973753242939374475654268478339061461930483108396537024790, 2, 2, 1, 0⟩
theorem s6_171_edges : next config 6 s6_171 = [s7_178] := by decide
theorem s6_171_safe : Safe 7 6 s6_171 := by
  apply safe_succ 6 6 s6_171 [s7_178] (by decide) s6_171_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_178_safe
def s6_172 : State := ⟨[1,4,96,210], 27973577474460502716723680785680915761193132438445569953339867414, 2, 2, 1, 0⟩
theorem s6_172_edges : next config 6 s6_172 = [s7_180] := by decide
theorem s6_172_safe : Safe 7 6 s6_172 := by
  apply safe_succ 6 6 s6_172 [s7_180] (by decide) s6_172_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_180_safe
def s6_173 : State := ⟨[1,4,96,210], 27973577474460502716745980169749978700580814303219788587773002006, 2, 2, 1, 0⟩
theorem s6_173_edges : next config 6 s6_173 = [s7_181] := by decide
theorem s6_173_safe : Safe 7 6 s6_173 := by
  apply safe_succ 6 6 s6_173 [s7_181] (by decide) s6_173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_181_safe
def s6_174 : State := ⟨[1,4,96,210], 27973602582867444263357533148044486099292653974776754363453997334, 2, 2, 1, 0⟩
theorem s6_174_edges : next config 6 s6_174 = [s7_182] := by decide
theorem s6_174_safe : Safe 7 6 s6_174 := by
  apply safe_succ 6 6 s6_174 [s7_182] (by decide) s6_174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_182_safe
def s6_175 : State := ⟨[1,4,96,210], 27973608859969179650038295622704441623205216223633769100415664406, 2, 2, 1, 0⟩
theorem s6_175_edges : next config 6 s6_175 = [s7_183] := by decide
theorem s6_175_safe : Safe 7 6 s6_175 := by
  apply safe_succ 6 6 s6_175 [s7_183] (by decide) s6_175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_183_safe
def s6_176 : State := ⟨[1,4,96,210], 28384953613790804227195519484595193834260355396537590107586232598, 2, 2, 1, 0⟩
theorem s6_176_edges : next config 6 s6_176 = [s7_184] := by decide
theorem s6_176_safe : Safe 7 6 s6_176 := by
  apply safe_succ 6 6 s6_176 [s7_184] (by decide) s6_176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_184_safe
def s6_177 : State := ⟨[1,4,96,210], 28384959890892539613853982575186086418785235780620386210114765078, 2, 2, 1, 0⟩
theorem s6_177_edges : next config 6 s6_177 = [s7_185] := by decide
theorem s6_177_safe : Safe 7 6 s6_177 := by
  apply safe_succ 6 6 s6_177 [s7_185] (by decide) s6_177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_185_safe
def s6_178 : State := ⟨[1,4,96,214], 26328072917139296674568711603123565256210396867959895269344084246, 2, 2, 1, 0⟩
theorem s6_178_edges : next config 6 s6_178 = [s7_186] := by decide
theorem s6_178_safe : Safe 7 6 s6_178 := by
  apply safe_succ 6 6 s6_178 [s7_186] (by decide) s6_178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_186_safe
def s6_179 : State := ⟨[1,4,96,214], 26328072917139296674591010987192628195598078732734113903777218838, 2, 2, 1, 0⟩
theorem s6_179_edges : next config 6 s6_179 = [s7_187] := by decide
theorem s6_179_safe : Safe 7 6 s6_179 := by
  apply safe_succ 6 6 s6_179 [s7_187] (by decide) s6_179_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_187_safe
def s6_180 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048536658170206926999838, 3, 3, 1, 0⟩
theorem s6_180_edges : next config 6 s6_180 = [s7_188] := by decide
theorem s6_180_safe : Safe 7 6 s6_180 := by
  apply safe_succ 6 6 s6_180 [s7_188] (by decide) s6_180_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_188_safe
def s6_181 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048536658170215516934422, 3, 3, 1, 0⟩
theorem s6_181_edges : next config 6 s6_181 = [s7_189] := by decide
theorem s6_181_safe : Safe 7 6 s6_181 := by
  apply safe_succ 6 6 s6_181 [s7_189] (by decide) s6_181_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_189_safe
def s6_182 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048573551658354346103062, 3, 3, 1, 0⟩
theorem s6_182_edges : next config 6 s6_182 = [s7_190] := by decide
theorem s6_182_safe : Safe 7 6 s6_182 := by
  apply safe_succ 6 6 s6_182 [s7_190] (by decide) s6_182_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_190_safe
def s6_183 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040795767373565186845394014900502, 3, 3, 1, 0⟩
theorem s6_183_edges : next config 6 s6_183 = [s7_191] := by decide
theorem s6_183_safe : Safe 7 6 s6_183 := by
  apply safe_succ 6 6 s6_183 [s7_191] (by decide) s6_183_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_191_safe
def s6_184 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913041904961648764887571703630201118, 3, 3, 1, 0⟩
theorem s6_184_edges : next config 6 s6_184 = [s7_192] := by decide
theorem s6_184_safe : Safe 7 6 s6_184 := by
  apply safe_succ 6 6 s6_184 [s7_192] (by decide) s6_184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_192_safe
def s6_185 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913041904961648801781059851049304342, 3, 3, 1, 0⟩
theorem s6_185_edges : next config 6 s6_185 = [s7_193] := by decide
theorem s6_185_safe : Safe 7 6 s6_185 := by
  apply safe_succ 6 6 s6_185 [s7_193] (by decide) s6_185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_193_safe
def s6_186 : State := ⟨[1,4,96,224], 80879840001451919384001045261399174387911599893617803132414147498262, 3, 3, 1, 0⟩
theorem s6_186_edges : next config 6 s6_186 = [s7_196] := by decide
theorem s6_186_safe : Safe 7 6 s6_186 := by
  apply safe_succ 6 6 s6_186 [s7_196] (by decide) s6_186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_196_safe
def s6_187 : State := ⟨[1,4,96,224], 458319093341560876509339256479674003818831621809185817867864690983198, 3, 3, 1, 0⟩
theorem s6_187_edges : next config 6 s6_187 = [s7_197] := by decide
theorem s6_187_safe : Safe 7 6 s6_187 := by
  apply safe_succ 6 6 s6_187 [s7_197] (by decide) s6_187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_197_safe
def s6_188 : State := ⟨[1,4,96,224], 458319093341560876509339256479674003818831621809222711356012110086422, 3, 3, 1, 0⟩
theorem s6_188_edges : next config 6 s6_188 = [s7_198] := by decide
theorem s6_188_safe : Safe 7 6 s6_188 := by
  apply safe_succ 6 6 s6_188 [s7_198] (by decide) s6_188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_198_safe
def s6_189 : State := ⟨[1,4,96,225], 53919893334301279589334030174379543714432911796105759326497625149718, 3, 3, 1, 0⟩
theorem s6_189_edges : next config 6 s6_189 = [s7_199] := by decide
theorem s6_189_safe : Safe 7 6 s6_189 := by
  apply safe_succ 6 6 s6_189 [s7_199] (by decide) s6_189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_199_safe
def s6_190 : State := ⟨[1,4,96,228], 431359146674410236714672241392654373146462127986873474788257783939358, 3, 3, 1, 0⟩
theorem s6_190_edges : next config 6 s6_190 = [s7_200] := by decide
theorem s6_190_safe : Safe 7 6 s6_190 := by
  apply safe_succ 6 6 s6_190 [s7_200] (by decide) s6_190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_200_safe
def s6_191 : State := ⟨[1,4,96,228], 431359146674410236714672241392654373146462127986910368276405203042582, 3, 3, 1, 0⟩
theorem s6_191_edges : next config 6 s6_191 = [s7_201] := by decide
theorem s6_191_safe : Safe 7 6 s6_191 := by
  apply safe_succ 6 6 s6_191 [s7_201] (by decide) s6_191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_201_safe
def s6_192 : State := ⟨[1,4,97,145], 44602511244162246782949387908875876953035030, 2, 2, 1, 0⟩
theorem s6_192_edges : next config 6 s6_192 = [] := by decide
theorem s6_192_safe : Safe 7 6 s6_192 := by
  apply safe_succ 6 6 s6_192 [] (by decide) s6_192_edges
  simp
def s6_193 : State := ⟨[1,4,97,145], 66902575877959028047558179432309374922592534, 2, 2, 1, 0⟩
theorem s6_193_edges : next config 6 s6_193 = [] := by decide
theorem s6_193_safe : Safe 7 6 s6_193 := by
  apply safe_succ 6 6 s6_193 [] (by decide) s6_193_edges
  simp
def s6_194 : State := ⟨[1,4,97,162], 5846006551025023507657116135743244872641207669014, 2, 2, 1, 0⟩
theorem s6_194_edges : next config 6 s6_194 = [] := by decide
theorem s6_194_safe : Safe 7 6 s6_194 := by
  apply safe_succ 6 6 s6_194 [] (by decide) s6_194_edges
  simp
def s6_195 : State := ⟨[1,4,97,162], 7307508186994796958177047114606029462570067366166, 2, 2, 1, 0⟩
theorem s6_195_edges : next config 6 s6_195 = [] := by decide
theorem s6_195_safe : Safe 7 6 s6_195 := by
  apply safe_succ 6 6 s6_195 [] (by decide) s6_195_edges
  simp
def s6_196 : State := ⟨[1,4,100,145], 44602511244163355977224587609602186568335646, 1, 1, 1, 0⟩
theorem s6_196_edges : next config 6 s6_196 = [] := by decide
theorem s6_196_safe : Safe 7 6 s6_196 := by
  apply safe_succ 6 6 s6_196 [] (by decide) s6_196_edges
  simp
def s6_197 : State := ⟨[1,4,100,145], 44602511244163355977224624503090333987438870, 1, 1, 1, 0⟩
theorem s6_197_edges : next config 6 s6_197 = [] := by decide
theorem s6_197_safe : Safe 7 6 s6_197 := by
  apply safe_succ 6 6 s6_197 [] (by decide) s6_197_edges
  simp
def s6_198 : State := ⟨[1,4,100,145], 66902575877960137241833379133035684537893150, 1, 1, 1, 0⟩
theorem s6_198_edges : next config 6 s6_198 = [] := by decide
theorem s6_198_safe : Safe 7 6 s6_198 := by
  apply safe_succ 6 6 s6_198 [] (by decide) s6_198_edges
  simp
def s6_199 : State := ⟨[1,4,100,145], 66902575877960137241833416026523831956996374, 1, 1, 1, 0⟩
theorem s6_199_edges : next config 6 s6_199 = [] := by decide
theorem s6_199_safe : Safe 7 6 s6_199 := by
  apply safe_succ 6 6 s6_199 [] (by decide) s6_199_edges
  simp
def s6_200 : State := ⟨[1,4,104,128], 340282387282576229647756113050568036638, 3, 3, 0, 0⟩
theorem s6_200_edges : next config 6 s6_200 = [s7_392, s7_65, s7_87, s7_202, s7_73, s7_95, s7_111, s7_126] := by decide
theorem s6_200_safe : Safe 7 6 s6_200 := by
  apply safe_succ 6 6 s6_200 [s7_392, s7_65, s7_87, s7_202, s7_73, s7_95, s7_111, s7_126] (by decide) s6_200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_392_safe
  · subst z; exact s7_65_safe
  · subst z; exact s7_87_safe
  · subst z; exact s7_202_safe
  · subst z; exact s7_73_safe
  · subst z; exact s7_95_safe
  · subst z; exact s7_111_safe
  · subst z; exact s7_126_safe
def s6_201 : State := ⟨[1,4,104,128], 340282387282576229647756113059157971222, 3, 3, 0, 0⟩
theorem s6_201_edges : next config 6 s6_201 = [s7_395, s7_66, s7_88, s7_203, s7_74, s7_96, s7_112, s7_127] := by decide
theorem s6_201_safe : Safe 7 6 s6_201 := by
  apply safe_succ 6 6 s6_201 [s7_395, s7_66, s7_88, s7_203, s7_74, s7_96, s7_112, s7_127] (by decide) s6_201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_395_safe
  · subst z; exact s7_66_safe
  · subst z; exact s7_88_safe
  · subst z; exact s7_203_safe
  · subst z; exact s7_74_safe
  · subst z; exact s7_96_safe
  · subst z; exact s7_112_safe
  · subst z; exact s7_127_safe
def s6_202 : State := ⟨[1,4,104,128], 340282387282576229684649601197987139862, 3, 3, 0, 0⟩
theorem s6_202_edges : next config 6 s6_202 = [s7_397, s7_67, s7_89, s7_204, s7_75, s7_97, s7_113, s7_128] := by decide
theorem s6_202_safe : Safe 7 6 s6_202 := by
  apply safe_succ 6 6 s6_202 [s7_397, s7_67, s7_89, s7_204, s7_75, s7_97, s7_113, s7_128] (by decide) s6_202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_397_safe
  · subst z; exact s7_67_safe
  · subst z; exact s7_89_safe
  · subst z; exact s7_204_safe
  · subst z; exact s7_75_safe
  · subst z; exact s7_97_safe
  · subst z; exact s7_113_safe
  · subst z; exact s7_128_safe
def s6_203 : State := ⟨[1,4,104,128], 340282387441032554676284788237655937302, 3, 3, 0, 0⟩
theorem s6_203_edges : next config 6 s6_203 = [s7_399, s7_68, s7_90, s7_205, s7_76, s7_98, s7_114, s7_129] := by decide
theorem s6_203_safe : Safe 7 6 s6_203 := by
  apply safe_succ 6 6 s6_203 [s7_399, s7_68, s7_90, s7_205, s7_76, s7_98, s7_114, s7_129] (by decide) s6_203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_399_safe
  · subst z; exact s7_68_safe
  · subst z; exact s7_90_safe
  · subst z; exact s7_205_safe
  · subst z; exact s7_76_safe
  · subst z; exact s7_98_safe
  · subst z; exact s7_114_safe
  · subst z; exact s7_129_safe
def s6_204 : State := ⟨[1,4,104,128], 340282388550226829875985514547271237918, 3, 3, 0, 0⟩
theorem s6_204_edges : next config 6 s6_204 = [s7_401, s7_69, s7_91, s7_206, s7_77, s7_99, s7_115, s7_130] := by decide
theorem s6_204_safe : Safe 7 6 s6_204 := by
  apply safe_succ 6 6 s6_204 [s7_401, s7_69, s7_91, s7_206, s7_77, s7_99, s7_115, s7_130] (by decide) s6_204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_401_safe
  · subst z; exact s7_69_safe
  · subst z; exact s7_91_safe
  · subst z; exact s7_206_safe
  · subst z; exact s7_77_safe
  · subst z; exact s7_99_safe
  · subst z; exact s7_115_safe
  · subst z; exact s7_130_safe
def s6_205 : State := ⟨[1,4,104,128], 340282388550226829912879002694690341142, 3, 3, 0, 0⟩
theorem s6_205_edges : next config 6 s6_205 = [s7_402, s7_70, s7_92, s7_207, s7_78, s7_100, s7_116, s7_131] := by decide
theorem s6_205_safe : Safe 7 6 s6_205 := by
  apply safe_succ 6 6 s6_205 [s7_402, s7_70, s7_92, s7_207, s7_78, s7_100, s7_116, s7_131] (by decide) s6_205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_402_safe
  · subst z; exact s7_70_safe
  · subst z; exact s7_92_safe
  · subst z; exact s7_207_safe
  · subst z; exact s7_78_safe
  · subst z; exact s7_100_safe
  · subst z; exact s7_116_safe
  · subst z; exact s7_131_safe
def s6_206 : State := ⟨[1,4,104,128], 340282711801129888074482896206588608798, 3, 3, 0, 0⟩
theorem s6_206_edges : next config 6 s6_206 = [s7_403, s7_71, s7_93, s7_208, s7_79, s7_101, s7_117, s7_132] := by decide
theorem s6_206_safe : Safe 7 6 s6_206 := by
  apply safe_succ 6 6 s6_206 [s7_403, s7_71, s7_93, s7_208, s7_79, s7_101, s7_117, s7_132] (by decide) s6_206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_403_safe
  · subst z; exact s7_71_safe
  · subst z; exact s7_93_safe
  · subst z; exact s7_208_safe
  · subst z; exact s7_79_safe
  · subst z; exact s7_101_safe
  · subst z; exact s7_117_safe
  · subst z; exact s7_132_safe
def s6_207 : State := ⟨[1,4,104,128], 340282711801129888111376384354007712022, 3, 3, 0, 0⟩
theorem s6_207_edges : next config 6 s6_207 = [s7_404, s7_72, s7_94, s7_209, s7_80, s7_102, s7_118, s7_133] := by decide
theorem s6_207_safe : Safe 7 6 s6_207 := by
  apply safe_succ 6 6 s6_207 [s7_404, s7_72, s7_94, s7_209, s7_80, s7_102, s7_118, s7_133] (by decide) s6_207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_404_safe
  · subst z; exact s7_72_safe
  · subst z; exact s7_94_safe
  · subst z; exact s7_209_safe
  · subst z; exact s7_80_safe
  · subst z; exact s7_102_safe
  · subst z; exact s7_118_safe
  · subst z; exact s7_133_safe
def s6_208 : State := ⟨[1,4,104,131], 3743106056491960864281502187368250151190, 2, 2, 1, 0⟩
theorem s6_208_edges : next config 6 s6_208 = [s7_138] := by decide
theorem s6_208_safe : Safe 7 6 s6_208 := by
  apply safe_succ 6 6 s6_208 [s7_138] (by decide) s6_208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_138_safe
def s6_209 : State := ⟨[1,4,104,131], 3743106057759611464509731588864953352470, 2, 2, 1, 0⟩
theorem s6_209_edges : next config 6 s6_209 = [] := by decide
theorem s6_209_safe : Safe 7 6 s6_209 := by
  apply safe_succ 6 6 s6_209 [] (by decide) s6_209_edges
  simp
def s6_210 : State := ⟨[1,4,104,131], 3743106381010514522708228970524270723350, 2, 2, 1, 0⟩
theorem s6_210_edges : next config 6 s6_210 = [] := by decide
theorem s6_210_safe : Safe 7 6 s6_210 := by
  apply safe_succ 6 6 s6_210 [] (by decide) s6_210_edges
  simp
def s6_211 : State := ⟨[1,4,104,131], 4423670790333837791208251402231786574102, 2, 2, 1, 0⟩
theorem s6_211_edges : next config 6 s6_211 = [s7_139] := by decide
theorem s6_211_safe : Safe 7 6 s6_211 := by
  apply safe_succ 6 6 s6_211 [s7_139] (by decide) s6_211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_139_safe
def s6_212 : State := ⟨[1,4,104,131], 4423670791601488391436480803728489775382, 2, 2, 1, 0⟩
theorem s6_212_edges : next config 6 s6_212 = [] := by decide
theorem s6_212_safe : Safe 7 6 s6_212 := by
  apply safe_succ 6 6 s6_212 [] (by decide) s6_212_edges
  simp
def s6_213 : State := ⟨[1,4,104,131], 4423671114852391449634978185387807146262, 2, 2, 1, 0⟩
theorem s6_213_edges : next config 6 s6_213 = [] := by decide
theorem s6_213_safe : Safe 7 6 s6_213 := by
  apply safe_succ 6 6 s6_213 [] (by decide) s6_213_edges
  simp
def s6_214 : State := ⟨[1,4,104,140], 1399581375166181537991044141872481453539614, 1, 1, 1, 0⟩
theorem s6_214_edges : next config 6 s6_214 = [] := by decide
theorem s6_214_safe : Safe 7 6 s6_214 := by
  apply safe_succ 6 6 s6_214 [] (by decide) s6_214_edges
  simp
def s6_215 : State := ⟨[1,4,104,140], 1399581375166181537991044141872490043474198, 1, 1, 1, 0⟩
theorem s6_215_edges : next config 6 s6_215 = [] := by decide
theorem s6_215_safe : Safe 7 6 s6_215 := by
  apply safe_succ 6 6 s6_215 [] (by decide) s6_215_edges
  simp
def s6_216 : State := ⟨[1,4,104,140], 1399581375166181537991081035360628872642838, 1, 1, 1, 0⟩
theorem s6_216_edges : next config 6 s6_216 = [] := by decide
theorem s6_216_safe : Safe 7 6 s6_216 := by
  apply safe_succ 6 6 s6_216 [] (by decide) s6_216_edges
  simp
def s6_217 : State := ⟨[1,4,104,140], 1399581375166339994316072670547668541440278, 1, 1, 1, 0⟩
theorem s6_217_edges : next config 6 s6_217 = [] := by decide
theorem s6_217_safe : Safe 7 6 s6_217 := by
  apply safe_succ 6 6 s6_217 [] (by decide) s6_217_edges
  simp
def s6_218 : State := ⟨[1,4,104,140], 1481249143227206769222254047656105824289054, 1, 1, 1, 0⟩
theorem s6_218_edges : next config 6 s6_218 = [] := by decide
theorem s6_218_safe : Safe 7 6 s6_218 := by
  apply safe_succ 6 6 s6_218 [] (by decide) s6_218_edges
  simp
def s6_219 : State := ⟨[1,4,104,140], 1481249143227206769222254047656114414223638, 1, 1, 1, 0⟩
theorem s6_219_edges : next config 6 s6_219 = [] := by decide
theorem s6_219_safe : Safe 7 6 s6_219 := by
  apply safe_succ 6 6 s6_219 [] (by decide) s6_219_edges
  simp
def s6_220 : State := ⟨[1,4,104,140], 1481249143227206769222290941144253243392278, 1, 1, 1, 0⟩
theorem s6_220_edges : next config 6 s6_220 = [] := by decide
theorem s6_220_safe : Safe 7 6 s6_220 := by
  apply safe_succ 6 6 s6_220 [] (by decide) s6_220_edges
  simp
def s6_221 : State := ⟨[1,4,104,140], 1481249143227365225547282576331292912189718, 1, 1, 1, 0⟩
theorem s6_221_edges : next config 6 s6_221 = [] := by decide
theorem s6_221_safe : Safe 7 6 s6_221 := by
  apply safe_succ 6 6 s6_221 [] (by decide) s6_221_edges
  simp
def s6_222 : State := ⟨[1,4,104,145], 44602511244182370736228011050624637116416286, 1, 1, 1, 0⟩
theorem s6_222_edges : next config 6 s6_222 = [s7_307, s7_241, s7_214, s7_226] := by decide
theorem s6_222_safe : Safe 7 6 s6_222 := by
  apply safe_succ 6 6 s6_222 [s7_307, s7_241, s7_214, s7_226] (by decide) s6_222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_307_safe
  · subst z; exact s7_241_safe
  · subst z; exact s7_214_safe
  · subst z; exact s7_226_safe
def s6_223 : State := ⟨[1,4,104,145], 44602511244182370736228011050624637116416790, 1, 1, 1, 0⟩
theorem s6_223_edges : next config 6 s6_223 = [] := by decide
theorem s6_223_safe : Safe 7 6 s6_223 := by
  apply safe_succ 6 6 s6_223 [] (by decide) s6_223_edges
  simp
def s6_224 : State := ⟨[1,4,104,145], 44602511244182370736228011050624637116420374, 2, 2, 1, 0⟩
theorem s6_224_edges : next config 6 s6_224 = [s7_322, s7_600] := by decide
theorem s6_224_safe : Safe 7 6 s6_224 := by
  apply safe_succ 6 6 s6_224 [s7_322, s7_600] (by decide) s6_224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_322_safe
  · subst z; exact s7_600_safe
def s6_225 : State := ⟨[1,4,104,145], 44602511244182370736228011050624645706350870, 1, 1, 1, 0⟩
theorem s6_225_edges : next config 6 s6_225 = [s7_242] := by decide
theorem s6_225_safe : Safe 7 6 s6_225 := by
  apply safe_succ 6 6 s6_225 [s7_242] (by decide) s6_225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_242_safe
def s6_226 : State := ⟨[1,4,104,145], 44602511244182370736228047944112784535519510, 1, 1, 1, 0⟩
theorem s6_226_edges : next config 6 s6_226 = [s7_308, s7_243, s7_215, s7_227] := by decide
theorem s6_226_safe : Safe 7 6 s6_226 := by
  apply safe_succ 6 6 s6_226 [s7_308, s7_243, s7_215, s7_227] (by decide) s6_226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_308_safe
  · subst z; exact s7_243_safe
  · subst z; exact s7_215_safe
  · subst z; exact s7_227_safe
def s6_227 : State := ⟨[1,4,104,145], 44602511244182370736228306198529816469242134, 2, 2, 1, 0⟩
theorem s6_227_edges : next config 6 s6_227 = [] := by decide
theorem s6_227_safe : Safe 7 6 s6_227 := by
  apply safe_succ 6 6 s6_227 [] (by decide) s6_227_edges
  simp
def s6_228 : State := ⟨[1,4,104,145], 44602511244182529192553039579299824204316950, 1, 1, 1, 0⟩
theorem s6_228_edges : next config 6 s6_228 = [s7_244] := by decide
theorem s6_228_safe : Safe 7 6 s6_228 := by
  apply safe_succ 6 6 s6_228 [s7_244] (by decide) s6_228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_244_safe
def s6_229 : State := ⟨[1,4,104,145], 44602511244183638386828239280026133819621654, 2, 2, 1, 0⟩
theorem s6_229_edges : next config 6 s6_229 = [s7_323] := by decide
theorem s6_229_safe : Safe 7 6 s6_229 := by
  apply safe_succ 6 6 s6_229 [s7_323] (by decide) s6_229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_323_safe
def s6_230 : State := ⟨[1,4,104,145], 44602511244506889289886437777407793136992534, 2, 2, 1, 0⟩
theorem s6_230_edges : next config 6 s6_230 = [s7_324] := by decide
theorem s6_230_safe : Safe 7 6 s6_230 := by
  apply safe_succ 6 6 s6_230 [s7_324] (by decide) s6_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_324_safe
def s6_231 : State := ⟨[1,4,104,145], 66902575877979152000836802574058135085973790, 1, 1, 1, 0⟩
theorem s6_231_edges : next config 6 s6_231 = [s7_309, s7_245, s7_216, s7_228] := by decide
theorem s6_231_safe : Safe 7 6 s6_231 := by
  apply safe_succ 6 6 s6_231 [s7_309, s7_245, s7_216, s7_228] (by decide) s6_231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_309_safe
  · subst z; exact s7_245_safe
  · subst z; exact s7_216_safe
  · subst z; exact s7_228_safe
def s6_232 : State := ⟨[1,4,104,145], 66902575877979152000836802574058135085974294, 1, 1, 1, 0⟩
theorem s6_232_edges : next config 6 s6_232 = [] := by decide
theorem s6_232_safe : Safe 7 6 s6_232 := by
  apply safe_succ 6 6 s6_232 [] (by decide) s6_232_edges
  simp
def s6_233 : State := ⟨[1,4,104,145], 66902575877979152000836802574058135085977878, 2, 2, 1, 0⟩
theorem s6_233_edges : next config 6 s6_233 = [s7_325, s7_601] := by decide
theorem s6_233_safe : Safe 7 6 s6_233 := by
  apply safe_succ 6 6 s6_233 [s7_325, s7_601] (by decide) s6_233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_325_safe
  · subst z; exact s7_601_safe
def s6_234 : State := ⟨[1,4,104,145], 66902575877979152000836802574058143675908374, 1, 1, 1, 0⟩
theorem s6_234_edges : next config 6 s6_234 = [s7_246] := by decide
theorem s6_234_safe : Safe 7 6 s6_234 := by
  apply safe_succ 6 6 s6_234 [s7_246] (by decide) s6_234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_246_safe
def s6_235 : State := ⟨[1,4,104,145], 66902575877979152000836839467546282505077014, 1, 1, 1, 0⟩
theorem s6_235_edges : next config 6 s6_235 = [s7_310, s7_247, s7_217, s7_229] := by decide
theorem s6_235_safe : Safe 7 6 s6_235 := by
  apply safe_succ 6 6 s6_235 [s7_310, s7_247, s7_217, s7_229] (by decide) s6_235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_310_safe
  · subst z; exact s7_247_safe
  · subst z; exact s7_217_safe
  · subst z; exact s7_229_safe
def s6_236 : State := ⟨[1,4,104,145], 66902575877979152000837097721963314438799638, 2, 2, 1, 0⟩
theorem s6_236_edges : next config 6 s6_236 = [] := by decide
theorem s6_236_safe : Safe 7 6 s6_236 := by
  apply safe_succ 6 6 s6_236 [] (by decide) s6_236_edges
  simp
def s6_237 : State := ⟨[1,4,104,145], 66902575877979310457161831102733322173874454, 1, 1, 1, 0⟩
theorem s6_237_edges : next config 6 s6_237 = [s7_248] := by decide
theorem s6_237_safe : Safe 7 6 s6_237 := by
  apply safe_succ 6 6 s6_237 [s7_248] (by decide) s6_237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_248_safe
def s6_238 : State := ⟨[1,4,104,145], 66902575877980419651437030803459631789179158, 2, 2, 1, 0⟩
theorem s6_238_edges : next config 6 s6_238 = [s7_326] := by decide
theorem s6_238_safe : Safe 7 6 s6_238 := by
  apply safe_succ 6 6 s6_238 [s7_326] (by decide) s6_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_326_safe
def s6_239 : State := ⟨[1,4,104,145], 66902575878303670554495229300841291106550038, 2, 2, 1, 0⟩
theorem s6_239_edges : next config 6 s6_239 = [s7_327] := by decide
theorem s6_239_safe : Safe 7 6 s6_239 := by
  apply safe_succ 6 6 s6_239 [s7_327] (by decide) s6_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_327_safe
def s6_240 : State := ⟨[1,4,104,146], 89204682205977458896226374345136223664800030, 1, 1, 1, 0⟩
theorem s6_240_edges : next config 6 s6_240 = [s7_249] := by decide
theorem s6_240_safe : Safe 7 6 s6_240 := by
  apply safe_succ 6 6 s6_240 [s7_249] (by decide) s6_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_249_safe
def s6_241 : State := ⟨[1,4,104,146], 89204682205977458896226374345136223664804118, 2, 2, 1, 0⟩
theorem s6_241_edges : next config 6 s6_241 = [s7_328] := by decide
theorem s6_241_safe : Safe 7 6 s6_241 := by
  apply safe_succ 6 6 s6_241 [s7_328] (by decide) s6_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_328_safe
def s6_242 : State := ⟨[1,4,104,146], 89204682205977458896226411238624371083903254, 1, 1, 1, 0⟩
theorem s6_242_edges : next config 6 s6_242 = [s7_250] := by decide
theorem s6_242_safe : Safe 7 6 s6_242 := by
  apply safe_succ 6 6 s6_242 [s7_250] (by decide) s6_242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_250_safe
def s6_243 : State := ⟨[1,4,104,146], 89204682205977458896226669493041403017625878, 2, 2, 1, 0⟩
theorem s6_243_edges : next config 6 s6_243 = [] := by decide
theorem s6_243_safe : Safe 7 6 s6_243 := by
  apply safe_succ 6 6 s6_243 [] (by decide) s6_243_edges
  simp
def s6_244 : State := ⟨[1,4,104,146], 89204682205978726546826602574537720368005398, 2, 2, 1, 0⟩
theorem s6_244_edges : next config 6 s6_244 = [] := by decide
theorem s6_244_safe : Safe 7 6 s6_244 := by
  apply safe_succ 6 6 s6_244 [] (by decide) s6_244_edges
  simp
def s6_245 : State := ⟨[1,4,104,146], 89204682206301977449884801071919379685376278, 2, 2, 1, 0⟩
theorem s6_245_edges : next config 6 s6_245 = [] := by decide
theorem s6_245_safe : Safe 7 6 s6_245 := by
  apply safe_succ 6 6 s6_245 [] (by decide) s6_245_edges
  simp
def s6_246 : State := ⟨[1,4,104,146], 89207404464912826403934081341995677810491670, 1, 1, 1, 0⟩
theorem s6_246_edges : next config 6 s6_246 = [s7_251] := by decide
theorem s6_246_safe : Safe 7 6 s6_246 := by
  apply safe_succ 6 6 s6_246 [s7_251] (by decide) s6_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_251_safe
def s6_247 : State := ⟨[1,4,104,146], 111504066275040398283908239119354858097934622, 1, 1, 1, 0⟩
theorem s6_247_edges : next config 6 s6_247 = [s7_252] := by decide
theorem s6_247_safe : Safe 7 6 s6_247 := by
  apply safe_succ 6 6 s6_247 [s7_252] (by decide) s6_247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_252_safe
def s6_248 : State := ⟨[1,4,104,146], 111504066275040398283908239119354858097938710, 2, 2, 1, 0⟩
theorem s6_248_edges : next config 6 s6_248 = [s7_329] := by decide
theorem s6_248_safe : Safe 7 6 s6_248 := by
  apply safe_succ 6 6 s6_248 [s7_329] (by decide) s6_248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_329_safe
def s6_249 : State := ⟨[1,4,104,146], 111504066275040398283908276012843005517037846, 1, 1, 1, 0⟩
theorem s6_249_edges : next config 6 s6_249 = [s7_253] := by decide
theorem s6_249_safe : Safe 7 6 s6_249 := by
  apply safe_succ 6 6 s6_249 [s7_253] (by decide) s6_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_253_safe
def s6_250 : State := ⟨[1,4,104,146], 111504066275040398283908534267260037450760470, 2, 2, 1, 0⟩
theorem s6_250_edges : next config 6 s6_250 = [] := by decide
theorem s6_250_safe : Safe 7 6 s6_250 := by
  apply safe_succ 6 6 s6_250 [] (by decide) s6_250_edges
  simp
def s6_251 : State := ⟨[1,4,104,146], 111504066275041665934508467348756354801139990, 2, 2, 1, 0⟩
theorem s6_251_edges : next config 6 s6_251 = [] := by decide
theorem s6_251_safe : Safe 7 6 s6_251 := by
  apply safe_succ 6 6 s6_251 [] (by decide) s6_251_edges
  simp
def s6_252 : State := ⟨[1,4,104,146], 111504066275364916837566665846138014118510870, 2, 2, 1, 0⟩
theorem s6_252_edges : next config 6 s6_252 = [] := by decide
theorem s6_252_safe : Safe 7 6 s6_252 := by
  apply safe_succ 6 6 s6_252 [] (by decide) s6_252_edges
  simp
def s6_253 : State := ⟨[1,4,104,146], 1516452374911937339954512343794631360047546646, 2, 2, 1, 0⟩
theorem s6_253_edges : next config 6 s6_253 = [] := by decide
theorem s6_253_safe : Safe 7 6 s6_253 := by
  apply safe_succ 6 6 s6_253 [] (by decide) s6_253_edges
  simp
def s6_254 : State := ⟨[1,4,104,146], 1538751758981000279342194208568849994480681238, 2, 2, 1, 0⟩
theorem s6_254_edges : next config 6 s6_254 = [] := by decide
theorem s6_254_safe : Safe 7 6 s6_254 := by
  apply safe_succ 6 6 s6_254 [] (by decide) s6_254_edges
  simp
def s6_255 : State := ⟨[1,4,104,161], 2923003275682652957531822822007071367225969545494, 2, 2, 1, 0⟩
theorem s6_255_edges : next config 6 s6_255 = [s7_140] := by decide
theorem s6_255_safe : Safe 7 6 s6_255 := by
  apply safe_succ 6 6 s6_255 [s7_140] (by decide) s6_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_140_safe
def s6_256 : State := ⟨[1,4,104,161], 4384504912332991141893630727796605172018365665558, 2, 2, 1, 0⟩
theorem s6_256_edges : next config 6 s6_256 = [s7_141] := by decide
theorem s6_256_safe : Safe 7 6 s6_256 := by
  apply safe_succ 6 6 s6_256 [s7_141] (by decide) s6_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_141_safe
def s6_257 : State := ⟨[1,4,104,162], 5846006551025023527781069414366386621401371050270, 1, 1, 1, 0⟩
theorem s6_257_edges : next config 6 s6_257 = [s7_254] := by decide
theorem s6_257_safe : Safe 7 6 s6_257 := by
  apply safe_succ 6 6 s6_257 [s7_254] (by decide) s6_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_254_safe
def s6_258 : State := ⟨[1,4,104,162], 5846006551025023527781069414366386621401371050774, 1, 1, 1, 0⟩
theorem s6_258_edges : next config 6 s6_258 = [] := by decide
theorem s6_258_safe : Safe 7 6 s6_258 := by
  apply safe_succ 6 6 s6_258 [] (by decide) s6_258_edges
  simp
def s6_259 : State := ⟨[1,4,104,162], 5846006551025023527781069414366386621401371054358, 2, 2, 1, 0⟩
theorem s6_259_edges : next config 6 s6_259 = [s7_935, s7_330, s7_142] := by decide
theorem s6_259_safe : Safe 7 6 s6_259 := by
  apply safe_succ 6 6 s6_259 [s7_935, s7_330, s7_142] (by decide) s6_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_935_safe
  · subst z; exact s7_330_safe
  · subst z; exact s7_142_safe
def s6_260 : State := ⟨[1,4,104,162], 5846006551025023527781069414403280109548790153494, 1, 1, 1, 0⟩
theorem s6_260_edges : next config 6 s6_260 = [s7_255] := by decide
theorem s6_260_safe : Safe 7 6 s6_260 := by
  apply safe_succ 6 6 s6_260 [s7_255] (by decide) s6_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_255_safe
def s6_261 : State := ⟨[1,4,104,162], 5846006551025023527939525739394915296588458950934, 1, 1, 1, 0⟩
theorem s6_261_edges : next config 6 s6_261 = [s7_256] := by decide
theorem s6_261_safe : Safe 7 6 s6_261 := by
  apply safe_succ 6 6 s6_261 [s7_256] (by decide) s6_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_256_safe
def s6_262 : State := ⟨[1,4,104,162], 5846006551025023529048720014594616022898074255638, 2, 2, 1, 0⟩
theorem s6_262_edges : next config 6 s6_262 = [] := by decide
theorem s6_262_safe : Safe 7 6 s6_262 := by
  apply safe_succ 6 6 s6_262 [] (by decide) s6_262_edges
  simp
def s6_263 : State := ⟨[1,4,104,162], 5846006551025023852299623072793113404557391626518, 2, 2, 1, 0⟩
theorem s6_263_edges : next config 6 s6_263 = [] := by decide
theorem s6_263_safe : Safe 7 6 s6_263 := by
  apply safe_succ 6 6 s6_263 [] (by decide) s6_263_edges
  simp
def s6_264 : State := ⟨[1,4,104,162], 5846006553747282463148577122073383480855516741910, 1, 1, 1, 0⟩
theorem s6_264_edges : next config 6 s6_264 = [s7_257] := by decide
theorem s6_264_safe : Safe 7 6 s6_264 := by
  apply safe_succ 6 6 s6_264 [s7_257] (by decide) s6_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_257_safe
def s6_265 : State := ⟨[1,4,104,162], 7307508186994796978301000393229171211330230747422, 1, 1, 1, 0⟩
theorem s6_265_edges : next config 6 s6_265 = [s7_258] := by decide
theorem s6_265_safe : Safe 7 6 s6_265 := by
  apply safe_succ 6 6 s6_265 [s7_258] (by decide) s6_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_258_safe
def s6_266 : State := ⟨[1,4,104,162], 7307508186994796978301000393229171211330230747926, 1, 1, 1, 0⟩
theorem s6_266_edges : next config 6 s6_266 = [] := by decide
theorem s6_266_safe : Safe 7 6 s6_266 := by
  apply safe_succ 6 6 s6_266 [] (by decide) s6_266_edges
  simp
def s6_267 : State := ⟨[1,4,104,162], 7307508186994796978301000393229171211330230751510, 2, 2, 1, 0⟩
theorem s6_267_edges : next config 6 s6_267 = [s7_936, s7_331, s7_143] := by decide
theorem s6_267_safe : Safe 7 6 s6_267 := by
  apply safe_succ 6 6 s6_267 [s7_936, s7_331, s7_143] (by decide) s6_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_936_safe
  · subst z; exact s7_331_safe
  · subst z; exact s7_143_safe
def s6_268 : State := ⟨[1,4,104,162], 7307508186994796978301000393266064699477649850646, 1, 1, 1, 0⟩
theorem s6_268_edges : next config 6 s6_268 = [s7_259] := by decide
theorem s6_268_safe : Safe 7 6 s6_268 := by
  apply safe_succ 6 6 s6_268 [s7_259] (by decide) s6_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_259_safe
def s6_269 : State := ⟨[1,4,104,162], 7307508186994796978459456718257699886517318648086, 1, 1, 1, 0⟩
theorem s6_269_edges : next config 6 s6_269 = [s7_260] := by decide
theorem s6_269_safe : Safe 7 6 s6_269 := by
  apply safe_succ 6 6 s6_269 [s7_260] (by decide) s6_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_260_safe
def s6_270 : State := ⟨[1,4,104,162], 7307508186994796979568650993457400612826933952790, 2, 2, 1, 0⟩
theorem s6_270_edges : next config 6 s6_270 = [] := by decide
theorem s6_270_safe : Safe 7 6 s6_270 := by
  apply safe_succ 6 6 s6_270 [] (by decide) s6_270_edges
  simp
def s6_271 : State := ⟨[1,4,104,162], 7307508186994797302819554051655897994486251323670, 2, 2, 1, 0⟩
theorem s6_271_edges : next config 6 s6_271 = [] := by decide
theorem s6_271_safe : Safe 7 6 s6_271 := by
  apply safe_succ 6 6 s6_271 [] (by decide) s6_271_edges
  simp
def s6_272 : State := ⟨[1,4,104,162], 17538019649672246873410548076096650778648831394070, 1, 1, 1, 0⟩
theorem s6_272_edges : next config 6 s6_272 = [s7_261] := by decide
theorem s6_272_safe : Safe 7 6 s6_272 := by
  apply safe_succ 6 6 s6_272 [s7_261] (by decide) s6_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_261_safe
def s6_273 : State := ⟨[1,4,104,162], 18999521285642020323930479054959435368577691091222, 1, 1, 1, 0⟩
theorem s6_273_edges : next config 6 s6_273 = [s7_262] := by decide
theorem s6_273_safe : Safe 7 6 s6_273 := by
  apply safe_succ 6 6 s6_273 [s7_262] (by decide) s6_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_262_safe
def s6_274 : State := ⟨[1,4,104,163], 11692013100348635200595808745231518700033691156758, 1, 1, 1, 0⟩
theorem s6_274_edges : next config 6 s6_274 = [s7_263, s7_148] := by decide
theorem s6_274_safe : Safe 7 6 s6_274 := by
  apply safe_succ 6 6 s6_274 [s7_263, s7_148] (by decide) s6_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_263_safe
  · subst z; exact s7_148_safe
def s6_275 : State := ⟨[1,4,104,163], 11692013101709764668279562599085017129752174067998, 1, 1, 1, 0⟩
theorem s6_275_edges : next config 6 s6_275 = [s7_264, s7_149] := by decide
theorem s6_275_safe : Safe 7 6 s6_275 := by
  apply safe_succ 6 6 s6_275 [s7_264, s7_149] (by decide) s6_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_264_safe
  · subst z; exact s7_149_safe
def s6_276 : State := ⟨[1,4,104,163], 13153514736318408651115739724094303289953960919326, 1, 1, 1, 0⟩
theorem s6_276_edges : next config 6 s6_276 = [s7_265, s7_150] := by decide
theorem s6_276_safe : Safe 7 6 s6_276 := by
  apply safe_succ 6 6 s6_276 [s7_265, s7_150] (by decide) s6_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_265_safe
  · subst z; exact s7_150_safe
def s6_277 : State := ⟨[1,4,104,163], 14615016373649311569319424556810586309618483396886, 1, 1, 1, 0⟩
theorem s6_277_edges : next config 6 s6_277 = [s7_266, s7_151] := by decide
theorem s6_277_safe : Safe 7 6 s6_277 := by
  apply safe_succ 6 6 s6_277 [s7_266, s7_151] (by decide) s6_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_266_safe
  · subst z; exact s7_151_safe
def s6_278 : State := ⟨[1,4,104,171], 3004847366356079505883267976928959390599965558505750, 0, 0, 1, 0⟩
theorem s6_278_edges : next config 6 s6_278 = [] := by decide
theorem s6_278_safe : Safe 7 6 s6_278 := by
  apply safe_succ 6 6 s6_278 [] (by decide) s6_278_edges
  simp
def s6_279 : State := ⟨[1,4,104,171], 3004847366356760070617109853855886139814829094928662, 0, 0, 1, 0⟩
theorem s6_279_edges : next config 6 s6_279 = [] := by decide
theorem s6_279_safe : Safe 7 6 s6_279 := by
  apply safe_succ 6 6 s6_279 [] (by decide) s6_279_edges
  simp
def s6_280 : State := ⟨[1,4,104,171], 3007770369628019052784307838886684959779823277900054, 0, 0, 1, 0⟩
theorem s6_280_edges : next config 6 s6_280 = [] := by decide
theorem s6_280_safe : Safe 7 6 s6_280 := by
  apply safe_succ 6 6 s6_280 [] (by decide) s6_280_edges
  simp
def s6_281 : State := ⟨[1,4,104,171], 3009231871264669390968669646792474493584615674020118, 0, 0, 1, 0⟩
theorem s6_281_edges : next config 6 s6_281 = [] := by decide
theorem s6_281_safe : Safe 7 6 s6_281 := by
  apply safe_succ 6 6 s6_281 [] (by decide) s6_281_edges
  simp
def s6_282 : State := ⟨[1,4,104,171], 3010693372903361423354557085479044275033998679408918, 0, 0, 1, 0⟩
theorem s6_282_edges : next config 6 s6_282 = [] := by decide
theorem s6_282_safe : Safe 7 6 s6_282 := by
  apply safe_succ 6 6 s6_282 [] (by decide) s6_282_edges
  simp
def s6_283 : State := ⟨[1,4,104,171], 3012154874539331196805077016457907059623927539106070, 0, 0, 1, 0⟩
theorem s6_283_edges : next config 6 s6_283 = [] := by decide
theorem s6_283_safe : Safe 7 6 s6_283 := by
  apply safe_succ 6 6 s6_283 [] (by decide) s6_283_edges
  simp
def s6_284 : State := ⟨[1,4,104,171], 4495579036431558788249500875518787823004426143072534, 0, 0, 1, 0⟩
theorem s6_284_edges : next config 6 s6_284 = [] := by decide
theorem s6_284_safe : Safe 7 6 s6_284 := by
  apply safe_succ 6 6 s6_284 [] (by decide) s6_284_edges
  simp
def s6_285 : State := ⟨[1,4,104,171], 4497040538067528561700020806497650607594355002769686, 0, 0, 1, 0⟩
theorem s6_285_edges : next config 6 s6_285 = [] := by decide
theorem s6_285_safe : Safe 7 6 s6_285 := by
  apply safe_succ 6 6 s6_285 [] (by decide) s6_285_edges
  simp
def s6_286 : State := ⟨[1,4,104,176], 95780971326419139128314594914659690004932607210488094, 1, 1, 1, 0⟩
theorem s6_286_edges : next config 6 s6_286 = [s7_267] := by decide
theorem s6_286_safe : Safe 7 6 s6_286 := by
  apply safe_succ 6 6 s6_286 [s7_267] (by decide) s6_286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_267_safe
def s6_287 : State := ⟨[1,4,104,176], 95780971326419139128314594914659690004932607210492182, 2, 2, 1, 0⟩
theorem s6_287_edges : next config 6 s6_287 = [s7_334] := by decide
theorem s6_287_safe : Safe 7 6 s6_287 := by
  apply safe_succ 6 6 s6_287 [s7_334] (by decide) s6_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_334_safe
def s6_288 : State := ⟨[1,4,104,176], 95780971326419139128314594914659726898420754629591318, 1, 1, 1, 0⟩
theorem s6_288_edges : next config 6 s6_288 = [s7_268] := by decide
theorem s6_288_safe : Safe 7 6 s6_288 := by
  apply safe_succ 6 6 s6_288 [s7_268] (by decide) s6_288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_268_safe
def s6_289 : State := ⟨[1,4,104,176], 95780971326419139128315862565259918234334103913693462, 2, 2, 1, 0⟩
theorem s6_289_edges : next config 6 s6_289 = [] := by decide
theorem s6_289_safe : Safe 7 6 s6_289 := by
  apply safe_succ 6 6 s6_289 [] (by decide) s6_289_edges
  simp
def s6_290 : State := ⟨[1,4,104,176], 95780971326419139128639113468318116731715763231064342, 2, 2, 1, 0⟩
theorem s6_290_edges : next config 6 s6_290 = [] := by decide
theorem s6_290_safe : Safe 7 6 s6_290 := by
  apply safe_succ 6 6 s6_290 [] (by decide) s6_290_edges
  simp
def s6_291 : State := ⟨[1,4,104,176], 95782432805755724832702175457956688015303901637050654, 1, 1, 1, 0⟩
theorem s6_291_edges : next config 6 s6_291 = [s7_269] := by decide
theorem s6_291_safe : Safe 7 6 s6_291 := by
  apply safe_succ 6 6 s6_291 [s7_269] (by decide) s6_291_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_269_safe
def s6_292 : State := ⟨[1,4,104,176], 95782432805755724832702175457956688015303901637054742, 2, 2, 1, 0⟩
theorem s6_292_edges : next config 6 s6_292 = [s7_335] := by decide
theorem s6_292_safe : Safe 7 6 s6_292 := by
  apply safe_succ 6 6 s6_292 [s7_335] (by decide) s6_292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_335_safe
def s6_293 : State := ⟨[1,4,104,176], 95782432805755724832702175457956724908792049056153878, 1, 1, 1, 0⟩
theorem s6_293_edges : next config 6 s6_293 = [s7_270] := by decide
theorem s6_293_safe : Safe 7 6 s6_293 := by
  apply safe_succ 6 6 s6_293 [s7_270] (by decide) s6_293_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_270_safe
def s6_294 : State := ⟨[1,4,104,176], 95782432805755724832703443108556916244705398340256022, 2, 2, 1, 0⟩
theorem s6_294_edges : next config 6 s6_294 = [] := by decide
theorem s6_294_safe : Safe 7 6 s6_294 := by
  apply safe_succ 6 6 s6_294 [] (by decide) s6_294_edges
  simp
def s6_295 : State := ⟨[1,4,104,176], 95782432805755724833026694011615114742087057657626902, 2, 2, 1, 0⟩
theorem s6_295_edges : next config 6 s6_295 = [] := by decide
theorem s6_295_safe : Safe 7 6 s6_295 := by
  apply safe_succ 6 6 s6_295 [] (by decide) s6_295_edges
  simp
def s6_296 : State := ⟨[1,4,104,186], 25206488152739816570824091998107884237136087752128453476630, 0, 0, 1, 0⟩
theorem s6_296_edges : next config 6 s6_296 = [] := by decide
theorem s6_296_safe : Safe 7 6 s6_296 := by
  apply safe_succ 6 6 s6_296 [] (by decide) s6_296_edges
  simp
def s6_297 : State := ⟨[1,4,104,186], 31483589888126497333298751953631796799384944766865415143702, 0, 0, 1, 0⟩
theorem s6_297_edges : next config 6 s6_297 = [] := by decide
theorem s6_297_safe : Safe 7 6 s6_297 := by
  apply safe_succ 6 6 s6_297 [] (by decide) s6_297_edges
  simp
def s6_298 : State := ⟨[1,4,104,186], 1645504655400920657661060799697537701498749991578019906763948310, 0, 0, 1, 0⟩
theorem s6_298_edges : next config 6 s6_298 = [] := by decide
theorem s6_298_safe : Safe 7 6 s6_298 := by
  apply safe_succ 6 6 s6_298 [] (by decide) s6_298_edges
  simp
def s6_299 : State := ⟨[1,4,104,186], 1645504655400920657683360183766600640886431856352238541197082902, 0, 0, 1, 0⟩
theorem s6_299_edges : next config 6 s6_299 = [] := by decide
theorem s6_299_safe : Safe 7 6 s6_299 := by
  apply safe_succ 6 6 s6_299 [] (by decide) s6_299_edges
  simp
def s6_300 : State := ⟨[1,4,104,186], 1645529763807862204294913162061108039598271527909204316878078230, 0, 0, 1, 0⟩
theorem s6_300_edges : next config 6 s6_300 = [] := by decide
theorem s6_300_safe : Safe 7 6 s6_300 := by
  apply safe_succ 6 6 s6_300 [] (by decide) s6_300_edges
  simp
def s6_301 : State := ⟨[1,4,104,186], 1645536040909597590975675636721063563510833776766219053839745302, 0, 0, 1, 0⟩
theorem s6_301_edges : next config 6 s6_301 = [] := by decide
theorem s6_301_safe : Safe 7 6 s6_301 := by
  apply safe_succ 6 6 s6_301 [] (by decide) s6_301_edges
  simp
def s6_302 : State := ⟨[1,4,104,186], 2056880794731222168132899498611815774565972949670040061010313494, 0, 0, 1, 0⟩
theorem s6_302_edges : next config 6 s6_302 = [] := by decide
theorem s6_302_safe : Safe 7 6 s6_302 := by
  apply safe_succ 6 6 s6_302 [] (by decide) s6_302_edges
  simp
def s6_303 : State := ⟨[1,4,104,186], 2056887071832957554791362589202708359090853333752836163538845974, 0, 0, 1, 0⟩
theorem s6_303_edges : next config 6 s6_303 = [] := by decide
theorem s6_303_safe : Safe 7 6 s6_303 := by
  apply safe_succ 6 6 s6_303 [] (by decide) s6_303_edges
  simp
def s6_304 : State := ⟨[1,4,104,193], 12554203470773361528692425967539785988779216216842173485334, 2, 2, 1, 0⟩
theorem s6_304_edges : next config 6 s6_304 = [] := by decide
theorem s6_304_safe : Safe 7 6 s6_304 := by
  apply safe_succ 6 6 s6_304 [] (by decide) s6_304_edges
  simp
def s6_305 : State := ⟨[1,4,104,193], 12554203470773361528692425968807436589007445618338876686614, 2, 2, 1, 0⟩
theorem s6_305_edges : next config 6 s6_305 = [] := by decide
theorem s6_305_safe : Safe 7 6 s6_305 := by
  apply safe_succ 6 6 s6_305 [] (by decide) s6_305_edges
  simp
def s6_306 : State := ⟨[1,4,104,193], 12554203470773361528692426292058339647205942999998194057494, 2, 2, 1, 0⟩
theorem s6_306_edges : next config 6 s6_306 = [] := by decide
theorem s6_306_safe : Safe 7 6 s6_306 := by
  apply safe_succ 6 6 s6_306 [] (by decide) s6_306_edges
  simp
def s6_307 : State := ⟨[1,4,104,193], 18831305206160042291847650656905575477954822446442671575318, 2, 2, 1, 0⟩
theorem s6_307_edges : next config 6 s6_307 = [] := by decide
theorem s6_307_safe : Safe 7 6 s6_307 := by
  apply safe_succ 6 6 s6_307 [] (by decide) s6_307_edges
  simp
def s6_308 : State := ⟨[1,4,104,193], 18831305206160042291847650658173226078183051847939374776598, 2, 2, 1, 0⟩
theorem s6_308_edges : next config 6 s6_308 = [] := by decide
theorem s6_308_safe : Safe 7 6 s6_308 := by
  apply safe_succ 6 6 s6_308 [] (by decide) s6_308_edges
  simp
def s6_309 : State := ⟨[1,4,104,193], 18831305206160042291847650981424129136381549229598692147478, 2, 2, 1, 0⟩
theorem s6_309_edges : next config 6 s6_309 = [] := by decide
theorem s6_309_safe : Safe 7 6 s6_309 := by
  apply safe_succ 6 6 s6_309 [] (by decide) s6_309_edges
  simp
def s6_310 : State := ⟨[1,4,104,194], 25108406941546723057044569547796995747910676320633778934038, 2, 2, 1, 0⟩
theorem s6_310_edges : next config 6 s6_310 = [s7_172] := by decide
theorem s6_310_safe : Safe 7 6 s6_310 := by
  apply safe_succ 6 6 s6_310 [s7_172] (by decide) s6_310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_172_safe
def s6_311 : State := ⟨[1,4,104,194], 25108406941546723057044569549064646348138905722130482135318, 2, 2, 1, 0⟩
theorem s6_311_edges : next config 6 s6_311 = [] := by decide
theorem s6_311_safe : Safe 7 6 s6_311 := by
  apply safe_succ 6 6 s6_311 [] (by decide) s6_311_edges
  simp
def s6_312 : State := ⟨[1,4,104,194], 25108406941546723057044569872315549406337403103789799506198, 2, 2, 1, 0⟩
theorem s6_312_edges : next config 6 s6_312 = [s7_173] := by decide
theorem s6_312_safe : Safe 7 6 s6_312 := by
  apply safe_succ 6 6 s6_312 [s7_173] (by decide) s6_312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_173_safe
def s6_313 : State := ⟨[1,4,104,194], 31385508676933403819519229503320908310159533335370740601110, 2, 2, 1, 0⟩
theorem s6_313_edges : next config 6 s6_313 = [s7_174] := by decide
theorem s6_313_safe : Safe 7 6 s6_313 := by
  apply safe_succ 6 6 s6_313 [s7_174] (by decide) s6_313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_174_safe
def s6_314 : State := ⟨[1,4,104,194], 31385508676933403819519229504588558910387762736867443802390, 2, 2, 1, 0⟩
theorem s6_314_edges : next config 6 s6_314 = [] := by decide
theorem s6_314_safe : Safe 7 6 s6_314 := by
  apply safe_succ 6 6 s6_314 [] (by decide) s6_314_edges
  simp
def s6_315 : State := ⟨[1,4,104,194], 31385508676933403819519229827839461968586260118526761173270, 2, 2, 1, 0⟩
theorem s6_315_edges : next config 6 s6_315 = [s7_175] := by decide
theorem s6_315_safe : Safe 7 6 s6_315 := by
  apply safe_succ 6 6 s6_315 [s7_175] (by decide) s6_315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_175_safe
def s6_316 : State := ⟨[1,4,104,208], 411376139330301510561043381120255531963449332437156377911169302, 2, 2, 1, 0⟩
theorem s6_316_edges : next config 6 s6_316 = [s7_176] := by decide
theorem s6_316_safe : Safe 7 6 s6_316 := by
  apply safe_succ 6 6 s6_316 [s7_176] (by decide) s6_316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_176_safe
def s6_317 : State := ⟨[1,4,104,208], 411376139330301510561043381120580050517107759163939533931741462, 2, 2, 1, 0⟩
theorem s6_317_edges : next config 6 s6_317 = [s7_177] := by decide
theorem s6_317_safe : Safe 7 6 s6_317 := by
  apply safe_succ 6 6 s6_317 [s7_177] (by decide) s6_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_177_safe
def s6_318 : State := ⟨[1,4,104,208], 411382416432036897219506471711148116488329716519952480439701782, 2, 2, 1, 0⟩
theorem s6_318_edges : next config 6 s6_318 = [s7_178] := by decide
theorem s6_318_safe : Safe 7 6 s6_318 := by
  apply safe_succ 6 6 s6_318 [s7_178] (by decide) s6_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_178_safe
def s6_319 : State := ⟨[1,4,104,208], 411382416432036897219506471711472635041988143246735636460273942, 2, 2, 1, 0⟩
theorem s6_319_edges : next config 6 s6_319 = [s7_179] := by decide
theorem s6_319_safe : Safe 7 6 s6_319 := by
  apply safe_succ 6 6 s6_319 [s7_179] (by decide) s6_319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_179_safe
def s6_320 : State := ⟨[1,4,104,214], 26328072917139296675995959295829545419678286193931909173625291030, 0, 0, 1, 0⟩
theorem s6_320_edges : next config 6 s6_320 = [] := by decide
theorem s6_320_safe : Safe 7 6 s6_320 := by
  apply safe_succ 6 6 s6_320 [] (by decide) s6_320_edges
  simp
def s6_321 : State := ⟨[1,4,104,214], 26328072917139296676018258679898608359065968058706127808058425622, 0, 0, 1, 0⟩
theorem s6_321_edges : next config 6 s6_321 = [] := by decide
theorem s6_321_safe : Safe 7 6 s6_321 := by
  apply safe_succ 6 6 s6_321 [] (by decide) s6_321_edges
  simp
def s6_322 : State := ⟨[1,4,104,214], 27973577474460502716723680785680936043602736090115993900591153430, 0, 0, 1, 0⟩
theorem s6_322_edges : next config 6 s6_322 = [] := by decide
theorem s6_322_safe : Safe 7 6 s6_322 := by
  apply safe_succ 6 6 s6_322 [] (by decide) s6_322_edges
  simp
def s6_323 : State := ⟨[1,4,104,214], 27973577474460502716745980169749998982990417954890212535024288022, 0, 0, 1, 0⟩
theorem s6_323_edges : next config 6 s6_323 = [] := by decide
theorem s6_323_safe : Safe 7 6 s6_323 := by
  apply safe_succ 6 6 s6_323 [] (by decide) s6_323_edges
  simp
def s6_324 : State := ⟨[1,4,104,214], 27973602582867444263357533148044506381702257626447178310705283350, 0, 0, 1, 0⟩
theorem s6_324_edges : next config 6 s6_324 = [] := by decide
theorem s6_324_safe : Safe 7 6 s6_324 := by
  apply safe_succ 6 6 s6_324 [] (by decide) s6_324_edges
  simp
def s6_325 : State := ⟨[1,4,104,214], 27973608859969179650038295622704461905614819875304193047666950422, 0, 0, 1, 0⟩
theorem s6_325_edges : next config 6 s6_325 = [] := by decide
theorem s6_325_safe : Safe 7 6 s6_325 := by
  apply safe_succ 6 6 s6_325 [] (by decide) s6_325_edges
  simp
def s6_326 : State := ⟨[1,4,104,214], 28384953613790804227195519484595214116669959048208014054837518614, 0, 0, 1, 0⟩
theorem s6_326_edges : next config 6 s6_326 = [] := by decide
theorem s6_326_safe : Safe 7 6 s6_326 := by
  apply safe_succ 6 6 s6_326 [] (by decide) s6_326_edges
  simp
def s6_327 : State := ⟨[1,4,104,214], 28384959890892539613853982575186106701194839432290810157366051094, 0, 0, 1, 0⟩
theorem s6_327_edges : next config 6 s6_327 = [] := by decide
theorem s6_327_safe : Safe 7 6 s6_327 := by
  apply safe_succ 6 6 s6_327 [] (by decide) s6_327_edges
  simp
def s6_328 : State := ⟨[1,4,104,225], 53919893334301279589334030175060108468398742001655650290121324957974, 2, 2, 1, 0⟩
theorem s6_328_edges : next config 6 s6_328 = [] := by decide
theorem s6_328_safe : Safe 7 6 s6_328 := by
  apply safe_succ 6 6 s6_328 [] (by decide) s6_328_edges
  simp
def s6_329 : State := ⟨[1,4,104,225], 80879840001451919384001045261399174408194009497269473556361398784278, 2, 2, 1, 0⟩
theorem s6_329_edges : next config 6 s6_329 = [] := by decide
theorem s6_329_safe : Safe 7 6 s6_329 := by
  apply safe_succ 6 6 s6_329 [] (by decide) s6_329_edges
  simp
def s6_330 : State := ⟨[1,4,104,228], 431359146674410236714672241398098891036211902405710909529616623403294, 1, 1, 1, 0⟩
theorem s6_330_edges : next config 6 s6_330 = [] := by decide
theorem s6_330_safe : Safe 7 6 s6_330 := by
  apply safe_succ 6 6 s6_330 [] (by decide) s6_330_edges
  simp
def s6_331 : State := ⟨[1,4,104,228], 431359146674410236714672241398098891036211902405747803017764042506518, 1, 1, 1, 0⟩
theorem s6_331_edges : next config 6 s6_331 = [] := by decide
theorem s6_331_safe : Safe 7 6 s6_331 := by
  apply safe_succ 6 6 s6_331 [] (by decide) s6_331_edges
  simp
def s6_332 : State := ⟨[1,4,104,228], 458319093341560876509339256479674003839114031412837488291811942269214, 1, 1, 1, 0⟩
theorem s6_332_edges : next config 6 s6_332 = [] := by decide
theorem s6_332_safe : Safe 7 6 s6_332 := by
  apply safe_succ 6 6 s6_332 [] (by decide) s6_332_edges
  simp
def s6_333 : State := ⟨[1,4,104,228], 458319093341560876509339256479674003839114031412874381779959361372438, 1, 1, 1, 0⟩
theorem s6_333_edges : next config 6 s6_333 = [] := by decide
theorem s6_333_safe : Safe 7 6 s6_333 := by
  apply safe_succ 6 6 s6_333 [] (by decide) s6_333_edges
  simp
def s6_334 : State := ⟨[1,4,104,236], 110427941548649020598956093796438192039475761146371246632432346440204574, 1, 1, 1, 0⟩
theorem s6_334_edges : next config 6 s6_334 = [] := by decide
theorem s6_334_safe : Safe 7 6 s6_334 := by
  apply safe_succ 6 6 s6_334 [] (by decide) s6_334_edges
  simp
def s6_335 : State := ⟨[1,4,104,236], 110427941548649020598956093796438192039475761146371283525920493859307798, 1, 1, 1, 0⟩
theorem s6_335_edges : next config 6 s6_335 = [] := by decide
theorem s6_335_safe : Safe 7 6 s6_335 := by
  apply safe_succ 6 6 s6_335 [] (by decide) s6_335_edges
  simp
def s6_336 : State := ⟨[1,4,104,236], 117329687895439584386390849658709772974056135103126219193875962372620574, 1, 1, 1, 0⟩
theorem s6_336_edges : next config 6 s6_336 = [] := by decide
theorem s6_336_safe : Safe 7 6 s6_336 := by
  apply safe_succ 6 6 s6_336 [] (by decide) s6_336_edges
  simp
def s6_337 : State := ⟨[1,4,104,236], 117329687895439584386390849658709772974056135103126256087364109791723798, 1, 1, 1, 0⟩
theorem s6_337_edges : next config 6 s6_337 = [] := by decide
theorem s6_337_safe : Safe 7 6 s6_337 := by
  apply safe_succ 6 6 s6_337 [] (by decide) s6_337_edges
  simp
def s6_338 : State := ⟨[1,4,104,240], 1766847064778384329583297500765219601308401802593384324150367613366636822, 2, 2, 1, 0⟩
theorem s6_338_edges : next config 6 s6_338 = [] := by decide
theorem s6_338_safe : Safe 7 6 s6_338 := by
  apply safe_succ 6 6 s6_338 [] (by decide) s6_338_edges
  simp
def s6_339 : State := ⟨[1,4,104,240], 1766874024725051480223092167758005875740544816596271146450200355470905622, 2, 2, 1, 0⟩
theorem s6_339_edges : next config 6 s6_339 = [] := by decide
theorem s6_339_safe : Safe 7 6 s6_339 := by
  apply safe_succ 6 6 s6_339 [] (by decide) s6_339_edges
  simp
def s6_340 : State := ⟨[1,4,108,129], 1020847445643006815001232111070125031710, 1, 1, 1, 0⟩
theorem s6_340_edges : next config 6 s6_340 = [s7_214] := by decide
theorem s6_340_safe : Safe 7 6 s6_340 := by
  apply safe_succ 6 6 s6_340 [s7_214] (by decide) s6_340_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_214_safe
def s6_341 : State := ⟨[1,4,108,129], 1020847445643006815038125599217544134934, 1, 1, 1, 0⟩
theorem s6_341_edges : next config 6 s6_341 = [s7_215] := by decide
theorem s6_341_safe : Safe 7 6 s6_341 := by
  apply safe_succ 6 6 s6_341 [s7_215] (by decide) s6_341_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_215_safe
def s6_342 : State := ⟨[1,4,108,130], 1701412179484883741927981325933661454622, 1, 1, 1, 0⟩
theorem s6_342_edges : next config 6 s6_342 = [] := by decide
theorem s6_342_safe : Safe 7 6 s6_342 := by
  apply safe_succ 6 6 s6_342 [] (by decide) s6_342_edges
  simp
def s6_343 : State := ⟨[1,4,108,130], 1701412179484883741964874814081080557846, 1, 1, 1, 0⟩
theorem s6_343_edges : next config 6 s6_343 = [] := by decide
theorem s6_343_safe : Safe 7 6 s6_343 := by
  apply safe_succ 6 6 s6_343 [] (by decide) s6_343_edges
  simp
def s6_344 : State := ⟨[1,4,108,130], 4423671114852391449634978185387807146262, 1, 1, 1, 0⟩
theorem s6_344_edges : next config 6 s6_344 = [] := by decide
theorem s6_344_safe : Safe 7 6 s6_344 := by
  apply safe_succ 6 6 s6_344 [] (by decide) s6_344_edges
  simp
def s6_345 : State := ⟨[1,4,108,131], 3062541647168637595781479755660734300446, 1, 1, 1, 0⟩
theorem s6_345_edges : next config 6 s6_345 = [] := by decide
theorem s6_345_safe : Safe 7 6 s6_345 := by
  apply safe_succ 6 6 s6_345 [] (by decide) s6_345_edges
  simp
def s6_346 : State := ⟨[1,4,108,132], 5784800582536145303488476615114879992094, 1, 1, 1, 0⟩
theorem s6_346_edges : next config 6 s6_346 = [] := by decide
theorem s6_346_safe : Safe 7 6 s6_346 := by
  apply safe_succ 6 6 s6_346 [] (by decide) s6_346_edges
  simp
def s6_347 : State := ⟨[1,4,108,132], 5784800582536145303525370103262299095318, 1, 1, 1, 0⟩
theorem s6_347_edges : next config 6 s6_347 = [] := by decide
theorem s6_347_safe : Safe 7 6 s6_347 := by
  apply safe_succ 6 6 s6_347 [] (by decide) s6_347_edges
  simp
def s6_348 : State := ⟨[1,4,108,136], 87452568643561376534698382398739250741534, 1, 1, 1, 0⟩
theorem s6_348_edges : next config 6 s6_348 = [] := by decide
theorem s6_348_safe : Safe 7 6 s6_348 := by
  apply safe_succ 6 6 s6_348 [] (by decide) s6_348_edges
  simp
def s6_349 : State := ⟨[1,4,108,136], 87452568643561376534735275886886669844758, 1, 1, 1, 0⟩
theorem s6_349_edges : next config 6 s6_349 = [] := by decide
theorem s6_349_safe : Safe 7 6 s6_349 := by
  apply safe_succ 6 6 s6_349 [] (by decide) s6_349_edges
  simp
def s6_350 : State := ⟨[1,4,108,144], 22301085481242424271423792755544568094589214, 1, 1, 1, 0⟩
theorem s6_350_edges : next config 6 s6_350 = [s7_216] := by decide
theorem s6_350_safe : Safe 7 6 s6_350 := by
  apply safe_succ 6 6 s6_350 [s7_216] (by decide) s6_350_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_216_safe
def s6_351 : State := ⟨[1,4,108,144], 22301085481242424271423829649032715513692438, 1, 1, 1, 0⟩
theorem s6_351_edges : next config 6 s6_351 = [s7_217] := by decide
theorem s6_351_safe : Safe 7 6 s6_351 := by
  apply safe_succ 6 6 s6_351 [s7_217] (by decide) s6_351_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_217_safe
def s6_352 : State := ⟨[1,4,108,145], 44601830679773047412959511028192929600700694, 1, 1, 1, 0⟩
theorem s6_352_edges : next config 6 s6_352 = [s7_336] := by decide
theorem s6_352_safe : Safe 7 6 s6_352 := by
  apply safe_succ 6 6 s6_352 [s7_336] (by decide) s6_352_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_336_safe
def s6_353 : State := ⟨[1,4,108,160], 1461501637671185630004814720790765915862521151774, 1, 1, 1, 0⟩
theorem s6_353_edges : next config 6 s6_353 = [] := by decide
theorem s6_353_safe : Safe 7 6 s6_353 := by
  apply safe_succ 6 6 s6_353 [] (by decide) s6_353_edges
  simp
def s6_354 : State := ⟨[1,4,108,160], 1461501637671185630004814720827659404009940254998, 1, 1, 1, 0⟩
theorem s6_354_edges : next config 6 s6_354 = [] := by decide
theorem s6_354_safe : Safe 7 6 s6_354 := by
  apply safe_succ 6 6 s6_354 [] (by decide) s6_354_edges
  simp
def s6_355 : State := ⟨[1,4,108,192], 6277101735386680764176072135008796304176838340670623121694, 1, 1, 1, 0⟩
theorem s6_355_edges : next config 6 s6_355 = [] := by decide
theorem s6_355_safe : Safe 7 6 s6_355 := by
  apply safe_succ 6 6 s6_355 [] (by decide) s6_355_edges
  simp
def s6_356 : State := ⟨[1,4,108,192], 6277101735386680764176072135008796304213731828818042224918, 1, 1, 1, 0⟩
theorem s6_356_edges : next config 6 s6_356 = [] := by decide
theorem s6_356_safe : Safe 7 6 s6_356 := by
  apply safe_succ 6 6 s6_356 [] (by decide) s6_356_edges
  simp
def s6_357 : State := ⟨[1,4,108,192], 18831305206160042291847650981424129136381549229598692147478, 1, 1, 1, 0⟩
theorem s6_357_edges : next config 6 s6_357 = [] := by decide
theorem s6_357_safe : Safe 7 6 s6_357 := by
  apply safe_succ 6 6 s6_357 [] (by decide) s6_357_edges
  simp
def s6_358 : State := ⟨[1,4,108,193], 12554203470773361528011861558216462720316087273282076737814, 1, 1, 1, 0⟩
theorem s6_358_edges : next config 6 s6_358 = [] := by decide
theorem s6_358_safe : Safe 7 6 s6_358 := by
  apply safe_succ 6 6 s6_358 [] (by decide) s6_358_edges
  simp
def s6_359 : State := ⟨[1,4,108,210], 1645504557321206042244173864763652482432620666705499243033985302, 0, 0, 1, 0⟩
theorem s6_359_edges : next config 6 s6_359 = [] := by decide
theorem s6_359_safe : Safe 7 6 s6_359 := by
  apply safe_succ 6 6 s6_359 [] (by decide) s6_359_edges
  simp
def s6_360 : State := ⟨[1,4,108,210], 1645504557321206042266473248832715421820302531479717877467119894, 0, 0, 1, 0⟩
theorem s6_360_edges : next config 6 s6_360 = [] := by decide
theorem s6_360_safe : Safe 7 6 s6_360 := by
  apply safe_succ 6 6 s6_360 [] (by decide) s6_360_edges
  simp
def s6_361 : State := ⟨[1,4,108,210], 1645529665728147588878026227127222820532142203036683653148115222, 0, 0, 1, 0⟩
theorem s6_361_edges : next config 6 s6_361 = [] := by decide
theorem s6_361_safe : Safe 7 6 s6_361 := by
  apply safe_succ 6 6 s6_361 [] (by decide) s6_361_edges
  simp
def s6_362 : State := ⟨[1,4,108,210], 1645535942829882975558788701787178344444704451893698390109782294, 0, 0, 1, 0⟩
theorem s6_362_edges : next config 6 s6_362 = [] := by decide
theorem s6_362_safe : Safe 7 6 s6_362 := by
  apply safe_succ 6 6 s6_362 [] (by decide) s6_362_edges
  simp
def s6_363 : State := ⟨[1,4,108,210], 2056880696651507552716012563677930555499843624797519397280350486, 0, 0, 1, 0⟩
theorem s6_363_edges : next config 6 s6_363 = [] := by decide
theorem s6_363_safe : Safe 7 6 s6_363 := by
  apply safe_succ 6 6 s6_363 [] (by decide) s6_363_edges
  simp
def s6_364 : State := ⟨[1,4,108,210], 2056886973753242939374475654268823140024724008880315499808882966, 0, 0, 1, 0⟩
theorem s6_364_edges : next config 6 s6_364 = [] := by decide
theorem s6_364_safe : Safe 7 6 s6_364 := by
  apply safe_succ 6 6 s6_364 [] (by decide) s6_364_edges
  simp
def s6_365 : State := ⟨[1,4,108,224], 26959946667150639794667015087359913385438274310615055377310198858014, 1, 1, 1, 0⟩
theorem s6_365_edges : next config 6 s6_365 = [] := by decide
theorem s6_365_safe : Safe 7 6 s6_365 := by
  apply safe_succ 6 6 s6_365 [] (by decide) s6_365_edges
  simp
def s6_366 : State := ⟨[1,4,108,224], 26959946667150639794667015087359913385438274310651948865457617961238, 1, 1, 1, 0⟩
theorem s6_366_edges : next config 6 s6_366 = [] := by decide
theorem s6_366_safe : Safe 7 6 s6_366 := by
  apply safe_succ 6 6 s6_366 [] (by decide) s6_366_edges
  simp
def s6_367 : State := ⟨[1,4,108,232], 6901746346790563787434755862277365735162910102058461038058730812408094, 1, 1, 1, 0⟩
theorem s6_367_edges : next config 6 s6_367 = [] := by decide
theorem s6_367_safe : Safe 7 6 s6_367 := by
  apply safe_succ 6 6 s6_367 [] (by decide) s6_367_edges
  simp
def s6_368 : State := ⟨[1,4,108,232], 6901746346790563787434755862277365735162910102058497931546878231511318, 1, 1, 1, 0⟩
theorem s6_368_edges : next config 6 s6_368 = [] := by decide
theorem s6_368_safe : Safe 7 6 s6_368 := by
  apply safe_succ 6 6 s6_368 [] (by decide) s6_368_edges
  simp
def s6_369 : State := ⟨[1,4,108,236], 110427941548649020598956093796432747521929544684614259365496594169397534, 1, 1, 1, 0⟩
theorem s6_369_edges : next config 6 s6_369 = [] := by decide
theorem s6_369_safe : Safe 7 6 s6_369 := by
  apply safe_succ 6 6 s6_369 [] (by decide) s6_369_edges
  simp
def s6_370 : State := ⟨[1,4,108,236], 110427941548649020598956093796432747521929544684614296258984741588500758, 1, 1, 1, 0⟩
theorem s6_370_edges : next config 6 s6_370 = [] := by decide
theorem s6_370_safe : Safe 7 6 s6_370 := by
  apply safe_succ 6 6 s6_370 [] (by decide) s6_370_edges
  simp
def s6_371 : State := ⟨[1,4,112,145], 44602511249354385185159187008731186194354454, 2, 2, 1, 0⟩
theorem s6_371_edges : next config 6 s6_371 = [] := by decide
theorem s6_371_safe : Safe 7 6 s6_371 := by
  apply safe_succ 6 6 s6_371 [] (by decide) s6_371_edges
  simp
def s6_372 : State := ⟨[1,4,112,145], 66902575883151166449767978532164684163911958, 2, 2, 1, 0⟩
theorem s6_372_edges : next config 6 s6_372 = [] := by decide
theorem s6_372_safe : Safe 7 6 s6_372 := by
  apply safe_succ 6 6 s6_372 [] (by decide) s6_372_edges
  simp
def s6_373 : State := ⟨[1,4,112,194], 25108406941546723057044574719811444679086634427182856868118, 2, 2, 1, 0⟩
theorem s6_373_edges : next config 6 s6_373 = [] := by decide
theorem s6_373_safe : Safe 7 6 s6_373 := by
  apply safe_succ 6 6 s6_373 [] (by decide) s6_373_edges
  simp
def s6_374 : State := ⟨[1,4,112,194], 31385508676933403819519234675335357241335491441919818535190, 2, 2, 1, 0⟩
theorem s6_374_edges : next config 6 s6_374 = [] := by decide
theorem s6_374_safe : Safe 7 6 s6_374 := by
  apply safe_succ 6 6 s6_374 [] (by decide) s6_374_edges
  simp
def s6_375 : State := ⟨[1,4,120,145], 44601832008676524644216957205216833860469014, 1, 1, 1, 0⟩
theorem s6_375_edges : next config 6 s6_375 = [] := by decide
theorem s6_375_safe : Safe 7 6 s6_375 := by
  apply safe_succ 6 6 s6_375 [] (by decide) s6_375_edges
  simp
def s6_376 : State := ⟨[1,4,120,186], 25206486656162139943980832985530400451535179431513809813782, 0, 0, 1, 0⟩
theorem s6_376_edges : next config 6 s6_376 = [] := by decide
theorem s6_376_safe : Safe 7 6 s6_376 := by
  apply safe_succ 6 6 s6_376 [] (by decide) s6_376_edges
  simp
def s6_377 : State := ⟨[1,4,120,186], 31483588391548820706455492941054313013784036446250771480854, 0, 0, 1, 0⟩
theorem s6_377_edges : next config 6 s6_377 = [] := by decide
theorem s6_377_safe : Safe 7 6 s6_377 := by
  apply safe_succ 6 6 s6_377 [] (by decide) s6_377_edges
  simp
def s6_378 : State := ⟨[1,4,121,145], 44601833337904520429132830109023894140813590, 1, 1, 1, 0⟩
theorem s6_378_edges : next config 6 s6_378 = [s7_337] := by decide
theorem s6_378_safe : Safe 7 6 s6_378 := by
  apply safe_succ 6 6 s6_378 [s7_337] (by decide) s6_378_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_337_safe
def s6_379 : State := ⟨[1,4,162,194], 25108406947392729606368181200329325475124137975310257819926, 2, 2, 1, 0⟩
theorem s6_379_edges : next config 6 s6_379 = [] := by decide
theorem s6_379_safe : Safe 7 6 s6_379 := by
  apply safe_succ 6 6 s6_379 [] (by decide) s6_379_edges
  simp
def s6_380 : State := ⟨[1,4,162,194], 31385508682779410368842841155853238037372994990047219486998, 2, 2, 1, 0⟩
theorem s6_380_edges : next config 6 s6_380 = [] := by decide
theorem s6_380_safe : Safe 7 6 s6_380 := by
  apply safe_succ 6 6 s6_380 [] (by decide) s6_380_edges
  simp
def s6_381 : State := ⟨[1,4,186,194], 25206486656162139943980832985530400451535179431513809813782, 0, 0, 1, 0⟩
theorem s6_381_edges : next config 6 s6_381 = [] := by decide
theorem s6_381_safe : Safe 7 6 s6_381 := by
  apply safe_succ 6 6 s6_381 [] (by decide) s6_381_edges
  simp
def s6_382 : State := ⟨[1,4,186,194], 25206488152739816570824091998107884237136087752128453476630, 0, 0, 1, 0⟩
theorem s6_382_edges : next config 6 s6_382 = [] := by decide
theorem s6_382_safe : Safe 7 6 s6_382 := by
  apply safe_succ 6 6 s6_382 [] (by decide) s6_382_edges
  simp
def s6_383 : State := ⟨[1,4,186,194], 31483588391548820706455492941054313013784036446250771480854, 0, 0, 1, 0⟩
theorem s6_383_edges : next config 6 s6_383 = [] := by decide
theorem s6_383_safe : Safe 7 6 s6_383 := by
  apply safe_succ 6 6 s6_383 [] (by decide) s6_383_edges
  simp
def s6_384 : State := ⟨[1,4,186,194], 31483589888126497333298751953631796799384944766865415143702, 0, 0, 1, 0⟩
theorem s6_384_edges : next config 6 s6_384 = [] := by decide
theorem s6_384_safe : Safe 7 6 s6_384 := by
  apply safe_succ 6 6 s6_384 [] (by decide) s6_384_edges
  simp
def s6_385 : State := ⟨[1,4,186,210], 1645504655400920657661060799697537701498749991578019906763948310, 0, 0, 1, 0⟩
theorem s6_385_edges : next config 6 s6_385 = [] := by decide
theorem s6_385_safe : Safe 7 6 s6_385 := by
  apply safe_succ 6 6 s6_385 [] (by decide) s6_385_edges
  simp
def s6_386 : State := ⟨[1,4,186,210], 1645504655400920657683360183766600640886431856352238541197082902, 0, 0, 1, 0⟩
theorem s6_386_edges : next config 6 s6_386 = [] := by decide
theorem s6_386_safe : Safe 7 6 s6_386 := by
  apply safe_succ 6 6 s6_386 [] (by decide) s6_386_edges
  simp
def s6_387 : State := ⟨[1,4,186,210], 1645529763807862204294913162061108039598271527909204316878078230, 0, 0, 1, 0⟩
theorem s6_387_edges : next config 6 s6_387 = [] := by decide
theorem s6_387_safe : Safe 7 6 s6_387 := by
  apply safe_succ 6 6 s6_387 [] (by decide) s6_387_edges
  simp
def s6_388 : State := ⟨[1,4,186,210], 1645536040909597590975675636721063563510833776766219053839745302, 0, 0, 1, 0⟩
theorem s6_388_edges : next config 6 s6_388 = [] := by decide
theorem s6_388_safe : Safe 7 6 s6_388 := by
  apply safe_succ 6 6 s6_388 [] (by decide) s6_388_edges
  simp
def s6_389 : State := ⟨[1,4,186,210], 2056880794731222168132899498611815774565972949670040061010313494, 0, 0, 1, 0⟩
theorem s6_389_edges : next config 6 s6_389 = [] := by decide
theorem s6_389_safe : Safe 7 6 s6_389 := by
  apply safe_succ 6 6 s6_389 [] (by decide) s6_389_edges
  simp
def s6_390 : State := ⟨[1,4,186,210], 2056887071832957554791362589202708359090853333752836163538845974, 0, 0, 1, 0⟩
theorem s6_390_edges : next config 6 s6_390 = [] := by decide
theorem s6_390_safe : Safe 7 6 s6_390 := by
  apply safe_succ 6 6 s6_390 [] (by decide) s6_390_edges
  simp
def s6_391 : State := ⟨[1,4,194,96], 25108406947392729606368181200329325475124137975310257819926, 2, 2, 1, 0⟩
theorem s6_391_edges : next config 6 s6_391 = [s7_223] := by decide
theorem s6_391_safe : Safe 7 6 s6_391 := by
  apply safe_succ 6 6 s6_391 [s7_223] (by decide) s6_391_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_223_safe
def s6_392 : State := ⟨[1,4,194,162], 25108406947392729606368181200329325475124137975310257819926, 2, 2, 1, 0⟩
theorem s6_392_edges : next config 6 s6_392 = [] := by decide
theorem s6_392_safe : Safe 7 6 s6_392 := by
  apply safe_succ 6 6 s6_392 [] (by decide) s6_392_edges
  simp
def s6_393 : State := ⟨[1,4,194,162], 25108406948854231242337954650849256453986922565239117517078, 2, 2, 1, 0⟩
theorem s6_393_edges : next config 6 s6_393 = [] := by decide
theorem s6_393_safe : Safe 7 6 s6_393 := by
  apply safe_succ 6 6 s6_393 [] (by decide) s6_393_edges
  simp
def s6_394 : State := ⟨[1,4,209,145], 822752278660603021122086421958103419712902851183438164459196694, 3, 3, 1, 0⟩
theorem s6_394_edges : next config 6 s6_394 = [] := by decide
theorem s6_394_safe : Safe 7 6 s6_394 := by
  apply safe_succ 6 6 s6_394 [] (by decide) s6_394_edges
  simp
def s6_395 : State := ⟨[1,4,209,145], 822752278660603021122086421958103419712902851183438164461289750, 3, 3, 1, 0⟩
theorem s6_395_edges : next config 6 s6_395 = [s7_271] := by decide
theorem s6_395_safe : Safe 7 6 s6_395 := by
  apply safe_succ 6 6 s6_395 [s7_271] (by decide) s6_395_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_271_safe
def s6_396 : State := ⟨[1,4,210,145], 1645504557321206042221871758435309295345806576059852752477557014, 2, 2, 1, 0⟩
theorem s6_396_edges : next config 6 s6_396 = [s7_8] := by decide
theorem s6_396_safe : Safe 7 6 s6_396 := by
  apply safe_succ 6 6 s6_396 [s7_8] (by decide) s6_396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_8_safe
def s6_397 : State := ⟨[1,4,210,145], 2056880696651507552760614054074646921591490468681271423476502806, 2, 2, 1, 0⟩
theorem s6_397_edges : next config 6 s6_397 = [s7_10] := by decide
theorem s6_397_safe : Safe 7 6 s6_397 := by
  apply safe_succ 6 6 s6_397 [s7_10] (by decide) s6_397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_10_safe
def s6_398 : State := ⟨[1,4,210,145], 27973577474460502716701378679352917375069580426197130566055297302, 2, 2, 1, 0⟩
theorem s6_398_edges : next config 6 s6_398 = [s7_11] := by decide
theorem s6_398_safe : Safe 7 6 s6_398 := by
  apply safe_succ 6 6 s6_398 [s7_11] (by decide) s6_398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_11_safe
def s6_399 : State := ⟨[1,4,210,145], 28384953613790804227240120974992255001315264318818549237054243094, 2, 2, 1, 0⟩
theorem s6_399_edges : next config 6 s6_399 = [s7_13] := by decide
theorem s6_399_safe : Safe 7 6 s6_399 := by
  apply safe_succ 6 6 s6_399 [s7_13] (by decide) s6_399_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_13_safe
def s6_400 : State := ⟨[1,4,225,145], 53919893334301279589334074776550505509362615469440525162897085632790, 2, 2, 1, 0⟩
theorem s6_400_edges : next config 6 s6_400 = [] := by decide
theorem s6_400_safe : Safe 7 6 s6_400 := by
  apply safe_succ 6 6 s6_400 [] (by decide) s6_400_edges
  simp
def s6_401 : State := ⟨[1,4,236,132], 110427941548649020598956093796438192039475761146371246632432346440204574, 1, 1, 1, 0⟩
theorem s6_401_edges : next config 6 s6_401 = [] := by decide
theorem s6_401_safe : Safe 7 6 s6_401 := by
  apply safe_succ 6 6 s6_401 [] (by decide) s6_401_edges
  simp
def s6_402 : State := ⟨[1,4,236,132], 110427941548649020598956093796438192039475761146371283525920493859307798, 1, 1, 1, 0⟩
theorem s6_402_edges : next config 6 s6_402 = [] := by decide
theorem s6_402_safe : Safe 7 6 s6_402 := by
  apply safe_succ 6 6 s6_402 [] (by decide) s6_402_edges
  simp
def s6_403 : State := ⟨[1,4,240,145], 1766847064778384329583297500809821091705442766466852109025240389127311638, 2, 2, 1, 0⟩
theorem s6_403_edges : next config 6 s6_403 = [] := by decide
theorem s6_403_safe : Safe 7 6 s6_403 := by
  apply safe_succ 6 6 s6_403 [] (by decide) s6_403_edges
  simp
def s6_404 : State := ⟨[1,4,241,145], 3533694129556768659166595001530439542899129882077862275623413092450369822, 1, 1, 1, 0⟩
theorem s6_404_edges : next config 6 s6_404 = [s7_272] := by decide
theorem s6_404_safe : Safe 7 6 s6_404 := by
  apply safe_succ 6 6 s6_404 [s7_272] (by decide) s6_404_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_272_safe
def s6_405 : State := ⟨[1,4,241,145], 3533694129556768659166595001530439542899129882077862275623413092450373910, 2, 2, 1, 0⟩
theorem s6_405_edges : next config 6 s6_405 = [s7_338] := by decide
theorem s6_405_safe : Safe 7 6 s6_405 := by
  apply safe_succ 6 6 s6_405 [s7_338] (by decide) s6_405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_338_safe
def s6_406 : State := ⟨[1,4,241,145], 3533694129556768659166595001530439542899129882077862312516901239869473046, 1, 1, 1, 0⟩
theorem s6_406_edges : next config 6 s6_406 = [s7_273] := by decide
theorem s6_406_safe : Safe 7 6 s6_406 := by
  apply safe_succ 6 6 s6_406 [s7_273] (by decide) s6_406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_273_safe
def s6_407 : State := ⟨[1,4,241,145], 3533694129556768659166595001552739607532926663342471067146846590419927326, 1, 1, 1, 0⟩
theorem s6_407_edges : next config 6 s6_407 = [s7_274] := by decide
theorem s6_407_safe : Safe 7 6 s6_407 := by
  apply safe_succ 6 6 s6_407 [s7_274] (by decide) s6_407_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_274_safe
def s6_408 : State := ⟨[1,4,241,145], 3533694129556768659166595001552739607532926663342471067146846590419931414, 2, 2, 1, 0⟩
theorem s6_408_edges : next config 6 s6_408 = [s7_339] := by decide
theorem s6_408_safe : Safe 7 6 s6_408 := by
  apply safe_succ 6 6 s6_408 [s7_339] (by decide) s6_408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_339_safe
def s6_409 : State := ⟨[1,4,241,145], 3533694129556768659166595001552739607532926663342471104040334737839030550, 1, 1, 1, 0⟩
theorem s6_409_edges : next config 6 s6_409 = [s7_275] := by decide
theorem s6_409_safe : Safe 7 6 s6_409 := by
  apply safe_succ 6 6 s6_409 [s7_275] (by decide) s6_409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_275_safe
def s6_410 : State := ⟨[1,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835401449750, 1, 1, 1, 0⟩
theorem s6_410_edges : next config 6 s6_410 = [s7_340] := by decide
theorem s6_410_safe : Safe 7 6 s6_410 := by
  apply safe_succ 6 6 s6_410 [s7_340] (by decide) s6_410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_340_safe
def s6_411 : State := ⟨[1,12,64,145], 44601830679428167221534918366648232786989334, 3, 3, 1, 0⟩
theorem s6_411_edges : next config 6 s6_411 = [s7_770, s7_341, s7_604, s7_230, s7_271, s7_231, s7_236, s7_238] := by decide
theorem s6_411_safe : Safe 7 6 s6_411 := by
  apply safe_succ 6 6 s6_411 [s7_770, s7_341, s7_604, s7_230, s7_271, s7_231, s7_236, s7_238] (by decide) s6_411_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_770_safe
  · subst z; exact s7_341_safe
  · subst z; exact s7_604_safe
  · subst z; exact s7_230_safe
  · subst z; exact s7_271_safe
  · subst z; exact s7_231_safe
  · subst z; exact s7_236_safe
  · subst z; exact s7_238_safe
def s6_412 : State := ⟨[1,12,64,145], 133806172603018343541531644955671405881528606, 3, 1, 1, 0⟩
theorem s6_412_edges : next config 6 s6_412 = [s7_0, s7_239] := by decide
theorem s6_412_safe : Safe 7 6 s6_412 := by
  apply safe_succ 6 6 s6_412 [s7_0, s7_239] (by decide) s6_412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_0_safe
  · subst z; exact s7_239_safe
def s6_413 : State := ⟨[1,12,64,145], 156105556672081282929213509729890040314663198, 3, 1, 1, 0⟩
theorem s6_413_edges : next config 6 s6_413 = [s7_1, s7_240] := by decide
theorem s6_413_safe : Safe 7 6 s6_413 := by
  apply safe_succ 6 6 s6_413 [s7_1, s7_240] (by decide) s6_413_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_1_safe
  · subst z; exact s7_240_safe
def s6_414 : State := ⟨[1,12,67,145], 44601830679428167221535102834088969880408342, 3, 1, 1, 0⟩
theorem s6_414_edges : next config 6 s6_414 = [s7_2] := by decide
theorem s6_414_safe : Safe 7 6 s6_414 := by
  apply safe_succ 6 6 s6_414 [s7_2] (by decide) s6_414_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_2_safe
def s6_415 : State := ⟨[1,12,67,145], 44601830679428167221535139727577117299511574, 3, 1, 1, 0⟩
theorem s6_415_edges : next config 6 s6_415 = [s7_4] := by decide
theorem s6_415_safe : Safe 7 6 s6_415 := by
  apply safe_succ 6 6 s6_415 [s7_4] (by decide) s6_415_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_4_safe
def s6_416 : State := ⟨[1,12,67,145], 44602511244162009098461992689815685997596958, 3, 1, 1, 0⟩
theorem s6_416_edges : next config 6 s6_416 = [s7_6] := by decide
theorem s6_416_safe : Safe 7 6 s6_416 := by
  apply safe_succ 6 6 s6_416 [s7_6] (by decide) s6_416_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_6_safe
def s6_417 : State := ⟨[1,12,67,145], 66902575877958790363070784213249183967154462, 3, 1, 1, 0⟩
theorem s6_417_edges : next config 6 s6_417 = [s7_7] := by decide
theorem s6_417_safe : Safe 7 6 s6_417 := by
  apply safe_succ 6 6 s6_417 [s7_7] (by decide) s6_417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_7_safe
def s6_418 : State := ⟨[1,12,67,145], 1645504557321206042221871758435309295345806723633805342153969942, 2, 0, 1, 0⟩
theorem s6_418_edges : next config 6 s6_418 = [s7_8] := by decide
theorem s6_418_safe : Safe 7 6 s6_418 := by
  apply safe_succ 6 6 s6_418 [s7_8] (by decide) s6_418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_8_safe
def s6_419 : State := ⟨[1,12,67,145], 1645529665728147588922626356394471502869935414782934836786041110, 2, 0, 1, 0⟩
theorem s6_419_edges : next config 6 s6_419 = [s7_9] := by decide
theorem s6_419_safe : Safe 7 6 s6_419 := by
  apply safe_succ 6 6 s6_419 [s7_9] (by decide) s6_419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_9_safe
def s6_420 : State := ⟨[1,12,67,145], 2056880696651507552760614054074646921591490616255224013152915734, 2, 0, 1, 0⟩
theorem s6_420_edges : next config 6 s6_420 = [s7_10] := by decide
theorem s6_420_safe : Safe 7 6 s6_420 := by
  apply safe_succ 6 6 s6_420 [s7_10] (by decide) s6_420_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_10_safe
def s6_421 : State := ⟨[1,12,67,146], 89204682205957097258460355984327272545980702, 3, 1, 1, 0⟩
theorem s6_421_edges : next config 6 s6_421 = [s7_14] := by decide
theorem s6_421_safe : Safe 7 6 s6_421 := by
  apply safe_succ 6 6 s6_421 [s7_14] (by decide) s6_421_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_14_safe
def s6_422 : State := ⟨[1,12,67,146], 111504066275020036646142220758545906979115294, 3, 1, 1, 0⟩
theorem s6_422_edges : next config 6 s6_422 = [s7_15] := by decide
theorem s6_422_safe : Safe 7 6 s6_422 := by
  apply safe_succ 6 6 s6_422 [s7_15] (by decide) s6_422_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_15_safe
def s6_423 : State := ⟨[1,12,67,162], 5846006551025023507419431648348025812450252230942, 3, 1, 1, 0⟩
theorem s6_423_edges : next config 6 s6_423 = [s7_16] := by decide
theorem s6_423_safe : Safe 7 6 s6_423 := by
  apply safe_succ 6 6 s6_423 [s7_16] (by decide) s6_423_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_16_safe
def s6_424 : State := ⟨[1,12,67,162], 7307508186994796957939362627210810402379111928094, 3, 1, 1, 0⟩
theorem s6_424_edges : next config 6 s6_424 = [s7_17] := by decide
theorem s6_424_safe : Safe 7 6 s6_424 := by
  apply safe_succ 6 6 s6_424 [s7_17] (by decide) s6_424_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_17_safe
def s6_425 : State := ⟨[1,12,67,163], 11692013101709764647917924833066656320801055248670, 3, 1, 1, 0⟩
theorem s6_425_edges : next config 6 s6_425 = [s7_18] := by decide
theorem s6_425_safe : Safe 7 6 s6_425 := by
  apply safe_succ 6 6 s6_425 [s7_18] (by decide) s6_425_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_18_safe
def s6_426 : State := ⟨[1,12,67,163], 13153514736318408630754101958075942481002842099998, 3, 1, 1, 0⟩
theorem s6_426_edges : next config 6 s6_426 = [s7_19] := by decide
theorem s6_426_safe : Safe 7 6 s6_426 := by
  apply safe_succ 6 6 s6_426 [s7_19] (by decide) s6_426_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_19_safe
def s6_427 : State := ⟨[1,12,67,176], 95780971326419139128294233276893671644123656091668766, 3, 1, 1, 0⟩
theorem s6_427_edges : next config 6 s6_427 = [s7_20] := by decide
theorem s6_427_safe : Safe 7 6 s6_427 := by
  apply safe_succ 6 6 s6_427 [s7_20] (by decide) s6_427_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_20_safe
def s6_428 : State := ⟨[1,12,67,176], 95782432805755724832681813820190669654494950518231326, 3, 1, 1, 0⟩
theorem s6_428_edges : next config 6 s6_428 = [s7_21] := by decide
theorem s6_428_safe : Safe 7 6 s6_428 := by
  apply safe_succ 6 6 s6_428 [s7_21] (by decide) s6_428_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_21_safe
def s6_429 : State := ⟨[1,12,82,145], 44601830679428167226370695432083044321923350, 3, 1, 1, 0⟩
theorem s6_429_edges : next config 6 s6_429 = [s7_22] := by decide
theorem s6_429_safe : Safe 7 6 s6_429 := by
  apply safe_succ 6 6 s6_429 [s7_22] (by decide) s6_429_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_22_safe
def s6_430 : State := ⟨[1,12,82,145], 44601830679428167227579547464721378658423062, 3, 1, 1, 0⟩
theorem s6_430_edges : next config 6 s6_430 = [s7_24] := by decide
theorem s6_430_safe : Safe 7 6 s6_430 := by
  apply safe_succ 6 6 s6_430 [s7_24] (by decide) s6_430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_24_safe
def s6_431 : State := ⟨[1,12,96,145], 44602511244162088326624359380200689865134366, 3, 1, 1, 0⟩
theorem s6_431_edges : next config 6 s6_431 = [s7_28, s7_272, s7_241] := by decide
theorem s6_431_safe : Safe 7 6 s6_431 := by
  apply safe_succ 6 6 s6_431 [s7_28, s7_272, s7_241] (by decide) s6_431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_28_safe
  · subst z; exact s7_272_safe
  · subst z; exact s7_241_safe
def s6_432 : State := ⟨[1,12,96,145], 44602511244162088326624359380200698455068950, 3, 1, 1, 0⟩
theorem s6_432_edges : next config 6 s6_432 = [s7_29, s7_242] := by decide
theorem s6_432_safe : Safe 7 6 s6_432 := by
  apply safe_succ 6 6 s6_432 [s7_29, s7_242] (by decide) s6_432_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_29_safe
  · subst z; exact s7_242_safe
def s6_433 : State := ⟨[1,12,96,145], 44602511244162088326624396273688837284237590, 3, 1, 1, 0⟩
theorem s6_433_edges : next config 6 s6_433 = [s7_30, s7_273, s7_243] := by decide
theorem s6_433_safe : Safe 7 6 s6_433 := by
  apply safe_succ 6 6 s6_433 [s7_30, s7_273, s7_243] (by decide) s6_433_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_30_safe
  · subst z; exact s7_273_safe
  · subst z; exact s7_243_safe
def s6_434 : State := ⟨[1,12,96,145], 44602511244162246782949387908875876953035030, 3, 1, 1, 0⟩
theorem s6_434_edges : next config 6 s6_434 = [s7_31, s7_244] := by decide
theorem s6_434_safe : Safe 7 6 s6_434 := by
  apply safe_succ 6 6 s6_434 [s7_31, s7_244] (by decide) s6_434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_31_safe
  · subst z; exact s7_244_safe
def s6_435 : State := ⟨[1,12,96,145], 66902575877958869591233150903634187834691870, 3, 1, 1, 0⟩
theorem s6_435_edges : next config 6 s6_435 = [s7_34, s7_274, s7_245] := by decide
theorem s6_435_safe : Safe 7 6 s6_435 := by
  apply safe_succ 6 6 s6_435 [s7_34, s7_274, s7_245] (by decide) s6_435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_34_safe
  · subst z; exact s7_274_safe
  · subst z; exact s7_245_safe
def s6_436 : State := ⟨[1,12,96,145], 66902575877958869591233150903634196424626454, 3, 1, 1, 0⟩
theorem s6_436_edges : next config 6 s6_436 = [s7_35, s7_246] := by decide
theorem s6_436_safe : Safe 7 6 s6_436 := by
  apply safe_succ 6 6 s6_436 [s7_35, s7_246] (by decide) s6_436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_35_safe
  · subst z; exact s7_246_safe
def s6_437 : State := ⟨[1,12,96,145], 66902575877958869591233187797122335253795094, 3, 1, 1, 0⟩
theorem s6_437_edges : next config 6 s6_437 = [s7_36, s7_275, s7_247] := by decide
theorem s6_437_safe : Safe 7 6 s6_437 := by
  apply safe_succ 6 6 s6_437 [s7_36, s7_275, s7_247] (by decide) s6_437_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_36_safe
  · subst z; exact s7_275_safe
  · subst z; exact s7_247_safe
def s6_438 : State := ⟨[1,12,96,145], 66902575877959028047558179432309374922592534, 3, 1, 1, 0⟩
theorem s6_438_edges : next config 6 s6_438 = [s7_37, s7_248] := by decide
theorem s6_438_safe : Safe 7 6 s6_438 := by
  apply safe_succ 6 6 s6_438 [s7_37, s7_248] (by decide) s6_438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_37_safe
  · subst z; exact s7_248_safe
def s6_439 : State := ⟨[1,12,96,146], 89204682205957176486622722674712276413518110, 3, 1, 1, 0⟩
theorem s6_439_edges : next config 6 s6_439 = [s7_40, s7_249] := by decide
theorem s6_439_safe : Safe 7 6 s6_439 := by
  apply safe_succ 6 6 s6_439 [s7_40, s7_249] (by decide) s6_439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_40_safe
  · subst z; exact s7_249_safe
def s6_440 : State := ⟨[1,12,96,146], 89204682205957176486622759568200423832621334, 3, 1, 1, 0⟩
theorem s6_440_edges : next config 6 s6_440 = [s7_41, s7_250] := by decide
theorem s6_440_safe : Safe 7 6 s6_440 := by
  apply safe_succ 6 6 s6_440 [s7_41, s7_250] (by decide) s6_440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_41_safe
  · subst z; exact s7_250_safe
def s6_441 : State := ⟨[1,12,96,146], 89207404464892543994330429671571730559209750, 3, 1, 1, 0⟩
theorem s6_441_edges : next config 6 s6_441 = [s7_42, s7_251] := by decide
theorem s6_441_safe : Safe 7 6 s6_441 := by
  apply safe_succ 6 6 s6_441 [s7_42, s7_251] (by decide) s6_441_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_42_safe
  · subst z; exact s7_251_safe
def s6_442 : State := ⟨[1,12,96,146], 111504066275020115874304587448930910846652702, 3, 1, 1, 0⟩
theorem s6_442_edges : next config 6 s6_442 = [s7_43, s7_252] := by decide
theorem s6_442_safe : Safe 7 6 s6_442 := by
  apply safe_succ 6 6 s6_442 [s7_43, s7_252] (by decide) s6_442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_43_safe
  · subst z; exact s7_252_safe
def s6_443 : State := ⟨[1,12,96,146], 111504066275020115874304624342419058265755926, 3, 1, 1, 0⟩
theorem s6_443_edges : next config 6 s6_443 = [s7_44, s7_253] := by decide
theorem s6_443_safe : Safe 7 6 s6_443 := by
  apply safe_succ 6 6 s6_443 [s7_44, s7_253] (by decide) s6_443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_44_safe
  · subst z; exact s7_253_safe
def s6_444 : State := ⟨[1,12,96,162], 5846006551025023507498659810714716197454119768350, 3, 1, 1, 0⟩
theorem s6_444_edges : next config 6 s6_444 = [s7_45, s7_254] := by decide
theorem s6_444_safe : Safe 7 6 s6_444 := by
  apply safe_succ 6 6 s6_444 [s7_45, s7_254] (by decide) s6_444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_45_safe
  · subst z; exact s7_254_safe
def s6_445 : State := ⟨[1,12,96,162], 5846006551025023507498659810751609685601538871574, 3, 1, 1, 0⟩
theorem s6_445_edges : next config 6 s6_445 = [s7_46, s7_255] := by decide
theorem s6_445_safe : Safe 7 6 s6_445 := by
  apply safe_succ 6 6 s6_445 [s7_46, s7_255] (by decide) s6_445_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_46_safe
  · subst z; exact s7_255_safe
def s6_446 : State := ⟨[1,12,96,162], 5846006551025023507657116135743244872641207669014, 3, 1, 1, 0⟩
theorem s6_446_edges : next config 6 s6_446 = [s7_47, s7_256] := by decide
theorem s6_446_safe : Safe 7 6 s6_446 := by
  apply safe_succ 6 6 s6_446 [s7_47, s7_256] (by decide) s6_446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_47_safe
  · subst z; exact s7_256_safe
def s6_447 : State := ⟨[1,12,96,162], 5846006553747282442866167518421713056908265459990, 3, 1, 1, 0⟩
theorem s6_447_edges : next config 6 s6_447 = [s7_48, s7_257] := by decide
theorem s6_447_safe : Safe 7 6 s6_447 := by
  apply safe_succ 6 6 s6_447 [s7_48, s7_257] (by decide) s6_447_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_48_safe
  · subst z; exact s7_257_safe
def s6_448 : State := ⟨[1,12,96,162], 7307508186994796958018590789577500787382979465502, 3, 1, 1, 0⟩
theorem s6_448_edges : next config 6 s6_448 = [s7_49, s7_258] := by decide
theorem s6_448_safe : Safe 7 6 s6_448 := by
  apply safe_succ 6 6 s6_448 [s7_49, s7_258] (by decide) s6_448_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_49_safe
  · subst z; exact s7_258_safe
def s6_449 : State := ⟨[1,12,96,162], 7307508186994796958018590789614394275530398568726, 3, 1, 1, 0⟩
theorem s6_449_edges : next config 6 s6_449 = [s7_50, s7_259] := by decide
theorem s6_449_safe : Safe 7 6 s6_449 := by
  apply safe_succ 6 6 s6_449 [s7_50, s7_259] (by decide) s6_449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_50_safe
  · subst z; exact s7_259_safe
def s6_450 : State := ⟨[1,12,96,162], 7307508186994796958177047114606029462570067366166, 3, 1, 1, 0⟩
theorem s6_450_edges : next config 6 s6_450 = [s7_51, s7_260] := by decide
theorem s6_450_safe : Safe 7 6 s6_450 := by
  apply safe_succ 6 6 s6_450 [s7_51, s7_260] (by decide) s6_450_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_51_safe
  · subst z; exact s7_260_safe
def s6_451 : State := ⟨[1,12,96,162], 17538019649672246853128138472444980354701580112150, 3, 1, 1, 0⟩
theorem s6_451_edges : next config 6 s6_451 = [s7_52, s7_261] := by decide
theorem s6_451_safe : Safe 7 6 s6_451 := by
  apply safe_succ 6 6 s6_451 [s7_52, s7_261] (by decide) s6_451_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_52_safe
  · subst z; exact s7_261_safe
def s6_452 : State := ⟨[1,12,96,162], 18999521285642020303648069451307764944630439809302, 3, 1, 1, 0⟩
theorem s6_452_edges : next config 6 s6_452 = [s7_53, s7_262] := by decide
theorem s6_452_safe : Safe 7 6 s6_452 := by
  apply safe_succ 6 6 s6_452 [s7_53, s7_262] (by decide) s6_452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_53_safe
  · subst z; exact s7_262_safe
def s6_453 : State := ⟨[1,12,96,163], 11692013100348635180313399141579848276086439874838, 3, 1, 1, 0⟩
theorem s6_453_edges : next config 6 s6_453 = [s7_54, s7_263] := by decide
theorem s6_453_safe : Safe 7 6 s6_453 := by
  apply safe_succ 6 6 s6_453 [s7_54, s7_263] (by decide) s6_453_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_54_safe
  · subst z; exact s7_263_safe
def s6_454 : State := ⟨[1,12,96,163], 11692013101709764647997152995433346705804922786078, 3, 1, 1, 0⟩
theorem s6_454_edges : next config 6 s6_454 = [s7_55, s7_264] := by decide
theorem s6_454_safe : Safe 7 6 s6_454 := by
  apply safe_succ 6 6 s6_454 [s7_55, s7_264] (by decide) s6_454_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_55_safe
  · subst z; exact s7_264_safe
def s6_455 : State := ⟨[1,12,96,163], 13153514736318408630833330120442632866006709637406, 3, 1, 1, 0⟩
theorem s6_455_edges : next config 6 s6_455 = [s7_56, s7_265] := by decide
theorem s6_455_safe : Safe 7 6 s6_455 := by
  apply safe_succ 6 6 s6_455 [s7_56, s7_265] (by decide) s6_455_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_56_safe
  · subst z; exact s7_265_safe
def s6_456 : State := ⟨[1,12,96,163], 14615016373649311549037014953158915885671232114966, 3, 1, 1, 0⟩
theorem s6_456_edges : next config 6 s6_456 = [s7_57, s7_266] := by decide
theorem s6_456_safe : Safe 7 6 s6_456 := by
  apply safe_succ 6 6 s6_456 [s7_57, s7_266] (by decide) s6_456_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_57_safe
  · subst z; exact s7_266_safe
def s6_457 : State := ⟨[1,12,96,176], 95780971326419139128294312505056038334508659959206174, 3, 1, 1, 0⟩
theorem s6_457_edges : next config 6 s6_457 = [s7_58, s7_267] := by decide
theorem s6_457_safe : Safe 7 6 s6_457 := by
  apply safe_succ 6 6 s6_457 [s7_58, s7_267] (by decide) s6_457_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_58_safe
  · subst z; exact s7_267_safe
def s6_458 : State := ⟨[1,12,96,176], 95780971326419139128294312505056075227996807378309398, 3, 1, 1, 0⟩
theorem s6_458_edges : next config 6 s6_458 = [s7_59, s7_268] := by decide
theorem s6_458_safe : Safe 7 6 s6_458 := by
  apply safe_succ 6 6 s6_458 [s7_59, s7_268] (by decide) s6_458_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_59_safe
  · subst z; exact s7_268_safe
def s6_459 : State := ⟨[1,12,96,176], 95782432805755724832681893048353036344879954385768734, 3, 1, 1, 0⟩
theorem s6_459_edges : next config 6 s6_459 = [s7_60, s7_269] := by decide
theorem s6_459_safe : Safe 7 6 s6_459 := by
  apply safe_succ 6 6 s6_459 [s7_60, s7_269] (by decide) s6_459_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_60_safe
  · subst z; exact s7_269_safe
def s6_460 : State := ⟨[1,12,96,176], 95782432805755724832681893048353073238368101804871958, 3, 1, 1, 0⟩
theorem s6_460_edges : next config 6 s6_460 = [s7_61, s7_270] := by decide
theorem s6_460_safe : Safe 7 6 s6_460 := by
  apply safe_succ 6 6 s6_460 [s7_61, s7_270] (by decide) s6_460_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_61_safe
  · subst z; exact s7_270_safe
def s6_461 : State := ⟨[1,12,97,145], 44601830679428404906022461159661013416743190, 3, 1, 1, 0⟩
theorem s6_461_edges : next config 6 s6_461 = [s7_62] := by decide
theorem s6_461_safe : Safe 7 6 s6_461 := by
  apply safe_succ 6 6 s6_461 [s7_62] (by decide) s6_461_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_62_safe
def s6_462 : State := ⟨[1,12,104,129], 1020847121124453156574505327914104459550, 3, 1, 1, 0⟩
theorem s6_462_edges : next config 6 s6_462 = [s7_65, s7_241] := by decide
theorem s6_462_safe : Safe 7 6 s6_462 := by
  apply safe_succ 6 6 s6_462 [s7_65, s7_241] (by decide) s6_462_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_65_safe
  · subst z; exact s7_241_safe
def s6_463 : State := ⟨[1,12,104,129], 1020847121124453156574505327922694394134, 3, 1, 1, 0⟩
theorem s6_463_edges : next config 6 s6_463 = [s7_66, s7_242] := by decide
theorem s6_463_safe : Safe 7 6 s6_463 := by
  apply safe_succ 6 6 s6_463 [s7_66, s7_242] (by decide) s6_463_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_66_safe
  · subst z; exact s7_242_safe
def s6_464 : State := ⟨[1,12,104,129], 1020847121124453156611398816061523562774, 3, 1, 1, 0⟩
theorem s6_464_edges : next config 6 s6_464 = [s7_67, s7_243] := by decide
theorem s6_464_safe : Safe 7 6 s6_464 := by
  apply safe_succ 6 6 s6_464 [s7_67, s7_243] (by decide) s6_464_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_67_safe
  · subst z; exact s7_243_safe
def s6_465 : State := ⟨[1,12,104,129], 1020847121282909481603034003101192360214, 3, 1, 1, 0⟩
theorem s6_465_edges : next config 6 s6_465 = [s7_68, s7_244] := by decide
theorem s6_465_safe : Safe 7 6 s6_465 := by
  apply safe_succ 6 6 s6_465 [s7_68, s7_244] (by decide) s6_465_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_68_safe
  · subst z; exact s7_244_safe
def s6_466 : State := ⟨[1,12,104,130], 1701411854966330083501254542777640882462, 3, 1, 1, 0⟩
theorem s6_466_edges : next config 6 s6_466 = [s7_73, s7_249, s7_254] := by decide
theorem s6_466_safe : Safe 7 6 s6_466 := by
  apply safe_succ 6 6 s6_466 [s7_73, s7_249, s7_254] (by decide) s6_466_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_73_safe
  · subst z; exact s7_249_safe
  · subst z; exact s7_254_safe
def s6_467 : State := ⟨[1,12,104,130], 1701411854966330083501254542786230817046, 3, 1, 1, 0⟩
theorem s6_467_edges : next config 6 s6_467 = [s7_74] := by decide
theorem s6_467_safe : Safe 7 6 s6_467 := by
  apply safe_succ 6 6 s6_467 [s7_74] (by decide) s6_467_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_74_safe
def s6_468 : State := ⟨[1,12,104,130], 1701411854966330083538148030925059985686, 3, 1, 1, 0⟩
theorem s6_468_edges : next config 6 s6_468 = [s7_75, s7_250, s7_255] := by decide
theorem s6_468_safe : Safe 7 6 s6_468 := by
  apply safe_succ 6 6 s6_468 [s7_75, s7_250, s7_255] (by decide) s6_468_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_75_safe
  · subst z; exact s7_250_safe
  · subst z; exact s7_255_safe
def s6_469 : State := ⟨[1,12,104,130], 1701411855124786408529783217964728783126, 3, 1, 1, 0⟩
theorem s6_469_edges : next config 6 s6_469 = [s7_76, s7_256] := by decide
theorem s6_469_safe : Safe 7 6 s6_469 := by
  apply safe_succ 6 6 s6_469 [s7_76, s7_256] (by decide) s6_469_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_76_safe
  · subst z; exact s7_256_safe
def s6_470 : State := ⟨[1,12,104,130], 4423670790333837791208251402231786574102, 3, 1, 1, 0⟩
theorem s6_470_edges : next config 6 s6_470 = [s7_81, s7_251, s7_257] := by decide
theorem s6_470_safe : Safe 7 6 s6_470 := by
  apply safe_succ 6 6 s6_470 [s7_81, s7_251, s7_257] (by decide) s6_470_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_81_safe
  · subst z; exact s7_251_safe
  · subst z; exact s7_257_safe
def s6_471 : State := ⟨[1,12,104,131], 3062541322650083937354752972504713728286, 3, 1, 1, 0⟩
theorem s6_471_edges : next config 6 s6_471 = [s7_84, s7_264] := by decide
theorem s6_471_safe : Safe 7 6 s6_471 := by
  apply safe_succ 6 6 s6_471 [s7_84, s7_264] (by decide) s6_471_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_84_safe
  · subst z; exact s7_264_safe
def s6_472 : State := ⟨[1,12,104,132], 5784800258017591645061749831958859419934, 3, 1, 1, 0⟩
theorem s6_472_edges : next config 6 s6_472 = [s7_87] := by decide
theorem s6_472_safe : Safe 7 6 s6_472 := by
  apply safe_succ 6 6 s6_472 [s7_87] (by decide) s6_472_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_87_safe
def s6_473 : State := ⟨[1,12,104,132], 5784800258017591645061749831967449354518, 3, 1, 1, 0⟩
theorem s6_473_edges : next config 6 s6_473 = [s7_88] := by decide
theorem s6_473_safe : Safe 7 6 s6_473 := by
  apply safe_succ 6 6 s6_473 [s7_88] (by decide) s6_473_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_88_safe
def s6_474 : State := ⟨[1,12,104,132], 5784800258017591645098643320106278523158, 3, 1, 1, 0⟩
theorem s6_474_edges : next config 6 s6_474 = [s7_89] := by decide
theorem s6_474_safe : Safe 7 6 s6_474 := by
  apply safe_succ 6 6 s6_474 [s7_89] (by decide) s6_474_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_89_safe
def s6_475 : State := ⟨[1,12,104,132], 5784800258176047970090278507145947320598, 3, 1, 1, 0⟩
theorem s6_475_edges : next config 6 s6_475 = [s7_90] := by decide
theorem s6_475_safe : Safe 7 6 s6_475 := by
  apply safe_succ 6 6 s6_475 [s7_90] (by decide) s6_475_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_90_safe
def s6_476 : State := ⟨[1,12,104,136], 87452568319042822876271655615583230169374, 3, 1, 1, 0⟩
theorem s6_476_edges : next config 6 s6_476 = [s7_95] := by decide
theorem s6_476_safe : Safe 7 6 s6_476 := by
  apply safe_succ 6 6 s6_476 [s7_95] (by decide) s6_476_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_95_safe
def s6_477 : State := ⟨[1,12,104,136], 87452568319042822876271655615591820103958, 3, 1, 1, 0⟩
theorem s6_477_edges : next config 6 s6_477 = [s7_96] := by decide
theorem s6_477_safe : Safe 7 6 s6_477 := by
  apply safe_succ 6 6 s6_477 [s7_96] (by decide) s6_477_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_96_safe
def s6_478 : State := ⟨[1,12,104,136], 87452568319042822876308549103730649272598, 3, 1, 1, 0⟩
theorem s6_478_edges : next config 6 s6_478 = [s7_97] := by decide
theorem s6_478_safe : Safe 7 6 s6_478 := by
  apply safe_succ 6 6 s6_478 [s7_97] (by decide) s6_478_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_97_safe
def s6_479 : State := ⟨[1,12,104,136], 87452568319201279201300184290770318070038, 3, 1, 1, 0⟩
theorem s6_479_edges : next config 6 s6_479 = [s7_98] := by decide
theorem s6_479_safe : Safe 7 6 s6_479 := by
  apply safe_succ 6 6 s6_479 [s7_98] (by decide) s6_479_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_98_safe
def s6_480 : State := ⟨[1,12,104,140], 1394136857295446522575630148153573162160414, 3, 1, 1, 0⟩
theorem s6_480_edges : next config 6 s6_480 = [s7_107] := by decide
theorem s6_480_safe : Safe 7 6 s6_480 := by
  apply safe_succ 6 6 s6_480 [s7_107] (by decide) s6_480_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_107_safe
def s6_481 : State := ⟨[1,12,104,140], 1394136857295446522575630148153581752094998, 3, 1, 1, 0⟩
theorem s6_481_edges : next config 6 s6_481 = [s7_108] := by decide
theorem s6_481_safe : Safe 7 6 s6_481 := by
  apply safe_succ 6 6 s6_481 [s7_108] (by decide) s6_481_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_108_safe
def s6_482 : State := ⟨[1,12,104,140], 1394136857295446522575667041641720581263638, 3, 1, 1, 0⟩
theorem s6_482_edges : next config 6 s6_482 = [s7_109] := by decide
theorem s6_482_safe : Safe 7 6 s6_482 := by
  apply safe_succ 6 6 s6_482 [s7_109] (by decide) s6_482_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_109_safe
def s6_483 : State := ⟨[1,12,104,140], 1394136857295604978900658676828760250061078, 3, 1, 1, 0⟩
theorem s6_483_edges : next config 6 s6_483 = [s7_110] := by decide
theorem s6_483_safe : Safe 7 6 s6_483 := by
  apply safe_succ 6 6 s6_483 [s7_110] (by decide) s6_483_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_110_safe
def s6_484 : State := ⟨[1,12,104,144], 22301085480917905717765366028761412074017054, 3, 1, 1, 0⟩
theorem s6_484_edges : next config 6 s6_484 = [s7_111, s7_245, s7_252, s7_267] := by decide
theorem s6_484_safe : Safe 7 6 s6_484 := by
  apply safe_succ 6 6 s6_484 [s7_111, s7_245, s7_252, s7_267] (by decide) s6_484_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_111_safe
  · subst z; exact s7_245_safe
  · subst z; exact s7_252_safe
  · subst z; exact s7_267_safe
def s6_485 : State := ⟨[1,12,104,144], 22301085480917905717765366028761420663951638, 3, 1, 1, 0⟩
theorem s6_485_edges : next config 6 s6_485 = [s7_112, s7_246] := by decide
theorem s6_485_safe : Safe 7 6 s6_485 := by
  apply safe_succ 6 6 s6_485 [s7_112, s7_246] (by decide) s6_485_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_112_safe
  · subst z; exact s7_246_safe
def s6_486 : State := ⟨[1,12,104,144], 22301085480917905717765402922249559493120278, 3, 1, 1, 0⟩
theorem s6_486_edges : next config 6 s6_486 = [s7_113, s7_247, s7_253, s7_268] := by decide
theorem s6_486_safe : Safe 7 6 s6_486 := by
  apply safe_succ 6 6 s6_486 [s7_113, s7_247, s7_253, s7_268] (by decide) s6_486_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_113_safe
  · subst z; exact s7_247_safe
  · subst z; exact s7_253_safe
  · subst z; exact s7_268_safe
def s6_487 : State := ⟨[1,12,104,144], 22301085480918064174090394557436599161917718, 3, 1, 1, 0⟩
theorem s6_487_edges : next config 6 s6_487 = [s7_114, s7_248] := by decide
theorem s6_487_safe : Safe 7 6 s6_487 := by
  apply safe_succ 6 6 s6_487 [s7_114, s7_248] (by decide) s6_487_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_114_safe
  · subst z; exact s7_248_safe
def s6_488 : State := ⟨[1,12,104,145], 44601830679448528859301084301409773580128534, 3, 1, 1, 0⟩
theorem s6_488_edges : next config 6 s6_488 = [s7_342, s7_605, s7_119] := by decide
theorem s6_488_safe : Safe 7 6 s6_488 := by
  apply safe_succ 6 6 s6_488 [s7_342, s7_605, s7_119] (by decide) s6_488_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_342_safe
  · subst z; exact s7_605_safe
  · subst z; exact s7_119_safe
def s6_489 : State := ⟨[1,12,104,160], 1461501637671185305486261062364039132706500579614, 3, 1, 1, 0⟩
theorem s6_489_edges : next config 6 s6_489 = [s7_126, s7_258, s7_269] := by decide
theorem s6_489_safe : Safe 7 6 s6_489 := by
  apply safe_succ 6 6 s6_489 [s7_126, s7_258, s7_269] (by decide) s6_489_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_126_safe
  · subst z; exact s7_258_safe
  · subst z; exact s7_269_safe
def s6_490 : State := ⟨[1,12,104,160], 1461501637671185305486261062364039132715090514198, 3, 1, 1, 0⟩
theorem s6_490_edges : next config 6 s6_490 = [s7_127] := by decide
theorem s6_490_safe : Safe 7 6 s6_490 := by
  apply safe_succ 6 6 s6_490 [s7_127] (by decide) s6_490_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_127_safe
def s6_491 : State := ⟨[1,12,104,160], 1461501637671185305486261062400932620853919682838, 3, 1, 1, 0⟩
theorem s6_491_edges : next config 6 s6_491 = [s7_128, s7_259, s7_270] := by decide
theorem s6_491_safe : Safe 7 6 s6_491 := by
  apply safe_succ 6 6 s6_491 [s7_128, s7_259, s7_270] (by decide) s6_491_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_128_safe
  · subst z; exact s7_259_safe
  · subst z; exact s7_270_safe
def s6_492 : State := ⟨[1,12,104,160], 1461501637671185305644717387392567807893588480278, 3, 1, 1, 0⟩
theorem s6_492_edges : next config 6 s6_492 = [s7_129, s7_260] := by decide
theorem s6_492_safe : Safe 7 6 s6_492 := by
  apply safe_succ 6 6 s6_492 [s7_129, s7_260] (by decide) s6_492_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_129_safe
  · subst z; exact s7_260_safe
def s6_493 : State := ⟨[1,12,104,160], 4384504912332991141893630727796605172018365665558, 3, 1, 1, 0⟩
theorem s6_493_edges : next config 6 s6_493 = [s7_134] := by decide
theorem s6_493_safe : Safe 7 6 s6_493 := by
  apply safe_succ 6 6 s6_493 [s7_134] (by decide) s6_493_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_134_safe
def s6_494 : State := ⟨[1,12,104,161], 2923003275002088223689945895080322152371023057174, 3, 1, 1, 0⟩
theorem s6_494_edges : next config 6 s6_494 = [s7_135, s7_266] := by decide
theorem s6_494_safe : Safe 7 6 s6_494 := by
  apply safe_succ 6 6 s6_494 [s7_135, s7_266] (by decide) s6_494_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_135_safe
  · subst z; exact s7_266_safe
def s6_495 : State := ⟨[1,12,104,162], 25108406947392729606368181220611735078775808399257509105942, 2, 0, 1, 0⟩
theorem s6_495_edges : next config 6 s6_495 = [s7_136] := by decide
theorem s6_495_safe : Safe 7 6 s6_495 := by
  apply safe_succ 6 6 s6_495 [s7_136] (by decide) s6_495_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_136_safe
def s6_496 : State := ⟨[1,12,104,162], 31385508682779410368842841176135647641024665413994470773014, 2, 0, 1, 0⟩
theorem s6_496_edges : next config 6 s6_496 = [s7_137] := by decide
theorem s6_496_safe : Safe 7 6 s6_496 := by
  apply safe_succ 6 6 s6_496 [s7_137] (by decide) s6_496_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_137_safe
def s6_497 : State := ⟨[1,12,104,163], 11692013102390329402121439526011766344615710494998, 2, 0, 1, 0⟩
theorem s6_497_edges : next config 6 s6_497 = [s7_138] := by decide
theorem s6_497_safe : Safe 7 6 s6_497 := by
  apply safe_succ 6 6 s6_497 [s7_138] (by decide) s6_497_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_138_safe
def s6_498 : State := ⟨[1,12,104,163], 11692013103070894135963316452938515559479246917910, 2, 0, 1, 0⟩
theorem s6_498_edges : next config 6 s6_498 = [s7_139] := by decide
theorem s6_498_safe : Safe 7 6 s6_498 := by
  apply safe_succ 6 6 s6_498 [s7_139] (by decide) s6_498_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_139_safe
def s6_499 : State := ⟨[1,12,104,163], 14615016374329876303161301483737335524473429889302, 2, 0, 1, 0⟩
theorem s6_499_edges : next config 6 s6_499 = [s7_140] := by decide
theorem s6_499_safe : Safe 7 6 s6_499 := by
  apply safe_succ 6 6 s6_499 [s7_140] (by decide) s6_499_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_140_safe
def s6_500 : State := ⟨[1,12,104,163], 16076518010980214487523109389526869329265826009366, 2, 0, 1, 0⟩
theorem s6_500_edges : next config 6 s6_500 = [s7_141] := by decide
theorem s6_500_safe : Safe 7 6 s6_500 := by
  apply safe_succ 6 6 s6_500 [s7_141] (by decide) s6_500_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_141_safe
def s6_501 : State := ⟨[1,12,104,163], 17538019649672246873410548076096650778648831398166, 2, 0, 1, 0⟩
theorem s6_501_edges : next config 6 s6_501 = [s7_142] := by decide
theorem s6_501_safe : Safe 7 6 s6_501 := by
  apply safe_succ 6 6 s6_501 [s7_142] (by decide) s6_501_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_142_safe
def s6_502 : State := ⟨[1,12,104,163], 18999521285642020323930479054959435368577691095318, 2, 0, 1, 0⟩
theorem s6_502_edges : next config 6 s6_502 = [s7_143] := by decide
theorem s6_502_safe : Safe 7 6 s6_502 := by
  apply safe_succ 6 6 s6_502 [s7_143] (by decide) s6_502_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_143_safe
def s6_503 : State := ⟨[1,12,104,192], 6277101735386680764176071810490242645750111557514602549534, 3, 1, 1, 0⟩
theorem s6_503_edges : next config 6 s6_503 = [s7_152] := by decide
theorem s6_503_safe : Safe 7 6 s6_503 := by
  apply safe_succ 6 6 s6_503 [s7_152] (by decide) s6_503_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_152_safe
def s6_504 : State := ⟨[1,12,104,192], 6277101735386680764176071810490242645750111557523192484118, 3, 1, 1, 0⟩
theorem s6_504_edges : next config 6 s6_504 = [s7_153] := by decide
theorem s6_504_safe : Safe 7 6 s6_504 := by
  apply safe_succ 6 6 s6_504 [s7_153] (by decide) s6_504_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_153_safe
def s6_505 : State := ⟨[1,12,104,192], 6277101735386680764176071810490242645787005045662021652758, 3, 1, 1, 0⟩
theorem s6_505_edges : next config 6 s6_505 = [s7_154] := by decide
theorem s6_505_safe : Safe 7 6 s6_505 := by
  apply safe_succ 6 6 s6_505 [s7_154] (by decide) s6_505_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_154_safe
def s6_506 : State := ⟨[1,12,104,192], 6277101735386680764176071810648698970778640232701690450198, 3, 1, 1, 0⟩
theorem s6_506_edges : next config 6 s6_506 = [s7_155] := by decide
theorem s6_506_safe : Safe 7 6 s6_506 := by
  apply safe_succ 6 6 s6_506 [s7_155] (by decide) s6_506_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_155_safe
def s6_507 : State := ⟨[1,12,104,192], 18831305206160042291847650656905575477954822446442671575318, 3, 1, 1, 0⟩
theorem s6_507_edges : next config 6 s6_507 = [s7_160] := by decide
theorem s6_507_safe : Safe 7 6 s6_507 := by
  apply safe_succ 6 6 s6_507 [s7_160] (by decide) s6_507_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_160_safe
def s6_508 : State := ⟨[1,12,104,193], 12554203470773361528011861233697909061889360490126056165654, 3, 1, 1, 0⟩
theorem s6_508_edges : next config 6 s6_508 = [s7_163] := by decide
theorem s6_508_safe : Safe 7 6 s6_508 := by
  apply safe_succ 6 6 s6_508 [s7_163] (by decide) s6_508_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_163_safe
def s6_509 : State := ⟨[1,12,104,194], 25108406947392729606368181220611735078775808399257509105942, 2, 0, 1, 0⟩
theorem s6_509_edges : next config 6 s6_509 = [s7_166] := by decide
theorem s6_509_safe : Safe 7 6 s6_509 := by
  apply safe_succ 6 6 s6_509 [s7_166] (by decide) s6_509_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_166_safe
def s6_510 : State := ⟨[1,12,104,194], 25108406948854231242337954671131666057638592989186368803094, 2, 0, 1, 0⟩
theorem s6_510_edges : next config 6 s6_510 = [s7_167] := by decide
theorem s6_510_safe : Safe 7 6 s6_510 := by
  apply safe_succ 6 6 s6_510 [s7_167] (by decide) s6_510_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_167_safe
def s6_511 : State := ⟨[1,12,104,210], 1645504557321206042244173864763327963878962239978716087013413142, 2, 0, 1, 0⟩
theorem s6_511_edges : next config 6 s6_511 = [s7_168] := by decide
theorem s6_511_safe : Safe 7 6 s6_511 := by
  apply safe_succ 6 6 s6_511 [s7_168] (by decide) s6_511_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_168_safe
def s6_512 : State := ⟨[1,12,104,210], 1645504557321206042266473248832390903266644104752934721446547734, 2, 0, 1, 0⟩
theorem s6_512_edges : next config 6 s6_512 = [s7_170] := by decide
theorem s6_512_safe : Safe 7 6 s6_512 := by
  apply safe_succ 6 6 s6_512 [s7_170] (by decide) s6_512_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_170_safe
def s6_513 : State := ⟨[1,12,104,210], 1645529665728147588878026227126898301978483776309900497127543062, 2, 0, 1, 0⟩
theorem s6_513_edges : next config 6 s6_513 = [s7_172] := by decide
theorem s6_513_safe : Safe 7 6 s6_513 := by
  apply safe_succ 6 6 s6_513 [s7_172] (by decide) s6_513_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_172_safe
def s6_514 : State := ⟨[1,12,104,210], 1645535942829882975558788701786853825891046025166915234089210134, 2, 0, 1, 0⟩
theorem s6_514_edges : next config 6 s6_514 = [s7_174] := by decide
theorem s6_514_safe : Safe 7 6 s6_514 := by
  apply safe_succ 6 6 s6_514 [s7_174] (by decide) s6_514_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_174_safe
def s6_515 : State := ⟨[1,12,104,210], 2056880696651507552716012563677606036946185198070736241259778326, 2, 0, 1, 0⟩
theorem s6_515_edges : next config 6 s6_515 = [s7_176] := by decide
theorem s6_515_safe : Safe 7 6 s6_515 := by
  apply safe_succ 6 6 s6_515 [s7_176] (by decide) s6_515_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_176_safe
def s6_516 : State := ⟨[1,12,104,210], 2056886973753242939374475654268498621471065582153532343788310806, 2, 0, 1, 0⟩
theorem s6_516_edges : next config 6 s6_516 = [s7_178] := by decide
theorem s6_516_safe : Safe 7 6 s6_516 := by
  apply safe_succ 6 6 s6_516 [s7_178] (by decide) s6_516_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_178_safe
def s6_517 : State := ⟨[1,12,104,224], 26959946667150639794667015087359913060919720652188328594154178285854, 3, 1, 1, 0⟩
theorem s6_517_edges : next config 6 s6_517 = [s7_188] := by decide
theorem s6_517_safe : Safe 7 6 s6_517 := by
  apply safe_succ 6 6 s6_517 [s7_188] (by decide) s6_517_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_188_safe
def s6_518 : State := ⟨[1,12,104,224], 26959946667150639794667015087359913060919720652188328594162768220438, 3, 1, 1, 0⟩
theorem s6_518_edges : next config 6 s6_518 = [s7_189] := by decide
theorem s6_518_safe : Safe 7 6 s6_518 := by
  apply safe_succ 6 6 s6_518 [s7_189] (by decide) s6_518_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_189_safe
def s6_519 : State := ⟨[1,12,104,224], 26959946667150639794667015087359913060919720652225222082301597389078, 3, 1, 1, 0⟩
theorem s6_519_edges : next config 6 s6_519 = [s7_190] := by decide
theorem s6_519_safe : Safe 7 6 s6_519 := by
  apply safe_succ 6 6 s6_519 [s7_190] (by decide) s6_519_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_190_safe
def s6_520 : State := ⟨[1,12,104,224], 26959946667150639794667015087359913061078176977216857269341266186518, 3, 1, 1, 0⟩
theorem s6_520_edges : next config 6 s6_520 = [s7_191] := by decide
theorem s6_520_safe : Safe 7 6 s6_520 := by
  apply safe_succ 6 6 s6_520 [s7_191] (by decide) s6_520_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_191_safe
def s6_521 : State := ⟨[1,12,104,224], 80879840001451919384001045261399174408194009497269473556361398784278, 3, 1, 1, 0⟩
theorem s6_521_edges : next config 6 s6_521 = [s7_196] := by decide
theorem s6_521_safe : Safe 7 6 s6_521 := by
  apply safe_succ 6 6 s6_521 [s7_196] (by decide) s6_521_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_196_safe
def s6_522 : State := ⟨[1,12,104,225], 53919893334301279589334030174379543734715321399757429750444876435734, 3, 1, 1, 0⟩
theorem s6_522_edges : next config 6 s6_522 = [s7_199] := by decide
theorem s6_522_safe : Safe 7 6 s6_522 := by
  apply safe_succ 6 6 s6_522 [s7_199] (by decide) s6_522_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_199_safe
def s6_523 : State := ⟨[1,12,104,232], 6901746346790563787434755862277365734838391548400034311275574791835934, 3, 1, 1, 0⟩
theorem s6_523_edges : next config 6 s6_523 = [s7_202] := by decide
theorem s6_523_safe : Safe 7 6 s6_523 := by
  apply safe_succ 6 6 s6_523 [s7_202] (by decide) s6_523_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_202_safe
def s6_524 : State := ⟨[1,12,104,232], 6901746346790563787434755862277365734838391548400034311275583381770518, 3, 1, 1, 0⟩
theorem s6_524_edges : next config 6 s6_524 = [s7_203] := by decide
theorem s6_524_safe : Safe 7 6 s6_524 := by
  apply safe_succ 6 6 s6_524 [s7_203] (by decide) s6_524_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_203_safe
def s6_525 : State := ⟨[1,12,104,232], 6901746346790563787434755862277365734838391548400071204763722210939158, 3, 1, 1, 0⟩
theorem s6_525_edges : next config 6 s6_525 = [s7_204] := by decide
theorem s6_525_safe : Safe 7 6 s6_525 := by
  apply safe_succ 6 6 s6_525 [s7_204] (by decide) s6_525_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_204_safe
def s6_526 : State := ⟨[1,12,104,232], 6901746346790563787434755862277365734838550004725062839950761879736598, 3, 1, 1, 0⟩
theorem s6_526_edges : next config 6 s6_526 = [s7_205] := by decide
theorem s6_526_safe : Safe 7 6 s6_526 := by
  apply safe_succ 6 6 s6_526 [s7_205] (by decide) s6_526_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_205_safe
def s6_527 : State := ⟨[1,12,112,145], 44601830684620543308232260259516322658062614, 3, 1, 1, 0⟩
theorem s6_527_edges : next config 6 s6_527 = [s7_218] := by decide
theorem s6_527_safe : Safe 7 6 s6_527 := by
  apply safe_succ 6 6 s6_527 [s7_218] (by decide) s6_527_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_218_safe
def s6_528 : State := ⟨[1,12,113,145], 44601830689812840166767087888046818987282710, 3, 1, 1, 0⟩
theorem s6_528_edges : next config 6 s6_528 = [s7_345, s7_220] := by decide
theorem s6_528_safe : Safe 7 6 s6_528 := by
  apply safe_succ 6 6 s6_528 [s7_345, s7_220] (by decide) s6_528_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_345_safe
  · subst z; exact s7_220_safe
def s6_529 : State := ⟨[1,12,194,104], 25108406947392729606368181220611735078775808399257509105942, 2, 0, 1, 0⟩
theorem s6_529_edges : next config 6 s6_529 = [s7_223] := by decide
theorem s6_529_safe : Safe 7 6 s6_529 := by
  apply safe_succ 6 6 s6_529 [s7_223] (by decide) s6_529_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_223_safe
def s6_530 : State := ⟨[1,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082070, 3, 1, 1, 0⟩
theorem s6_530_edges : next config 6 s6_530 = [s7_346, s7_224] := by decide
theorem s6_530_safe : Safe 7 6 s6_530 := by
  apply safe_succ 6 6 s6_530 [s7_346, s7_224] (by decide) s6_530_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_346_safe
  · subst z; exact s7_224_safe
def s6_531 : State := ⟨[1,21,64,145], 44601830679428167221534918366648232786989334, 3, 3, 1, 0⟩
theorem s6_531_edges : next config 6 s6_531 = [s7_773, s7_347, s7_606, s7_276, s7_291, s7_277, s7_280, s7_284] := by decide
theorem s6_531_safe : Safe 7 6 s6_531 := by
  apply safe_succ 6 6 s6_531 [s7_773, s7_347, s7_606, s7_276, s7_291, s7_277, s7_280, s7_284] (by decide) s6_531_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_773_safe
  · subst z; exact s7_347_safe
  · subst z; exact s7_606_safe
  · subst z; exact s7_276_safe
  · subst z; exact s7_291_safe
  · subst z; exact s7_277_safe
  · subst z; exact s7_280_safe
  · subst z; exact s7_284_safe
def s6_532 : State := ⟨[1,21,64,145], 44601830679428167221535213514553412139811094, 3, 3, 1, 0⟩
theorem s6_532_edges : next config 6 s6_532 = [s7_285] := by decide
theorem s6_532_safe : Safe 7 6 s6_532 := by
  apply safe_succ 6 6 s6_532 [s7_285] (by decide) s6_532_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_285_safe
def s6_533 : State := ⟨[1,21,67,145], 44601830679428167221535102834088969882501398, 3, 1, 1, 0⟩
theorem s6_533_edges : next config 6 s6_533 = [s7_298, s7_293] := by decide
theorem s6_533_safe : Safe 7 6 s6_533 := by
  apply safe_succ 6 6 s6_533 [s7_298, s7_293] (by decide) s6_533_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_298_safe
  · subst z; exact s7_293_safe
def s6_534 : State := ⟨[1,21,67,145], 44601830679428167221535139727577117301604630, 3, 1, 1, 0⟩
theorem s6_534_edges : next config 6 s6_534 = [s7_299, s7_294] := by decide
theorem s6_534_safe : Safe 7 6 s6_534 := by
  apply safe_succ 6 6 s6_534 [s7_299, s7_294] (by decide) s6_534_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_299_safe
  · subst z; exact s7_294_safe
def s6_535 : State := ⟨[1,21,82,145], 44601830679428167226370695432083044324016406, 3, 1, 1, 0⟩
theorem s6_535_edges : next config 6 s6_535 = [] := by decide
theorem s6_535_safe : Safe 7 6 s6_535 := by
  apply safe_succ 6 6 s6_535 [] (by decide) s6_535_edges
  simp
def s6_536 : State := ⟨[1,21,82,145], 44601830679428167227579547464721378660516118, 3, 1, 1, 0⟩
theorem s6_536_edges : next config 6 s6_536 = [] := by decide
theorem s6_536_safe : Safe 7 6 s6_536 := by
  apply safe_succ 6 6 s6_536 [] (by decide) s6_536_edges
  simp
def s6_537 : State := ⟨[1,21,97,145], 44601830679428404906022461159661013418836246, 3, 1, 1, 0⟩
theorem s6_537_edges : next config 6 s6_537 = [] := by decide
theorem s6_537_safe : Safe 7 6 s6_537 := by
  apply safe_succ 6 6 s6_537 [] (by decide) s6_537_edges
  simp
def s6_538 : State := ⟨[1,21,100,145], 44601830679429514100297660860387323034140950, 3, 1, 1, 0⟩
theorem s6_538_edges : next config 6 s6_538 = [s7_348] := by decide
theorem s6_538_safe : Safe 7 6 s6_538 := by
  apply safe_succ 6 6 s6_538 [s7_348] (by decide) s6_538_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_348_safe
def s6_539 : State := ⟨[1,21,104,145], 44601830679448528859301084301409773582221590, 3, 1, 1, 0⟩
theorem s6_539_edges : next config 6 s6_539 = [s7_349, s7_366, s7_607, s7_312, s7_295, s7_296, s7_290, s7_292, s7_288] := by decide
theorem s6_539_safe : Safe 7 6 s6_539 := by
  apply safe_succ 6 6 s6_539 [s7_349, s7_366, s7_607, s7_312, s7_295, s7_296, s7_290, s7_292, s7_288] (by decide) s6_539_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s7_349_safe
  · subst z; exact s7_366_safe
  · subst z; exact s7_607_safe
  · subst z; exact s7_312_safe
  · subst z; exact s7_295_safe
  · subst z; exact s7_296_safe
  · subst z; exact s7_290_safe
  · subst z; exact s7_292_safe
  · subst z; exact s7_288_safe
def s6_540 : State := ⟨[1,21,112,145], 44601830684620543308232260259516322660155670, 3, 1, 1, 0⟩
theorem s6_540_edges : next config 6 s6_540 = [] := by decide
theorem s6_540_safe : Safe 7 6 s6_540 := by
  apply safe_succ 6 6 s6_540 [] (by decide) s6_540_edges
  simp
def s6_541 : State := ⟨[1,21,113,145], 44601830689812840166767087888046818989375766, 3, 1, 1, 0⟩
theorem s6_541_edges : next config 6 s6_541 = [s7_350] := by decide
theorem s6_541_safe : Safe 7 6 s6_541 := by
  apply safe_succ 6 6 s6_541 [s7_350] (by decide) s6_541_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_350_safe
def s6_542 : State := ⟨[1,21,117,145], 44601830845581745922811916743961708865978646, 3, 1, 1, 0⟩
theorem s6_542_edges : next config 6 s6_542 = [s7_351] := by decide
theorem s6_542_safe : Safe 7 6 s6_542 := by
  apply safe_succ 6 6 s6_542 [s7_351] (by decide) s6_542_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_351_safe
def s6_543 : State := ⟨[1,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175126, 3, 1, 1, 0⟩
theorem s6_543_edges : next config 6 s6_543 = [s7_352] := by decide
theorem s6_543_safe : Safe 7 6 s6_543 := by
  apply safe_succ 6 6 s6_543 [s7_352] (by decide) s6_543_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_352_safe
def s6_544 : State := ⟨[1,29,65,145], 44601830679428167221534955260136380742959382, 3, 1, 1, 0⟩
theorem s6_544_edges : next config 6 s6_544 = [s7_293] := by decide
theorem s6_544_safe : Safe 7 6 s6_544 := by
  apply safe_succ 6 6 s6_544 [s7_293] (by decide) s6_544_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_293_safe
def s6_545 : State := ⟨[1,29,66,145], 44601830679428167221534992153624528162062614, 3, 1, 1, 0⟩
theorem s6_545_edges : next config 6 s6_545 = [s7_294] := by decide
theorem s6_545_safe : Safe 7 6 s6_545 := by
  apply safe_succ 6 6 s6_545 [s7_294] (by decide) s6_545_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_294_safe
def s6_546 : State := ⟨[1,29,96,145], 44601830679428246449697432630985826867806486, 3, 1, 1, 0⟩
theorem s6_546_edges : next config 6 s6_546 = [s7_356, s7_608, s7_295] := by decide
theorem s6_546_safe : Safe 7 6 s6_546 := by
  apply safe_succ 6 6 s6_546 [s7_356, s7_608, s7_295] (by decide) s6_546_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_356_safe
  · subst z; exact s7_608_safe
  · subst z; exact s7_295_safe
def s6_547 : State := ⟨[1,53,96,145], 44601830679428246449697432639993025585676566, 3, 1, 1, 0⟩
theorem s6_547_edges : next config 6 s6_547 = [s7_358, s7_296] := by decide
theorem s6_547_safe : Safe 7 6 s6_547 := by
  apply safe_succ 6 6 s6_547 [s7_358, s7_296] (by decide) s6_547_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_358_safe
  · subst z; exact s7_296_safe
def s6_548 : State := ⟨[1,68,64,145], 44601830679428167221535213514553412139811094, 3, 3, 1, 0⟩
theorem s6_548_edges : next config 6 s6_548 = [s7_297] := by decide
theorem s6_548_safe : Safe 7 6 s6_548 := by
  apply safe_succ 6 6 s6_548 [s7_297] (by decide) s6_548_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_297_safe
def s6_549 : State := ⟨[1,68,104,145], 44601830679448528859301379449314952932950294, 3, 1, 1, 0⟩
theorem s6_549_edges : next config 6 s6_549 = [] := by decide
theorem s6_549_safe : Safe 7 6 s6_549 := by
  apply safe_succ 6 6 s6_549 [] (by decide) s6_549_edges
  simp
def s6_550 : State := ⟨[1,68,104,214], 26328072917139296674568711603123585538620000519630319216595370262, 2, 0, 1, 0⟩
theorem s6_550_edges : next config 6 s6_550 = [] := by decide
theorem s6_550_safe : Safe 7 6 s6_550 := by
  apply safe_succ 6 6 s6_550 [] (by decide) s6_550_edges
  simp
def s6_551 : State := ⟨[1,68,104,214], 26328072917139296674591010987192648478007682384404537851028504854, 2, 0, 1, 0⟩
theorem s6_551_edges : next config 6 s6_551 = [] := by decide
theorem s6_551_safe : Safe 7 6 s6_551 := by
  apply safe_succ 6 6 s6_551 [] (by decide) s6_551_edges
  simp
def s6_552 : State := ⟨[1,86,82,145], 44601830679428167303741947887419311503114518, 3, 1, 1, 0⟩
theorem s6_552_edges : next config 6 s6_552 = [s7_26] := by decide
theorem s6_552_safe : Safe 7 6 s6_552 := by
  apply safe_succ 6 6 s6_552 [s7_26] (by decide) s6_552_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_26_safe
def s6_553 : State := ⟨[1,86,82,145], 44601830679428167304950799920057645839614230, 3, 1, 1, 0⟩
theorem s6_553_edges : next config 6 s6_553 = [s7_27] := by decide
theorem s6_553_safe : Safe 7 6 s6_553 := by
  apply safe_succ 6 6 s6_553 [s7_27] (by decide) s6_553_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_27_safe
def s6_554 : State := ⟨[1,100,96,145], 44602511244163355977224587609602186568335646, 3, 1, 1, 0⟩
theorem s6_554_edges : next config 6 s6_554 = [s7_32, s7_303] := by decide
theorem s6_554_safe : Safe 7 6 s6_554 := by
  apply safe_succ 6 6 s6_554 [s7_32, s7_303] (by decide) s6_554_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_32_safe
  · subst z; exact s7_303_safe
def s6_555 : State := ⟨[1,100,96,145], 44602511244163355977224624503090333987438870, 3, 1, 1, 0⟩
theorem s6_555_edges : next config 6 s6_555 = [s7_33, s7_304] := by decide
theorem s6_555_safe : Safe 7 6 s6_555 := by
  apply safe_succ 6 6 s6_555 [s7_33, s7_304] (by decide) s6_555_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_33_safe
  · subst z; exact s7_304_safe
def s6_556 : State := ⟨[1,100,96,145], 66902575877960137241833379133035684537893150, 3, 1, 1, 0⟩
theorem s6_556_edges : next config 6 s6_556 = [s7_38, s7_305] := by decide
theorem s6_556_safe : Safe 7 6 s6_556 := by
  apply safe_succ 6 6 s6_556 [s7_38, s7_305] (by decide) s6_556_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_38_safe
  · subst z; exact s7_305_safe
def s6_557 : State := ⟨[1,100,96,145], 66902575877960137241833416026523831956996374, 3, 1, 1, 0⟩
theorem s6_557_edges : next config 6 s6_557 = [s7_39, s7_306] := by decide
theorem s6_557_safe : Safe 7 6 s6_557 := by
  apply safe_succ 6 6 s6_557 [s7_39, s7_306] (by decide) s6_557_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_39_safe
  · subst z; exact s7_306_safe
def s6_558 : State := ⟨[1,100,104,129], 1020847122392103756802734729410807660830, 3, 1, 1, 0⟩
theorem s6_558_edges : next config 6 s6_558 = [s7_303] := by decide
theorem s6_558_safe : Safe 7 6 s6_558 := by
  apply safe_succ 6 6 s6_558 [s7_303] (by decide) s6_558_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_303_safe
def s6_559 : State := ⟨[1,100,104,129], 1020847122392103756839628217558226764054, 3, 1, 1, 0⟩
theorem s6_559_edges : next config 6 s6_559 = [s7_304] := by decide
theorem s6_559_safe : Safe 7 6 s6_559 := by
  apply safe_succ 6 6 s6_559 [s7_304] (by decide) s6_559_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_304_safe
def s6_560 : State := ⟨[1,100,104,130], 1701411856233980683729483944274344083742, 3, 1, 1, 0⟩
theorem s6_560_edges : next config 6 s6_560 = [] := by decide
theorem s6_560_safe : Safe 7 6 s6_560 := by
  apply safe_succ 6 6 s6_560 [] (by decide) s6_560_edges
  simp
def s6_561 : State := ⟨[1,100,104,130], 1701411856233980683766377432421763186966, 3, 1, 1, 0⟩
theorem s6_561_edges : next config 6 s6_561 = [] := by decide
theorem s6_561_safe : Safe 7 6 s6_561 := by
  apply safe_succ 6 6 s6_561 [] (by decide) s6_561_edges
  simp
def s6_562 : State := ⟨[1,100,104,130], 4423670791601488391436480803728489775382, 3, 1, 1, 0⟩
theorem s6_562_edges : next config 6 s6_562 = [] := by decide
theorem s6_562_safe : Safe 7 6 s6_562 := by
  apply safe_succ 6 6 s6_562 [] (by decide) s6_562_edges
  simp
def s6_563 : State := ⟨[1,100,104,131], 3062541323917734537582982374001416929566, 3, 1, 1, 0⟩
theorem s6_563_edges : next config 6 s6_563 = [] := by decide
theorem s6_563_safe : Safe 7 6 s6_563 := by
  apply safe_succ 6 6 s6_563 [] (by decide) s6_563_edges
  simp
def s6_564 : State := ⟨[1,100,104,132], 5784800259285242245289979233455562621214, 3, 1, 1, 0⟩
theorem s6_564_edges : next config 6 s6_564 = [] := by decide
theorem s6_564_safe : Safe 7 6 s6_564 := by
  apply safe_succ 6 6 s6_564 [] (by decide) s6_564_edges
  simp
def s6_565 : State := ⟨[1,100,104,132], 5784800259285242245326872721602981724438, 3, 1, 1, 0⟩
theorem s6_565_edges : next config 6 s6_565 = [] := by decide
theorem s6_565_safe : Safe 7 6 s6_565 := by
  apply safe_succ 6 6 s6_565 [] (by decide) s6_565_edges
  simp
def s6_566 : State := ⟨[1,100,104,136], 87452568320310473476499885017079933370654, 3, 1, 1, 0⟩
theorem s6_566_edges : next config 6 s6_566 = [] := by decide
theorem s6_566_safe : Safe 7 6 s6_566 := by
  apply safe_succ 6 6 s6_566 [] (by decide) s6_566_edges
  simp
def s6_567 : State := ⟨[1,100,104,136], 87452568320310473476536778505227352473878, 3, 1, 1, 0⟩
theorem s6_567_edges : next config 6 s6_567 = [] := by decide
theorem s6_567_safe : Safe 7 6 s6_567 := by
  apply safe_succ 6 6 s6_567 [] (by decide) s6_567_edges
  simp
def s6_568 : State := ⟨[1,100,104,144], 22301085480919173368365594258162908777218334, 3, 1, 1, 0⟩
theorem s6_568_edges : next config 6 s6_568 = [s7_305] := by decide
theorem s6_568_safe : Safe 7 6 s6_568 := by
  apply safe_succ 6 6 s6_568 [s7_305] (by decide) s6_568_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_305_safe
def s6_569 : State := ⟨[1,100,104,144], 22301085480919173368365631151651056196321558, 3, 1, 1, 0⟩
theorem s6_569_edges : next config 6 s6_569 = [s7_306] := by decide
theorem s6_569_safe : Safe 7 6 s6_569 := by
  apply safe_succ 6 6 s6_569 [s7_306] (by decide) s6_569_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_306_safe
def s6_570 : State := ⟨[1,100,104,145], 44601830679449796509901312530811270283329814, 3, 1, 1, 0⟩
theorem s6_570_edges : next config 6 s6_570 = [s7_362] := by decide
theorem s6_570_safe : Safe 7 6 s6_570 := by
  apply safe_succ 6 6 s6_570 [s7_362] (by decide) s6_570_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_362_safe
def s6_571 : State := ⟨[1,100,104,160], 1461501637671185306753911662592268534203203780894, 3, 1, 1, 0⟩
theorem s6_571_edges : next config 6 s6_571 = [] := by decide
theorem s6_571_safe : Safe 7 6 s6_571 := by
  apply safe_succ 6 6 s6_571 [] (by decide) s6_571_edges
  simp
def s6_572 : State := ⟨[1,100,104,160], 1461501637671185306753911662629162022350622884118, 3, 1, 1, 0⟩
theorem s6_572_edges : next config 6 s6_572 = [] := by decide
theorem s6_572_safe : Safe 7 6 s6_572 := by
  apply safe_succ 6 6 s6_572 [] (by decide) s6_572_edges
  simp
def s6_573 : State := ⟨[1,100,104,192], 6277101735386680764176071811757893245978340959011305750814, 3, 1, 1, 0⟩
theorem s6_573_edges : next config 6 s6_573 = [] := by decide
theorem s6_573_safe : Safe 7 6 s6_573 := by
  apply safe_succ 6 6 s6_573 [] (by decide) s6_573_edges
  simp
def s6_574 : State := ⟨[1,100,104,192], 6277101735386680764176071811757893246015234447158724854038, 3, 1, 1, 0⟩
theorem s6_574_edges : next config 6 s6_574 = [] := by decide
theorem s6_574_safe : Safe 7 6 s6_574 := by
  apply safe_succ 6 6 s6_574 [] (by decide) s6_574_edges
  simp
def s6_575 : State := ⟨[1,100,104,192], 18831305206160042291847650658173226078183051847939374776598, 3, 1, 1, 0⟩
theorem s6_575_edges : next config 6 s6_575 = [] := by decide
theorem s6_575_safe : Safe 7 6 s6_575 := by
  apply safe_succ 6 6 s6_575 [] (by decide) s6_575_edges
  simp
def s6_576 : State := ⟨[1,100,104,193], 12554203470773361528011861234965559662117589891622759366934, 3, 1, 1, 0⟩
theorem s6_576_edges : next config 6 s6_576 = [] := by decide
theorem s6_576_safe : Safe 7 6 s6_576 := by
  apply safe_succ 6 6 s6_576 [] (by decide) s6_576_edges
  simp
def s6_577 : State := ⟨[1,100,104,224], 26959946667150639794667015087359913062187371252416557995650881487134, 3, 1, 1, 0⟩
theorem s6_577_edges : next config 6 s6_577 = [] := by decide
theorem s6_577_safe : Safe 7 6 s6_577 := by
  apply safe_succ 6 6 s6_577 [] (by decide) s6_577_edges
  simp
def s6_578 : State := ⟨[1,100,104,224], 26959946667150639794667015087359913062187371252453451483798300590358, 3, 1, 1, 0⟩
theorem s6_578_edges : next config 6 s6_578 = [] := by decide
theorem s6_578_safe : Safe 7 6 s6_578 := by
  apply safe_succ 6 6 s6_578 [] (by decide) s6_578_edges
  simp
def s6_579 : State := ⟨[1,100,104,228], 431359146674410236714672241392654373166744537590525145212205035225374, 3, 1, 1, 0⟩
theorem s6_579_edges : next config 6 s6_579 = [] := by decide
theorem s6_579_safe : Safe 7 6 s6_579 := by
  apply safe_succ 6 6 s6_579 [] (by decide) s6_579_edges
  simp
def s6_580 : State := ⟨[1,100,104,228], 431359146674410236714672241392654373166744537590562038700352454328598, 3, 1, 1, 0⟩
theorem s6_580_edges : next config 6 s6_580 = [] := by decide
theorem s6_580_safe : Safe 7 6 s6_580 := by
  apply safe_succ 6 6 s6_580 [] (by decide) s6_580_edges
  simp
def s6_581 : State := ⟨[1,100,104,232], 6901746346790563787434755862277365734839659199000262540677071495037214, 3, 1, 1, 0⟩
theorem s6_581_edges : next config 6 s6_581 = [] := by decide
theorem s6_581_safe : Safe 7 6 s6_581 := by
  apply safe_succ 6 6 s6_581 [] (by decide) s6_581_edges
  simp
def s6_582 : State := ⟨[1,100,104,232], 6901746346790563787434755862277365734839659199000299434165218914140438, 3, 1, 1, 0⟩
theorem s6_582_edges : next config 6 s6_582 = [] := by decide
theorem s6_582_safe : Safe 7 6 s6_582 := by
  apply safe_succ 6 6 s6_582 [] (by decide) s6_582_edges
  simp
def s6_583 : State := ⟨[1,108,104,129], 1020847445643006815001232111070125031710, 3, 1, 1, 0⟩
theorem s6_583_edges : next config 6 s6_583 = [s7_71, s7_307] := by decide
theorem s6_583_safe : Safe 7 6 s6_583 := by
  apply safe_succ 6 6 s6_583 [s7_71, s7_307] (by decide) s6_583_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_71_safe
  · subst z; exact s7_307_safe
def s6_584 : State := ⟨[1,108,104,129], 1020847445643006815038125599217544134934, 3, 1, 1, 0⟩
theorem s6_584_edges : next config 6 s6_584 = [s7_72, s7_308] := by decide
theorem s6_584_safe : Safe 7 6 s6_584 := by
  apply safe_succ 6 6 s6_584 [s7_72, s7_308] (by decide) s6_584_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_72_safe
  · subst z; exact s7_308_safe
def s6_585 : State := ⟨[1,108,104,130], 1701412179484883741927981325933661454622, 3, 1, 1, 0⟩
theorem s6_585_edges : next config 6 s6_585 = [s7_79] := by decide
theorem s6_585_safe : Safe 7 6 s6_585 := by
  apply safe_succ 6 6 s6_585 [s7_79] (by decide) s6_585_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_79_safe
def s6_586 : State := ⟨[1,108,104,130], 1701412179484883741964874814081080557846, 3, 1, 1, 0⟩
theorem s6_586_edges : next config 6 s6_586 = [s7_80] := by decide
theorem s6_586_safe : Safe 7 6 s6_586 := by
  apply safe_succ 6 6 s6_586 [s7_80] (by decide) s6_586_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_80_safe
def s6_587 : State := ⟨[1,108,104,130], 4423671114852391449634978185387807146262, 3, 1, 1, 0⟩
theorem s6_587_edges : next config 6 s6_587 = [s7_83] := by decide
theorem s6_587_safe : Safe 7 6 s6_587 := by
  apply safe_succ 6 6 s6_587 [s7_83] (by decide) s6_587_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_83_safe
def s6_588 : State := ⟨[1,108,104,131], 3062541647168637595781479755660734300446, 3, 1, 1, 0⟩
theorem s6_588_edges : next config 6 s6_588 = [s7_86] := by decide
theorem s6_588_safe : Safe 7 6 s6_588 := by
  apply safe_succ 6 6 s6_588 [s7_86] (by decide) s6_588_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_86_safe
def s6_589 : State := ⟨[1,108,104,132], 5784800582536145303488476615114879992094, 3, 1, 1, 0⟩
theorem s6_589_edges : next config 6 s6_589 = [s7_93] := by decide
theorem s6_589_safe : Safe 7 6 s6_589 := by
  apply safe_succ 6 6 s6_589 [s7_93] (by decide) s6_589_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_93_safe
def s6_590 : State := ⟨[1,108,104,132], 5784800582536145303525370103262299095318, 3, 1, 1, 0⟩
theorem s6_590_edges : next config 6 s6_590 = [s7_94] := by decide
theorem s6_590_safe : Safe 7 6 s6_590 := by
  apply safe_succ 6 6 s6_590 [s7_94] (by decide) s6_590_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_94_safe
def s6_591 : State := ⟨[1,108,104,136], 87452568643561376534698382398739250741534, 3, 1, 1, 0⟩
theorem s6_591_edges : next config 6 s6_591 = [s7_101] := by decide
theorem s6_591_safe : Safe 7 6 s6_591 := by
  apply safe_succ 6 6 s6_591 [s7_101] (by decide) s6_591_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_101_safe
def s6_592 : State := ⟨[1,108,104,136], 87452568643561376534735275886886669844758, 3, 1, 1, 0⟩
theorem s6_592_edges : next config 6 s6_592 = [s7_102] := by decide
theorem s6_592_safe : Safe 7 6 s6_592 := by
  apply safe_succ 6 6 s6_592 [s7_102] (by decide) s6_592_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_102_safe
def s6_593 : State := ⟨[1,108,104,144], 22301085481242424271423792755544568094589214, 3, 1, 1, 0⟩
theorem s6_593_edges : next config 6 s6_593 = [s7_117, s7_309] := by decide
theorem s6_593_safe : Safe 7 6 s6_593 := by
  apply safe_succ 6 6 s6_593 [s7_117, s7_309] (by decide) s6_593_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_117_safe
  · subst z; exact s7_309_safe
def s6_594 : State := ⟨[1,108,104,144], 22301085481242424271423829649032715513692438, 3, 1, 1, 0⟩
theorem s6_594_edges : next config 6 s6_594 = [s7_118, s7_310] := by decide
theorem s6_594_safe : Safe 7 6 s6_594 := by
  apply safe_succ 6 6 s6_594 [s7_118, s7_310] (by decide) s6_594_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_118_safe
  · subst z; exact s7_310_safe
def s6_595 : State := ⟨[1,108,104,145], 44601830679773047412959511028192929600700694, 3, 1, 1, 0⟩
theorem s6_595_edges : next config 6 s6_595 = [s7_363, s7_123] := by decide
theorem s6_595_safe : Safe 7 6 s6_595 := by
  apply safe_succ 6 6 s6_595 [s7_363, s7_123] (by decide) s6_595_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_363_safe
  · subst z; exact s7_123_safe
def s6_596 : State := ⟨[1,108,104,160], 1461501637671185630004814720790765915862521151774, 3, 1, 1, 0⟩
theorem s6_596_edges : next config 6 s6_596 = [s7_132] := by decide
theorem s6_596_safe : Safe 7 6 s6_596 := by
  apply safe_succ 6 6 s6_596 [s7_132] (by decide) s6_596_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_132_safe
def s6_597 : State := ⟨[1,108,104,160], 1461501637671185630004814720827659404009940254998, 3, 1, 1, 0⟩
theorem s6_597_edges : next config 6 s6_597 = [s7_133] := by decide
theorem s6_597_safe : Safe 7 6 s6_597 := by
  apply safe_succ 6 6 s6_597 [s7_133] (by decide) s6_597_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_133_safe
def s6_598 : State := ⟨[1,108,104,192], 6277101735386680764176072135008796304176838340670623121694, 3, 1, 1, 0⟩
theorem s6_598_edges : next config 6 s6_598 = [s7_158] := by decide
theorem s6_598_safe : Safe 7 6 s6_598 := by
  apply safe_succ 6 6 s6_598 [s7_158] (by decide) s6_598_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_158_safe
def s6_599 : State := ⟨[1,108,104,192], 6277101735386680764176072135008796304213731828818042224918, 3, 1, 1, 0⟩
theorem s6_599_edges : next config 6 s6_599 = [s7_159] := by decide
theorem s6_599_safe : Safe 7 6 s6_599 := by
  apply safe_succ 6 6 s6_599 [s7_159] (by decide) s6_599_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_159_safe
def s6_600 : State := ⟨[1,108,104,192], 18831305206160042291847650981424129136381549229598692147478, 3, 1, 1, 0⟩
theorem s6_600_edges : next config 6 s6_600 = [s7_162] := by decide
theorem s6_600_safe : Safe 7 6 s6_600 := by
  apply safe_succ 6 6 s6_600 [s7_162] (by decide) s6_600_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_162_safe
def s6_601 : State := ⟨[1,108,104,193], 12554203470773361528011861558216462720316087273282076737814, 3, 1, 1, 0⟩
theorem s6_601_edges : next config 6 s6_601 = [s7_165] := by decide
theorem s6_601_safe : Safe 7 6 s6_601 := by
  apply safe_succ 6 6 s6_601 [s7_165] (by decide) s6_601_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_165_safe
def s6_602 : State := ⟨[1,108,104,210], 1645504557321206042244173864763652482432620666705499243033985302, 2, 0, 1, 0⟩
theorem s6_602_edges : next config 6 s6_602 = [s7_169] := by decide
theorem s6_602_safe : Safe 7 6 s6_602 := by
  apply safe_succ 6 6 s6_602 [s7_169] (by decide) s6_602_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_169_safe
def s6_603 : State := ⟨[1,108,104,210], 1645504557321206042266473248832715421820302531479717877467119894, 2, 0, 1, 0⟩
theorem s6_603_edges : next config 6 s6_603 = [s7_171] := by decide
theorem s6_603_safe : Safe 7 6 s6_603 := by
  apply safe_succ 6 6 s6_603 [s7_171] (by decide) s6_603_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_171_safe
def s6_604 : State := ⟨[1,108,104,210], 1645529665728147588878026227127222820532142203036683653148115222, 2, 0, 1, 0⟩
theorem s6_604_edges : next config 6 s6_604 = [s7_173] := by decide
theorem s6_604_safe : Safe 7 6 s6_604 := by
  apply safe_succ 6 6 s6_604 [s7_173] (by decide) s6_604_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_173_safe
def s6_605 : State := ⟨[1,108,104,210], 1645535942829882975558788701787178344444704451893698390109782294, 2, 0, 1, 0⟩
theorem s6_605_edges : next config 6 s6_605 = [s7_175] := by decide
theorem s6_605_safe : Safe 7 6 s6_605 := by
  apply safe_succ 6 6 s6_605 [s7_175] (by decide) s6_605_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_175_safe
def s6_606 : State := ⟨[1,108,104,210], 2056880696651507552716012563677930555499843624797519397280350486, 2, 0, 1, 0⟩
theorem s6_606_edges : next config 6 s6_606 = [s7_177] := by decide
theorem s6_606_safe : Safe 7 6 s6_606 := by
  apply safe_succ 6 6 s6_606 [s7_177] (by decide) s6_606_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_177_safe
def s6_607 : State := ⟨[1,108,104,210], 2056886973753242939374475654268823140024724008880315499808882966, 2, 0, 1, 0⟩
theorem s6_607_edges : next config 6 s6_607 = [s7_179] := by decide
theorem s6_607_safe : Safe 7 6 s6_607 := by
  apply safe_succ 6 6 s6_607 [s7_179] (by decide) s6_607_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_179_safe
def s6_608 : State := ⟨[1,108,104,224], 26959946667150639794667015087359913385438274310615055377310198858014, 3, 1, 1, 0⟩
theorem s6_608_edges : next config 6 s6_608 = [s7_194] := by decide
theorem s6_608_safe : Safe 7 6 s6_608 := by
  apply safe_succ 6 6 s6_608 [s7_194] (by decide) s6_608_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_194_safe
def s6_609 : State := ⟨[1,108,104,224], 26959946667150639794667015087359913385438274310651948865457617961238, 3, 1, 1, 0⟩
theorem s6_609_edges : next config 6 s6_609 = [s7_195] := by decide
theorem s6_609_safe : Safe 7 6 s6_609 := by
  apply safe_succ 6 6 s6_609 [s7_195] (by decide) s6_609_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_195_safe
def s6_610 : State := ⟨[1,108,104,232], 6901746346790563787434755862277365735162910102058461038058730812408094, 3, 1, 1, 0⟩
theorem s6_610_edges : next config 6 s6_610 = [s7_208] := by decide
theorem s6_610_safe : Safe 7 6 s6_610 := by
  apply safe_succ 6 6 s6_610 [s7_208] (by decide) s6_610_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_208_safe
def s6_611 : State := ⟨[1,108,104,232], 6901746346790563787434755862277365735162910102058497931546878231511318, 3, 1, 1, 0⟩
theorem s6_611_edges : next config 6 s6_611 = [s7_209] := by decide
theorem s6_611_safe : Safe 7 6 s6_611 := by
  apply safe_succ 6 6 s6_611 [s7_209] (by decide) s6_611_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_209_safe
def s6_612 : State := ⟨[1,108,104,236], 110427941548649020598956093796432747521929544684614259365496594169397534, 3, 1, 1, 0⟩
theorem s6_612_edges : next config 6 s6_612 = [s7_212] := by decide
theorem s6_612_safe : Safe 7 6 s6_612 := by
  apply safe_succ 6 6 s6_612 [s7_212] (by decide) s6_612_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_212_safe
def s6_613 : State := ⟨[1,108,104,236], 110427941548649020598956093796432747521929544684614296258984741588500758, 3, 1, 1, 0⟩
theorem s6_613_edges : next config 6 s6_613 = [s7_213] := by decide
theorem s6_613_safe : Safe 7 6 s6_613 := by
  apply safe_succ 6 6 s6_613 [s7_213] (by decide) s6_613_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_213_safe
def s6_614 : State := ⟨[1,117,96,145], 44601830845581745922811916743961708865978646, 3, 1, 1, 0⟩
theorem s6_614_edges : next config 6 s6_614 = [s7_364, s7_311] := by decide
theorem s6_614_safe : Safe 7 6 s6_614 := by
  apply safe_succ 6 6 s6_614 [s7_364, s7_311] (by decide) s6_614_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_364_safe
  · subst z; exact s7_311_safe
def s6_615 : State := ⟨[1,140,104,136], 1481249143227206769222254047656105824289054, 3, 1, 1, 0⟩
theorem s6_615_edges : next config 6 s6_615 = [s7_103] := by decide
theorem s6_615_safe : Safe 7 6 s6_615 := by
  apply safe_succ 6 6 s6_615 [s7_103] (by decide) s6_615_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_103_safe
def s6_616 : State := ⟨[1,140,104,136], 1481249143227206769222254047656114414223638, 3, 1, 1, 0⟩
theorem s6_616_edges : next config 6 s6_616 = [s7_104] := by decide
theorem s6_616_safe : Safe 7 6 s6_616 := by
  apply safe_succ 6 6 s6_616 [s7_104] (by decide) s6_616_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_104_safe
def s6_617 : State := ⟨[1,140,104,136], 1481249143227206769222290941144253243392278, 3, 1, 1, 0⟩
theorem s6_617_edges : next config 6 s6_617 = [s7_105] := by decide
theorem s6_617_safe : Safe 7 6 s6_617 := by
  apply safe_succ 6 6 s6_617 [s7_105] (by decide) s6_617_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_105_safe
def s6_618 : State := ⟨[1,140,104,136], 1481249143227365225547282576331292912189718, 3, 1, 1, 0⟩
theorem s6_618_edges : next config 6 s6_618 = [s7_106] := by decide
theorem s6_618_safe : Safe 7 6 s6_618 := by
  apply safe_succ 6 6 s6_618 [s7_106] (by decide) s6_618_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_106_safe
def s6_619 : State := ⟨[1,214,67,145], 27973577474460502716701378679352917375069580573771083155731710230, 2, 0, 1, 0⟩
theorem s6_619_edges : next config 6 s6_619 = [] := by decide
theorem s6_619_safe : Safe 7 6 s6_619 := by
  apply safe_succ 6 6 s6_619 [] (by decide) s6_619_edges
  simp
def s6_620 : State := ⟨[1,214,67,145], 27973602582867444263402133277312079582593709264920212650363781398, 2, 0, 1, 0⟩
theorem s6_620_edges : next config 6 s6_620 = [] := by decide
theorem s6_620_safe : Safe 7 6 s6_620 := by
  apply safe_succ 6 6 s6_620 [] (by decide) s6_620_edges
  simp
def s6_621 : State := ⟨[1,214,67,145], 28384953613790804227240120974992255001315264466392501826730656022, 2, 0, 1, 0⟩
theorem s6_621_edges : next config 6 s6_621 = [] := by decide
theorem s6_621_safe : Safe 7 6 s6_621 := by
  apply safe_succ 6 6 s6_621 [] (by decide) s6_621_edges
  simp
def s6_622 : State := ⟨[1,214,104,146], 26328072917139296674568711603123585538620000519630319216595370262, 2, 0, 1, 0⟩
theorem s6_622_edges : next config 6 s6_622 = [] := by decide
theorem s6_622_safe : Safe 7 6 s6_622 := by
  apply safe_succ 6 6 s6_622 [] (by decide) s6_622_edges
  simp
def s6_623 : State := ⟨[1,214,104,146], 26328072917139296674591010987192648478007682384404537851028504854, 2, 0, 1, 0⟩
theorem s6_623_edges : next config 6 s6_623 = [] := by decide
theorem s6_623_safe : Safe 7 6 s6_623 := by
  apply safe_succ 6 6 s6_623 [] (by decide) s6_623_edges
  simp
def s6_624 : State := ⟨[1,214,104,146], 26328072917139296675995959295829545419678286193931909173625291030, 2, 0, 1, 0⟩
theorem s6_624_edges : next config 6 s6_624 = [] := by decide
theorem s6_624_safe : Safe 7 6 s6_624 := by
  apply safe_succ 6 6 s6_624 [] (by decide) s6_624_edges
  simp
def s6_625 : State := ⟨[1,214,104,146], 26328072917139296676018258679898608359065968058706127808058425622, 2, 0, 1, 0⟩
theorem s6_625_edges : next config 6 s6_625 = [] := by decide
theorem s6_625_safe : Safe 7 6 s6_625 := by
  apply safe_succ 6 6 s6_625 [] (by decide) s6_625_edges
  simp
def s6_626 : State := ⟨[1,214,104,210], 27973577474460502716723680785680936043602736090115993900591153430, 2, 0, 1, 0⟩
theorem s6_626_edges : next config 6 s6_626 = [s7_180] := by decide
theorem s6_626_safe : Safe 7 6 s6_626 := by
  apply safe_succ 6 6 s6_626 [s7_180] (by decide) s6_626_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_180_safe
def s6_627 : State := ⟨[1,214,104,210], 27973577474460502716745980169749998982990417954890212535024288022, 2, 0, 1, 0⟩
theorem s6_627_edges : next config 6 s6_627 = [s7_181] := by decide
theorem s6_627_safe : Safe 7 6 s6_627 := by
  apply safe_succ 6 6 s6_627 [s7_181] (by decide) s6_627_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_181_safe
def s6_628 : State := ⟨[1,214,104,210], 27973602582867444263357533148044506381702257626447178310705283350, 2, 0, 1, 0⟩
theorem s6_628_edges : next config 6 s6_628 = [s7_182] := by decide
theorem s6_628_safe : Safe 7 6 s6_628 := by
  apply safe_succ 6 6 s6_628 [s7_182] (by decide) s6_628_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_182_safe
def s6_629 : State := ⟨[1,214,104,210], 27973608859969179650038295622704461905614819875304193047666950422, 2, 0, 1, 0⟩
theorem s6_629_edges : next config 6 s6_629 = [s7_183] := by decide
theorem s6_629_safe : Safe 7 6 s6_629 := by
  apply safe_succ 6 6 s6_629 [s7_183] (by decide) s6_629_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_183_safe
def s6_630 : State := ⟨[1,214,104,210], 28384953613790804227195519484595214116669959048208014054837518614, 2, 0, 1, 0⟩
theorem s6_630_edges : next config 6 s6_630 = [s7_184] := by decide
theorem s6_630_safe : Safe 7 6 s6_630 := by
  apply safe_succ 6 6 s6_630 [s7_184] (by decide) s6_630_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_184_safe
def s6_631 : State := ⟨[1,214,104,210], 28384959890892539613853982575186106701194839432290810157366051094, 2, 0, 1, 0⟩
theorem s6_631_edges : next config 6 s6_631 = [s7_185] := by decide
theorem s6_631_safe : Safe 7 6 s6_631 := by
  apply safe_succ 6 6 s6_631 [s7_185] (by decide) s6_631_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_185_safe
def s6_632 : State := ⟨[1,228,104,224], 458319093341560876509339256479674003839114031412837488291811942269214, 3, 1, 1, 0⟩
theorem s6_632_edges : next config 6 s6_632 = [s7_197] := by decide
theorem s6_632_safe : Safe 7 6 s6_632 := by
  apply safe_succ 6 6 s6_632 [s7_197] (by decide) s6_632_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_197_safe
def s6_633 : State := ⟨[1,228,104,224], 458319093341560876509339256479674003839114031412874381779959361372438, 3, 1, 1, 0⟩
theorem s6_633_edges : next config 6 s6_633 = [s7_198] := by decide
theorem s6_633_safe : Safe 7 6 s6_633 := by
  apply safe_succ 6 6 s6_633 [s7_198] (by decide) s6_633_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_198_safe
def s6_634 : State := ⟨[1,236,104,232], 117329687895439584386390849658709772974056135103126219193875962372620574, 3, 1, 1, 0⟩
theorem s6_634_edges : next config 6 s6_634 = [s7_210] := by decide
theorem s6_634_safe : Safe 7 6 s6_634 := by
  apply safe_succ 6 6 s6_634 [s7_210] (by decide) s6_634_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_210_safe
def s6_635 : State := ⟨[1,236,104,232], 117329687895439584386390849658709772974056135103126256087364109791723798, 3, 1, 1, 0⟩
theorem s6_635_edges : next config 6 s6_635 = [s7_211] := by decide
theorem s6_635_safe : Safe 7 6 s6_635 := by
  apply safe_succ 6 6 s6_635 [s7_211] (by decide) s6_635_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_211_safe
def s6_636 : State := ⟨[3,4,64,145], 44601830679428167221534918366648232784892190, 3, 3, 1, 0⟩
theorem s6_636_edges : next config 6 s6_636 = [s7_918, s7_609, s7_313, s7_317] := by decide
theorem s6_636_safe : Safe 7 6 s6_636 := by
  apply safe_succ 6 6 s6_636 [s7_918, s7_609, s7_313, s7_317] (by decide) s6_636_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_918_safe
  · subst z; exact s7_609_safe
  · subst z; exact s7_313_safe
  · subst z; exact s7_317_safe
def s6_637 : State := ⟨[3,4,64,145], 44601830679428167221534918366648232786985246, 3, 3, 1, 0⟩
theorem s6_637_edges : next config 6 s6_637 = [s7_919, s7_610, s7_341, s7_314, s7_318] := by decide
theorem s6_637_safe : Safe 7 6 s6_637 := by
  apply safe_succ 6 6 s6_637 [s7_919, s7_610, s7_341, s7_314, s7_318] (by decide) s6_637_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_919_safe
  · subst z; exact s7_610_safe
  · subst z; exact s7_341_safe
  · subst z; exact s7_314_safe
  · subst z; exact s7_318_safe
def s6_638 : State := ⟨[3,4,64,145], 133806172603018343541531644955671405881528606, 3, 2, 1, 0⟩
theorem s6_638_edges : next config 6 s6_638 = [s7_0, s7_315, s7_320] := by decide
theorem s6_638_safe : Safe 7 6 s6_638 := by
  apply safe_succ 6 6 s6_638 [s7_0, s7_315, s7_320] (by decide) s6_638_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_0_safe
  · subst z; exact s7_315_safe
  · subst z; exact s7_320_safe
def s6_639 : State := ⟨[3,4,64,145], 156105556672081282929213509729890040314663198, 3, 2, 1, 0⟩
theorem s6_639_edges : next config 6 s6_639 = [s7_1, s7_316, s7_321] := by decide
theorem s6_639_safe : Safe 7 6 s6_639 := by
  apply safe_succ 6 6 s6_639 [s7_1, s7_316, s7_321] (by decide) s6_639_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_1_safe
  · subst z; exact s7_316_safe
  · subst z; exact s7_321_safe
def s6_640 : State := ⟨[3,4,67,145], 44602511244162009098461992689815685997596958, 3, 2, 1, 0⟩
theorem s6_640_edges : next config 6 s6_640 = [s7_920, s7_6, s7_630] := by decide
theorem s6_640_safe : Safe 7 6 s6_640 := by
  apply safe_succ 6 6 s6_640 [s7_920, s7_6, s7_630] (by decide) s6_640_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_920_safe
  · subst z; exact s7_6_safe
  · subst z; exact s7_630_safe
def s6_641 : State := ⟨[3,4,67,145], 66902575877958790363070784213249183967154462, 3, 2, 1, 0⟩
theorem s6_641_edges : next config 6 s6_641 = [s7_921, s7_7, s7_631] := by decide
theorem s6_641_safe : Safe 7 6 s6_641 := by
  apply safe_succ 6 6 s6_641 [s7_921, s7_7, s7_631] (by decide) s6_641_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_921_safe
  · subst z; exact s7_7_safe
  · subst z; exact s7_631_safe
def s6_642 : State := ⟨[3,4,67,146], 89204682205957097258460355984327272545980702, 3, 2, 1, 0⟩
theorem s6_642_edges : next config 6 s6_642 = [s7_14, s7_315] := by decide
theorem s6_642_safe : Safe 7 6 s6_642 := by
  apply safe_succ 6 6 s6_642 [s7_14, s7_315] (by decide) s6_642_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_14_safe
  · subst z; exact s7_315_safe
def s6_643 : State := ⟨[3,4,67,146], 111504066275020036646142220758545906979115294, 3, 2, 1, 0⟩
theorem s6_643_edges : next config 6 s6_643 = [s7_15, s7_316] := by decide
theorem s6_643_safe : Safe 7 6 s6_643 := by
  apply safe_succ 6 6 s6_643 [s7_15, s7_316] (by decide) s6_643_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_15_safe
  · subst z; exact s7_316_safe
def s6_644 : State := ⟨[3,4,67,162], 5846006551025023507419431648348025812450252230942, 3, 2, 1, 0⟩
theorem s6_644_edges : next config 6 s6_644 = [s7_16] := by decide
theorem s6_644_safe : Safe 7 6 s6_644 := by
  apply safe_succ 6 6 s6_644 [s7_16] (by decide) s6_644_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_16_safe
def s6_645 : State := ⟨[3,4,67,162], 7307508186994796957939362627210810402379111928094, 3, 2, 1, 0⟩
theorem s6_645_edges : next config 6 s6_645 = [s7_17] := by decide
theorem s6_645_safe : Safe 7 6 s6_645 := by
  apply safe_succ 6 6 s6_645 [s7_17] (by decide) s6_645_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_17_safe
def s6_646 : State := ⟨[3,4,67,163], 11692013101709764647917924833066656320801055248670, 3, 2, 1, 0⟩
theorem s6_646_edges : next config 6 s6_646 = [s7_18] := by decide
theorem s6_646_safe : Safe 7 6 s6_646 := by
  apply safe_succ 6 6 s6_646 [s7_18] (by decide) s6_646_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_18_safe
def s6_647 : State := ⟨[3,4,67,163], 13153514736318408630754101958075942481002842099998, 3, 2, 1, 0⟩
theorem s6_647_edges : next config 6 s6_647 = [s7_19] := by decide
theorem s6_647_safe : Safe 7 6 s6_647 := by
  apply safe_succ 6 6 s6_647 [s7_19] (by decide) s6_647_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_19_safe
def s6_648 : State := ⟨[3,4,67,176], 95780971326419139128294233276893671644123656091668766, 3, 2, 1, 0⟩
theorem s6_648_edges : next config 6 s6_648 = [s7_20] := by decide
theorem s6_648_safe : Safe 7 6 s6_648 := by
  apply safe_succ 6 6 s6_648 [s7_20] (by decide) s6_648_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_20_safe
def s6_649 : State := ⟨[3,4,67,176], 95782432805755724832681813820190669654494950518231326, 3, 2, 1, 0⟩
theorem s6_649_edges : next config 6 s6_649 = [s7_21] := by decide
theorem s6_649_safe : Safe 7 6 s6_649 := by
  apply safe_succ 6 6 s6_649 [s7_21] (by decide) s6_649_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_21_safe
def s6_650 : State := ⟨[3,4,96,145], 44602511244162088326624359380200689865134366, 3, 2, 1, 0⟩
theorem s6_650_edges : next config 6 s6_650 = [s7_922, s7_28, s7_643, s7_338, s7_322] := by decide
theorem s6_650_safe : Safe 7 6 s6_650 := by
  apply safe_succ 6 6 s6_650 [s7_922, s7_28, s7_643, s7_338, s7_322] (by decide) s6_650_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_922_safe
  · subst z; exact s7_28_safe
  · subst z; exact s7_643_safe
  · subst z; exact s7_338_safe
  · subst z; exact s7_322_safe
def s6_651 : State := ⟨[3,4,96,145], 44602511244163355977224587609602186568335646, 3, 2, 1, 0⟩
theorem s6_651_edges : next config 6 s6_651 = [s7_32, s7_323] := by decide
theorem s6_651_safe : Safe 7 6 s6_651 := by
  apply safe_succ 6 6 s6_651 [s7_32, s7_323] (by decide) s6_651_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_32_safe
  · subst z; exact s7_323_safe
def s6_652 : State := ⟨[3,4,96,145], 66902575877958869591233150903634187834691870, 3, 2, 1, 0⟩
theorem s6_652_edges : next config 6 s6_652 = [s7_923, s7_34, s7_645, s7_339, s7_325] := by decide
theorem s6_652_safe : Safe 7 6 s6_652 := by
  apply safe_succ 6 6 s6_652 [s7_923, s7_34, s7_645, s7_339, s7_325] (by decide) s6_652_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_923_safe
  · subst z; exact s7_34_safe
  · subst z; exact s7_645_safe
  · subst z; exact s7_339_safe
  · subst z; exact s7_325_safe
def s6_653 : State := ⟨[3,4,96,145], 66902575877960137241833379133035684537893150, 3, 2, 1, 0⟩
theorem s6_653_edges : next config 6 s6_653 = [s7_38, s7_326] := by decide
theorem s6_653_safe : Safe 7 6 s6_653 := by
  apply safe_succ 6 6 s6_653 [s7_38, s7_326] (by decide) s6_653_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_38_safe
  · subst z; exact s7_326_safe
def s6_654 : State := ⟨[3,4,96,146], 89204682205957176486622722674712276413518110, 3, 2, 1, 0⟩
theorem s6_654_edges : next config 6 s6_654 = [s7_40, s7_328, s7_320] := by decide
theorem s6_654_safe : Safe 7 6 s6_654 := by
  apply safe_succ 6 6 s6_654 [s7_40, s7_328, s7_320] (by decide) s6_654_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_40_safe
  · subst z; exact s7_328_safe
  · subst z; exact s7_320_safe
def s6_655 : State := ⟨[3,4,96,146], 111504066275020115874304587448930910846652702, 3, 2, 1, 0⟩
theorem s6_655_edges : next config 6 s6_655 = [s7_43, s7_329, s7_321] := by decide
theorem s6_655_safe : Safe 7 6 s6_655 := by
  apply safe_succ 6 6 s6_655 [s7_43, s7_329, s7_321] (by decide) s6_655_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_43_safe
  · subst z; exact s7_329_safe
  · subst z; exact s7_321_safe
def s6_656 : State := ⟨[3,4,96,162], 5846006551025023507498659810714716197454119768350, 3, 2, 1, 0⟩
theorem s6_656_edges : next config 6 s6_656 = [s7_45, s7_330] := by decide
theorem s6_656_safe : Safe 7 6 s6_656 := by
  apply safe_succ 6 6 s6_656 [s7_45, s7_330] (by decide) s6_656_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_45_safe
  · subst z; exact s7_330_safe
def s6_657 : State := ⟨[3,4,96,162], 7307508186994796958018590789577500787382979465502, 3, 2, 1, 0⟩
theorem s6_657_edges : next config 6 s6_657 = [s7_49, s7_331] := by decide
theorem s6_657_safe : Safe 7 6 s6_657 := by
  apply safe_succ 6 6 s6_657 [s7_49, s7_331] (by decide) s6_657_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_49_safe
  · subst z; exact s7_331_safe
def s6_658 : State := ⟨[3,4,96,163], 11692013101709764647997152995433346705804922786078, 3, 2, 1, 0⟩
theorem s6_658_edges : next config 6 s6_658 = [s7_55, s7_332] := by decide
theorem s6_658_safe : Safe 7 6 s6_658 := by
  apply safe_succ 6 6 s6_658 [s7_55, s7_332] (by decide) s6_658_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_55_safe
  · subst z; exact s7_332_safe
def s6_659 : State := ⟨[3,4,96,163], 13153514736318408630833330120442632866006709637406, 3, 2, 1, 0⟩
theorem s6_659_edges : next config 6 s6_659 = [s7_56, s7_333] := by decide
theorem s6_659_safe : Safe 7 6 s6_659 := by
  apply safe_succ 6 6 s6_659 [s7_56, s7_333] (by decide) s6_659_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_56_safe
  · subst z; exact s7_333_safe
def s6_660 : State := ⟨[3,4,96,176], 95780971326419139128294312505056038334508659959206174, 3, 2, 1, 0⟩
theorem s6_660_edges : next config 6 s6_660 = [s7_58, s7_334] := by decide
theorem s6_660_safe : Safe 7 6 s6_660 := by
  apply safe_succ 6 6 s6_660 [s7_58, s7_334] (by decide) s6_660_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_58_safe
  · subst z; exact s7_334_safe
def s6_661 : State := ⟨[3,4,96,176], 95782432805755724832681893048353036344879954385768734, 3, 2, 1, 0⟩
theorem s6_661_edges : next config 6 s6_661 = [s7_60, s7_335] := by decide
theorem s6_661_safe : Safe 7 6 s6_661 := by
  apply safe_succ 6 6 s6_661 [s7_60, s7_335] (by decide) s6_661_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_60_safe
  · subst z; exact s7_335_safe
def s6_662 : State := ⟨[3,4,100,145], 44601830679429514100297660860387323032043806, 1, 1, 1, 0⟩
theorem s6_662_edges : next config 6 s6_662 = [] := by decide
theorem s6_662_safe : Safe 7 6 s6_662 := by
  apply safe_succ 6 6 s6_662 [] (by decide) s6_662_edges
  simp
def s6_663 : State := ⟨[3,4,104,129], 1020847121124453156574505327914104459550, 3, 2, 1, 0⟩
theorem s6_663_edges : next config 6 s6_663 = [s7_65, s7_647, s7_322] := by decide
theorem s6_663_safe : Safe 7 6 s6_663 := by
  apply safe_succ 6 6 s6_663 [s7_65, s7_647, s7_322] (by decide) s6_663_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_65_safe
  · subst z; exact s7_647_safe
  · subst z; exact s7_322_safe
def s6_664 : State := ⟨[3,4,104,129], 1020847122392103756802734729410807660830, 3, 2, 1, 0⟩
theorem s6_664_edges : next config 6 s6_664 = [s7_69, s7_323] := by decide
theorem s6_664_safe : Safe 7 6 s6_664 := by
  apply safe_succ 6 6 s6_664 [s7_69, s7_323] (by decide) s6_664_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_69_safe
  · subst z; exact s7_323_safe
def s6_665 : State := ⟨[3,4,104,129], 1020847445643006815001232111070125031710, 3, 2, 1, 0⟩
theorem s6_665_edges : next config 6 s6_665 = [s7_71, s7_324] := by decide
theorem s6_665_safe : Safe 7 6 s6_665 := by
  apply safe_succ 6 6 s6_665 [s7_71, s7_324] (by decide) s6_665_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_71_safe
  · subst z; exact s7_324_safe
def s6_666 : State := ⟨[3,4,104,130], 1701411854966330083501254542777640882462, 3, 2, 1, 0⟩
theorem s6_666_edges : next config 6 s6_666 = [s7_73, s7_649, s7_328, s7_330] := by decide
theorem s6_666_safe : Safe 7 6 s6_666 := by
  apply safe_succ 6 6 s6_666 [s7_73, s7_649, s7_328, s7_330] (by decide) s6_666_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_73_safe
  · subst z; exact s7_649_safe
  · subst z; exact s7_328_safe
  · subst z; exact s7_330_safe
def s6_667 : State := ⟨[3,4,104,130], 1701411856233980683729483944274344083742, 3, 2, 1, 0⟩
theorem s6_667_edges : next config 6 s6_667 = [s7_77] := by decide
theorem s6_667_safe : Safe 7 6 s6_667 := by
  apply safe_succ 6 6 s6_667 [s7_77] (by decide) s6_667_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_77_safe
def s6_668 : State := ⟨[3,4,104,130], 1701412179484883741927981325933661454622, 3, 2, 1, 0⟩
theorem s6_668_edges : next config 6 s6_668 = [s7_79] := by decide
theorem s6_668_safe : Safe 7 6 s6_668 := by
  apply safe_succ 6 6 s6_668 [s7_79] (by decide) s6_668_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_79_safe
def s6_669 : State := ⟨[3,4,104,131], 3062541322650083937354752972504713728286, 3, 2, 1, 0⟩
theorem s6_669_edges : next config 6 s6_669 = [s7_84, s7_651, s7_332] := by decide
theorem s6_669_safe : Safe 7 6 s6_669 := by
  apply safe_succ 6 6 s6_669 [s7_84, s7_651, s7_332] (by decide) s6_669_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_84_safe
  · subst z; exact s7_651_safe
  · subst z; exact s7_332_safe
def s6_670 : State := ⟨[3,4,104,131], 3062541323917734537582982374001416929566, 3, 2, 1, 0⟩
theorem s6_670_edges : next config 6 s6_670 = [s7_85] := by decide
theorem s6_670_safe : Safe 7 6 s6_670 := by
  apply safe_succ 6 6 s6_670 [s7_85] (by decide) s6_670_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_85_safe
def s6_671 : State := ⟨[3,4,104,131], 3062541647168637595781479755660734300446, 3, 2, 1, 0⟩
theorem s6_671_edges : next config 6 s6_671 = [s7_86] := by decide
theorem s6_671_safe : Safe 7 6 s6_671 := by
  apply safe_succ 6 6 s6_671 [s7_86] (by decide) s6_671_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_86_safe
def s6_672 : State := ⟨[3,4,104,132], 5784800258017591645061749831958859419934, 3, 2, 1, 0⟩
theorem s6_672_edges : next config 6 s6_672 = [s7_87, s7_652] := by decide
theorem s6_672_safe : Safe 7 6 s6_672 := by
  apply safe_succ 6 6 s6_672 [s7_87, s7_652] (by decide) s6_672_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_87_safe
  · subst z; exact s7_652_safe
def s6_673 : State := ⟨[3,4,104,132], 5784800259285242245289979233455562621214, 3, 2, 1, 0⟩
theorem s6_673_edges : next config 6 s6_673 = [s7_91] := by decide
theorem s6_673_safe : Safe 7 6 s6_673 := by
  apply safe_succ 6 6 s6_673 [s7_91] (by decide) s6_673_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_91_safe
def s6_674 : State := ⟨[3,4,104,132], 5784800582536145303488476615114879992094, 3, 2, 1, 0⟩
theorem s6_674_edges : next config 6 s6_674 = [s7_93] := by decide
theorem s6_674_safe : Safe 7 6 s6_674 := by
  apply safe_succ 6 6 s6_674 [s7_93] (by decide) s6_674_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_93_safe
def s6_675 : State := ⟨[3,4,104,136], 87452568319042822876271655615583230169374, 3, 2, 1, 0⟩
theorem s6_675_edges : next config 6 s6_675 = [s7_95, s7_654] := by decide
theorem s6_675_safe : Safe 7 6 s6_675 := by
  apply safe_succ 6 6 s6_675 [s7_95, s7_654] (by decide) s6_675_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_95_safe
  · subst z; exact s7_654_safe
def s6_676 : State := ⟨[3,4,104,136], 87452568320310473476499885017079933370654, 3, 2, 1, 0⟩
theorem s6_676_edges : next config 6 s6_676 = [s7_99] := by decide
theorem s6_676_safe : Safe 7 6 s6_676 := by
  apply safe_succ 6 6 s6_676 [s7_99] (by decide) s6_676_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_99_safe
def s6_677 : State := ⟨[3,4,104,136], 87452568643561376534698382398739250741534, 3, 2, 1, 0⟩
theorem s6_677_edges : next config 6 s6_677 = [s7_101] := by decide
theorem s6_677_safe : Safe 7 6 s6_677 := by
  apply safe_succ 6 6 s6_677 [s7_101] (by decide) s6_677_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_101_safe
def s6_678 : State := ⟨[3,4,104,136], 1481249143227206769222254047656105824289054, 3, 2, 1, 0⟩
theorem s6_678_edges : next config 6 s6_678 = [s7_103, s7_656] := by decide
theorem s6_678_safe : Safe 7 6 s6_678 := by
  apply safe_succ 6 6 s6_678 [s7_103, s7_656] (by decide) s6_678_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_103_safe
  · subst z; exact s7_656_safe
def s6_679 : State := ⟨[3,4,104,140], 1394136857295446522575630148153573162160414, 3, 2, 1, 0⟩
theorem s6_679_edges : next config 6 s6_679 = [s7_107, s7_658] := by decide
theorem s6_679_safe : Safe 7 6 s6_679 := by
  apply safe_succ 6 6 s6_679 [s7_107, s7_658] (by decide) s6_679_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_107_safe
  · subst z; exact s7_658_safe
def s6_680 : State := ⟨[3,4,104,144], 22301085480917905717765366028761412074017054, 3, 2, 1, 0⟩
theorem s6_680_edges : next config 6 s6_680 = [s7_111, s7_660, s7_329, s7_334] := by decide
theorem s6_680_safe : Safe 7 6 s6_680 := by
  apply safe_succ 6 6 s6_680 [s7_111, s7_660, s7_329, s7_334] (by decide) s6_680_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_111_safe
  · subst z; exact s7_660_safe
  · subst z; exact s7_329_safe
  · subst z; exact s7_334_safe
def s6_681 : State := ⟨[3,4,104,144], 22301085480919173368365594258162908777218334, 3, 2, 1, 0⟩
theorem s6_681_edges : next config 6 s6_681 = [s7_115] := by decide
theorem s6_681_safe : Safe 7 6 s6_681 := by
  apply safe_succ 6 6 s6_681 [s7_115] (by decide) s6_681_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_115_safe
def s6_682 : State := ⟨[3,4,104,144], 22301085481242424271423792755544568094589214, 3, 2, 1, 0⟩
theorem s6_682_edges : next config 6 s6_682 = [s7_117] := by decide
theorem s6_682_safe : Safe 7 6 s6_682 := by
  apply safe_succ 6 6 s6_682 [s7_117] (by decide) s6_682_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_117_safe
def s6_683 : State := ⟨[3,4,104,145], 44601830679448528859301084301409773580124446, 1, 1, 1, 0⟩
theorem s6_683_edges : next config 6 s6_683 = [s7_924, s7_662, s7_363, s7_342, s7_336, s7_340] := by decide
theorem s6_683_safe : Safe 7 6 s6_683 := by
  apply safe_succ 6 6 s6_683 [s7_924, s7_662, s7_363, s7_342, s7_336, s7_340] (by decide) s6_683_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s7_924_safe
  · subst z; exact s7_662_safe
  · subst z; exact s7_363_safe
  · subst z; exact s7_342_safe
  · subst z; exact s7_336_safe
  · subst z; exact s7_340_safe
def s6_684 : State := ⟨[3,4,104,145], 133806172603038705179297810890432946676760862, 1, 0, 1, 0⟩
theorem s6_684_edges : next config 6 s6_684 = [s7_124, s7_343] := by decide
theorem s6_684_safe : Safe 7 6 s6_684 := by
  apply safe_succ 6 6 s6_684 [s7_124, s7_343] (by decide) s6_684_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_124_safe
  · subst z; exact s7_343_safe
def s6_685 : State := ⟨[3,4,104,145], 156105556672101644566979675664651581109895454, 1, 0, 1, 0⟩
theorem s6_685_edges : next config 6 s6_685 = [s7_125, s7_344] := by decide
theorem s6_685_safe : Safe 7 6 s6_685 := by
  apply safe_succ 6 6 s6_685 [s7_125, s7_344] (by decide) s6_685_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_125_safe
  · subst z; exact s7_344_safe
def s6_686 : State := ⟨[3,4,104,160], 1461501637671185305486261062364039132706500579614, 3, 2, 1, 0⟩
theorem s6_686_edges : next config 6 s6_686 = [s7_933, s7_126, s7_664, s7_333, s7_331, s7_335] := by decide
theorem s6_686_safe : Safe 7 6 s6_686 := by
  apply safe_succ 6 6 s6_686 [s7_933, s7_126, s7_664, s7_333, s7_331, s7_335] (by decide) s6_686_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s7_933_safe
  · subst z; exact s7_126_safe
  · subst z; exact s7_664_safe
  · subst z; exact s7_333_safe
  · subst z; exact s7_331_safe
  · subst z; exact s7_335_safe
def s6_687 : State := ⟨[3,4,104,160], 1461501637671185306753911662592268534203203780894, 3, 2, 1, 0⟩
theorem s6_687_edges : next config 6 s6_687 = [s7_130] := by decide
theorem s6_687_safe : Safe 7 6 s6_687 := by
  apply safe_succ 6 6 s6_687 [s7_130] (by decide) s6_687_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_130_safe
def s6_688 : State := ⟨[3,4,104,160], 1461501637671185630004814720790765915862521151774, 3, 2, 1, 0⟩
theorem s6_688_edges : next config 6 s6_688 = [s7_132] := by decide
theorem s6_688_safe : Safe 7 6 s6_688 := by
  apply safe_succ 6 6 s6_688 [s7_132] (by decide) s6_688_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_132_safe
def s6_689 : State := ⟨[3,4,104,171], 3004847366355398941149426100002032641385102022082846, 1, 0, 1, 0⟩
theorem s6_689_edges : next config 6 s6_689 = [s7_149] := by decide
theorem s6_689_safe : Safe 7 6 s6_689 := by
  apply safe_succ 6 6 s6_689 [s7_149] (by decide) s6_689_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_149_safe
def s6_690 : State := ⟨[3,4,104,171], 3006308867990007585132262277127041927545303808934174, 1, 0, 1, 0⟩
theorem s6_690_edges : next config 6 s6_690 = [s7_150] := by decide
theorem s6_690_safe : Safe 7 6 s6_690 := by
  apply safe_succ 6 6 s6_690 [s7_150] (by decide) s6_690_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_150_safe
def s6_691 : State := ⟨[3,4,104,192], 6277101735386680764176071810490242645750111557514602549534, 3, 2, 1, 0⟩
theorem s6_691_edges : next config 6 s6_691 = [s7_152, s7_669] := by decide
theorem s6_691_safe : Safe 7 6 s6_691 := by
  apply safe_succ 6 6 s6_691 [s7_152, s7_669] (by decide) s6_691_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_152_safe
  · subst z; exact s7_669_safe
def s6_692 : State := ⟨[3,4,104,192], 6277101735386680764176071811757893245978340959011305750814, 3, 2, 1, 0⟩
theorem s6_692_edges : next config 6 s6_692 = [s7_156] := by decide
theorem s6_692_safe : Safe 7 6 s6_692 := by
  apply safe_succ 6 6 s6_692 [s7_156] (by decide) s6_692_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_156_safe
def s6_693 : State := ⟨[3,4,104,192], 6277101735386680764176072135008796304176838340670623121694, 3, 2, 1, 0⟩
theorem s6_693_edges : next config 6 s6_693 = [s7_158] := by decide
theorem s6_693_safe : Safe 7 6 s6_693 := by
  apply safe_succ 6 6 s6_693 [s7_158] (by decide) s6_693_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_158_safe
def s6_694 : State := ⟨[3,4,104,224], 26959946667150639794667015087359913060919720652188328594154178285854, 3, 2, 1, 0⟩
theorem s6_694_edges : next config 6 s6_694 = [s7_188, s7_671] := by decide
theorem s6_694_safe : Safe 7 6 s6_694 := by
  apply safe_succ 6 6 s6_694 [s7_188, s7_671] (by decide) s6_694_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_188_safe
  · subst z; exact s7_671_safe
def s6_695 : State := ⟨[3,4,104,224], 26959946667150639794667015087359913062187371252416557995650881487134, 3, 2, 1, 0⟩
theorem s6_695_edges : next config 6 s6_695 = [s7_192] := by decide
theorem s6_695_safe : Safe 7 6 s6_695 := by
  apply safe_succ 6 6 s6_695 [s7_192] (by decide) s6_695_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_192_safe
def s6_696 : State := ⟨[3,4,104,224], 26959946667150639794667015087359913385438274310615055377310198858014, 3, 2, 1, 0⟩
theorem s6_696_edges : next config 6 s6_696 = [s7_194] := by decide
theorem s6_696_safe : Safe 7 6 s6_696 := by
  apply safe_succ 6 6 s6_696 [s7_194] (by decide) s6_696_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_194_safe
def s6_697 : State := ⟨[3,4,104,224], 458319093341560876509339256479674003839114031412837488291811942269214, 3, 2, 1, 0⟩
theorem s6_697_edges : next config 6 s6_697 = [s7_197] := by decide
theorem s6_697_safe : Safe 7 6 s6_697 := by
  apply safe_succ 6 6 s6_697 [s7_197] (by decide) s6_697_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_197_safe
def s6_698 : State := ⟨[3,4,104,228], 431359146674410236714672241392654373166744537590525145212205035225374, 3, 2, 1, 0⟩
theorem s6_698_edges : next config 6 s6_698 = [s7_200] := by decide
theorem s6_698_safe : Safe 7 6 s6_698 := by
  apply safe_succ 6 6 s6_698 [s7_200] (by decide) s6_698_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_200_safe
def s6_699 : State := ⟨[3,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791835934, 3, 2, 1, 0⟩
theorem s6_699_edges : next config 6 s6_699 = [s7_202, s7_673] := by decide
theorem s6_699_safe : Safe 7 6 s6_699 := by
  apply safe_succ 6 6 s6_699 [s7_202, s7_673] (by decide) s6_699_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_202_safe
  · subst z; exact s7_673_safe
def s6_700 : State := ⟨[3,4,104,232], 6901746346790563787434755862277365734839659199000262540677071495037214, 3, 2, 1, 0⟩
theorem s6_700_edges : next config 6 s6_700 = [s7_206] := by decide
theorem s6_700_safe : Safe 7 6 s6_700 := by
  apply safe_succ 6 6 s6_700 [s7_206] (by decide) s6_700_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_206_safe
def s6_701 : State := ⟨[3,4,104,232], 6901746346790563787434755862277365735162910102058461038058730812408094, 3, 2, 1, 0⟩
theorem s6_701_edges : next config 6 s6_701 = [s7_208] := by decide
theorem s6_701_safe : Safe 7 6 s6_701 := by
  apply safe_succ 6 6 s6_701 [s7_208] (by decide) s6_701_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_208_safe
def s6_702 : State := ⟨[3,4,104,232], 117329687895439584386390849658709772974056135103126219193875962372620574, 3, 2, 1, 0⟩
theorem s6_702_edges : next config 6 s6_702 = [s7_210] := by decide
theorem s6_702_safe : Safe 7 6 s6_702 := by
  apply safe_succ 6 6 s6_702 [s7_210] (by decide) s6_702_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_210_safe
def s6_703 : State := ⟨[3,4,104,236], 110427941548649020598956093796432747521929544684614259365496594169397534, 3, 2, 1, 0⟩
theorem s6_703_edges : next config 6 s6_703 = [s7_212] := by decide
theorem s6_703_safe : Safe 7 6 s6_703 := by
  apply safe_succ 6 6 s6_703 [s7_212] (by decide) s6_703_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_212_safe
def s6_704 : State := ⟨[3,4,108,145], 44602511244506889289886437777407793136992542, 1, 0, 1, 0⟩
theorem s6_704_edges : next config 6 s6_704 = [s7_214] := by decide
theorem s6_704_safe : Safe 7 6 s6_704 := by
  apply safe_succ 6 6 s6_704 [s7_214] (by decide) s6_704_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_214_safe
def s6_705 : State := ⟨[3,4,108,145], 66902575878303670554495229300841291106550046, 1, 0, 1, 0⟩
theorem s6_705_edges : next config 6 s6_705 = [s7_216] := by decide
theorem s6_705_safe : Safe 7 6 s6_705 := by
  apply safe_succ 6 6 s6_705 [s7_216] (by decide) s6_705_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_216_safe
def s6_706 : State := ⟨[3,4,113,145], 44601830689812840166767087888046818987278622, 1, 1, 1, 0⟩
theorem s6_706_edges : next config 6 s6_706 = [s7_345] := by decide
theorem s6_706_safe : Safe 7 6 s6_706 := by
  apply safe_succ 6 6 s6_706 [s7_345] (by decide) s6_706_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_345_safe
def s6_707 : State := ⟨[3,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914077982, 1, 1, 1, 0⟩
theorem s6_707_edges : next config 6 s6_707 = [s7_346] := by decide
theorem s6_707_safe : Safe 7 6 s6_707 := by
  apply safe_succ 6 6 s6_707 [s7_346] (by decide) s6_707_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_346_safe
def s6_708 : State := ⟨[3,4,249,145], 904625697166532776746648320380418882614915937571053134569312999698937741598, 1, 0, 1, 0⟩
theorem s6_708_edges : next config 6 s6_708 = [s7_226] := by decide
theorem s6_708_safe : Safe 7 6 s6_708 := by
  apply safe_succ 6 6 s6_708 [s7_226] (by decide) s6_708_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_226_safe
def s6_709 : State := ⟨[3,4,249,145], 904625697166532776746648320380441182679549734352317743360836433196907299102, 1, 0, 1, 0⟩
theorem s6_709_edges : next config 6 s6_709 = [s7_228] := by decide
theorem s6_709_safe : Safe 7 6 s6_709 := by
  apply safe_succ 6 6 s6_709 [s7_228] (by decide) s6_709_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_228_safe
def s6_710 : State := ⟨[3,12,67,145], 44601830679428167221535065940600822461305118, 3, 1, 1, 0⟩
theorem s6_710_edges : next config 6 s6_710 = [s7_925, s7_675, s7_313] := by decide
theorem s6_710_safe : Safe 7 6 s6_710 := by
  apply safe_succ 6 6 s6_710 [s7_925, s7_675, s7_313] (by decide) s6_710_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_925_safe
  · subst z; exact s7_675_safe
  · subst z; exact s7_313_safe
def s6_711 : State := ⟨[3,12,67,145], 133806172603018343541531792529623995557941534, 3, 0, 1, 0⟩
theorem s6_711_edges : next config 6 s6_711 = [s7_234, s7_315] := by decide
theorem s6_711_safe : Safe 7 6 s6_711 := by
  apply safe_succ 6 6 s6_711 [s7_234, s7_315] (by decide) s6_711_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_234_safe
  · subst z; exact s7_315_safe
def s6_712 : State := ⟨[3,12,67,145], 156105556672081282929213657303842629991076126, 3, 0, 1, 0⟩
theorem s6_712_edges : next config 6 s6_712 = [s7_235, s7_316] := by decide
theorem s6_712_safe : Safe 7 6 s6_712 := by
  apply safe_succ 6 6 s6_712 [s7_235, s7_316] (by decide) s6_712_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_235_safe
  · subst z; exact s7_316_safe
def s6_713 : State := ⟨[3,12,96,145], 44601830679428246449697432630985826328842526, 3, 1, 1, 0⟩
theorem s6_713_edges : next config 6 s6_713 = [s7_926, s7_680, s7_317, s7_346, s7_342] := by decide
theorem s6_713_safe : Safe 7 6 s6_713 := by
  apply safe_succ 6 6 s6_713 [s7_926, s7_680, s7_317, s7_346, s7_342] (by decide) s6_713_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_926_safe
  · subst z; exact s7_680_safe
  · subst z; exact s7_317_safe
  · subst z; exact s7_346_safe
  · subst z; exact s7_342_safe
def s6_714 : State := ⟨[3,12,96,145], 133806172603018422769694159220008999425478942, 3, 0, 1, 0⟩
theorem s6_714_edges : next config 6 s6_714 = [s7_239, s7_320, s7_343] := by decide
theorem s6_714_safe : Safe 7 6 s6_714 := by
  apply safe_succ 6 6 s6_714 [s7_239, s7_320, s7_343] (by decide) s6_714_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_239_safe
  · subst z; exact s7_320_safe
  · subst z; exact s7_343_safe
def s6_715 : State := ⟨[3,12,96,145], 156105556672081362157376023994227633858613534, 3, 0, 1, 0⟩
theorem s6_715_edges : next config 6 s6_715 = [s7_240, s7_321, s7_344] := by decide
theorem s6_715_safe : Safe 7 6 s6_715 := by
  apply safe_succ 6 6 s6_715 [s7_240, s7_321, s7_344] (by decide) s6_715_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_240_safe
  · subst z; exact s7_321_safe
  · subst z; exact s7_344_safe
def s6_716 : State := ⟨[3,12,104,145], 44602511244182370736228011050624637116420382, 3, 0, 1, 0⟩
theorem s6_716_edges : next config 6 s6_716 = [s7_927, s7_241, s7_682, s7_322] := by decide
theorem s6_716_safe : Safe 7 6 s6_716 := by
  apply safe_succ 6 6 s6_716 [s7_927, s7_241, s7_682, s7_322] (by decide) s6_716_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_927_safe
  · subst z; exact s7_241_safe
  · subst z; exact s7_682_safe
  · subst z; exact s7_322_safe
def s6_717 : State := ⟨[3,12,104,145], 66902575877979152000836802574058135085977886, 3, 0, 1, 0⟩
theorem s6_717_edges : next config 6 s6_717 = [s7_928, s7_245, s7_684, s7_325] := by decide
theorem s6_717_safe : Safe 7 6 s6_717 := by
  apply safe_succ 6 6 s6_717 [s7_928, s7_245, s7_684, s7_325] (by decide) s6_717_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_928_safe
  · subst z; exact s7_245_safe
  · subst z; exact s7_684_safe
  · subst z; exact s7_325_safe
def s6_718 : State := ⟨[3,12,104,146], 89204682205977458896226374345136223664804126, 3, 0, 1, 0⟩
theorem s6_718_edges : next config 6 s6_718 = [s7_249, s7_328, s7_343] := by decide
theorem s6_718_safe : Safe 7 6 s6_718 := by
  apply safe_succ 6 6 s6_718 [s7_249, s7_328, s7_343] (by decide) s6_718_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_249_safe
  · subst z; exact s7_328_safe
  · subst z; exact s7_343_safe
def s6_719 : State := ⟨[3,12,104,146], 111504066275040398283908239119354858097938718, 3, 0, 1, 0⟩
theorem s6_719_edges : next config 6 s6_719 = [s7_252, s7_329, s7_344] := by decide
theorem s6_719_safe : Safe 7 6 s6_719 := by
  apply safe_succ 6 6 s6_719 [s7_252, s7_329, s7_344] (by decide) s6_719_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_252_safe
  · subst z; exact s7_329_safe
  · subst z; exact s7_344_safe
def s6_720 : State := ⟨[3,12,104,162], 5846006551025023527781069414366386621401371054366, 3, 0, 1, 0⟩
theorem s6_720_edges : next config 6 s6_720 = [s7_254, s7_330] := by decide
theorem s6_720_safe : Safe 7 6 s6_720 := by
  apply safe_succ 6 6 s6_720 [s7_254, s7_330] (by decide) s6_720_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_254_safe
  · subst z; exact s7_330_safe
def s6_721 : State := ⟨[3,12,104,162], 7307508186994796978301000393229171211330230751518, 3, 0, 1, 0⟩
theorem s6_721_edges : next config 6 s6_721 = [s7_258, s7_331] := by decide
theorem s6_721_safe : Safe 7 6 s6_721 := by
  apply safe_succ 6 6 s6_721 [s7_258, s7_331] (by decide) s6_721_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_258_safe
  · subst z; exact s7_331_safe
def s6_722 : State := ⟨[3,12,104,163], 11692013101709764668279562599085017129752174072094, 3, 0, 1, 0⟩
theorem s6_722_edges : next config 6 s6_722 = [s7_264, s7_332] := by decide
theorem s6_722_safe : Safe 7 6 s6_722 := by
  apply safe_succ 6 6 s6_722 [s7_264, s7_332] (by decide) s6_722_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_264_safe
  · subst z; exact s7_332_safe
def s6_723 : State := ⟨[3,12,104,163], 13153514736318408651115739724094303289953960923422, 3, 0, 1, 0⟩
theorem s6_723_edges : next config 6 s6_723 = [s7_265, s7_333] := by decide
theorem s6_723_safe : Safe 7 6 s6_723 := by
  apply safe_succ 6 6 s6_723 [s7_265, s7_333] (by decide) s6_723_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_265_safe
  · subst z; exact s7_333_safe
def s6_724 : State := ⟨[3,12,104,176], 95780971326419139128314594914659690004932607210492190, 3, 0, 1, 0⟩
theorem s6_724_edges : next config 6 s6_724 = [s7_267, s7_334] := by decide
theorem s6_724_safe : Safe 7 6 s6_724 := by
  apply safe_succ 6 6 s6_724 [s7_267, s7_334] (by decide) s6_724_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_267_safe
  · subst z; exact s7_334_safe
def s6_725 : State := ⟨[3,12,104,176], 95782432805755724832702175457956688015303901637054750, 3, 0, 1, 0⟩
theorem s6_725_edges : next config 6 s6_725 = [s7_269, s7_335] := by decide
theorem s6_725_safe : Safe 7 6 s6_725 := by
  apply safe_succ 6 6 s6_725 [s7_269, s7_335] (by decide) s6_725_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_269_safe
  · subst z; exact s7_335_safe
def s6_726 : State := ⟨[3,12,241,145], 3533694129556768659166595001530439542899129882077862275623413092450373918, 3, 0, 1, 0⟩
theorem s6_726_edges : next config 6 s6_726 = [s7_272, s7_338] := by decide
theorem s6_726_safe : Safe 7 6 s6_726 := by
  apply safe_succ 6 6 s6_726 [s7_272, s7_338] (by decide) s6_726_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_272_safe
  · subst z; exact s7_338_safe
def s6_727 : State := ⟨[3,12,241,145], 3533694129556768659166595001552739607532926663342471067146846590419931422, 3, 0, 1, 0⟩
theorem s6_727_edges : next config 6 s6_727 = [s7_274, s7_339] := by decide
theorem s6_727_safe : Safe 7 6 s6_727 := by
  apply safe_succ 6 6 s6_727 [s7_274, s7_339] (by decide) s6_727_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_274_safe
  · subst z; exact s7_339_safe
def s6_728 : State := ⟨[3,21,67,145], 44601830679428167221535065940600822463398174, 3, 1, 1, 0⟩
theorem s6_728_edges : next config 6 s6_728 = [s7_582, s7_929, s7_686, s7_353, s7_361, s7_355, s7_357] := by decide
theorem s6_728_safe : Safe 7 6 s6_728 := by
  apply safe_succ 6 6 s6_728 [s7_582, s7_929, s7_686, s7_353, s7_361, s7_355, s7_357] (by decide) s6_728_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_582_safe
  · subst z; exact s7_929_safe
  · subst z; exact s7_686_safe
  · subst z; exact s7_353_safe
  · subst z; exact s7_361_safe
  · subst z; exact s7_355_safe
  · subst z; exact s7_357_safe
def s6_729 : State := ⟨[3,21,96,145], 44601830679428246449697432630985826330935582, 3, 1, 1, 0⟩
theorem s6_729_edges : next config 6 s6_729 = [s7_583, s7_930, s7_687, s7_354, s7_364, s7_356, s7_358, s7_351, s7_352, s7_349] := by decide
theorem s6_729_safe : Safe 7 6 s6_729 := by
  apply safe_succ 6 6 s6_729 [s7_583, s7_930, s7_687, s7_354, s7_364, s7_356, s7_358, s7_351, s7_352, s7_349] (by decide) s6_729_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s7_583_safe
  · subst z; exact s7_930_safe
  · subst z; exact s7_687_safe
  · subst z; exact s7_354_safe
  · subst z; exact s7_364_safe
  · subst z; exact s7_356_safe
  · subst z; exact s7_358_safe
  · subst z; exact s7_351_safe
  · subst z; exact s7_352_safe
  · subst z; exact s7_349_safe
def s6_730 : State := ⟨[3,22,64,145], 44601830679428167221534918366648232791179550, 3, 1, 1, 0⟩
theorem s6_730_edges : next config 6 s6_730 = [s7_359, s7_353, s7_354] := by decide
theorem s6_730_safe : Safe 7 6 s6_730 := by
  apply safe_succ 6 6 s6_730 [s7_359, s7_353, s7_354] (by decide) s6_730_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_359_safe
  · subst z; exact s7_353_safe
  · subst z; exact s7_354_safe
def s6_731 : State := ⟨[3,29,64,145], 44601830679428167221534918366648233323856158, 3, 1, 1, 0⟩
theorem s6_731_edges : next config 6 s6_731 = [s7_689, s7_355, s7_356] := by decide
theorem s6_731_safe : Safe 7 6 s6_731 := by
  apply safe_succ 6 6 s6_731 [s7_689, s7_355, s7_356] (by decide) s6_731_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_689_safe
  · subst z; exact s7_355_safe
  · subst z; exact s7_356_safe
def s6_732 : State := ⟨[3,53,64,145], 44601830679428167221534918375655432041726238, 3, 1, 1, 0⟩
theorem s6_732_edges : next config 6 s6_732 = [s7_750, s7_360, s7_357, s7_358] := by decide
theorem s6_732_safe : Safe 7 6 s6_732 := by
  apply safe_succ 6 6 s6_732 [s7_750, s7_360, s7_357, s7_358] (by decide) s6_732_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_750_safe
  · subst z; exact s7_360_safe
  · subst z; exact s7_357_safe
  · subst z; exact s7_358_safe
def s6_733 : State := ⟨[3,100,96,145], 44601830679429514100297660860387323032043806, 3, 1, 1, 0⟩
theorem s6_733_edges : next config 6 s6_733 = [s7_319, s7_362] := by decide
theorem s6_733_safe : Safe 7 6 s6_733 := by
  apply safe_succ 6 6 s6_733 [s7_319, s7_362] (by decide) s6_733_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_319_safe
  · subst z; exact s7_362_safe
def s6_734 : State := ⟨[3,100,104,145], 44602511244183638386828239280026133819621662, 3, 0, 1, 0⟩
theorem s6_734_edges : next config 6 s6_734 = [s7_303] := by decide
theorem s6_734_safe : Safe 7 6 s6_734 := by
  apply safe_succ 6 6 s6_734 [s7_303] (by decide) s6_734_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_303_safe
def s6_735 : State := ⟨[3,100,104,145], 66902575877980419651437030803459631789179166, 3, 0, 1, 0⟩
theorem s6_735_edges : next config 6 s6_735 = [s7_305] := by decide
theorem s6_735_safe : Safe 7 6 s6_735 := by
  apply safe_succ 6 6 s6_735 [s7_305] (by decide) s6_735_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_305_safe
def s6_736 : State := ⟨[3,108,104,145], 44602511244506889289886437777407793136992542, 3, 0, 1, 0⟩
theorem s6_736_edges : next config 6 s6_736 = [s7_307, s7_324] := by decide
theorem s6_736_safe : Safe 7 6 s6_736 := by
  apply safe_succ 6 6 s6_736 [s7_307, s7_324] (by decide) s6_736_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_307_safe
  · subst z; exact s7_324_safe
def s6_737 : State := ⟨[3,108,104,145], 66902575878303670554495229300841291106550046, 3, 0, 1, 0⟩
theorem s6_737_edges : next config 6 s6_737 = [s7_309, s7_327] := by decide
theorem s6_737_safe : Safe 7 6 s6_737 := by
  apply safe_succ 6 6 s6_737 [s7_309, s7_327] (by decide) s6_737_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_309_safe
  · subst z; exact s7_327_safe
def s6_738 : State := ⟨[9,4,64,145], 44601830679428167221534918366648232786985750, 3, 3, 1, 0⟩
theorem s6_738_edges : next config 6 s6_738 = [s7_365] := by decide
theorem s6_738_safe : Safe 7 6 s6_738 := by
  apply safe_succ 6 6 s6_738 [s7_365] (by decide) s6_738_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_365_safe
def s6_739 : State := ⟨[9,4,104,145], 44601830679448528859301084301409773580124950, 1, 1, 1, 0⟩
theorem s6_739_edges : next config 6 s6_739 = [] := by decide
theorem s6_739_safe : Safe 7 6 s6_739 := by
  apply safe_succ 6 6 s6_739 [] (by decide) s6_739_edges
  simp
def s6_740 : State := ⟨[9,4,104,171], 2999001359804714200008927606817314010876751219065622, 1, 0, 1, 0⟩
theorem s6_740_edges : next config 6 s6_740 = [s7_146] := by decide
theorem s6_740_safe : Safe 7 6 s6_740 := by
  apply safe_succ 6 6 s6_740 [s7_146] (by decide) s6_740_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_146_safe
def s6_741 : State := ⟨[9,4,104,171], 3000462861440683973459447537796176795466680078762774, 1, 0, 1, 0⟩
theorem s6_741_edges : next config 6 s6_741 = [s7_147] := by decide
theorem s6_741_safe : Safe 7 6 s6_741 := by
  apply safe_succ 6 6 s6_741 [s7_147] (by decide) s6_741_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_147_safe
def s6_742 : State := ⟨[9,21,96,145], 44601830679428246449697432630985826330936086, 3, 1, 1, 0⟩
theorem s6_742_edges : next config 6 s6_742 = [s7_366] := by decide
theorem s6_742_safe : Safe 7 6 s6_742 := by
  apply safe_succ 6 6 s6_742 [s7_366] (by decide) s6_742_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_366_safe
def s6_743 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232784892190, 3, 3, 1, 0⟩
theorem s6_743_edges : next config 6 s6_743 = [s7_539, s7_732, s7_450, s7_379] := by decide
theorem s6_743_safe : Safe 7 6 s6_743 := by
  apply safe_succ 6 6 s6_743 [s7_539, s7_732, s7_450, s7_379] (by decide) s6_743_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_539_safe
  · subst z; exact s7_732_safe
  · subst z; exact s7_450_safe
  · subst z; exact s7_379_safe
def s6_744 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232786985246, 3, 3, 1, 0⟩
theorem s6_744_edges : next config 6 s6_744 = [s7_584, s7_733, s7_422, s7_380] := by decide
theorem s6_744_safe : Safe 7 6 s6_744 := by
  apply safe_succ 6 6 s6_744 [s7_584, s7_733, s7_422, s7_380] (by decide) s6_744_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_584_safe
  · subst z; exact s7_733_safe
  · subst z; exact s7_422_safe
  · subst z; exact s7_380_safe
def s6_745 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232786985750, 3, 3, 1, 0⟩
theorem s6_745_edges : next config 6 s6_745 = [s7_381] := by decide
theorem s6_745_safe : Safe 7 6 s6_745 := by
  apply safe_succ 6 6 s6_745 [s7_381] (by decide) s6_745_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_381_safe
def s6_746 : State := ⟨[17,4,64,145], 44601830679428167221534918366648241374826774, 3, 3, 1, 0⟩
theorem s6_746_edges : next config 6 s6_746 = [s7_540, s7_451, s7_382] := by decide
theorem s6_746_safe : Safe 7 6 s6_746 := by
  apply safe_succ 6 6 s6_746 [s7_540, s7_451, s7_382] (by decide) s6_746_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_540_safe
  · subst z; exact s7_451_safe
  · subst z; exact s7_382_safe
def s6_747 : State := ⟨[17,4,64,145], 44601830679428167221534918366648241376919830, 3, 3, 1, 0⟩
theorem s6_747_edges : next config 6 s6_747 = [s7_423, s7_383] := by decide
theorem s6_747_safe : Safe 7 6 s6_747 := by
  apply safe_succ 6 6 s6_747 [s7_423, s7_383] (by decide) s6_747_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_423_safe
  · subst z; exact s7_383_safe
def s6_748 : State := ⟨[17,4,64,145], 44601830679428167221534955260136380203995414, 3, 3, 1, 0⟩
theorem s6_748_edges : next config 6 s6_748 = [s7_541, s7_452, s7_384] := by decide
theorem s6_748_safe : Safe 7 6 s6_748 := by
  apply safe_succ 6 6 s6_748 [s7_541, s7_452, s7_384] (by decide) s6_748_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_541_safe
  · subst z; exact s7_452_safe
  · subst z; exact s7_384_safe
def s6_749 : State := ⟨[17,4,64,145], 44601830679428167221534955260136380206088470, 3, 3, 1, 0⟩
theorem s6_749_edges : next config 6 s6_749 = [s7_585, s7_424, s7_385] := by decide
theorem s6_749_safe : Safe 7 6 s6_749 := by
  apply safe_succ 6 6 s6_749 [s7_585, s7_424, s7_385] (by decide) s6_749_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_585_safe
  · subst z; exact s7_424_safe
  · subst z; exact s7_385_safe
def s6_750 : State := ⟨[17,4,67,128], 340282366920938463629395304099449344286, 3, 3, 0, 0⟩
theorem s6_750_edges : next config 6 s6_750 = [s7_453, s7_369] := by decide
theorem s6_750_safe : Safe 7 6 s6_750 := by
  apply safe_succ 6 6 s6_750 [s7_453, s7_369] (by decide) s6_750_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_453_safe
  · subst z; exact s7_369_safe
def s6_751 : State := ⟨[17,4,67,128], 340282366920938463629395304099451437342, 3, 3, 0, 0⟩
theorem s6_751_edges : next config 6 s6_751 = [s7_425, s7_370] := by decide
theorem s6_751_safe : Safe 7 6 s6_751 := by
  apply safe_succ 6 6 s6_751 [s7_425, s7_370] (by decide) s6_751_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_425_safe
  · subst z; exact s7_370_safe
def s6_752 : State := ⟨[17,4,67,128], 340282366920943299406460738910986375446, 3, 2, 0, 0⟩
theorem s6_752_edges : next config 6 s6_752 = [s7_454, s7_371] := by decide
theorem s6_752_safe : Safe 7 6 s6_752 := by
  apply safe_succ 6 6 s6_752 [s7_454, s7_371] (by decide) s6_752_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_454_safe
  · subst z; exact s7_371_safe
def s6_753 : State := ⟨[17,4,67,128], 340282366920943299406460738910988468502, 3, 2, 0, 0⟩
theorem s6_753_edges : next config 6 s6_753 = [s7_426, s7_372] := by decide
theorem s6_753_safe : Safe 7 6 s6_753 := by
  apply safe_succ 6 6 s6_753 [s7_426, s7_372] (by decide) s6_753_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_426_safe
  · subst z; exact s7_372_safe
def s6_754 : State := ⟨[17,4,67,128], 340282366920944508258493377245322875158, 3, 2, 0, 0⟩
theorem s6_754_edges : next config 6 s6_754 = [s7_455, s7_373] := by decide
theorem s6_754_safe : Safe 7 6 s6_754 := by
  apply safe_succ 6 6 s6_754 [s7_455, s7_373] (by decide) s6_754_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_455_safe
  · subst z; exact s7_373_safe
def s6_755 : State := ⟨[17,4,67,128], 340282366920944508258493377245324968214, 3, 2, 0, 0⟩
theorem s6_755_edges : next config 6 s6_755 = [s7_427, s7_374] := by decide
theorem s6_755_safe : Safe 7 6 s6_755 := by
  apply safe_succ 6 6 s6_755 [s7_427, s7_374] (by decide) s6_755_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_427_safe
  · subst z; exact s7_374_safe
def s6_756 : State := ⟨[17,4,67,128], 340282366921020670658916075178167566614, 3, 2, 0, 0⟩
theorem s6_756_edges : next config 6 s6_756 = [s7_456, s7_375] := by decide
theorem s6_756_safe : Safe 7 6 s6_756 := by
  apply safe_succ 6 6 s6_756 [s7_456, s7_375] (by decide) s6_756_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_456_safe
  · subst z; exact s7_375_safe
def s6_757 : State := ⟨[17,4,67,128], 340282366921021879510948713512504066326, 3, 2, 0, 0⟩
theorem s6_757_edges : next config 6 s6_757 = [s7_457, s7_376] := by decide
theorem s6_757_safe : Safe 7 6 s6_757 := by
  apply safe_succ 6 6 s6_757 [s7_457, s7_376] (by decide) s6_757_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_457_safe
  · subst z; exact s7_376_safe
def s6_758 : State := ⟨[17,4,67,145], 44601830679428167221535102834088969880408342, 3, 2, 1, 0⟩
theorem s6_758_edges : next config 6 s6_758 = [s7_542, s7_787, s7_2, s7_458] := by decide
theorem s6_758_safe : Safe 7 6 s6_758 := by
  apply safe_succ 6 6 s6_758 [s7_542, s7_787, s7_2, s7_458] (by decide) s6_758_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_542_safe
  · subst z; exact s7_787_safe
  · subst z; exact s7_2_safe
  · subst z; exact s7_458_safe
def s6_759 : State := ⟨[17,4,67,145], 44601830679428167221535102834088969882501398, 3, 2, 1, 0⟩
theorem s6_759_edges : next config 6 s6_759 = [s7_788, s7_586, s7_3, s7_428] := by decide
theorem s6_759_safe : Safe 7 6 s6_759 := by
  apply safe_succ 6 6 s6_759 [s7_788, s7_586, s7_3, s7_428] (by decide) s6_759_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_788_safe
  · subst z; exact s7_586_safe
  · subst z; exact s7_3_safe
  · subst z; exact s7_428_safe
def s6_760 : State := ⟨[17,4,67,145], 44601830679428167221535139727577117299511574, 3, 2, 1, 0⟩
theorem s6_760_edges : next config 6 s6_760 = [s7_543, s7_789, s7_4, s7_459] := by decide
theorem s6_760_safe : Safe 7 6 s6_760 := by
  apply safe_succ 6 6 s6_760 [s7_543, s7_789, s7_4, s7_459] (by decide) s6_760_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_543_safe
  · subst z; exact s7_789_safe
  · subst z; exact s7_4_safe
  · subst z; exact s7_459_safe
def s6_761 : State := ⟨[17,4,67,145], 44601830679428167221535139727577117301604630, 3, 2, 1, 0⟩
theorem s6_761_edges : next config 6 s6_761 = [s7_790, s7_587, s7_5, s7_429] := by decide
theorem s6_761_safe : Safe 7 6 s6_761 := by
  apply safe_succ 6 6 s6_761 [s7_790, s7_587, s7_5, s7_429] (by decide) s6_761_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_790_safe
  · subst z; exact s7_587_safe
  · subst z; exact s7_5_safe
  · subst z; exact s7_429_safe
def s6_762 : State := ⟨[17,4,82,145], 44601830679428167226370695432083044321923350, 3, 2, 1, 0⟩
theorem s6_762_edges : next config 6 s6_762 = [s7_547, s7_22, s7_462, s7_371] := by decide
theorem s6_762_safe : Safe 7 6 s6_762 := by
  apply safe_succ 6 6 s6_762 [s7_547, s7_22, s7_462, s7_371] (by decide) s6_762_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_547_safe
  · subst z; exact s7_22_safe
  · subst z; exact s7_462_safe
  · subst z; exact s7_371_safe
def s6_763 : State := ⟨[17,4,82,145], 44601830679428167226370695432083044324016406, 3, 2, 1, 0⟩
theorem s6_763_edges : next config 6 s6_763 = [s7_23, s7_520, s7_430, s7_372, s7_377] := by decide
theorem s6_763_safe : Safe 7 6 s6_763 := by
  apply safe_succ 6 6 s6_763 [s7_23, s7_520, s7_430, s7_372, s7_377] (by decide) s6_763_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_23_safe
  · subst z; exact s7_520_safe
  · subst z; exact s7_430_safe
  · subst z; exact s7_372_safe
  · subst z; exact s7_377_safe
def s6_764 : State := ⟨[17,4,82,145], 44601830679428167227579547464721378658423062, 3, 2, 1, 0⟩
theorem s6_764_edges : next config 6 s6_764 = [s7_548, s7_24, s7_463, s7_373] := by decide
theorem s6_764_safe : Safe 7 6 s6_764 := by
  apply safe_succ 6 6 s6_764 [s7_548, s7_24, s7_463, s7_373] (by decide) s6_764_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_548_safe
  · subst z; exact s7_24_safe
  · subst z; exact s7_463_safe
  · subst z; exact s7_373_safe
def s6_765 : State := ⟨[17,4,82,145], 44601830679428167227579547464721378660516118, 3, 2, 1, 0⟩
theorem s6_765_edges : next config 6 s6_765 = [s7_25, s7_521, s7_431, s7_374, s7_378] := by decide
theorem s6_765_safe : Safe 7 6 s6_765 := by
  apply safe_succ 6 6 s6_765 [s7_25, s7_521, s7_431, s7_374, s7_378] (by decide) s6_765_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_25_safe
  · subst z; exact s7_521_safe
  · subst z; exact s7_431_safe
  · subst z; exact s7_374_safe
  · subst z; exact s7_378_safe
def s6_766 : State := ⟨[17,4,82,145], 44601830679428167303741947887419311503114518, 3, 2, 1, 0⟩
theorem s6_766_edges : next config 6 s6_766 = [s7_549, s7_26, s7_464, s7_375] := by decide
theorem s6_766_safe : Safe 7 6 s6_766 := by
  apply safe_succ 6 6 s6_766 [s7_549, s7_26, s7_464, s7_375] (by decide) s6_766_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_549_safe
  · subst z; exact s7_26_safe
  · subst z; exact s7_464_safe
  · subst z; exact s7_375_safe
def s6_767 : State := ⟨[17,4,82,145], 44601830679428167304950799920057645839614230, 3, 2, 1, 0⟩
theorem s6_767_edges : next config 6 s6_767 = [s7_550, s7_27, s7_465, s7_376] := by decide
theorem s6_767_safe : Safe 7 6 s6_767 := by
  apply safe_succ 6 6 s6_767 [s7_550, s7_27, s7_465, s7_376] (by decide) s6_767_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_550_safe
  · subst z; exact s7_27_safe
  · subst z; exact s7_465_safe
  · subst z; exact s7_376_safe
def s6_768 : State := ⟨[17,4,86,128], 340282366921020670511342122588493250838, 3, 2, 0, 0⟩
theorem s6_768_edges : next config 6 s6_768 = [s7_377] := by decide
theorem s6_768_safe : Safe 7 6 s6_768 := by
  apply safe_succ 6 6 s6_768 [s7_377] (by decide) s6_768_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_377_safe
def s6_769 : State := ⟨[17,4,86,128], 340282366921021879363374760922829750550, 3, 2, 0, 0⟩
theorem s6_769_edges : next config 6 s6_769 = [s7_378] := by decide
theorem s6_769_safe : Safe 7 6 s6_769 := by
  apply safe_succ 6 6 s6_769 [s7_378] (by decide) s6_769_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_378_safe
def s6_770 : State := ⟨[17,4,96,128], 340282367000166625996085689103316881694, 3, 3, 0, 0⟩
theorem s6_770_edges : next config 6 s6_770 = [s7_466, s7_408, s7_392, s7_379] := by decide
theorem s6_770_safe : Safe 7 6 s6_770 := by
  apply safe_succ 6 6 s6_770 [s7_466, s7_408, s7_392, s7_379] (by decide) s6_770_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_466_safe
  · subst z; exact s7_408_safe
  · subst z; exact s7_392_safe
  · subst z; exact s7_379_safe
def s6_771 : State := ⟨[17,4,96,128], 340282367000166625996085689103318974750, 3, 3, 0, 0⟩
theorem s6_771_edges : next config 6 s6_771 = [s7_522, s7_432, s7_409, s7_390, s7_393, s7_380] := by decide
theorem s6_771_safe : Safe 7 6 s6_771 := by
  apply safe_succ 6 6 s6_771 [s7_522, s7_432, s7_409, s7_390, s7_393, s7_380] (by decide) s6_771_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s7_522_safe
  · subst z; exact s7_432_safe
  · subst z; exact s7_409_safe
  · subst z; exact s7_390_safe
  · subst z; exact s7_393_safe
  · subst z; exact s7_380_safe
def s6_772 : State := ⟨[17,4,96,128], 340282367000166625996085689103318975254, 3, 3, 0, 0⟩
theorem s6_772_edges : next config 6 s6_772 = [s7_394, s7_381] := by decide
theorem s6_772_safe : Safe 7 6 s6_772 := by
  apply safe_succ 6 6 s6_772 [s7_394, s7_381] (by decide) s6_772_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_394_safe
  · subst z; exact s7_381_safe
def s6_773 : State := ⟨[17,4,96,128], 340282367000166625996085689111906816278, 3, 3, 0, 0⟩
theorem s6_773_edges : next config 6 s6_773 = [s7_467, s7_395, s7_382] := by decide
theorem s6_773_safe : Safe 7 6 s6_773 := by
  apply safe_succ 6 6 s6_773 [s7_467, s7_395, s7_382] (by decide) s6_773_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_467_safe
  · subst z; exact s7_395_safe
  · subst z; exact s7_382_safe
def s6_774 : State := ⟨[17,4,96,128], 340282367000166625996085689111908909334, 3, 3, 0, 0⟩
theorem s6_774_edges : next config 6 s6_774 = [s7_433, s7_396, s7_383] := by decide
theorem s6_774_safe : Safe 7 6 s6_774 := by
  apply safe_succ 6 6 s6_774 [s7_433, s7_396, s7_383] (by decide) s6_774_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_433_safe
  · subst z; exact s7_396_safe
  · subst z; exact s7_383_safe
def s6_775 : State := ⟨[17,4,96,128], 340282367000166626032979177250735984918, 3, 3, 0, 0⟩
theorem s6_775_edges : next config 6 s6_775 = [s7_468, s7_410, s7_397, s7_384] := by decide
theorem s6_775_safe : Safe 7 6 s6_775 := by
  apply safe_succ 6 6 s6_775 [s7_468, s7_410, s7_397, s7_384] (by decide) s6_775_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_468_safe
  · subst z; exact s7_410_safe
  · subst z; exact s7_397_safe
  · subst z; exact s7_384_safe
def s6_776 : State := ⟨[17,4,96,128], 340282367000166626032979177250738077974, 3, 3, 0, 0⟩
theorem s6_776_edges : next config 6 s6_776 = [s7_523, s7_434, s7_411, s7_391, s7_398, s7_385] := by decide
theorem s6_776_safe : Safe 7 6 s6_776 := by
  apply safe_succ 6 6 s6_776 [s7_523, s7_434, s7_411, s7_391, s7_398, s7_385] (by decide) s6_776_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s7_523_safe
  · subst z; exact s7_434_safe
  · subst z; exact s7_411_safe
  · subst z; exact s7_391_safe
  · subst z; exact s7_398_safe
  · subst z; exact s7_385_safe
def s6_777 : State := ⟨[17,4,96,128], 340282367158622951024614364290404782358, 3, 3, 0, 0⟩
theorem s6_777_edges : next config 6 s6_777 = [s7_469, s7_399, s7_386] := by decide
theorem s6_777_safe : Safe 7 6 s6_777 := by
  apply safe_succ 6 6 s6_777 [s7_469, s7_399, s7_386] (by decide) s6_777_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_469_safe
  · subst z; exact s7_399_safe
  · subst z; exact s7_386_safe
def s6_778 : State := ⟨[17,4,96,128], 340282367158622951024614364290406875414, 3, 3, 0, 0⟩
theorem s6_778_edges : next config 6 s6_778 = [s7_435, s7_400, s7_387] := by decide
theorem s6_778_safe : Safe 7 6 s6_778 := by
  apply safe_succ 6 6 s6_778 [s7_435, s7_400, s7_387] (by decide) s6_778_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_435_safe
  · subst z; exact s7_400_safe
  · subst z; exact s7_387_safe
def s6_779 : State := ⟨[17,4,96,128], 340282368267817226224315090600020082974, 3, 3, 0, 0⟩
theorem s6_779_edges : next config 6 s6_779 = [s7_470, s7_401, s7_388] := by decide
theorem s6_779_safe : Safe 7 6 s6_779 := by
  apply safe_succ 6 6 s6_779 [s7_470, s7_401, s7_388] (by decide) s6_779_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_470_safe
  · subst z; exact s7_401_safe
  · subst z; exact s7_388_safe
def s6_780 : State := ⟨[17,4,96,128], 340282368267817226261208578747439186198, 3, 3, 0, 0⟩
theorem s6_780_edges : next config 6 s6_780 = [s7_471, s7_402, s7_389] := by decide
theorem s6_780_safe : Safe 7 6 s6_780 := by
  apply safe_succ 6 6 s6_780 [s7_471, s7_402, s7_389] (by decide) s6_780_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_471_safe
  · subst z; exact s7_402_safe
  · subst z; exact s7_389_safe
def s6_781 : State := ⟨[17,4,97,145], 44601830679428404906022461159661013416743190, 3, 2, 1, 0⟩
theorem s6_781_edges : next config 6 s6_781 = [s7_551, s7_62, s7_472] := by decide
theorem s6_781_safe : Safe 7 6 s6_781 := by
  apply safe_succ 6 6 s6_781 [s7_551, s7_62, s7_472] (by decide) s6_781_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_551_safe
  · subst z; exact s7_62_safe
  · subst z; exact s7_472_safe
def s6_782 : State := ⟨[17,4,97,145], 44601830679428404906022461159661013418836246, 3, 2, 1, 0⟩
theorem s6_782_edges : next config 6 s6_782 = [s7_63, s7_436] := by decide
theorem s6_782_safe : Safe 7 6 s6_782 := by
  apply safe_succ 6 6 s6_782 [s7_63, s7_436] (by decide) s6_782_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_63_safe
  · subst z; exact s7_436_safe
def s6_783 : State := ⟨[17,4,100,145], 44601830679429514100297660860387323032043806, 1, 1, 1, 0⟩
theorem s6_783_edges : next config 6 s6_783 = [s7_552, s7_473] := by decide
theorem s6_783_safe : Safe 7 6 s6_783 := by
  apply safe_succ 6 6 s6_783 [s7_552, s7_473] (by decide) s6_783_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_552_safe
  · subst z; exact s7_473_safe
def s6_784 : State := ⟨[17,4,100,145], 44601830679429514100297660860387323034140950, 3, 2, 1, 0⟩
theorem s6_784_edges : next config 6 s6_784 = [s7_64] := by decide
theorem s6_784_safe : Safe 7 6 s6_784 := by
  apply safe_succ 6 6 s6_784 [s7_64] (by decide) s6_784_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_64_safe
def s6_785 : State := ⟨[17,4,100,145], 44601830679429514100297697753875470451147030, 1, 1, 1, 0⟩
theorem s6_785_edges : next config 6 s6_785 = [s7_553, s7_474] := by decide
theorem s6_785_safe : Safe 7 6 s6_785 := by
  apply safe_succ 6 6 s6_785 [s7_553, s7_474] (by decide) s6_785_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_553_safe
  · subst z; exact s7_474_safe
def s6_786 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773580124446, 1, 1, 1, 0⟩
theorem s6_786_edges : next config 6 s6_786 = [s7_554, s7_912, s7_588, s7_734, s7_475, s7_527, s7_437, s7_415, s7_405, s7_419] := by decide
theorem s6_786_safe : Safe 7 6 s6_786 := by
  apply safe_succ 6 6 s6_786 [s7_554, s7_912, s7_588, s7_734, s7_475, s7_527, s7_437, s7_415, s7_405, s7_419] (by decide) s6_786_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s7_554_safe
  · subst z; exact s7_912_safe
  · subst z; exact s7_588_safe
  · subst z; exact s7_734_safe
  · subst z; exact s7_475_safe
  · subst z; exact s7_527_safe
  · subst z; exact s7_437_safe
  · subst z; exact s7_415_safe
  · subst z; exact s7_405_safe
  · subst z; exact s7_419_safe
def s6_787 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773580124950, 1, 1, 1, 0⟩
theorem s6_787_edges : next config 6 s6_787 = [s7_555, s7_476] := by decide
theorem s6_787_safe : Safe 7 6 s6_787 := by
  apply safe_succ 6 6 s6_787 [s7_555, s7_476] (by decide) s6_787_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_555_safe
  · subst z; exact s7_476_safe
def s6_788 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773580128534, 3, 2, 1, 0⟩
theorem s6_788_edges : next config 6 s6_788 = [s7_556, s7_119, s7_735, s7_477] := by decide
theorem s6_788_safe : Safe 7 6 s6_788 := by
  apply safe_succ 6 6 s6_788 [s7_556, s7_119, s7_735, s7_477] (by decide) s6_788_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_556_safe
  · subst z; exact s7_119_safe
  · subst z; exact s7_735_safe
  · subst z; exact s7_477_safe
def s6_789 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773582221590, 3, 2, 1, 0⟩
theorem s6_789_edges : next config 6 s6_789 = [s7_913, s7_589, s7_120, s7_736, s7_528, s7_438, s7_416, s7_406, s7_420, s7_414] := by decide
theorem s6_789_safe : Safe 7 6 s6_789 := by
  apply safe_succ 6 6 s6_789 [s7_913, s7_589, s7_120, s7_736, s7_528, s7_438, s7_416, s7_406, s7_420, s7_414] (by decide) s6_789_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s7_913_safe
  · subst z; exact s7_589_safe
  · subst z; exact s7_120_safe
  · subst z; exact s7_736_safe
  · subst z; exact s7_528_safe
  · subst z; exact s7_438_safe
  · subst z; exact s7_416_safe
  · subst z; exact s7_406_safe
  · subst z; exact s7_420_safe
  · subst z; exact s7_414_safe
def s6_790 : State := ⟨[17,4,104,145], 44601830679448528859301084301409782170059030, 1, 1, 1, 0⟩
theorem s6_790_edges : next config 6 s6_790 = [s7_557, s7_478, s7_439] := by decide
theorem s6_790_safe : Safe 7 6 s6_790 := by
  apply safe_succ 6 6 s6_790 [s7_557, s7_478, s7_439] (by decide) s6_790_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_557_safe
  · subst z; exact s7_478_safe
  · subst z; exact s7_439_safe
def s6_791 : State := ⟨[17,4,104,145], 44601830679448528859301121194897920999227670, 1, 1, 1, 0⟩
theorem s6_791_edges : next config 6 s6_791 = [s7_558, s7_914, s7_590, s7_479, s7_529, s7_440, s7_417, s7_407, s7_421] := by decide
theorem s6_791_safe : Safe 7 6 s6_791 := by
  apply safe_succ 6 6 s6_791 [s7_558, s7_914, s7_590, s7_479, s7_529, s7_440, s7_417, s7_407, s7_421] (by decide) s6_791_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s7_558_safe
  · subst z; exact s7_914_safe
  · subst z; exact s7_590_safe
  · subst z; exact s7_479_safe
  · subst z; exact s7_529_safe
  · subst z; exact s7_440_safe
  · subst z; exact s7_417_safe
  · subst z; exact s7_407_safe
  · subst z; exact s7_421_safe
def s6_792 : State := ⟨[17,4,104,145], 44601830679448528859301379449314952932950294, 3, 2, 1, 0⟩
theorem s6_792_edges : next config 6 s6_792 = [s7_559, s7_121, s7_480] := by decide
theorem s6_792_safe : Safe 7 6 s6_792 := by
  apply safe_succ 6 6 s6_792 [s7_559, s7_121, s7_480] (by decide) s6_792_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_559_safe
  · subst z; exact s7_121_safe
  · subst z; exact s7_480_safe
def s6_793 : State := ⟨[17,4,104,145], 44601830679448687315626112830084960668025110, 1, 1, 1, 0⟩
theorem s6_793_edges : next config 6 s6_793 = [s7_560, s7_481, s7_441] := by decide
theorem s6_793_safe : Safe 7 6 s6_793 := by
  apply safe_succ 6 6 s6_793 [s7_560, s7_481, s7_441] (by decide) s6_793_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_560_safe
  · subst z; exact s7_481_safe
  · subst z; exact s7_441_safe
def s6_794 : State := ⟨[17,4,104,145], 44601830679449796509901312530811270283329814, 3, 2, 1, 0⟩
theorem s6_794_edges : next config 6 s6_794 = [s7_561, s7_122, s7_482] := by decide
theorem s6_794_safe : Safe 7 6 s6_794 := by
  apply safe_succ 6 6 s6_794 [s7_561, s7_122, s7_482] (by decide) s6_794_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_561_safe
  · subst z; exact s7_122_safe
  · subst z; exact s7_482_safe
def s6_795 : State := ⟨[17,4,104,145], 44601830679773047412959511028192929600700694, 3, 2, 1, 0⟩
theorem s6_795_edges : next config 6 s6_795 = [s7_562, s7_123, s7_483] := by decide
theorem s6_795_safe : Safe 7 6 s6_795 := by
  apply safe_succ 6 6 s6_795 [s7_562, s7_123, s7_483] (by decide) s6_795_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_562_safe
  · subst z; exact s7_123_safe
  · subst z; exact s7_483_safe
def s6_796 : State := ⟨[17,4,108,128], 340282711801129888074482896206588739870, 1, 1, 0, 0⟩
theorem s6_796_edges : next config 6 s6_796 = [s7_484, s7_405] := by decide
theorem s6_796_safe : Safe 7 6 s6_796 := by
  apply safe_succ 6 6 s6_796 [s7_484, s7_405] (by decide) s6_796_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_484_safe
  · subst z; exact s7_405_safe
def s6_797 : State := ⟨[17,4,108,128], 340282711801129888074482896206590837014, 3, 2, 0, 0⟩
theorem s6_797_edges : next config 6 s6_797 = [s7_406] := by decide
theorem s6_797_safe : Safe 7 6 s6_797 := by
  apply safe_succ 6 6 s6_797 [s7_406] (by decide) s6_797_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_406_safe
def s6_798 : State := ⟨[17,4,108,128], 340282711801129888111376384354007843094, 1, 1, 0, 0⟩
theorem s6_798_edges : next config 6 s6_798 = [s7_485, s7_407] := by decide
theorem s6_798_safe : Safe 7 6 s6_798 := by
  apply safe_succ 6 6 s6_798 [s7_485, s7_407] (by decide) s6_798_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_485_safe
  · subst z; exact s7_407_safe
def s6_799 : State := ⟨[17,4,112,145], 44601830684620543308232260259516322658062614, 3, 2, 1, 0⟩
theorem s6_799_edges : next config 6 s6_799 = [s7_563, s7_218, s7_486] := by decide
theorem s6_799_safe : Safe 7 6 s6_799 := by
  apply safe_succ 6 6 s6_799 [s7_563, s7_218, s7_486] (by decide) s6_799_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_563_safe
  · subst z; exact s7_218_safe
  · subst z; exact s7_486_safe
def s6_800 : State := ⟨[17,4,112,145], 44601830684620543308232260259516322660155670, 3, 2, 1, 0⟩
theorem s6_800_edges : next config 6 s6_800 = [s7_219, s7_442] := by decide
theorem s6_800_safe : Safe 7 6 s6_800 := by
  apply safe_succ 6 6 s6_800 [s7_219, s7_442] (by decide) s6_800_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_219_safe
  · subst z; exact s7_442_safe
def s6_801 : State := ⟨[17,4,113,145], 44601830689812840166767087888046818987278622, 1, 1, 1, 0⟩
theorem s6_801_edges : next config 6 s6_801 = [s7_564, s7_487, s7_443] := by decide
theorem s6_801_safe : Safe 7 6 s6_801 := by
  apply safe_succ 6 6 s6_801 [s7_564, s7_487, s7_443] (by decide) s6_801_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_564_safe
  · subst z; exact s7_487_safe
  · subst z; exact s7_443_safe
def s6_802 : State := ⟨[17,4,113,145], 44601830689812840166767087888046818987282710, 3, 2, 1, 0⟩
theorem s6_802_edges : next config 6 s6_802 = [s7_565, s7_220, s7_488] := by decide
theorem s6_802_safe : Safe 7 6 s6_802 := by
  apply safe_succ 6 6 s6_802 [s7_565, s7_220, s7_488] (by decide) s6_802_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_565_safe
  · subst z; exact s7_220_safe
  · subst z; exact s7_488_safe
def s6_803 : State := ⟨[17,4,113,145], 44601830689812840166767087888046818989375766, 3, 2, 1, 0⟩
theorem s6_803_edges : next config 6 s6_803 = [s7_221, s7_444] := by decide
theorem s6_803_safe : Safe 7 6 s6_803 := by
  apply safe_succ 6 6 s6_803 [s7_221, s7_444] (by decide) s6_803_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_221_safe
  · subst z; exact s7_444_safe
def s6_804 : State := ⟨[17,4,113,145], 44601830689812840166767124781534966406381846, 1, 1, 1, 0⟩
theorem s6_804_edges : next config 6 s6_804 = [s7_566, s7_489, s7_445] := by decide
theorem s6_804_safe : Safe 7 6 s6_804 := by
  apply safe_succ 6 6 s6_804 [s7_566, s7_489, s7_445] (by decide) s6_804_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_566_safe
  · subst z; exact s7_489_safe
  · subst z; exact s7_445_safe
def s6_805 : State := ⟨[17,4,117,145], 44601830845581745922811916743961708865978646, 3, 2, 1, 0⟩
theorem s6_805_edges : next config 6 s6_805 = [s7_222] := by decide
theorem s6_805_safe : Safe 7 6 s6_805 := by
  apply safe_succ 6 6 s6_805 [s7_222] (by decide) s6_805_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_222_safe
def s6_806 : State := ⟨[17,4,120,128], 341611615278361145520659920110850605334, 3, 2, 0, 0⟩
theorem s6_806_edges : next config 6 s6_806 = [s7_414] := by decide
theorem s6_806_safe : Safe 7 6 s6_806 := by
  apply safe_succ 6 6 s6_806 [s7_414] (by decide) s6_806_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_414_safe
def s6_807 : State := ⟨[17,4,121,128], 342940843274146061393563727171128852766, 1, 1, 0, 0⟩
theorem s6_807_edges : next config 6 s6_807 = [s7_492, s7_415] := by decide
theorem s6_807_safe : Safe 7 6 s6_807 := by
  apply safe_succ 6 6 s6_807 [s7_492, s7_415] (by decide) s6_807_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_492_safe
  · subst z; exact s7_415_safe
def s6_808 : State := ⟨[17,4,121,128], 342940843274146061393563727171130949910, 3, 2, 0, 0⟩
theorem s6_808_edges : next config 6 s6_808 = [s7_416] := by decide
theorem s6_808_safe : Safe 7 6 s6_808 := by
  apply safe_succ 6 6 s6_808 [s7_416] (by decide) s6_808_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_416_safe
def s6_809 : State := ⟨[17,4,121,128], 342940843274146061430457215318547955990, 1, 1, 0, 0⟩
theorem s6_809_edges : next config 6 s6_809 = [s7_493, s7_417] := by decide
theorem s6_809_safe : Safe 7 6 s6_809 := by
  apply safe_succ 6 6 s6_809 [s7_493, s7_417] (by decide) s6_809_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_493_safe
  · subst z; exact s7_417_safe
def s6_810 : State := ⟨[17,4,125,128], 382817683147693537580677938979541287190, 3, 2, 0, 0⟩
theorem s6_810_edges : next config 6 s6_810 = [s7_446, s7_418] := by decide
theorem s6_810_safe : Safe 7 6 s6_810 := by
  apply safe_succ 6 6 s6_810 [s7_446, s7_418] (by decide) s6_810_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_446_safe
  · subst z; exact s7_418_safe
def s6_811 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914077982, 1, 1, 1, 0⟩
theorem s6_811_edges : next config 6 s6_811 = [s7_569, s7_499, s7_447] := by decide
theorem s6_811_safe : Safe 7 6 s6_811 := by
  apply safe_succ 6 6 s6_811 [s7_569, s7_499, s7_447] (by decide) s6_811_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_569_safe
  · subst z; exact s7_499_safe
  · subst z; exact s7_447_safe
def s6_812 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082070, 3, 2, 1, 0⟩
theorem s6_812_edges : next config 6 s6_812 = [s7_570, s7_224, s7_500] := by decide
theorem s6_812_safe : Safe 7 6 s6_812 := by
  apply safe_succ 6 6 s6_812 [s7_570, s7_224, s7_500] (by decide) s6_812_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_570_safe
  · subst z; exact s7_224_safe
  · subst z; exact s7_500_safe
def s6_813 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175126, 3, 2, 1, 0⟩
theorem s6_813_edges : next config 6 s6_813 = [s7_225, s7_448] := by decide
theorem s6_813_safe : Safe 7 6 s6_813 := by
  apply safe_succ 6 6 s6_813 [s7_225, s7_448] (by decide) s6_813_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_225_safe
  · subst z; exact s7_448_safe
def s6_814 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376333181206, 1, 1, 1, 0⟩
theorem s6_814_edges : next config 6 s6_814 = [s7_571, s7_501, s7_449] := by decide
theorem s6_814_safe : Safe 7 6 s6_814 := by
  apply safe_succ 6 6 s6_814 [s7_571, s7_501, s7_449] (by decide) s6_814_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_571_safe
  · subst z; exact s7_501_safe
  · subst z; exact s7_449_safe
def s6_815 : State := ⟨[17,12,64,128], 340282366920938463481821351509775028510, 3, 3, 0, 0⟩
theorem s6_815_edges : next config 6 s6_815 = [s7_432, s7_422] := by decide
theorem s6_815_safe : Safe 7 6 s6_815 := by
  apply safe_succ 6 6 s6_815 [s7_432, s7_422] (by decide) s6_815_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_432_safe
  · subst z; exact s7_422_safe
def s6_816 : State := ⟨[17,12,64,128], 340282366920938463481821351518364963094, 3, 3, 0, 0⟩
theorem s6_816_edges : next config 6 s6_816 = [s7_433, s7_423] := by decide
theorem s6_816_safe : Safe 7 6 s6_816 := by
  apply safe_succ 6 6 s6_816 [s7_433, s7_423] (by decide) s6_816_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_433_safe
  · subst z; exact s7_423_safe
def s6_817 : State := ⟨[17,12,64,128], 340282366920938463518714839657194131734, 3, 3, 0, 0⟩
theorem s6_817_edges : next config 6 s6_817 = [s7_434, s7_424] := by decide
theorem s6_817_safe : Safe 7 6 s6_817 := by
  apply safe_succ 6 6 s6_817 [s7_434, s7_424] (by decide) s6_817_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_434_safe
  · subst z; exact s7_424_safe
def s6_818 : State := ⟨[17,12,65,145], 44601830679428167221534955260136380206092566, 3, 2, 1, 0⟩
theorem s6_818_edges : next config 6 s6_818 = [s7_230, s7_428] := by decide
theorem s6_818_safe : Safe 7 6 s6_818 := by
  apply safe_succ 6 6 s6_818 [s7_230, s7_428] (by decide) s6_818_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_230_safe
  · subst z; exact s7_428_safe
def s6_819 : State := ⟨[17,12,66,145], 44601830679428167221534992153624527625195798, 3, 2, 1, 0⟩
theorem s6_819_edges : next config 6 s6_819 = [s7_231, s7_430] := by decide
theorem s6_819_safe : Safe 7 6 s6_819 := by
  apply safe_succ 6 6 s6_819 [s7_231, s7_430] (by decide) s6_819_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_231_safe
  · subst z; exact s7_430_safe
def s6_820 : State := ⟨[17,12,67,128], 340282366920938463666288792246870544662, 3, 2, 0, 0⟩
theorem s6_820_edges : next config 6 s6_820 = [s7_428] := by decide
theorem s6_820_safe : Safe 7 6 s6_820 := by
  apply safe_succ 6 6 s6_820 [s7_428] (by decide) s6_820_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_428_safe
def s6_821 : State := ⟨[17,12,67,128], 340282366920938463703182280394289647894, 3, 2, 0, 0⟩
theorem s6_821_edges : next config 6 s6_821 = [s7_429] := by decide
theorem s6_821_safe : Safe 7 6 s6_821 := by
  apply safe_succ 6 6 s6_821 [s7_429] (by decide) s6_821_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_429_safe
def s6_822 : State := ⟨[17,12,67,145], 44601830679428167221535065940600822461305118, 3, 1, 1, 0⟩
theorem s6_822_edges : next config 6 s6_822 = [s7_795, s7_737, s7_369] := by decide
theorem s6_822_safe : Safe 7 6 s6_822 := by
  apply safe_succ 6 6 s6_822 [s7_795, s7_737, s7_369] (by decide) s6_822_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_795_safe
  · subst z; exact s7_737_safe
  · subst z; exact s7_369_safe
def s6_823 : State := ⟨[17,12,67,145], 44601830679428167226370843006035633998336278, 3, 0, 1, 0⟩
theorem s6_823_edges : next config 6 s6_823 = [s7_232, s7_371] := by decide
theorem s6_823_safe : Safe 7 6 s6_823 := by
  apply safe_succ 6 6 s6_823 [s7_232, s7_371] (by decide) s6_823_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_232_safe
  · subst z; exact s7_371_safe
def s6_824 : State := ⟨[17,12,67,145], 44601830679428167227579695038673968334835990, 3, 0, 1, 0⟩
theorem s6_824_edges : next config 6 s6_824 = [s7_233, s7_373] := by decide
theorem s6_824_safe : Safe 7 6 s6_824 := by
  apply safe_succ 6 6 s6_824 [s7_233, s7_373] (by decide) s6_824_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_233_safe
  · subst z; exact s7_373_safe
def s6_825 : State := ⟨[17,12,80,145], 44601830679428167222743844186262861961695510, 3, 2, 1, 0⟩
theorem s6_825_edges : next config 6 s6_825 = [s7_236, s7_431] := by decide
theorem s6_825_safe : Safe 7 6 s6_825 := by
  apply safe_succ 6 6 s6_825 [s7_236, s7_431] (by decide) s6_825_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_236_safe
  · subst z; exact s7_431_safe
def s6_826 : State := ⟨[17,12,81,145], 44601830679428167223952770005877491136401686, 3, 2, 1, 0⟩
theorem s6_826_edges : next config 6 s6_826 = [s7_237] := by decide
theorem s6_826_safe : Safe 7 6 s6_826 := by
  apply safe_succ 6 6 s6_826 [s7_237] (by decide) s6_826_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_237_safe
def s6_827 : State := ⟨[17,12,82,128], 340282366920943299258886786321312059670, 3, 2, 0, 0⟩
theorem s6_827_edges : next config 6 s6_827 = [s7_426, s7_430] := by decide
theorem s6_827_safe : Safe 7 6 s6_827 := by
  apply safe_succ 6 6 s6_827 [s7_426, s7_430] (by decide) s6_827_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_426_safe
  · subst z; exact s7_430_safe
def s6_828 : State := ⟨[17,12,82,128], 340282366920944508110919424655648559382, 3, 2, 0, 0⟩
theorem s6_828_edges : next config 6 s6_828 = [s7_427, s7_431] := by decide
theorem s6_828_safe : Safe 7 6 s6_828 := by
  apply safe_succ 6 6 s6_828 [s7_427, s7_431] (by decide) s6_828_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_427_safe
  · subst z; exact s7_431_safe
def s6_829 : State := ⟨[17,12,96,145], 44601830679428246449697432630985826328842526, 3, 1, 1, 0⟩
theorem s6_829_edges : next config 6 s6_829 = [s7_902, s7_738, s7_379, s7_443, s7_447, s7_437] := by decide
theorem s6_829_safe : Safe 7 6 s6_829 := by
  apply safe_succ 6 6 s6_829 [s7_902, s7_738, s7_379, s7_443, s7_447, s7_437] (by decide) s6_829_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s7_902_safe
  · subst z; exact s7_738_safe
  · subst z; exact s7_379_safe
  · subst z; exact s7_443_safe
  · subst z; exact s7_447_safe
  · subst z; exact s7_437_safe
def s6_830 : State := ⟨[17,12,96,145], 44601830679428246449697432630985826330939670, 3, 2, 1, 0⟩
theorem s6_830_edges : next config 6 s6_830 = [s7_903, s7_238, s7_739, s7_444, s7_448, s7_438, s7_442] := by decide
theorem s6_830_safe : Safe 7 6 s6_830 := by
  apply safe_succ 6 6 s6_830 [s7_903, s7_238, s7_739, s7_444, s7_448, s7_438, s7_442] (by decide) s6_830_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_903_safe
  · subst z; exact s7_238_safe
  · subst z; exact s7_739_safe
  · subst z; exact s7_444_safe
  · subst z; exact s7_448_safe
  · subst z; exact s7_438_safe
  · subst z; exact s7_442_safe
def s6_831 : State := ⟨[17,12,96,145], 44601830679428246449697432630985834918777110, 3, 1, 1, 0⟩
theorem s6_831_edges : next config 6 s6_831 = [s7_382, s7_439] := by decide
theorem s6_831_safe : Safe 7 6 s6_831 := by
  apply safe_succ 6 6 s6_831 [s7_382, s7_439] (by decide) s6_831_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_382_safe
  · subst z; exact s7_439_safe
def s6_832 : State := ⟨[17,12,96,145], 44601830679428246449697469524473973747945750, 3, 1, 1, 0⟩
theorem s6_832_edges : next config 6 s6_832 = [s7_904, s7_384, s7_445, s7_449, s7_440] := by decide
theorem s6_832_safe : Safe 7 6 s6_832 := by
  apply safe_succ 6 6 s6_832 [s7_904, s7_384, s7_445, s7_449, s7_440] (by decide) s6_832_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_904_safe
  · subst z; exact s7_384_safe
  · subst z; exact s7_445_safe
  · subst z; exact s7_449_safe
  · subst z; exact s7_440_safe
def s6_833 : State := ⟨[17,12,96,145], 44601830679428404906022461159661013416743190, 3, 1, 1, 0⟩
theorem s6_833_edges : next config 6 s6_833 = [s7_386, s7_441] := by decide
theorem s6_833_safe : Safe 7 6 s6_833 := by
  apply safe_succ 6 6 s6_833 [s7_386, s7_441] (by decide) s6_833_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_386_safe
  · subst z; exact s7_441_safe
def s6_834 : State := ⟨[17,12,97,128], 340282367158622951024614364290406879510, 3, 2, 0, 0⟩
theorem s6_834_edges : next config 6 s6_834 = [s7_436] := by decide
theorem s6_834_safe : Safe 7 6 s6_834 := by
  apply safe_succ 6 6 s6_834 [s7_436] (by decide) s6_834_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_436_safe
def s6_835 : State := ⟨[17,12,104,128], 340282387282576229647756113050568167710, 3, 1, 0, 0⟩
theorem s6_835_edges : next config 6 s6_835 = [s7_392, s7_437] := by decide
theorem s6_835_safe : Safe 7 6 s6_835 := by
  apply safe_succ 6 6 s6_835 [s7_392, s7_437] (by decide) s6_835_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_392_safe
  · subst z; exact s7_437_safe
def s6_836 : State := ⟨[17,12,104,128], 340282387282576229647756113050570264854, 3, 2, 0, 0⟩
theorem s6_836_edges : next config 6 s6_836 = [s7_438] := by decide
theorem s6_836_safe : Safe 7 6 s6_836 := by
  apply safe_succ 6 6 s6_836 [s7_438] (by decide) s6_836_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_438_safe
def s6_837 : State := ⟨[17,12,104,128], 340282387282576229647756113059158102294, 3, 1, 0, 0⟩
theorem s6_837_edges : next config 6 s6_837 = [s7_395, s7_439] := by decide
theorem s6_837_safe : Safe 7 6 s6_837 := by
  apply safe_succ 6 6 s6_837 [s7_395, s7_439] (by decide) s6_837_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_395_safe
  · subst z; exact s7_439_safe
def s6_838 : State := ⟨[17,12,104,128], 340282387282576229684649601197987270934, 3, 1, 0, 0⟩
theorem s6_838_edges : next config 6 s6_838 = [s7_397, s7_440] := by decide
theorem s6_838_safe : Safe 7 6 s6_838 := by
  apply safe_succ 6 6 s6_838 [s7_397, s7_440] (by decide) s6_838_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_397_safe
  · subst z; exact s7_440_safe
def s6_839 : State := ⟨[17,12,104,128], 340282387441032554676284788237656068374, 3, 1, 0, 0⟩
theorem s6_839_edges : next config 6 s6_839 = [s7_399, s7_441] := by decide
theorem s6_839_safe : Safe 7 6 s6_839 := by
  apply safe_succ 6 6 s6_839 [s7_399, s7_441] (by decide) s6_839_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_399_safe
  · subst z; exact s7_441_safe
def s6_840 : State := ⟨[17,12,112,128], 340287559297025160823714219599648198934, 3, 2, 0, 0⟩
theorem s6_840_edges : next config 6 s6_840 = [s7_442] := by decide
theorem s6_840_safe : Safe 7 6 s6_840 := by
  apply safe_succ 6 6 s6_840 [s7_442] (by decide) s6_840_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_442_safe
def s6_841 : State := ⟨[17,12,113,128], 340292751593883695651342750095975321886, 3, 1, 0, 0⟩
theorem s6_841_edges : next config 6 s6_841 = [s7_408, s7_443] := by decide
theorem s6_841_safe : Safe 7 6 s6_841 := by
  apply safe_succ 6 6 s6_841 [s7_408, s7_443] (by decide) s6_841_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_408_safe
  · subst z; exact s7_443_safe
def s6_842 : State := ⟨[17,12,113,128], 340292751593883695651342750095977419030, 3, 2, 0, 0⟩
theorem s6_842_edges : next config 6 s6_842 = [s7_444] := by decide
theorem s6_842_safe : Safe 7 6 s6_842 := by
  apply safe_succ 6 6 s6_842 [s7_444] (by decide) s6_842_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_444_safe
def s6_843 : State := ⟨[17,12,113,128], 340292751593883695688236238243394425110, 3, 1, 0, 0⟩
theorem s6_843_edges : next config 6 s6_843 = [s7_410, s7_445] := by decide
theorem s6_843_safe : Safe 7 6 s6_843 := by
  apply safe_succ 6 6 s6_843 [s7_410, s7_445] (by decide) s6_843_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_410_safe
  · subst z; exact s7_445_safe
def s6_844 : State := ⟨[17,12,209,145], 822752278660603021122086421958103419712902851183438164461293846, 3, 2, 1, 0⟩
theorem s6_844_edges : next config 6 s6_844 = [s7_271] := by decide
theorem s6_844_safe : Safe 7 6 s6_844 := by
  apply safe_succ 6 6 s6_844 [s7_271] (by decide) s6_844_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_271_safe
def s6_845 : State := ⟨[17,21,64,128], 340282366920938463481821351509775028510, 3, 3, 0, 0⟩
theorem s6_845_edges : next config 6 s6_845 = [s7_466, s7_450] := by decide
theorem s6_845_safe : Safe 7 6 s6_845 := by
  apply safe_succ 6 6 s6_845 [s7_466, s7_450] (by decide) s6_845_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_466_safe
  · subst z; exact s7_450_safe
def s6_846 : State := ⟨[17,21,64,128], 340282366920938463481821351518364963094, 3, 3, 0, 0⟩
theorem s6_846_edges : next config 6 s6_846 = [s7_467, s7_451] := by decide
theorem s6_846_safe : Safe 7 6 s6_846 := by
  apply safe_succ 6 6 s6_846 [s7_467, s7_451] (by decide) s6_846_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_467_safe
  · subst z; exact s7_451_safe
def s6_847 : State := ⟨[17,21,64,128], 340282366920938463518714839657194131734, 3, 3, 0, 0⟩
theorem s6_847_edges : next config 6 s6_847 = [s7_468, s7_452] := by decide
theorem s6_847_safe : Safe 7 6 s6_847 := by
  apply safe_succ 6 6 s6_847 [s7_468, s7_452] (by decide) s6_847_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_468_safe
  · subst z; exact s7_452_safe
def s6_848 : State := ⟨[17,21,65,145], 44601830679428167221534955260136380206092566, 3, 2, 1, 0⟩
theorem s6_848_edges : next config 6 s6_848 = [s7_276, s7_458] := by decide
theorem s6_848_safe : Safe 7 6 s6_848 := by
  apply safe_succ 6 6 s6_848 [s7_276, s7_458] (by decide) s6_848_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_276_safe
  · subst z; exact s7_458_safe
def s6_849 : State := ⟨[17,21,66,145], 44601830679428167221534992153624527625195798, 3, 2, 1, 0⟩
theorem s6_849_edges : next config 6 s6_849 = [s7_277, s7_462] := by decide
theorem s6_849_safe : Safe 7 6 s6_849 := by
  apply safe_succ 6 6 s6_849 [s7_277, s7_462] (by decide) s6_849_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_277_safe
  · subst z; exact s7_462_safe
def s6_850 : State := ⟨[17,21,67,128], 340282366920938463666288792246870544662, 3, 2, 0, 0⟩
theorem s6_850_edges : next config 6 s6_850 = [s7_513, s7_458] := by decide
theorem s6_850_safe : Safe 7 6 s6_850 := by
  apply safe_succ 6 6 s6_850 [s7_513, s7_458] (by decide) s6_850_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_513_safe
  · subst z; exact s7_458_safe
def s6_851 : State := ⟨[17,21,67,128], 340282366920938463703182280394289647894, 3, 2, 0, 0⟩
theorem s6_851_edges : next config 6 s6_851 = [s7_514, s7_459] := by decide
theorem s6_851_safe : Safe 7 6 s6_851 := by
  apply safe_succ 6 6 s6_851 [s7_514, s7_459] (by decide) s6_851_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_514_safe
  · subst z; exact s7_459_safe
def s6_852 : State := ⟨[17,21,67,128], 340282366921020670658916075178169663766, 3, 0, 0, 0⟩
theorem s6_852_edges : next config 6 s6_852 = [s7_367, s7_460] := by decide
theorem s6_852_safe : Safe 7 6 s6_852 := by
  apply safe_succ 6 6 s6_852 [s7_367, s7_460] (by decide) s6_852_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_367_safe
  · subst z; exact s7_460_safe
def s6_853 : State := ⟨[17,21,67,128], 340282366921021879510948713512506163478, 3, 0, 0, 0⟩
theorem s6_853_edges : next config 6 s6_853 = [s7_368, s7_461] := by decide
theorem s6_853_safe : Safe 7 6 s6_853 := by
  apply safe_succ 6 6 s6_853 [s7_368, s7_461] (by decide) s6_853_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_368_safe
  · subst z; exact s7_461_safe
def s6_854 : State := ⟨[17,21,67,145], 44601830679428167221535065940600822463398174, 3, 1, 1, 0⟩
theorem s6_854_edges : next config 6 s6_854 = [s7_796, s7_591, s7_740, s7_370, s7_517, s7_502, s7_509] := by decide
theorem s6_854_safe : Safe 7 6 s6_854 := by
  apply safe_succ 6 6 s6_854 [s7_796, s7_591, s7_740, s7_370, s7_517, s7_502, s7_509] (by decide) s6_854_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_796_safe
  · subst z; exact s7_591_safe
  · subst z; exact s7_740_safe
  · subst z; exact s7_370_safe
  · subst z; exact s7_517_safe
  · subst z; exact s7_502_safe
  · subst z; exact s7_509_safe
def s6_855 : State := ⟨[17,21,67,145], 44601830679428167226370843006035634000429334, 3, 0, 1, 0⟩
theorem s6_855_edges : next config 6 s6_855 = [s7_278, s7_372, s7_518] := by decide
theorem s6_855_safe : Safe 7 6 s6_855 := by
  apply safe_succ 6 6 s6_855 [s7_278, s7_372, s7_518] (by decide) s6_855_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_278_safe
  · subst z; exact s7_372_safe
  · subst z; exact s7_518_safe
def s6_856 : State := ⟨[17,21,67,145], 44601830679428167227579695038673968336929046, 3, 0, 1, 0⟩
theorem s6_856_edges : next config 6 s6_856 = [s7_279, s7_374, s7_519] := by decide
theorem s6_856_safe : Safe 7 6 s6_856 := by
  apply safe_succ 6 6 s6_856 [s7_279, s7_374, s7_519] (by decide) s6_856_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_279_safe
  · subst z; exact s7_374_safe
  · subst z; exact s7_519_safe
def s6_857 : State := ⟨[17,21,80,145], 44601830679428167222743844186262861961695510, 3, 2, 1, 0⟩
theorem s6_857_edges : next config 6 s6_857 = [s7_280, s7_463] := by decide
theorem s6_857_safe : Safe 7 6 s6_857 := by
  apply safe_succ 6 6 s6_857 [s7_280, s7_463] (by decide) s6_857_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_280_safe
  · subst z; exact s7_463_safe
def s6_858 : State := ⟨[17,21,81,145], 44601830679428167223952770005877491136401686, 3, 2, 1, 0⟩
theorem s6_858_edges : next config 6 s6_858 = [s7_281] := by decide
theorem s6_858_safe : Safe 7 6 s6_858 := by
  apply safe_succ 6 6 s6_858 [s7_281] (by decide) s6_858_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_281_safe
def s6_859 : State := ⟨[17,21,82,128], 340282366920943299258886786321312059670, 3, 2, 0, 0⟩
theorem s6_859_edges : next config 6 s6_859 = [s7_454, s7_462] := by decide
theorem s6_859_safe : Safe 7 6 s6_859 := by
  apply safe_succ 6 6 s6_859 [s7_454, s7_462] (by decide) s6_859_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_454_safe
  · subst z; exact s7_462_safe
def s6_860 : State := ⟨[17,21,82,128], 340282366920944508110919424655648559382, 3, 2, 0, 0⟩
theorem s6_860_edges : next config 6 s6_860 = [s7_455, s7_463] := by decide
theorem s6_860_safe : Safe 7 6 s6_860 := by
  apply safe_succ 6 6 s6_860 [s7_455, s7_463] (by decide) s6_860_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_455_safe
  · subst z; exact s7_463_safe
def s6_861 : State := ⟨[17,21,82,128], 340282366921020670511342122588493250838, 3, 2, 0, 0⟩
theorem s6_861_edges : next config 6 s6_861 = [s7_456, s7_464] := by decide
theorem s6_861_safe : Safe 7 6 s6_861 := by
  apply safe_succ 6 6 s6_861 [s7_456, s7_464] (by decide) s6_861_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_456_safe
  · subst z; exact s7_464_safe
def s6_862 : State := ⟨[17,21,82,128], 340282366921021879363374760922829750550, 3, 2, 0, 0⟩
theorem s6_862_edges : next config 6 s6_862 = [s7_457, s7_465] := by decide
theorem s6_862_safe : Safe 7 6 s6_862 := by
  apply safe_succ 6 6 s6_862 [s7_457, s7_465] (by decide) s6_862_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_457_safe
  · subst z; exact s7_465_safe
def s6_863 : State := ⟨[17,21,86,145], 44601830679428167303741947887419311505211670, 3, 0, 1, 0⟩
theorem s6_863_edges : next config 6 s6_863 = [s7_282, s7_377, s7_460] := by decide
theorem s6_863_safe : Safe 7 6 s6_863 := by
  apply safe_succ 6 6 s6_863 [s7_282, s7_377, s7_460] (by decide) s6_863_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_282_safe
  · subst z; exact s7_377_safe
  · subst z; exact s7_460_safe
def s6_864 : State := ⟨[17,21,86,145], 44601830679428167304950799920057645841711382, 3, 0, 1, 0⟩
theorem s6_864_edges : next config 6 s6_864 = [s7_283, s7_378, s7_461] := by decide
theorem s6_864_safe : Safe 7 6 s6_864 := by
  apply safe_succ 6 6 s6_864 [s7_283, s7_378, s7_461] (by decide) s6_864_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_283_safe
  · subst z; exact s7_378_safe
  · subst z; exact s7_461_safe
def s6_865 : State := ⟨[17,21,96,145], 44601830679428246449697432630985826330935582, 3, 1, 1, 0⟩
theorem s6_865_edges : next config 6 s6_865 = [s7_905, s7_592, s7_741, s7_380, s7_530, s7_503, s7_510, s7_487, s7_490, s7_499, s7_475] := by decide
theorem s6_865_safe : Safe 7 6 s6_865 := by
  apply safe_succ 6 6 s6_865 [s7_905, s7_592, s7_741, s7_380, s7_530, s7_503, s7_510, s7_487, s7_490, s7_499, s7_475] (by decide) s6_865_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s7_905_safe
  · subst z; exact s7_592_safe
  · subst z; exact s7_741_safe
  · subst z; exact s7_380_safe
  · subst z; exact s7_530_safe
  · subst z; exact s7_503_safe
  · subst z; exact s7_510_safe
  · subst z; exact s7_487_safe
  · subst z; exact s7_490_safe
  · subst z; exact s7_499_safe
  · subst z; exact s7_475_safe
def s6_866 : State := ⟨[17,21,96,145], 44601830679428246449697432630985826330936086, 3, 1, 1, 0⟩
theorem s6_866_edges : next config 6 s6_866 = [s7_381, s7_476] := by decide
theorem s6_866_safe : Safe 7 6 s6_866 := by
  apply safe_succ 6 6 s6_866 [s7_381, s7_476] (by decide) s6_866_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_381_safe
  · subst z; exact s7_476_safe
def s6_867 : State := ⟨[17,21,96,145], 44601830679428246449697432630985826330939670, 3, 2, 1, 0⟩
theorem s6_867_edges : next config 6 s6_867 = [s7_906, s7_284, s7_742, s7_488, s7_500, s7_477, s7_486] := by decide
theorem s6_867_safe : Safe 7 6 s6_867 := by
  apply safe_succ 6 6 s6_867 [s7_906, s7_284, s7_742, s7_488, s7_500, s7_477, s7_486] (by decide) s6_867_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_906_safe
  · subst z; exact s7_284_safe
  · subst z; exact s7_742_safe
  · subst z; exact s7_488_safe
  · subst z; exact s7_500_safe
  · subst z; exact s7_477_safe
  · subst z; exact s7_486_safe
def s6_868 : State := ⟨[17,21,96,145], 44601830679428246449697432630985834920870166, 3, 1, 1, 0⟩
theorem s6_868_edges : next config 6 s6_868 = [s7_383, s7_504, s7_478] := by decide
theorem s6_868_safe : Safe 7 6 s6_868 := by
  apply safe_succ 6 6 s6_868 [s7_383, s7_504, s7_478] (by decide) s6_868_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_383_safe
  · subst z; exact s7_504_safe
  · subst z; exact s7_478_safe
def s6_869 : State := ⟨[17,21,96,145], 44601830679428246449697469524473973750038806, 3, 1, 1, 0⟩
theorem s6_869_edges : next config 6 s6_869 = [s7_907, s7_593, s7_385, s7_531, s7_505, s7_489, s7_491, s7_501, s7_479] := by decide
theorem s6_869_safe : Safe 7 6 s6_869 := by
  apply safe_succ 6 6 s6_869 [s7_907, s7_593, s7_385, s7_531, s7_505, s7_489, s7_491, s7_501, s7_479] (by decide) s6_869_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s7_907_safe
  · subst z; exact s7_593_safe
  · subst z; exact s7_385_safe
  · subst z; exact s7_531_safe
  · subst z; exact s7_505_safe
  · subst z; exact s7_489_safe
  · subst z; exact s7_491_safe
  · subst z; exact s7_501_safe
  · subst z; exact s7_479_safe
def s6_870 : State := ⟨[17,21,96,145], 44601830679428246449697727778891005683761430, 3, 2, 1, 0⟩
theorem s6_870_edges : next config 6 s6_870 = [s7_285, s7_480] := by decide
theorem s6_870_safe : Safe 7 6 s6_870 := by
  apply safe_succ 6 6 s6_870 [s7_285, s7_480] (by decide) s6_870_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_285_safe
  · subst z; exact s7_480_safe
def s6_871 : State := ⟨[17,21,96,145], 44601830679428404906022461159661013418836246, 3, 1, 1, 0⟩
theorem s6_871_edges : next config 6 s6_871 = [s7_387, s7_481] := by decide
theorem s6_871_safe : Safe 7 6 s6_871 := by
  apply safe_succ 6 6 s6_871 [s7_387, s7_481] (by decide) s6_871_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_387_safe
  · subst z; exact s7_481_safe
def s6_872 : State := ⟨[17,21,96,145], 44601830679429514100297660860387323034140950, 3, 2, 1, 0⟩
theorem s6_872_edges : next config 6 s6_872 = [s7_286, s7_482] := by decide
theorem s6_872_safe : Safe 7 6 s6_872 := by
  apply safe_succ 6 6 s6_872 [s7_286, s7_482] (by decide) s6_872_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_286_safe
  · subst z; exact s7_482_safe
def s6_873 : State := ⟨[17,21,97,128], 340282367158622951024614364290406879510, 3, 2, 0, 0⟩
theorem s6_873_edges : next config 6 s6_873 = [s7_472] := by decide
theorem s6_873_safe : Safe 7 6 s6_873 := by
  apply safe_succ 6 6 s6_873 [s7_472] (by decide) s6_873_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_472_safe
def s6_874 : State := ⟨[17,21,100,128], 340282368267817226224315090600022180126, 3, 1, 0, 0⟩
theorem s6_874_edges : next config 6 s6_874 = [s7_390, s7_473] := by decide
theorem s6_874_safe : Safe 7 6 s6_874 := by
  apply safe_succ 6 6 s6_874 [s7_390, s7_473] (by decide) s6_874_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_390_safe
  · subst z; exact s7_473_safe
def s6_875 : State := ⟨[17,21,100,128], 340282368267817226261208578747441283350, 3, 1, 0, 0⟩
theorem s6_875_edges : next config 6 s6_875 = [s7_391, s7_474] := by decide
theorem s6_875_safe : Safe 7 6 s6_875 := by
  apply safe_succ 6 6 s6_875 [s7_391, s7_474] (by decide) s6_875_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_391_safe
  · subst z; exact s7_474_safe
def s6_876 : State := ⟨[17,21,104,128], 340282387282576229647756113050570260766, 3, 1, 0, 0⟩
theorem s6_876_edges : next config 6 s6_876 = [s7_393, s7_534, s7_506, s7_511, s7_492, s7_494, s7_475] := by decide
theorem s6_876_safe : Safe 7 6 s6_876 := by
  apply safe_succ 6 6 s6_876 [s7_393, s7_534, s7_506, s7_511, s7_492, s7_494, s7_475] (by decide) s6_876_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_393_safe
  · subst z; exact s7_534_safe
  · subst z; exact s7_506_safe
  · subst z; exact s7_511_safe
  · subst z; exact s7_492_safe
  · subst z; exact s7_494_safe
  · subst z; exact s7_475_safe
def s6_877 : State := ⟨[17,21,104,128], 340282387282576229647756113050570261270, 3, 1, 0, 0⟩
theorem s6_877_edges : next config 6 s6_877 = [s7_394, s7_476] := by decide
theorem s6_877_safe : Safe 7 6 s6_877 := by
  apply safe_succ 6 6 s6_877 [s7_394, s7_476] (by decide) s6_877_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_394_safe
  · subst z; exact s7_476_safe
def s6_878 : State := ⟨[17,21,104,128], 340282387282576229647756113050570264854, 3, 2, 0, 0⟩
theorem s6_878_edges : next config 6 s6_878 = [s7_535, s7_495, s7_477] := by decide
theorem s6_878_safe : Safe 7 6 s6_878 := by
  apply safe_succ 6 6 s6_878 [s7_535, s7_495, s7_477] (by decide) s6_878_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_535_safe
  · subst z; exact s7_495_safe
  · subst z; exact s7_477_safe
def s6_879 : State := ⟨[17,21,104,128], 340282387282576229647756113059160195350, 3, 1, 0, 0⟩
theorem s6_879_edges : next config 6 s6_879 = [s7_396, s7_536, s7_507, s7_496, s7_478] := by decide
theorem s6_879_safe : Safe 7 6 s6_879 := by
  apply safe_succ 6 6 s6_879 [s7_396, s7_536, s7_507, s7_496, s7_478] (by decide) s6_879_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_396_safe
  · subst z; exact s7_536_safe
  · subst z; exact s7_507_safe
  · subst z; exact s7_496_safe
  · subst z; exact s7_478_safe
def s6_880 : State := ⟨[17,21,104,128], 340282387282576229684649601197989363990, 3, 1, 0, 0⟩
theorem s6_880_edges : next config 6 s6_880 = [s7_398, s7_537, s7_508, s7_493, s7_497, s7_479] := by decide
theorem s6_880_safe : Safe 7 6 s6_880 := by
  apply safe_succ 6 6 s6_880 [s7_398, s7_537, s7_508, s7_493, s7_497, s7_479] (by decide) s6_880_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s7_398_safe
  · subst z; exact s7_537_safe
  · subst z; exact s7_508_safe
  · subst z; exact s7_493_safe
  · subst z; exact s7_497_safe
  · subst z; exact s7_479_safe
def s6_881 : State := ⟨[17,21,104,128], 340282387282576229942904018229923086614, 3, 2, 0, 0⟩
theorem s6_881_edges : next config 6 s6_881 = [s7_480] := by decide
theorem s6_881_safe : Safe 7 6 s6_881 := by
  apply safe_succ 6 6 s6_881 [s7_480] (by decide) s6_881_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_480_safe
def s6_882 : State := ⟨[17,21,104,128], 340282387441032554676284788237658161430, 3, 1, 0, 0⟩
theorem s6_882_edges : next config 6 s6_882 = [s7_400, s7_538, s7_498, s7_481] := by decide
theorem s6_882_safe : Safe 7 6 s6_882 := by
  apply safe_succ 6 6 s6_882 [s7_400, s7_538, s7_498, s7_481] (by decide) s6_882_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_400_safe
  · subst z; exact s7_538_safe
  · subst z; exact s7_498_safe
  · subst z; exact s7_481_safe
def s6_883 : State := ⟨[17,21,104,128], 340282388550226829875985514547273466134, 3, 2, 0, 0⟩
theorem s6_883_edges : next config 6 s6_883 = [s7_482] := by decide
theorem s6_883_safe : Safe 7 6 s6_883 := by
  apply safe_succ 6 6 s6_883 [s7_482] (by decide) s6_883_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_482_safe
def s6_884 : State := ⟨[17,21,104,128], 340282711801129888074482896206590837014, 3, 2, 0, 0⟩
theorem s6_884_edges : next config 6 s6_884 = [s7_483] := by decide
theorem s6_884_safe : Safe 7 6 s6_884 := by
  apply safe_succ 6 6 s6_884 [s7_483] (by decide) s6_884_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_483_safe
def s6_885 : State := ⟨[17,21,108,145], 44601830679773047412959511028192929602797846, 3, 0, 1, 0⟩
theorem s6_885_edges : next config 6 s6_885 = [s7_287, s7_406] := by decide
theorem s6_885_safe : Safe 7 6 s6_885 := by
  apply safe_succ 6 6 s6_885 [s7_287, s7_406] (by decide) s6_885_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_287_safe
  · subst z; exact s7_406_safe
def s6_886 : State := ⟨[17,21,112,128], 340287559297025160823714219599648198934, 3, 2, 0, 0⟩
theorem s6_886_edges : next config 6 s6_886 = [s7_486] := by decide
theorem s6_886_safe : Safe 7 6 s6_886 := by
  apply safe_succ 6 6 s6_886 [s7_486] (by decide) s6_886_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_486_safe
def s6_887 : State := ⟨[17,21,113,128], 340292751593883695651342750095977414942, 3, 1, 0, 0⟩
theorem s6_887_edges : next config 6 s6_887 = [s7_409, s7_487] := by decide
theorem s6_887_safe : Safe 7 6 s6_887 := by
  apply safe_succ 6 6 s6_887 [s7_409, s7_487] (by decide) s6_887_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_409_safe
  · subst z; exact s7_487_safe
def s6_888 : State := ⟨[17,21,113,128], 340292751593883695651342750095977419030, 3, 2, 0, 0⟩
theorem s6_888_edges : next config 6 s6_888 = [s7_488] := by decide
theorem s6_888_safe : Safe 7 6 s6_888 := by
  apply safe_succ 6 6 s6_888 [s7_488] (by decide) s6_888_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_488_safe
def s6_889 : State := ⟨[17,21,113,128], 340292751593883695688236238243396518166, 3, 1, 0, 0⟩
theorem s6_889_edges : next config 6 s6_889 = [s7_411, s7_489] := by decide
theorem s6_889_safe : Safe 7 6 s6_889 := by
  apply safe_succ 6 6 s6_889 [s7_411, s7_489] (by decide) s6_889_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_411_safe
  · subst z; exact s7_489_safe
def s6_890 : State := ⟨[17,21,117,128], 340448520499639740480198664985854017822, 3, 1, 0, 0⟩
theorem s6_890_edges : next config 6 s6_890 = [s7_412, s7_490] := by decide
theorem s6_890_safe : Safe 7 6 s6_890 := by
  apply safe_succ 6 6 s6_890 [s7_412, s7_490] (by decide) s6_890_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_412_safe
  · subst z; exact s7_490_safe
def s6_891 : State := ⟨[17,21,117,128], 340448520499639740517092153133273121046, 3, 1, 0, 0⟩
theorem s6_891_edges : next config 6 s6_891 = [s7_413, s7_491] := by decide
theorem s6_891_safe : Safe 7 6 s6_891 := by
  apply safe_succ 6 6 s6_891 [s7_413, s7_491] (by decide) s6_891_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_413_safe
  · subst z; exact s7_491_safe
def s6_892 : State := ⟨[17,21,120,145], 44601832008676524644216957205216833862566166, 3, 0, 1, 0⟩
theorem s6_892_edges : next config 6 s6_892 = [s7_288, s7_414] := by decide
theorem s6_892_safe : Safe 7 6 s6_892 := by
  apply safe_succ 6 6 s6_892 [s7_288, s7_414] (by decide) s6_892_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_288_safe
  · subst z; exact s7_414_safe
def s6_893 : State := ⟨[17,21,121,145], 44601833337904520429132830109023894142910742, 3, 0, 1, 0⟩
theorem s6_893_edges : next config 6 s6_893 = [s7_289, s7_416] := by decide
theorem s6_893_safe : Safe 7 6 s6_893 := by
  apply safe_succ 6 6 s6_893 [s7_289, s7_416] (by decide) s6_893_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_289_safe
  · subst z; exact s7_416_safe
def s6_894 : State := ⟨[17,21,125,145], 44601873214744393976609017223235702553248022, 3, 0, 1, 0⟩
theorem s6_894_edges : next config 6 s6_894 = [s7_290, s7_743, s7_418] := by decide
theorem s6_894_safe : Safe 7 6 s6_894 := by
  apply safe_succ 6 6 s6_894 [s7_290, s7_743, s7_418] (by decide) s6_894_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_290_safe
  · subst z; exact s7_743_safe
  · subst z; exact s7_418_safe
def s6_895 : State := ⟨[17,21,209,145], 822752278660603021122086421958103419712902851183438164461293846, 3, 2, 1, 0⟩
theorem s6_895_edges : next config 6 s6_895 = [s7_291] := by decide
theorem s6_895_safe : Safe 7 6 s6_895 := by
  apply safe_succ 6 6 s6_895 [s7_291] (by decide) s6_895_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_291_safe
def s6_896 : State := ⟨[17,21,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546902, 3, 0, 1, 0⟩
theorem s6_896_edges : next config 6 s6_896 = [s7_292, s7_420] := by decide
theorem s6_896_safe : Safe 7 6 s6_896 := by
  apply safe_succ 6 6 s6_896 [s7_292, s7_420] (by decide) s6_896_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_292_safe
  · subst z; exact s7_420_safe
def s6_897 : State := ⟨[17,29,64,145], 44601830679428167221534918366648233323856158, 3, 1, 1, 0⟩
theorem s6_897_edges : next config 6 s6_897 = [s7_503] := by decide
theorem s6_897_safe : Safe 7 6 s6_897 := by
  apply safe_succ 6 6 s6_897 [s7_503] (by decide) s6_897_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_503_safe
def s6_898 : State := ⟨[17,29,64,145], 44601830679428167221534918366648241913790742, 3, 1, 1, 0⟩
theorem s6_898_edges : next config 6 s6_898 = [s7_504] := by decide
theorem s6_898_safe : Safe 7 6 s6_898 := by
  apply safe_succ 6 6 s6_898 [s7_504] (by decide) s6_898_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_504_safe
def s6_899 : State := ⟨[17,29,64,145], 44601830679428167221534955260136380742959382, 3, 1, 1, 0⟩
theorem s6_899_edges : next config 6 s6_899 = [s7_505] := by decide
theorem s6_899_safe : Safe 7 6 s6_899 := by
  apply safe_succ 6 6 s6_899 [s7_505] (by decide) s6_899_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_505_safe
def s6_900 : State := ⟨[17,29,67,128], 340282366920938463629395304099988308254, 3, 1, 0, 0⟩
theorem s6_900_edges : next config 6 s6_900 = [s7_502] := by decide
theorem s6_900_safe : Safe 7 6 s6_900 := by
  apply safe_succ 6 6 s6_900 [s7_502] (by decide) s6_900_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_502_safe
def s6_901 : State := ⟨[17,29,67,145], 44601830679428167221535102834088970419372310, 3, 0, 1, 0⟩
theorem s6_901_edges : next config 6 s6_901 = [s7_293] := by decide
theorem s6_901_safe : Safe 7 6 s6_901 := by
  apply safe_succ 6 6 s6_901 [s7_293] (by decide) s6_901_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_293_safe
def s6_902 : State := ⟨[17,29,67,145], 44601830679428167221535139727577117838475542, 3, 0, 1, 0⟩
theorem s6_902_edges : next config 6 s6_902 = [s7_294] := by decide
theorem s6_902_safe : Safe 7 6 s6_902 := by
  apply safe_succ 6 6 s6_902 [s7_294] (by decide) s6_902_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_294_safe
def s6_903 : State := ⟨[17,29,96,128], 340282367000166625996085689103855845662, 3, 1, 0, 0⟩
theorem s6_903_edges : next config 6 s6_903 = [s7_506, s7_503] := by decide
theorem s6_903_safe : Safe 7 6 s6_903 := by
  apply safe_succ 6 6 s6_903 [s7_506, s7_503] (by decide) s6_903_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_506_safe
  · subst z; exact s7_503_safe
def s6_904 : State := ⟨[17,29,96,128], 340282367000166625996085689112445780246, 3, 1, 0, 0⟩
theorem s6_904_edges : next config 6 s6_904 = [s7_507, s7_504] := by decide
theorem s6_904_safe : Safe 7 6 s6_904 := by
  apply safe_succ 6 6 s6_904 [s7_507, s7_504] (by decide) s6_904_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_507_safe
  · subst z; exact s7_504_safe
def s6_905 : State := ⟨[17,29,96,128], 340282367000166626032979177251274948886, 3, 1, 0, 0⟩
theorem s6_905_edges : next config 6 s6_905 = [s7_508, s7_505] := by decide
theorem s6_905_safe : Safe 7 6 s6_905 := by
  apply safe_succ 6 6 s6_905 [s7_508, s7_505] (by decide) s6_905_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_508_safe
  · subst z; exact s7_505_safe
def s6_906 : State := ⟨[17,29,104,145], 44601830679448528859301084301409774119092502, 3, 0, 1, 0⟩
theorem s6_906_edges : next config 6 s6_906 = [s7_295] := by decide
theorem s6_906_safe : Safe 7 6 s6_906 := by
  apply safe_succ 6 6 s6_906 [s7_295] (by decide) s6_906_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_295_safe
def s6_907 : State := ⟨[17,53,64,145], 44601830679428167221534918375655432041726238, 3, 1, 1, 0⟩
theorem s6_907_edges : next config 6 s6_907 = [s7_510] := by decide
theorem s6_907_safe : Safe 7 6 s6_907 := by
  apply safe_succ 6 6 s6_907 [s7_510] (by decide) s6_907_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_510_safe
def s6_908 : State := ⟨[17,53,67,128], 340282366920938463629404311298706178334, 3, 1, 0, 0⟩
theorem s6_908_edges : next config 6 s6_908 = [s7_509] := by decide
theorem s6_908_safe : Safe 7 6 s6_908 := by
  apply safe_succ 6 6 s6_908 [s7_509] (by decide) s6_908_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_509_safe
def s6_909 : State := ⟨[17,53,96,128], 340282367000166625996094696302573715742, 3, 1, 0, 0⟩
theorem s6_909_edges : next config 6 s6_909 = [s7_511, s7_510] := by decide
theorem s6_909_safe : Safe 7 6 s6_909 := by
  apply safe_succ 6 6 s6_909 [s7_511, s7_510] (by decide) s6_909_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_511_safe
  · subst z; exact s7_510_safe
def s6_910 : State := ⟨[17,53,104,145], 44601830679448528859301084310416972836962582, 3, 0, 1, 0⟩
theorem s6_910_edges : next config 6 s6_910 = [s7_296] := by decide
theorem s6_910_safe : Safe 7 6 s6_910 := by
  apply safe_succ 6 6 s6_910 [s7_296] (by decide) s6_910_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_296_safe
def s6_911 : State := ⟨[17,68,96,145], 44601830679428246449697727778891005683761430, 3, 2, 1, 0⟩
theorem s6_911_edges : next config 6 s6_911 = [s7_297, s7_512] := by decide
theorem s6_911_safe : Safe 7 6 s6_911 := by
  apply safe_succ 6 6 s6_911 [s7_297, s7_512] (by decide) s6_911_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_297_safe
  · subst z; exact s7_512_safe
def s6_912 : State := ⟨[17,68,104,128], 340282387282576229942904018229923086614, 3, 2, 0, 0⟩
theorem s6_912_edges : next config 6 s6_912 = [s7_512] := by decide
theorem s6_912_safe : Safe 7 6 s6_912 := by
  apply safe_succ 6 6 s6_912 [s7_512] (by decide) s6_912_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_512_safe
def s6_913 : State := ⟨[17,86,67,128], 340282366921015834881850640366632632606, 3, 1, 0, 0⟩
theorem s6_913_edges : next config 6 s6_913 = [s7_517] := by decide
theorem s6_913_safe : Safe 7 6 s6_913 := by
  apply safe_succ 6 6 s6_913 [s7_517] (by decide) s6_913_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_517_safe
def s6_914 : State := ⟨[17,86,67,128], 340282366921020670658916075178169663766, 3, 0, 0, 0⟩
theorem s6_914_edges : next config 6 s6_914 = [s7_518] := by decide
theorem s6_914_safe : Safe 7 6 s6_914 := by
  apply safe_succ 6 6 s6_914 [s7_518] (by decide) s6_914_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_518_safe
def s6_915 : State := ⟨[17,86,67,128], 340282366921021879510948713512506163478, 3, 0, 0, 0⟩
theorem s6_915_edges : next config 6 s6_915 = [s7_519] := by decide
theorem s6_915_safe : Safe 7 6 s6_915 := by
  apply safe_succ 6 6 s6_915 [s7_519] (by decide) s6_915_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_519_safe
def s6_916 : State := ⟨[17,86,67,145], 44601830679428167298906355289425237063696662, 3, 0, 1, 0⟩
theorem s6_916_edges : next config 6 s6_916 = [s7_800, s7_298] := by decide
theorem s6_916_safe : Safe 7 6 s6_916 := by
  apply safe_succ 6 6 s6_916 [s7_800, s7_298] (by decide) s6_916_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_800_safe
  · subst z; exact s7_298_safe
def s6_917 : State := ⟨[17,86,67,145], 44601830679428167298906392182913384482799894, 3, 0, 1, 0⟩
theorem s6_917_edges : next config 6 s6_917 = [s7_801, s7_299] := by decide
theorem s6_917_safe : Safe 7 6 s6_917 := by
  apply safe_succ 6 6 s6_917 [s7_801, s7_299] (by decide) s6_917_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_801_safe
  · subst z; exact s7_299_safe
def s6_918 : State := ⟨[17,86,67,145], 44601830679428167303742095461371901179527446, 3, 0, 1, 0⟩
theorem s6_918_edges : next config 6 s6_918 = [s7_300, s7_460] := by decide
theorem s6_918_safe : Safe 7 6 s6_918 := by
  apply safe_succ 6 6 s6_918 [s7_300, s7_460] (by decide) s6_918_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_300_safe
  · subst z; exact s7_460_safe
def s6_919 : State := ⟨[17,86,67,145], 44601830679428167304950947494010235516027158, 3, 0, 1, 0⟩
theorem s6_919_edges : next config 6 s6_919 = [s7_301, s7_461] := by decide
theorem s6_919_safe : Safe 7 6 s6_919 := by
  apply safe_succ 6 6 s6_919 [s7_301, s7_461] (by decide) s6_919_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_301_safe
  · subst z; exact s7_461_safe
def s6_920 : State := ⟨[17,86,82,128], 340282366921020670511342122588493250838, 3, 2, 0, 0⟩
theorem s6_920_edges : next config 6 s6_920 = [s7_515, s7_520] := by decide
theorem s6_920_safe : Safe 7 6 s6_920 := by
  apply safe_succ 6 6 s6_920 [s7_515, s7_520] (by decide) s6_920_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_515_safe
  · subst z; exact s7_520_safe
def s6_921 : State := ⟨[17,86,82,128], 340282366921021879363374760922829750550, 3, 2, 0, 0⟩
theorem s6_921_edges : next config 6 s6_921 = [s7_516, s7_521] := by decide
theorem s6_921_safe : Safe 7 6 s6_921 := by
  apply safe_succ 6 6 s6_921 [s7_516, s7_521] (by decide) s6_921_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_516_safe
  · subst z; exact s7_521_safe
def s6_922 : State := ⟨[17,100,96,145], 44601830679429514100297660860387323032043806, 3, 1, 1, 0⟩
theorem s6_922_edges : next config 6 s6_922 = [s7_388, s7_524] := by decide
theorem s6_922_safe : Safe 7 6 s6_922 := by
  apply safe_succ 6 6 s6_922 [s7_388, s7_524] (by decide) s6_922_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_388_safe
  · subst z; exact s7_524_safe
def s6_923 : State := ⟨[17,100,96,145], 44601830679429514100297660860387323034140950, 3, 2, 1, 0⟩
theorem s6_923_edges : next config 6 s6_923 = [s7_302, s7_525] := by decide
theorem s6_923_safe : Safe 7 6 s6_923 := by
  apply safe_succ 6 6 s6_923 [s7_302, s7_525] (by decide) s6_923_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_302_safe
  · subst z; exact s7_525_safe
def s6_924 : State := ⟨[17,100,96,145], 44601830679429514100297697753875470451147030, 3, 1, 1, 0⟩
theorem s6_924_edges : next config 6 s6_924 = [s7_389, s7_526] := by decide
theorem s6_924_safe : Safe 7 6 s6_924 := by
  apply safe_succ 6 6 s6_924 [s7_389, s7_526] (by decide) s6_924_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_389_safe
  · subst z; exact s7_526_safe
def s6_925 : State := ⟨[17,100,104,128], 340282388550226829875985514547271368990, 3, 1, 0, 0⟩
theorem s6_925_edges : next config 6 s6_925 = [s7_524] := by decide
theorem s6_925_safe : Safe 7 6 s6_925 := by
  apply safe_succ 6 6 s6_925 [s7_524] (by decide) s6_925_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_524_safe
def s6_926 : State := ⟨[17,100,104,128], 340282388550226829875985514547273466134, 3, 2, 0, 0⟩
theorem s6_926_edges : next config 6 s6_926 = [s7_525] := by decide
theorem s6_926_safe : Safe 7 6 s6_926 := by
  apply safe_succ 6 6 s6_926 [s7_525] (by decide) s6_926_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_525_safe
def s6_927 : State := ⟨[17,100,104,128], 340282388550226829912879002694690472214, 3, 1, 0, 0⟩
theorem s6_927_edges : next config 6 s6_927 = [s7_526] := by decide
theorem s6_927_safe : Safe 7 6 s6_927 := by
  apply safe_succ 6 6 s6_927 [s7_526] (by decide) s6_927_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_526_safe
def s6_928 : State := ⟨[17,108,104,128], 340282711801129888074482896206588739870, 3, 1, 0, 0⟩
theorem s6_928_edges : next config 6 s6_928 = [s7_403, s7_527] := by decide
theorem s6_928_safe : Safe 7 6 s6_928 := by
  apply safe_succ 6 6 s6_928 [s7_403, s7_527] (by decide) s6_928_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_403_safe
  · subst z; exact s7_527_safe
def s6_929 : State := ⟨[17,108,104,128], 340282711801129888074482896206590837014, 3, 2, 0, 0⟩
theorem s6_929_edges : next config 6 s6_929 = [s7_528] := by decide
theorem s6_929_safe : Safe 7 6 s6_929 := by
  apply safe_succ 6 6 s6_929 [s7_528] (by decide) s6_929_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_528_safe
def s6_930 : State := ⟨[17,108,104,128], 340282711801129888111376384354007843094, 3, 1, 0, 0⟩
theorem s6_930_edges : next config 6 s6_930 = [s7_404, s7_529] := by decide
theorem s6_930_safe : Safe 7 6 s6_930 := by
  apply safe_succ 6 6 s6_930 [s7_404, s7_529] (by decide) s6_930_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_404_safe
  · subst z; exact s7_529_safe
def s6_931 : State := ⟨[17,117,96,128], 340448520499639740480198664985854017822, 3, 1, 0, 0⟩
theorem s6_931_edges : next config 6 s6_931 = [s7_532, s7_530] := by decide
theorem s6_931_safe : Safe 7 6 s6_931 := by
  apply safe_succ 6 6 s6_931 [s7_532, s7_530] (by decide) s6_931_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_532_safe
  · subst z; exact s7_530_safe
def s6_932 : State := ⟨[17,117,96,128], 340448520499639740517092153133273121046, 3, 1, 0, 0⟩
theorem s6_932_edges : next config 6 s6_932 = [s7_533, s7_531] := by decide
theorem s6_932_safe : Safe 7 6 s6_932 := by
  apply safe_succ 6 6 s6_932 [s7_533, s7_531] (by decide) s6_932_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_533_safe
  · subst z; exact s7_531_safe
def s6_933 : State := ⟨[17,117,104,145], 44601830845602028332415568414385656117264662, 3, 0, 1, 0⟩
theorem s6_933_edges : next config 6 s6_933 = [s7_311] := by decide
theorem s6_933_safe : Safe 7 6 s6_933 := by
  apply safe_succ 6 6 s6_933 [s7_311] (by decide) s6_933_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_311_safe
def s6_934 : State := ⟨[17,125,104,145], 44601873214744393976609017223235702553248022, 3, 0, 1, 0⟩
theorem s6_934_edges : next config 6 s6_934 = [s7_312, s7_744] := by decide
theorem s6_934_safe : Safe 7 6 s6_934 := by
  apply safe_succ 6 6 s6_934 [s7_312, s7_744] (by decide) s6_934_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_312_safe
  · subst z; exact s7_744_safe
def s6_935 : State := ⟨[21,4,65,145], 44601830679428167221534955260136380206092566, 3, 2, 1, 0⟩
theorem s6_935_edges : next config 6 s6_935 = [s7_542] := by decide
theorem s6_935_safe : Safe 7 6 s6_935 := by
  apply safe_succ 6 6 s6_935 [s7_542] (by decide) s6_935_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_542_safe
def s6_936 : State := ⟨[21,4,66,145], 44601830679428167221534992153624527625195798, 3, 2, 1, 0⟩
theorem s6_936_edges : next config 6 s6_936 = [s7_547] := by decide
theorem s6_936_safe : Safe 7 6 s6_936 := by
  apply safe_succ 6 6 s6_936 [s7_547] (by decide) s6_936_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_547_safe
def s6_937 : State := ⟨[21,4,67,145], 44601830679428167221535065940600822463398174, 1, 1, 1, 0⟩
theorem s6_937_edges : next config 6 s6_937 = [s7_802, s7_594, s7_745, s7_572] := by decide
theorem s6_937_safe : Safe 7 6 s6_937 := by
  apply safe_succ 6 6 s6_937 [s7_802, s7_594, s7_745, s7_572] (by decide) s6_937_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_802_safe
  · subst z; exact s7_594_safe
  · subst z; exact s7_745_safe
  · subst z; exact s7_572_safe
def s6_938 : State := ⟨[21,4,67,145], 44601830679428167226370843006035634000429334, 1, 0, 1, 0⟩
theorem s6_938_edges : next config 6 s6_938 = [s7_804, s7_573] := by decide
theorem s6_938_safe : Safe 7 6 s6_938 := by
  apply safe_succ 6 6 s6_938 [s7_804, s7_573] (by decide) s6_938_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_804_safe
  · subst z; exact s7_573_safe
def s6_939 : State := ⟨[21,4,67,145], 44601830679428167227579695038673968336929046, 1, 0, 1, 0⟩
theorem s6_939_edges : next config 6 s6_939 = [s7_805, s7_574] := by decide
theorem s6_939_safe : Safe 7 6 s6_939 := by
  apply safe_succ 6 6 s6_939 [s7_805, s7_574] (by decide) s6_939_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_805_safe
  · subst z; exact s7_574_safe
def s6_940 : State := ⟨[21,4,80,145], 44601830679428167222743844186262861961695510, 3, 2, 1, 0⟩
theorem s6_940_edges : next config 6 s6_940 = [s7_548] := by decide
theorem s6_940_safe : Safe 7 6 s6_940 := by
  apply safe_succ 6 6 s6_940 [s7_548] (by decide) s6_940_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_548_safe
def s6_941 : State := ⟨[21,4,81,145], 44601830679428167223952770005877491136401686, 3, 2, 1, 0⟩
theorem s6_941_edges : next config 6 s6_941 = [] := by decide
theorem s6_941_safe : Safe 7 6 s6_941 := by
  apply safe_succ 6 6 s6_941 [] (by decide) s6_941_edges
  simp
def s6_942 : State := ⟨[21,4,86,145], 44601830679428167303741947887419311505211670, 1, 0, 1, 0⟩
theorem s6_942_edges : next config 6 s6_942 = [s7_545] := by decide
theorem s6_942_safe : Safe 7 6 s6_942 := by
  apply safe_succ 6 6 s6_942 [s7_545] (by decide) s6_942_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_545_safe
def s6_943 : State := ⟨[21,4,86,145], 44601830679428167304950799920057645841711382, 1, 0, 1, 0⟩
theorem s6_943_edges : next config 6 s6_943 = [s7_546] := by decide
theorem s6_943_safe : Safe 7 6 s6_943 := by
  apply safe_succ 6 6 s6_943 [s7_546] (by decide) s6_943_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_546_safe
def s6_944 : State := ⟨[21,4,96,145], 44601830679428246449697432630985826330935582, 1, 1, 1, 0⟩
theorem s6_944_edges : next config 6 s6_944 = [s7_910, s7_595, s7_746, s7_580, s7_575, s7_567, s7_552, s7_569, s7_554] := by decide
theorem s6_944_safe : Safe 7 6 s6_944 := by
  apply safe_succ 6 6 s6_944 [s7_910, s7_595, s7_746, s7_580, s7_575, s7_567, s7_552, s7_569, s7_554] (by decide) s6_944_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s7_910_safe
  · subst z; exact s7_595_safe
  · subst z; exact s7_746_safe
  · subst z; exact s7_580_safe
  · subst z; exact s7_575_safe
  · subst z; exact s7_567_safe
  · subst z; exact s7_552_safe
  · subst z; exact s7_569_safe
  · subst z; exact s7_554_safe
def s6_945 : State := ⟨[21,4,96,145], 44601830679428246449697432630985826330936086, 1, 1, 1, 0⟩
theorem s6_945_edges : next config 6 s6_945 = [s7_555] := by decide
theorem s6_945_safe : Safe 7 6 s6_945 := by
  apply safe_succ 6 6 s6_945 [s7_555] (by decide) s6_945_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_555_safe
def s6_946 : State := ⟨[21,4,96,145], 44601830679428246449697432630985826330939670, 3, 2, 1, 0⟩
theorem s6_946_edges : next config 6 s6_946 = [s7_570, s7_556, s7_563] := by decide
theorem s6_946_safe : Safe 7 6 s6_946 := by
  apply safe_succ 6 6 s6_946 [s7_570, s7_556, s7_563] (by decide) s6_946_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_570_safe
  · subst z; exact s7_556_safe
  · subst z; exact s7_563_safe
def s6_947 : State := ⟨[21,4,96,145], 44601830679428246449697432630985834920870166, 1, 1, 1, 0⟩
theorem s6_947_edges : next config 6 s6_947 = [s7_596, s7_576, s7_557] := by decide
theorem s6_947_safe : Safe 7 6 s6_947 := by
  apply safe_succ 6 6 s6_947 [s7_596, s7_576, s7_557] (by decide) s6_947_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_596_safe
  · subst z; exact s7_576_safe
  · subst z; exact s7_557_safe
def s6_948 : State := ⟨[21,4,96,145], 44601830679428246449697469524473973750038806, 1, 1, 1, 0⟩
theorem s6_948_edges : next config 6 s6_948 = [s7_911, s7_597, s7_581, s7_577, s7_568, s7_553, s7_571, s7_558] := by decide
theorem s6_948_safe : Safe 7 6 s6_948 := by
  apply safe_succ 6 6 s6_948 [s7_911, s7_597, s7_581, s7_577, s7_568, s7_553, s7_571, s7_558] (by decide) s6_948_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_911_safe
  · subst z; exact s7_597_safe
  · subst z; exact s7_581_safe
  · subst z; exact s7_577_safe
  · subst z; exact s7_568_safe
  · subst z; exact s7_553_safe
  · subst z; exact s7_571_safe
  · subst z; exact s7_558_safe
def s6_949 : State := ⟨[21,4,96,145], 44601830679428246449697727778891005683761430, 3, 2, 1, 0⟩
theorem s6_949_edges : next config 6 s6_949 = [s7_559] := by decide
theorem s6_949_safe : Safe 7 6 s6_949 := by
  apply safe_succ 6 6 s6_949 [s7_559] (by decide) s6_949_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_559_safe
def s6_950 : State := ⟨[21,4,96,145], 44601830679428404906022461159661013418836246, 1, 1, 1, 0⟩
theorem s6_950_edges : next config 6 s6_950 = [s7_578, s7_560] := by decide
theorem s6_950_safe : Safe 7 6 s6_950 := by
  apply safe_succ 6 6 s6_950 [s7_578, s7_560] (by decide) s6_950_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_578_safe
  · subst z; exact s7_560_safe
def s6_951 : State := ⟨[21,4,96,145], 44601830679429514100297660860387323034140950, 3, 2, 1, 0⟩
theorem s6_951_edges : next config 6 s6_951 = [s7_561] := by decide
theorem s6_951_safe : Safe 7 6 s6_951 := by
  apply safe_succ 6 6 s6_951 [s7_561] (by decide) s6_951_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_561_safe
def s6_952 : State := ⟨[21,4,108,145], 44601830679773047412959511028192929602797846, 1, 0, 1, 0⟩
theorem s6_952_edges : next config 6 s6_952 = [] := by decide
theorem s6_952_safe : Safe 7 6 s6_952 := by
  apply safe_succ 6 6 s6_952 [] (by decide) s6_952_edges
  simp
def s6_953 : State := ⟨[21,4,120,145], 44601832008676524644216957205216833862566166, 1, 0, 1, 0⟩
theorem s6_953_edges : next config 6 s6_953 = [] := by decide
theorem s6_953_safe : Safe 7 6 s6_953 := by
  apply safe_succ 6 6 s6_953 [] (by decide) s6_953_edges
  simp
def s6_954 : State := ⟨[21,4,121,145], 44601833337904520429132830109023894142910742, 1, 0, 1, 0⟩
theorem s6_954_edges : next config 6 s6_954 = [] := by decide
theorem s6_954_safe : Safe 7 6 s6_954 := by
  apply safe_succ 6 6 s6_954 [] (by decide) s6_954_edges
  simp
def s6_955 : State := ⟨[21,4,125,145], 44601873214744393976609017223235702553248022, 1, 0, 1, 0⟩
theorem s6_955_edges : next config 6 s6_955 = [s7_579] := by decide
theorem s6_955_safe : Safe 7 6 s6_955 := by
  apply safe_succ 6 6 s6_955 [s7_579] (by decide) s6_955_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_579_safe
def s6_956 : State := ⟨[21,4,209,145], 822752278660603021122086421958103419712902851183438164461293846, 3, 2, 1, 0⟩
theorem s6_956_edges : next config 6 s6_956 = [] := by decide
theorem s6_956_safe : Safe 7 6 s6_956 := by
  apply safe_succ 6 6 s6_956 [] (by decide) s6_956_edges
  simp
def s6_957 : State := ⟨[21,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546902, 1, 0, 1, 0⟩
theorem s6_957_edges : next config 6 s6_957 = [] := by decide
theorem s6_957_safe : Safe 7 6 s6_957 := by
  apply safe_succ 6 6 s6_957 [] (by decide) s6_957_edges
  simp
def s6_958 : State := ⟨[21,12,64,145], 44601830679428167221534918366648232786989342, 3, 1, 1, 0⟩
theorem s6_958_edges : next config 6 s6_958 = [s7_539, s7_575] := by decide
theorem s6_958_safe : Safe 7 6 s6_958 := by
  apply safe_succ 6 6 s6_958 [s7_539, s7_575] (by decide) s6_958_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_539_safe
  · subst z; exact s7_575_safe
def s6_959 : State := ⟨[21,12,64,145], 44601830679428167221534918366648241376923926, 3, 1, 1, 0⟩
theorem s6_959_edges : next config 6 s6_959 = [s7_540, s7_576] := by decide
theorem s6_959_safe : Safe 7 6 s6_959 := by
  apply safe_succ 6 6 s6_959 [s7_540, s7_576] (by decide) s6_959_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_540_safe
  · subst z; exact s7_576_safe
def s6_960 : State := ⟨[21,12,64,145], 44601830679428167221534955260136380206092566, 3, 1, 1, 0⟩
theorem s6_960_edges : next config 6 s6_960 = [s7_541, s7_577] := by decide
theorem s6_960_safe : Safe 7 6 s6_960 := by
  apply safe_succ 6 6 s6_960 [s7_541, s7_577] (by decide) s6_960_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_541_safe
  · subst z; exact s7_577_safe
def s6_961 : State := ⟨[21,12,67,145], 44601830679428167221535102834088969882505494, 3, 0, 1, 0⟩
theorem s6_961_edges : next config 6 s6_961 = [s7_806, s7_542] := by decide
theorem s6_961_safe : Safe 7 6 s6_961 := by
  apply safe_succ 6 6 s6_961 [s7_806, s7_542] (by decide) s6_961_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_806_safe
  · subst z; exact s7_542_safe
def s6_962 : State := ⟨[21,12,67,145], 44601830679428167221535139727577117301608726, 3, 0, 1, 0⟩
theorem s6_962_edges : next config 6 s6_962 = [s7_807, s7_543] := by decide
theorem s6_962_safe : Safe 7 6 s6_962 := by
  apply safe_succ 6 6 s6_962 [s7_807, s7_543] (by decide) s6_962_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_807_safe
  · subst z; exact s7_543_safe
def s6_963 : State := ⟨[21,12,82,145], 44601830679428167226370695432083044324020502, 3, 0, 1, 0⟩
theorem s6_963_edges : next config 6 s6_963 = [s7_547] := by decide
theorem s6_963_safe : Safe 7 6 s6_963 := by
  apply safe_succ 6 6 s6_963 [s7_547] (by decide) s6_963_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_547_safe
def s6_964 : State := ⟨[21,12,82,145], 44601830679428167227579547464721378660520214, 3, 0, 1, 0⟩
theorem s6_964_edges : next config 6 s6_964 = [s7_548] := by decide
theorem s6_964_safe : Safe 7 6 s6_964 := by
  apply safe_succ 6 6 s6_964 [s7_548] (by decide) s6_964_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_548_safe
def s6_965 : State := ⟨[21,12,97,145], 44601830679428404906022461159661013418840342, 3, 0, 1, 0⟩
theorem s6_965_edges : next config 6 s6_965 = [s7_551] := by decide
theorem s6_965_safe : Safe 7 6 s6_965 := by
  apply safe_succ 6 6 s6_965 [s7_551] (by decide) s6_965_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_551_safe
def s6_966 : State := ⟨[21,12,104,145], 44601830679448528859301084301409773582225686, 3, 0, 1, 0⟩
theorem s6_966_edges : next config 6 s6_966 = [s7_915, s7_556, s7_579] := by decide
theorem s6_966_safe : Safe 7 6 s6_966 := by
  apply safe_succ 6 6 s6_966 [s7_915, s7_556, s7_579] (by decide) s6_966_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_915_safe
  · subst z; exact s7_556_safe
  · subst z; exact s7_579_safe
def s6_967 : State := ⟨[21,12,112,145], 44601830684620543308232260259516322660159766, 3, 0, 1, 0⟩
theorem s6_967_edges : next config 6 s6_967 = [s7_563] := by decide
theorem s6_967_safe : Safe 7 6 s6_967 := by
  apply safe_succ 6 6 s6_967 [s7_563] (by decide) s6_967_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_563_safe
def s6_968 : State := ⟨[21,12,113,145], 44601830689812840166767087888046818989379862, 3, 0, 1, 0⟩
theorem s6_968_edges : next config 6 s6_968 = [s7_565] := by decide
theorem s6_968_safe : Safe 7 6 s6_968 := by
  apply safe_succ 6 6 s6_968 [s7_565] (by decide) s6_968_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_565_safe
def s6_969 : State := ⟨[21,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179222, 3, 0, 1, 0⟩
theorem s6_969_edges : next config 6 s6_969 = [s7_570] := by decide
theorem s6_969_safe : Safe 7 6 s6_969 := by
  apply safe_succ 6 6 s6_969 [s7_570] (by decide) s6_969_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_570_safe
def s6_970 : State := ⟨[21,68,104,145], 44601830679448528859301379449314952935047446, 3, 0, 1, 0⟩
theorem s6_970_edges : next config 6 s6_970 = [] := by decide
theorem s6_970_safe : Safe 7 6 s6_970 := by
  apply safe_succ 6 6 s6_970 [] (by decide) s6_970_edges
  simp
def s6_971 : State := ⟨[21,86,82,145], 44601830679428167303741947887419311505211670, 3, 0, 1, 0⟩
theorem s6_971_edges : next config 6 s6_971 = [s7_549] := by decide
theorem s6_971_safe : Safe 7 6 s6_971 := by
  apply safe_succ 6 6 s6_971 [s7_549] (by decide) s6_971_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_549_safe
def s6_972 : State := ⟨[21,86,82,145], 44601830679428167304950799920057645841711382, 3, 0, 1, 0⟩
theorem s6_972_edges : next config 6 s6_972 = [s7_550] := by decide
theorem s6_972_safe : Safe 7 6 s6_972 := by
  apply safe_succ 6 6 s6_972 [s7_550] (by decide) s6_972_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_550_safe
def s6_973 : State := ⟨[21,100,104,145], 44601830679449796509901312530811270285426966, 3, 0, 1, 0⟩
theorem s6_973_edges : next config 6 s6_973 = [] := by decide
theorem s6_973_safe : Safe 7 6 s6_973 := by
  apply safe_succ 6 6 s6_973 [] (by decide) s6_973_edges
  simp
def s6_974 : State := ⟨[21,108,104,145], 44601830679773047412959511028192929602797846, 3, 0, 1, 0⟩
theorem s6_974_edges : next config 6 s6_974 = [s7_562] := by decide
theorem s6_974_safe : Safe 7 6 s6_974 := by
  apply safe_succ 6 6 s6_974 [s7_562] (by decide) s6_974_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_562_safe
def s6_975 : State := ⟨[22,21,64,145], 44601830679428167221534918366648232791179550, 3, 1, 1, 0⟩
theorem s6_975_edges : next config 6 s6_975 = [s7_747, s7_583] := by decide
theorem s6_975_safe : Safe 7 6 s6_975 := by
  apply safe_succ 6 6 s6_975 [s7_747, s7_583] (by decide) s6_975_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_747_safe
  · subst z; exact s7_583_safe
def s6_976 : State := ⟨[25,4,65,145], 44601830679428167221534955260136380239642902, 3, 2, 1, 0⟩
theorem s6_976_edges : next config 6 s6_976 = [s7_586] := by decide
theorem s6_976_safe : Safe 7 6 s6_976 := by
  apply safe_succ 6 6 s6_976 [s7_586] (by decide) s6_976_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_586_safe
def s6_977 : State := ⟨[25,4,66,145], 44601830679428167221534992153624527658746134, 3, 2, 1, 0⟩
theorem s6_977_edges : next config 6 s6_977 = [] := by decide
theorem s6_977_safe : Safe 7 6 s6_977 := by
  apply safe_succ 6 6 s6_977 [] (by decide) s6_977_edges
  simp
def s6_978 : State := ⟨[25,4,67,145], 44601830679428167221535065940600822494855454, 1, 1, 1, 0⟩
theorem s6_978_edges : next config 6 s6_978 = [] := by decide
theorem s6_978_safe : Safe 7 6 s6_978 := by
  apply safe_succ 6 6 s6_978 [] (by decide) s6_978_edges
  simp
def s6_979 : State := ⟨[25,4,96,145], 44601830679428246449697432630985826362392862, 1, 1, 1, 0⟩
theorem s6_979_edges : next config 6 s6_979 = [s7_588] := by decide
theorem s6_979_safe : Safe 7 6 s6_979 := by
  apply safe_succ 6 6 s6_979 [s7_588] (by decide) s6_979_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_588_safe
def s6_980 : State := ⟨[25,4,96,145], 44601830679428246449697432630985826364490006, 3, 2, 1, 0⟩
theorem s6_980_edges : next config 6 s6_980 = [s7_589] := by decide
theorem s6_980_safe : Safe 7 6 s6_980 := by
  apply safe_succ 6 6 s6_980 [s7_589] (by decide) s6_980_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_589_safe
def s6_981 : State := ⟨[25,4,96,145], 44601830679428246449697469524473973781496086, 1, 1, 1, 0⟩
theorem s6_981_edges : next config 6 s6_981 = [s7_590] := by decide
theorem s6_981_safe : Safe 7 6 s6_981 := by
  apply safe_succ 6 6 s6_981 [s7_590] (by decide) s6_981_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_590_safe
def s6_982 : State := ⟨[25,21,64,145], 44601830679428167221534918366648232820539678, 3, 1, 1, 0⟩
theorem s6_982_edges : next config 6 s6_982 = [s7_592] := by decide
theorem s6_982_safe : Safe 7 6 s6_982 := by
  apply safe_succ 6 6 s6_982 [s7_592] (by decide) s6_982_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_592_safe
def s6_983 : State := ⟨[25,21,64,145], 44601830679428167221534955260136380239642902, 3, 1, 1, 0⟩
theorem s6_983_edges : next config 6 s6_983 = [s7_593] := by decide
theorem s6_983_safe : Safe 7 6 s6_983 := by
  apply safe_succ 6 6 s6_983 [s7_593] (by decide) s6_983_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_593_safe
def s6_984 : State := ⟨[25,21,67,145], 44601830679428167221535102834088969916055830, 3, 0, 1, 0⟩
theorem s6_984_edges : next config 6 s6_984 = [] := by decide
theorem s6_984_safe : Safe 7 6 s6_984 := by
  apply safe_succ 6 6 s6_984 [] (by decide) s6_984_edges
  simp
def s6_985 : State := ⟨[25,21,67,145], 44601830679428167221535139727577117335159062, 3, 0, 1, 0⟩
theorem s6_985_edges : next config 6 s6_985 = [] := by decide
theorem s6_985_safe : Safe 7 6 s6_985 := by
  apply safe_succ 6 6 s6_985 [] (by decide) s6_985_edges
  simp
def s6_986 : State := ⟨[25,21,104,145], 44601830679448528859301084301409773615776022, 3, 0, 1, 0⟩
theorem s6_986_edges : next config 6 s6_986 = [] := by decide
theorem s6_986_safe : Safe 7 6 s6_986 := by
  apply safe_succ 6 6 s6_986 [] (by decide) s6_986_edges
  simp
def s6_987 : State := ⟨[29,4,64,145], 44601830679428167221534918366648233323856158, 1, 1, 1, 0⟩
theorem s6_987_edges : next config 6 s6_987 = [s7_595] := by decide
theorem s6_987_safe : Safe 7 6 s6_987 := by
  apply safe_succ 6 6 s6_987 [s7_595] (by decide) s6_987_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_595_safe
def s6_988 : State := ⟨[29,4,64,145], 44601830679428167221534918366648241913790742, 1, 1, 1, 0⟩
theorem s6_988_edges : next config 6 s6_988 = [s7_596] := by decide
theorem s6_988_safe : Safe 7 6 s6_988 := by
  apply safe_succ 6 6 s6_988 [s7_596] (by decide) s6_988_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_596_safe
def s6_989 : State := ⟨[29,4,64,145], 44601830679428167221534955260136380742959382, 1, 1, 1, 0⟩
theorem s6_989_edges : next config 6 s6_989 = [s7_597] := by decide
theorem s6_989_safe : Safe 7 6 s6_989 := by
  apply safe_succ 6 6 s6_989 [s7_597] (by decide) s6_989_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_597_safe
def s6_990 : State := ⟨[29,4,67,145], 44601830679428167221535102834088970419372310, 1, 0, 1, 0⟩
theorem s6_990_edges : next config 6 s6_990 = [] := by decide
theorem s6_990_safe : Safe 7 6 s6_990 := by
  apply safe_succ 6 6 s6_990 [] (by decide) s6_990_edges
  simp
def s6_991 : State := ⟨[29,4,67,145], 44601830679428167221535139727577117838475542, 1, 0, 1, 0⟩
theorem s6_991_edges : next config 6 s6_991 = [] := by decide
theorem s6_991_safe : Safe 7 6 s6_991 := by
  apply safe_succ 6 6 s6_991 [] (by decide) s6_991_edges
  simp
def s6_992 : State := ⟨[29,4,104,145], 44601830679448528859301084301409774119092502, 1, 0, 1, 0⟩
theorem s6_992_edges : next config 6 s6_992 = [] := by decide
theorem s6_992_safe : Safe 7 6 s6_992 := by
  apply safe_succ 6 6 s6_992 [] (by decide) s6_992_edges
  simp
def s6_993 : State := ⟨[33,4,64,145], 44601830679428167221534918366648241374826774, 3, 3, 1, 0⟩
theorem s6_993_edges : next config 6 s6_993 = [s7_611, s7_598] := by decide
theorem s6_993_safe : Safe 7 6 s6_993 := by
  apply safe_succ 6 6 s6_993 [s7_611, s7_598] (by decide) s6_993_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_611_safe
  · subst z; exact s7_598_safe
def s6_994 : State := ⟨[33,4,64,145], 44601830679428167221534918366648241376919830, 3, 3, 1, 0⟩
theorem s6_994_edges : next config 6 s6_994 = [s7_612, s7_604, s7_599] := by decide
theorem s6_994_safe : Safe 7 6 s6_994 := by
  apply safe_succ 6 6 s6_994 [s7_612, s7_604, s7_599] (by decide) s6_994_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_612_safe
  · subst z; exact s7_604_safe
  · subst z; exact s7_599_safe
def s6_995 : State := ⟨[33,4,96,145], 44602511244162088326624359380200698455068950, 3, 2, 1, 0⟩
theorem s6_995_edges : next config 6 s6_995 = [s7_644, s7_29, s7_600] := by decide
theorem s6_995_safe : Safe 7 6 s6_995 := by
  apply safe_succ 6 6 s6_995 [s7_644, s7_29, s7_600] (by decide) s6_995_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_644_safe
  · subst z; exact s7_29_safe
  · subst z; exact s7_600_safe
def s6_996 : State := ⟨[33,4,96,145], 66902575877958869591233150903634196424626454, 3, 2, 1, 0⟩
theorem s6_996_edges : next config 6 s6_996 = [s7_646, s7_35, s7_601] := by decide
theorem s6_996_safe : Safe 7 6 s6_996 := by
  apply safe_succ 6 6 s6_996 [s7_646, s7_35, s7_601] (by decide) s6_996_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_646_safe
  · subst z; exact s7_35_safe
  · subst z; exact s7_601_safe
def s6_997 : State := ⟨[33,4,96,163], 11692013100348635180313399141579848276086439874838, 3, 2, 1, 0⟩
theorem s6_997_edges : next config 6 s6_997 = [s7_54, s7_602] := by decide
theorem s6_997_safe : Safe 7 6 s6_997 := by
  apply safe_succ 6 6 s6_997 [s7_54, s7_602] (by decide) s6_997_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_54_safe
  · subst z; exact s7_602_safe
def s6_998 : State := ⟨[33,4,96,163], 14615016373649311549037014953158915885671232114966, 3, 2, 1, 0⟩
theorem s6_998_edges : next config 6 s6_998 = [s7_57, s7_603] := by decide
theorem s6_998_safe : Safe 7 6 s6_998 := by
  apply safe_succ 6 6 s6_998 [s7_57, s7_603] (by decide) s6_998_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_57_safe
  · subst z; exact s7_603_safe
def s6_999 : State := ⟨[33,4,104,129], 1020847121124453156574505327922694394134, 3, 2, 1, 0⟩
theorem s6_999_edges : next config 6 s6_999 = [s7_648, s7_66, s7_600] := by decide
theorem s6_999_safe : Safe 7 6 s6_999 := by
  apply safe_succ 6 6 s6_999 [s7_648, s7_66, s7_600] (by decide) s6_999_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_648_safe
  · subst z; exact s7_66_safe
  · subst z; exact s7_600_safe
def s6_1000 : State := ⟨[33,4,104,130], 1701411854966330083501254542786230817046, 3, 2, 1, 0⟩
theorem s6_1000_edges : next config 6 s6_1000 = [s7_931, s7_650, s7_74, s7_602] := by decide
theorem s6_1000_safe : Safe 7 6 s6_1000 := by
  apply safe_succ 6 6 s6_1000 [s7_931, s7_650, s7_74, s7_602] (by decide) s6_1000_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_931_safe
  · subst z; exact s7_650_safe
  · subst z; exact s7_74_safe
  · subst z; exact s7_602_safe
def s6_1001 : State := ⟨[33,4,104,132], 5784800258017591645061749831967449354518, 3, 2, 1, 0⟩
theorem s6_1001_edges : next config 6 s6_1001 = [s7_653, s7_88] := by decide
theorem s6_1001_safe : Safe 7 6 s6_1001 := by
  apply safe_succ 6 6 s6_1001 [s7_653, s7_88] (by decide) s6_1001_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_653_safe
  · subst z; exact s7_88_safe
def s6_1002 : State := ⟨[33,4,104,136], 87452568319042822876271655615591820103958, 3, 2, 1, 0⟩
theorem s6_1002_edges : next config 6 s6_1002 = [s7_655, s7_96] := by decide
theorem s6_1002_safe : Safe 7 6 s6_1002 := by
  apply safe_succ 6 6 s6_1002 [s7_655, s7_96] (by decide) s6_1002_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_655_safe
  · subst z; exact s7_96_safe
def s6_1003 : State := ⟨[33,4,104,136], 1481249143227206769222254047656114414223638, 3, 2, 1, 0⟩
theorem s6_1003_edges : next config 6 s6_1003 = [s7_657, s7_104] := by decide
theorem s6_1003_safe : Safe 7 6 s6_1003 := by
  apply safe_succ 6 6 s6_1003 [s7_657, s7_104] (by decide) s6_1003_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_657_safe
  · subst z; exact s7_104_safe
def s6_1004 : State := ⟨[33,4,104,140], 1394136857295446522575630148153581752094998, 3, 2, 1, 0⟩
theorem s6_1004_edges : next config 6 s6_1004 = [s7_659, s7_108] := by decide
theorem s6_1004_safe : Safe 7 6 s6_1004 := by
  apply safe_succ 6 6 s6_1004 [s7_659, s7_108] (by decide) s6_1004_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_659_safe
  · subst z; exact s7_108_safe
def s6_1005 : State := ⟨[33,4,104,144], 22301085480917905717765366028761420663951638, 3, 2, 1, 0⟩
theorem s6_1005_edges : next config 6 s6_1005 = [s7_661, s7_112] := by decide
theorem s6_1005_safe : Safe 7 6 s6_1005 := by
  apply safe_succ 6 6 s6_1005 [s7_661, s7_112] (by decide) s6_1005_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_661_safe
  · subst z; exact s7_112_safe
def s6_1006 : State := ⟨[33,4,104,145], 44601830679448528859301084301409782170059030, 1, 1, 1, 0⟩
theorem s6_1006_edges : next config 6 s6_1006 = [s7_663, s7_605] := by decide
theorem s6_1006_safe : Safe 7 6 s6_1006 := by
  apply safe_succ 6 6 s6_1006 [s7_663, s7_605] (by decide) s6_1006_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_663_safe
  · subst z; exact s7_605_safe
def s6_1007 : State := ⟨[33,4,104,160], 1461501637671185305486261062364039132715090514198, 3, 2, 1, 0⟩
theorem s6_1007_edges : next config 6 s6_1007 = [s7_665, s7_127] := by decide
theorem s6_1007_safe : Safe 7 6 s6_1007 := by
  apply safe_succ 6 6 s6_1007 [s7_665, s7_127] (by decide) s6_1007_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_665_safe
  · subst z; exact s7_127_safe
def s6_1008 : State := ⟨[33,4,104,161], 2923003275002088223689945895080322152371023057174, 3, 2, 1, 0⟩
theorem s6_1008_edges : next config 6 s6_1008 = [s7_666, s7_135, s7_603] := by decide
theorem s6_1008_safe : Safe 7 6 s6_1008 := by
  apply safe_succ 6 6 s6_1008 [s7_666, s7_135, s7_603] (by decide) s6_1008_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_666_safe
  · subst z; exact s7_135_safe
  · subst z; exact s7_603_safe
def s6_1009 : State := ⟨[33,4,104,171], 3004847366354037811681742346148179142955383539171606, 1, 0, 1, 0⟩
theorem s6_1009_edges : next config 6 s6_1009 = [s7_148] := by decide
theorem s6_1009_safe : Safe 7 6 s6_1009 := by
  apply safe_succ 6 6 s6_1009 [s7_148] (by decide) s6_1009_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_148_safe
def s6_1010 : State := ⟨[33,4,104,171], 3007770369627338488050465961959758210564968331411734, 1, 0, 1, 0⟩
theorem s6_1010_edges : next config 6 s6_1010 = [s7_151] := by decide
theorem s6_1010_safe : Safe 7 6 s6_1010 := by
  apply safe_succ 6 6 s6_1010 [s7_151] (by decide) s6_1010_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_151_safe
def s6_1011 : State := ⟨[33,4,104,192], 6277101735386680764176071810490242645750111557523192484118, 3, 2, 1, 0⟩
theorem s6_1011_edges : next config 6 s6_1011 = [s7_670, s7_153] := by decide
theorem s6_1011_safe : Safe 7 6 s6_1011 := by
  apply safe_succ 6 6 s6_1011 [s7_670, s7_153] (by decide) s6_1011_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_670_safe
  · subst z; exact s7_153_safe
def s6_1012 : State := ⟨[33,4,104,224], 26959946667150639794667015087359913060919720652188328594162768220438, 3, 2, 1, 0⟩
theorem s6_1012_edges : next config 6 s6_1012 = [s7_672, s7_189] := by decide
theorem s6_1012_safe : Safe 7 6 s6_1012 := by
  apply safe_succ 6 6 s6_1012 [s7_672, s7_189] (by decide) s6_1012_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_672_safe
  · subst z; exact s7_189_safe
def s6_1013 : State := ⟨[33,4,104,232], 6901746346790563787434755862277365734838391548400034311275583381770518, 3, 2, 1, 0⟩
theorem s6_1013_edges : next config 6 s6_1013 = [s7_674, s7_203] := by decide
theorem s6_1013_safe : Safe 7 6 s6_1013 := by
  apply safe_succ 6 6 s6_1013 [s7_674, s7_203] (by decide) s6_1013_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_674_safe
  · subst z; exact s7_203_safe
def s6_1014 : State := ⟨[33,12,96,145], 44601830679428246449697432630985834918777110, 3, 1, 1, 0⟩
theorem s6_1014_edges : next config 6 s6_1014 = [s7_681, s7_598, s7_605] := by decide
theorem s6_1014_safe : Safe 7 6 s6_1014 := by
  apply safe_succ 6 6 s6_1014 [s7_681, s7_598, s7_605] (by decide) s6_1014_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_681_safe
  · subst z; exact s7_598_safe
  · subst z; exact s7_605_safe
def s6_1015 : State := ⟨[33,12,104,145], 44602511244182370736228011050624645706354966, 3, 0, 1, 0⟩
theorem s6_1015_edges : next config 6 s6_1015 = [s7_683, s7_242, s7_600] := by decide
theorem s6_1015_safe : Safe 7 6 s6_1015 := by
  apply safe_succ 6 6 s6_1015 [s7_683, s7_242, s7_600] (by decide) s6_1015_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_683_safe
  · subst z; exact s7_242_safe
  · subst z; exact s7_600_safe
def s6_1016 : State := ⟨[33,12,104,145], 66902575877979152000836802574058143675912470, 3, 0, 1, 0⟩
theorem s6_1016_edges : next config 6 s6_1016 = [s7_685, s7_246, s7_601] := by decide
theorem s6_1016_safe : Safe 7 6 s6_1016 := by
  apply safe_succ 6 6 s6_1016 [s7_685, s7_246, s7_601] (by decide) s6_1016_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_685_safe
  · subst z; exact s7_246_safe
  · subst z; exact s7_601_safe
def s6_1017 : State := ⟨[33,12,104,163], 11692013100348635200595808745231518700033691160854, 3, 0, 1, 0⟩
theorem s6_1017_edges : next config 6 s6_1017 = [s7_263, s7_602] := by decide
theorem s6_1017_safe : Safe 7 6 s6_1017 := by
  apply safe_succ 6 6 s6_1017 [s7_263, s7_602] (by decide) s6_1017_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_263_safe
  · subst z; exact s7_602_safe
def s6_1018 : State := ⟨[33,12,104,163], 14615016373649311569319424556810586309618483400982, 3, 0, 1, 0⟩
theorem s6_1018_edges : next config 6 s6_1018 = [s7_266, s7_603] := by decide
theorem s6_1018_safe : Safe 7 6 s6_1018 := by
  apply safe_succ 6 6 s6_1018 [s7_266, s7_603] (by decide) s6_1018_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_266_safe
  · subst z; exact s7_603_safe
def s6_1019 : State := ⟨[33,21,96,145], 44601830679428246449697432630985834920870166, 3, 1, 1, 0⟩
theorem s6_1019_edges : next config 6 s6_1019 = [s7_688, s7_608, s7_607] := by decide
theorem s6_1019_safe : Safe 7 6 s6_1019 := by
  apply safe_succ 6 6 s6_1019 [s7_688, s7_608, s7_607] (by decide) s6_1019_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_688_safe
  · subst z; exact s7_608_safe
  · subst z; exact s7_607_safe
def s6_1020 : State := ⟨[33,29,64,145], 44601830679428167221534918366648241913790742, 3, 1, 1, 0⟩
theorem s6_1020_edges : next config 6 s6_1020 = [s7_690, s7_608] := by decide
theorem s6_1020_safe : Safe 7 6 s6_1020 := by
  apply safe_succ 6 6 s6_1020 [s7_690, s7_608] (by decide) s6_1020_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_690_safe
  · subst z; exact s7_608_safe
def s6_1021 : State := ⟨[35,4,64,145], 44602511244162009098461845115863130680922398, 3, 2, 1, 0⟩
theorem s6_1021_edges : next config 6 s6_1021 = [s7_643] := by decide
theorem s6_1021_safe : Safe 7 6 s6_1021 := by
  apply safe_succ 6 6 s6_1021 [s7_643] (by decide) s6_1021_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_643_safe
def s6_1022 : State := ⟨[35,4,64,145], 44602511244162009098461845115863139270856982, 3, 2, 1, 0⟩
theorem s6_1022_edges : next config 6 s6_1022 = [s7_644] := by decide
theorem s6_1022_safe : Safe 7 6 s6_1022 := by
  apply safe_succ 6 6 s6_1022 [s7_644] (by decide) s6_1022_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_644_safe
def s6_1023 : State := ⟨[35,4,64,145], 66902575877958790363070636639296628650479902, 3, 2, 1, 0⟩
theorem s6_1023_edges : next config 6 s6_1023 = [s7_645] := by decide
theorem s6_1023_safe : Safe 7 6 s6_1023 := by
  apply safe_succ 6 6 s6_1023 [s7_645] (by decide) s6_1023_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_645_safe
def s6_1024 : State := ⟨[35,4,64,145], 66902575877958790363070636639296637240414486, 3, 2, 1, 0⟩
theorem s6_1024_edges : next config 6 s6_1024 = [s7_646] := by decide
theorem s6_1024_safe : Safe 7 6 s6_1024 := by
  apply safe_succ 6 6 s6_1024 [s7_646] (by decide) s6_1024_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_646_safe
def s6_1025 : State := ⟨[35,4,67,128], 340282367000166626143659641727352901918, 3, 2, 0, 0⟩
theorem s6_1025_edges : next config 6 s6_1025 = [s7_635, s7_618, s7_639, s7_615, s7_620, s7_626, s7_632] := by decide
theorem s6_1025_safe : Safe 7 6 s6_1025 := by
  apply safe_succ 6 6 s6_1025 [s7_635, s7_618, s7_639, s7_615, s7_620, s7_626, s7_632] (by decide) s6_1025_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_635_safe
  · subst z; exact s7_618_safe
  · subst z; exact s7_639_safe
  · subst z; exact s7_615_safe
  · subst z; exact s7_620_safe
  · subst z; exact s7_626_safe
  · subst z; exact s7_632_safe
def s6_1026 : State := ⟨[35,4,67,128], 340282367000166626143659641735942836502, 3, 2, 0, 0⟩
theorem s6_1026_edges : next config 6 s6_1026 = [s7_636, s7_619, s7_640, s7_616, s7_621, s7_627, s7_633] := by decide
theorem s6_1026_safe : Safe 7 6 s6_1026 := by
  apply safe_succ 6 6 s6_1026 [s7_636, s7_619, s7_640, s7_616, s7_621, s7_627, s7_633] (by decide) s6_1026_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_636_safe
  · subst z; exact s7_619_safe
  · subst z; exact s7_640_safe
  · subst z; exact s7_616_safe
  · subst z; exact s7_621_safe
  · subst z; exact s7_627_safe
  · subst z; exact s7_633_safe
def s6_1027 : State := ⟨[35,4,67,129], 1020847100762815390556144518997345374494, 3, 2, 1, 0⟩
theorem s6_1027_edges : next config 6 s6_1027 = [s7_810, s7_630] := by decide
theorem s6_1027_safe : Safe 7 6 s6_1027 := by
  apply safe_succ 6 6 s6_1027 [s7_810, s7_630] (by decide) s6_1027_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_810_safe
  · subst z; exact s7_630_safe
def s6_1028 : State := ⟨[35,4,67,130], 1701411834604692317482893733860881797406, 3, 2, 1, 0⟩
theorem s6_1028_edges : next config 6 s6_1028 = [s7_812] := by decide
theorem s6_1028_safe : Safe 7 6 s6_1028 := by
  apply safe_succ 6 6 s6_1028 [s7_812] (by decide) s6_1028_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_812_safe
def s6_1029 : State := ⟨[35,4,67,131], 3062541302288446171336392163587954643230, 3, 2, 1, 0⟩
theorem s6_1029_edges : next config 6 s6_1029 = [s7_814] := by decide
theorem s6_1029_safe : Safe 7 6 s6_1029 := by
  apply safe_succ 6 6 s6_1029 [s7_814] (by decide) s6_1029_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_814_safe
def s6_1030 : State := ⟨[35,4,67,132], 5784800237655953879043389023042100334878, 3, 2, 1, 0⟩
theorem s6_1030_edges : next config 6 s6_1030 = [s7_816] := by decide
theorem s6_1030_safe : Safe 7 6 s6_1030 := by
  apply safe_succ 6 6 s6_1030 [s7_816] (by decide) s6_1030_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_816_safe
def s6_1031 : State := ⟨[35,4,67,136], 87452568298681185110253294806666471084318, 3, 2, 1, 0⟩
theorem s6_1031_edges : next config 6 s6_1031 = [s7_818] := by decide
theorem s6_1031_safe : Safe 7 6 s6_1031 := by
  apply safe_succ 6 6 s6_1031 [s7_818] (by decide) s6_1031_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_818_safe
def s6_1032 : State := ⟨[35,4,67,136], 1481249143206845131456235686847189065203998, 3, 2, 1, 0⟩
theorem s6_1032_edges : next config 6 s6_1032 = [s7_820] := by decide
theorem s6_1032_safe : Safe 7 6 s6_1032 := by
  apply safe_succ 6 6 s6_1032 [s7_820] (by decide) s6_1032_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_820_safe
def s6_1033 : State := ⟨[35,4,67,140], 1394136857275084884809611787344656403075358, 3, 2, 1, 0⟩
theorem s6_1033_edges : next config 6 s6_1033 = [s7_821] := by decide
theorem s6_1033_safe : Safe 7 6 s6_1033 := by
  apply safe_succ 6 6 s6_1033 [s7_821] (by decide) s6_1033_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_821_safe
def s6_1034 : State := ⟨[35,4,67,140], 1399581375145899128387540045401158238404894, 1, 0, 1, 0⟩
theorem s6_1034_edges : next config 6 s6_1034 = [] := by decide
theorem s6_1034_safe : Safe 7 6 s6_1034 := by
  apply safe_succ 6 6 s6_1034 [] (by decide) s6_1034_edges
  simp
def s6_1035 : State := ⟨[35,4,67,140], 1399581375145899128387540045401166828339478, 1, 0, 1, 0⟩
theorem s6_1035_edges : next config 6 s6_1035 = [] := by decide
theorem s6_1035_safe : Safe 7 6 s6_1035 := by
  apply safe_succ 6 6 s6_1035 [] (by decide) s6_1035_edges
  simp
def s6_1036 : State := ⟨[35,4,67,140], 1481249143206924359618749951184782609154334, 1, 0, 1, 0⟩
theorem s6_1036_edges : next config 6 s6_1036 = [] := by decide
theorem s6_1036_safe : Safe 7 6 s6_1036 := by
  apply safe_succ 6 6 s6_1036 [] (by decide) s6_1036_edges
  simp
def s6_1037 : State := ⟨[35,4,67,140], 1481249143206924359618749951184791199088918, 1, 0, 1, 0⟩
theorem s6_1037_edges : next config 6 s6_1037 = [] := by decide
theorem s6_1037_safe : Safe 7 6 s6_1037 := by
  apply safe_succ 6 6 s6_1037 [] (by decide) s6_1037_edges
  simp
def s6_1038 : State := ⟨[35,4,67,144], 22301085480897544079999347667952495314931998, 3, 2, 1, 0⟩
theorem s6_1038_edges : next config 6 s6_1038 = [s7_822] := by decide
theorem s6_1038_safe : Safe 7 6 s6_1038 := by
  apply safe_succ 6 6 s6_1038 [s7_822] (by decide) s6_1038_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_822_safe
def s6_1039 : State := ⟨[35,4,67,145], 44601830679428167221535065940600856821039390, 1, 1, 1, 0⟩
theorem s6_1039_edges : next config 6 s6_1039 = [s7_824, s7_704, s7_675] := by decide
theorem s6_1039_safe : Safe 7 6 s6_1039 := by
  apply safe_succ 6 6 s6_1039 [s7_824, s7_704, s7_675] (by decide) s6_1039_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_824_safe
  · subst z; exact s7_704_safe
  · subst z; exact s7_675_safe
def s6_1040 : State := ⟨[35,4,67,145], 44602511244162088326624506954153313901281566, 1, 0, 1, 0⟩
theorem s6_1040_edges : next config 6 s6_1040 = [s7_705, s7_676] := by decide
theorem s6_1040_safe : Safe 7 6 s6_1040 := by
  apply safe_succ 6 6 s6_1040 [s7_705, s7_676] (by decide) s6_1040_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_705_safe
  · subst z; exact s7_676_safe
def s6_1041 : State := ⟨[35,4,67,145], 44602511244162088326624506954153322491216150, 1, 0, 1, 0⟩
theorem s6_1041_edges : next config 6 s6_1041 = [s7_706, s7_677] := by decide
theorem s6_1041_safe : Safe 7 6 s6_1041 := by
  apply safe_succ 6 6 s6_1041 [s7_706, s7_677] (by decide) s6_1041_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_706_safe
  · subst z; exact s7_677_safe
def s6_1042 : State := ⟨[35,4,67,145], 66902575877958869591233298477586811870839070, 1, 0, 1, 0⟩
theorem s6_1042_edges : next config 6 s6_1042 = [s7_707, s7_678] := by decide
theorem s6_1042_safe : Safe 7 6 s6_1042 := by
  apply safe_succ 6 6 s6_1042 [s7_707, s7_678] (by decide) s6_1042_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_707_safe
  · subst z; exact s7_678_safe
def s6_1043 : State := ⟨[35,4,67,145], 66902575877958869591233298477586820460773654, 1, 0, 1, 0⟩
theorem s6_1043_edges : next config 6 s6_1043 = [s7_708, s7_679] := by decide
theorem s6_1043_safe : Safe 7 6 s6_1043 := by
  apply safe_succ 6 6 s6_1043 [s7_708, s7_679] (by decide) s6_1043_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_708_safe
  · subst z; exact s7_679_safe
def s6_1044 : State := ⟨[35,4,67,160], 1461501637671185285124623296345678323789741494558, 3, 2, 1, 0⟩
theorem s6_1044_edges : next config 6 s6_1044 = [s7_825] := by decide
theorem s6_1044_safe : Safe 7 6 s6_1044 := by
  apply safe_succ 6 6 s6_1044 [s7_825] (by decide) s6_1044_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_825_safe
def s6_1045 : State := ⟨[35,4,67,163], 11692013098987505712550417125359659461381269295390, 3, 2, 1, 0⟩
theorem s6_1045_edges : next config 6 s6_1045 = [s7_827] := by decide
theorem s6_1045_safe : Safe 7 6 s6_1045 := by
  apply safe_succ 6 6 s6_1045 [s7_827] (by decide) s6_1045_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_827_safe
def s6_1046 : State := ⟨[35,4,67,171], 2993155353341141744779906950675715183399609863045406, 1, 0, 1, 0⟩
theorem s6_1046_edges : next config 6 s6_1046 = [] := by decide
theorem s6_1046_safe : Safe 7 6 s6_1046 := by
  apply safe_succ 6 6 s6_1046 [] (by decide) s6_1046_edges
  simp
def s6_1047 : State := ⟨[35,4,67,171], 2993155353341141744779906950675715183399618452979990, 1, 0, 1, 0⟩
theorem s6_1047_edges : next config 6 s6_1047 = [] := by decide
theorem s6_1047_safe : Safe 7 6 s6_1047 := by
  apply safe_succ 6 6 s6_1047 [] (by decide) s6_1047_edges
  simp
def s6_1048 : State := ⟨[35,4,67,171], 3004847366352676682193776182690821548054324661256478, 1, 0, 1, 0⟩
theorem s6_1048_edges : next config 6 s6_1048 = [] := by decide
theorem s6_1048_safe : Safe 7 6 s6_1048 := by
  apply safe_succ 6 6 s6_1048 [] (by decide) s6_1048_edges
  simp
def s6_1049 : State := ⟨[35,4,67,171], 3004847366352676682193776182690821548054333251191062, 1, 0, 1, 0⟩
theorem s6_1049_edges : next config 6 s6_1049 = [] := by decide
theorem s6_1049_safe : Safe 7 6 s6_1049 := by
  apply safe_succ 6 6 s6_1049 [] (by decide) s6_1049_edges
  simp
def s6_1050 : State := ⟨[35,4,67,192], 6277101735386680764176071790128604879731750748597843464478, 3, 2, 1, 0⟩
theorem s6_1050_edges : next config 6 s6_1050 = [s7_830] := by decide
theorem s6_1050_safe : Safe 7 6 s6_1050 := by
  apply safe_succ 6 6 s6_1050 [s7_830] (by decide) s6_1050_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_830_safe
def s6_1051 : State := ⟨[35,4,67,195], 50216813883093446111026597752582269792448238859846085054750, 3, 2, 1, 0⟩
theorem s6_1051_edges : next config 6 s6_1051 = [s7_832] := by decide
theorem s6_1051_safe : Safe 7 6 s6_1051 := by
  apply safe_succ 6 6 s6_1051 [s7_832] (by decide) s6_1051_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_832_safe
def s6_1052 : State := ⟨[35,4,96,129], 1020847100842043552922834904001212911902, 3, 2, 1, 0⟩
theorem s6_1052_edges : next config 6 s6_1052 = [s7_613, s7_647, s7_643] := by decide
theorem s6_1052_safe : Safe 7 6 s6_1052 := by
  apply safe_succ 6 6 s6_1052 [s7_613, s7_647, s7_643] (by decide) s6_1052_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_613_safe
  · subst z; exact s7_647_safe
  · subst z; exact s7_643_safe
def s6_1053 : State := ⟨[35,4,96,129], 1020847100842043552922834904009802846486, 3, 2, 1, 0⟩
theorem s6_1053_edges : next config 6 s6_1053 = [s7_614, s7_648, s7_644] := by decide
theorem s6_1053_safe : Safe 7 6 s6_1053 := by
  apply safe_succ 6 6 s6_1053 [s7_614, s7_648, s7_644] (by decide) s6_1053_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_614_safe
  · subst z; exact s7_648_safe
  · subst z; exact s7_644_safe
def s6_1054 : State := ⟨[35,4,96,130], 1701411834683920479849584118864749334814, 3, 2, 1, 0⟩
theorem s6_1054_edges : next config 6 s6_1054 = [s7_615, s7_649] := by decide
theorem s6_1054_safe : Safe 7 6 s6_1054 := by
  apply safe_succ 6 6 s6_1054 [s7_615, s7_649] (by decide) s6_1054_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_615_safe
  · subst z; exact s7_649_safe
def s6_1055 : State := ⟨[35,4,96,130], 1701411834683920479849584118873339269398, 3, 2, 1, 0⟩
theorem s6_1055_edges : next config 6 s6_1055 = [s7_616, s7_650] := by decide
theorem s6_1055_safe : Safe 7 6 s6_1055 := by
  apply safe_succ 6 6 s6_1055 [s7_616, s7_650] (by decide) s6_1055_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_616_safe
  · subst z; exact s7_650_safe
def s6_1056 : State := ⟨[35,4,96,131], 3062541302367674333703082548591822180638, 3, 2, 1, 0⟩
theorem s6_1056_edges : next config 6 s6_1056 = [s7_617, s7_651] := by decide
theorem s6_1056_safe : Safe 7 6 s6_1056 := by
  apply safe_succ 6 6 s6_1056 [s7_617, s7_651] (by decide) s6_1056_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_617_safe
  · subst z; exact s7_651_safe
def s6_1057 : State := ⟨[35,4,96,132], 5784800237735182041410079408045967872286, 3, 2, 1, 0⟩
theorem s6_1057_edges : next config 6 s6_1057 = [s7_618, s7_652] := by decide
theorem s6_1057_safe : Safe 7 6 s6_1057 := by
  apply safe_succ 6 6 s6_1057 [s7_618, s7_652] (by decide) s6_1057_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_618_safe
  · subst z; exact s7_652_safe
def s6_1058 : State := ⟨[35,4,96,132], 5784800237735182041410079408054557806870, 3, 2, 1, 0⟩
theorem s6_1058_edges : next config 6 s6_1058 = [s7_619, s7_653] := by decide
theorem s6_1058_safe : Safe 7 6 s6_1058 := by
  apply safe_succ 6 6 s6_1058 [s7_619, s7_653] (by decide) s6_1058_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_619_safe
  · subst z; exact s7_653_safe
def s6_1059 : State := ⟨[35,4,96,136], 87452568298760413272619985191670338621726, 3, 2, 1, 0⟩
theorem s6_1059_edges : next config 6 s6_1059 = [s7_620, s7_654] := by decide
theorem s6_1059_safe : Safe 7 6 s6_1059 := by
  apply safe_succ 6 6 s6_1059 [s7_620, s7_654] (by decide) s6_1059_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_620_safe
  · subst z; exact s7_654_safe
def s6_1060 : State := ⟨[35,4,96,136], 87452568298760413272619985191678928556310, 3, 2, 1, 0⟩
theorem s6_1060_edges : next config 6 s6_1060 = [s7_621, s7_655] := by decide
theorem s6_1060_safe : Safe 7 6 s6_1060 := by
  apply safe_succ 6 6 s6_1060 [s7_621, s7_655] (by decide) s6_1060_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_621_safe
  · subst z; exact s7_655_safe
def s6_1061 : State := ⟨[35,4,96,136], 1481249143206924359618602377232192932741406, 3, 2, 1, 0⟩
theorem s6_1061_edges : next config 6 s6_1061 = [s7_622, s7_656] := by decide
theorem s6_1061_safe : Safe 7 6 s6_1061 := by
  apply safe_succ 6 6 s6_1061 [s7_622, s7_656] (by decide) s6_1061_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_622_safe
  · subst z; exact s7_656_safe
def s6_1062 : State := ⟨[35,4,96,136], 1481249143206924359618602377232201522675990, 3, 2, 1, 0⟩
theorem s6_1062_edges : next config 6 s6_1062 = [s7_623, s7_657] := by decide
theorem s6_1062_safe : Safe 7 6 s6_1062 := by
  apply safe_succ 6 6 s6_1062 [s7_623, s7_657] (by decide) s6_1062_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_623_safe
  · subst z; exact s7_657_safe
def s6_1063 : State := ⟨[35,4,96,140], 1394136857275164112971978477729660270612766, 3, 2, 1, 0⟩
theorem s6_1063_edges : next config 6 s6_1063 = [s7_624, s7_658] := by decide
theorem s6_1063_safe : Safe 7 6 s6_1063 := by
  apply safe_succ 6 6 s6_1063 [s7_624, s7_658] (by decide) s6_1063_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_624_safe
  · subst z; exact s7_658_safe
def s6_1064 : State := ⟨[35,4,96,140], 1394136857275164112971978477729668860547350, 3, 2, 1, 0⟩
theorem s6_1064_edges : next config 6 s6_1064 = [s7_625, s7_659] := by decide
theorem s6_1064_safe : Safe 7 6 s6_1064 := by
  apply safe_succ 6 6 s6_1064 [s7_625, s7_659] (by decide) s6_1064_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_625_safe
  · subst z; exact s7_659_safe
def s6_1065 : State := ⟨[35,4,96,144], 22301085480897623308161714358337499182469406, 3, 2, 1, 0⟩
theorem s6_1065_edges : next config 6 s6_1065 = [s7_626, s7_660] := by decide
theorem s6_1065_safe : Safe 7 6 s6_1065 := by
  apply safe_succ 6 6 s6_1065 [s7_626, s7_660] (by decide) s6_1065_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_626_safe
  · subst z; exact s7_660_safe
def s6_1066 : State := ⟨[35,4,96,144], 22301085480897623308161714358337507772403990, 3, 2, 1, 0⟩
theorem s6_1066_edges : next config 6 s6_1066 = [s7_627, s7_661] := by decide
theorem s6_1066_safe : Safe 7 6 s6_1066 := by
  apply safe_succ 6 6 s6_1066 [s7_627, s7_661] (by decide) s6_1066_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_627_safe
  · subst z; exact s7_661_safe
def s6_1067 : State := ⟨[35,4,96,145], 44601830679428246449697432630985860688576798, 1, 1, 1, 0⟩
theorem s6_1067_edges : next config 6 s6_1067 = [s7_724, s7_680, s7_628, s7_662] := by decide
theorem s6_1067_safe : Safe 7 6 s6_1067 := by
  apply safe_succ 6 6 s6_1067 [s7_724, s7_680, s7_628, s7_662] (by decide) s6_1067_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_724_safe
  · subst z; exact s7_680_safe
  · subst z; exact s7_628_safe
  · subst z; exact s7_662_safe
def s6_1068 : State := ⟨[35,4,96,145], 44601830679428246449697432630985869278511382, 1, 1, 1, 0⟩
theorem s6_1068_edges : next config 6 s6_1068 = [s7_725, s7_681, s7_629, s7_663] := by decide
theorem s6_1068_safe : Safe 7 6 s6_1068 := by
  apply safe_succ 6 6 s6_1068 [s7_725, s7_681, s7_629, s7_663] (by decide) s6_1068_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_725_safe
  · subst z; exact s7_681_safe
  · subst z; exact s7_629_safe
  · subst z; exact s7_663_safe
def s6_1069 : State := ⟨[35,4,96,160], 1461501637671185285203851458712368708793609031966, 3, 2, 1, 0⟩
theorem s6_1069_edges : next config 6 s6_1069 = [s7_632, s7_664] := by decide
theorem s6_1069_safe : Safe 7 6 s6_1069 := by
  apply safe_succ 6 6 s6_1069 [s7_632, s7_664] (by decide) s6_1069_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_632_safe
  · subst z; exact s7_664_safe
def s6_1070 : State := ⟨[35,4,96,160], 1461501637671185285203851458712368708802198966550, 3, 2, 1, 0⟩
theorem s6_1070_edges : next config 6 s6_1070 = [s7_633, s7_665] := by decide
theorem s6_1070_safe : Safe 7 6 s6_1070 := by
  apply safe_succ 6 6 s6_1070 [s7_633, s7_665] (by decide) s6_1070_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_633_safe
  · subst z; exact s7_665_safe
def s6_1071 : State := ⟨[35,4,96,161], 2923003275002088203407536291428651728458131509526, 3, 2, 1, 0⟩
theorem s6_1071_edges : next config 6 s6_1071 = [s7_634, s7_666] := by decide
theorem s6_1071_safe : Safe 7 6 s6_1071 := by
  apply safe_succ 6 6 s6_1071 [s7_634, s7_666] (by decide) s6_1071_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_634_safe
  · subst z; exact s7_666_safe
def s6_1072 : State := ⟨[35,4,96,163], 11692013098987505712629645287726349846385136832798, 3, 2, 1, 0⟩
theorem s6_1072_edges : next config 6 s6_1072 = [s7_635, s7_667] := by decide
theorem s6_1072_safe : Safe 7 6 s6_1072 := by
  apply safe_succ 6 6 s6_1072 [s7_635, s7_667] (by decide) s6_1072_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_635_safe
  · subst z; exact s7_667_safe
def s6_1073 : State := ⟨[35,4,96,163], 11692013098987505712629645287726349846393726767382, 3, 2, 1, 0⟩
theorem s6_1073_edges : next config 6 s6_1073 = [s7_636, s7_668] := by decide
theorem s6_1073_safe : Safe 7 6 s6_1073 := by
  apply safe_succ 6 6 s6_1073 [s7_636, s7_668] (by decide) s6_1073_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_636_safe
  · subst z; exact s7_668_safe
def s6_1074 : State := ⟨[35,4,96,192], 6277101735386680764176071790207833042098441133601711001886, 3, 2, 1, 0⟩
theorem s6_1074_edges : next config 6 s6_1074 = [s7_637, s7_669] := by decide
theorem s6_1074_safe : Safe 7 6 s6_1074 := by
  apply safe_succ 6 6 s6_1074 [s7_637, s7_669] (by decide) s6_1074_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_637_safe
  · subst z; exact s7_669_safe
def s6_1075 : State := ⟨[35,4,96,192], 6277101735386680764176071790207833042098441133610300936470, 3, 2, 1, 0⟩
theorem s6_1075_edges : next config 6 s6_1075 = [s7_638, s7_670] := by decide
theorem s6_1075_safe : Safe 7 6 s6_1075 := by
  apply safe_succ 6 6 s6_1075 [s7_638, s7_670] (by decide) s6_1075_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_638_safe
  · subst z; exact s7_670_safe
def s6_1076 : State := ⟨[35,4,96,224], 26959946667150639794667015087359913040637311048536658170241286738206, 3, 2, 1, 0⟩
theorem s6_1076_edges : next config 6 s6_1076 = [s7_641, s7_671] := by decide
theorem s6_1076_safe : Safe 7 6 s6_1076 := by
  apply safe_succ 6 6 s6_1076 [s7_641, s7_671] (by decide) s6_1076_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_641_safe
  · subst z; exact s7_671_safe
def s6_1077 : State := ⟨[35,4,96,224], 26959946667150639794667015087359913040637311048536658170249876672790, 3, 2, 1, 0⟩
theorem s6_1077_edges : next config 6 s6_1077 = [s7_642, s7_672] := by decide
theorem s6_1077_safe : Safe 7 6 s6_1077 := by
  apply safe_succ 6 6 s6_1077 [s7_642, s7_672] (by decide) s6_1077_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_642_safe
  · subst z; exact s7_672_safe
def s6_1078 : State := ⟨[35,4,104,128], 340282387282576229647756113084927775006, 3, 2, 0, 0⟩
theorem s6_1078_edges : next config 6 s6_1078 = [s7_667, s7_652, s7_673, s7_649, s7_654, s7_660, s7_664] := by decide
theorem s6_1078_safe : Safe 7 6 s6_1078 := by
  apply safe_succ 6 6 s6_1078 [s7_667, s7_652, s7_673, s7_649, s7_654, s7_660, s7_664] (by decide) s6_1078_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_667_safe
  · subst z; exact s7_652_safe
  · subst z; exact s7_673_safe
  · subst z; exact s7_649_safe
  · subst z; exact s7_654_safe
  · subst z; exact s7_660_safe
  · subst z; exact s7_664_safe
def s6_1079 : State := ⟨[35,4,104,128], 340282387282576229647756113093517709590, 3, 2, 0, 0⟩
theorem s6_1079_edges : next config 6 s6_1079 = [s7_668, s7_653, s7_674, s7_650, s7_655, s7_661, s7_665] := by decide
theorem s6_1079_safe : Safe 7 6 s6_1079 := by
  apply safe_succ 6 6 s6_1079 [s7_668, s7_653, s7_674, s7_650, s7_655, s7_661, s7_665] (by decide) s6_1079_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_668_safe
  · subst z; exact s7_653_safe
  · subst z; exact s7_674_safe
  · subst z; exact s7_650_safe
  · subst z; exact s7_655_safe
  · subst z; exact s7_661_safe
  · subst z; exact s7_665_safe
def s6_1080 : State := ⟨[35,4,104,140], 1399581375166181537991044141872515813277982, 1, 0, 1, 0⟩
theorem s6_1080_edges : next config 6 s6_1080 = [] := by decide
theorem s6_1080_safe : Safe 7 6 s6_1080 := by
  apply safe_succ 6 6 s6_1080 [] (by decide) s6_1080_edges
  simp
def s6_1081 : State := ⟨[35,4,104,140], 1399581375166181537991044141872524403212566, 1, 0, 1, 0⟩
theorem s6_1081_edges : next config 6 s6_1081 = [] := by decide
theorem s6_1081_safe : Safe 7 6 s6_1081 := by
  apply safe_succ 6 6 s6_1081 [] (by decide) s6_1081_edges
  simp
def s6_1082 : State := ⟨[35,4,104,140], 1481249143227206769222254047656140184027422, 1, 0, 1, 0⟩
theorem s6_1082_edges : next config 6 s6_1082 = [] := by decide
theorem s6_1082_safe : Safe 7 6 s6_1082 := by
  apply safe_succ 6 6 s6_1082 [] (by decide) s6_1082_edges
  simp
def s6_1083 : State := ⟨[35,4,104,140], 1481249143227206769222254047656148773962006, 1, 0, 1, 0⟩
theorem s6_1083_edges : next config 6 s6_1083 = [] := by decide
theorem s6_1083_safe : Safe 7 6 s6_1083 := by
  apply safe_succ 6 6 s6_1083 [] (by decide) s6_1083_edges
  simp
def s6_1084 : State := ⟨[35,4,104,145], 44602511244182370736228011050624671476154654, 1, 0, 1, 0⟩
theorem s6_1084_edges : next config 6 s6_1084 = [s7_726, s7_682] := by decide
theorem s6_1084_safe : Safe 7 6 s6_1084 := by
  apply safe_succ 6 6 s6_1084 [s7_726, s7_682] (by decide) s6_1084_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_726_safe
  · subst z; exact s7_682_safe
def s6_1085 : State := ⟨[35,4,104,145], 44602511244182370736228011050624680066089238, 1, 0, 1, 0⟩
theorem s6_1085_edges : next config 6 s6_1085 = [s7_727, s7_683] := by decide
theorem s6_1085_safe : Safe 7 6 s6_1085 := by
  apply safe_succ 6 6 s6_1085 [s7_727, s7_683] (by decide) s6_1085_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_727_safe
  · subst z; exact s7_683_safe
def s6_1086 : State := ⟨[35,4,104,145], 66902575877979152000836802574058169445712158, 1, 0, 1, 0⟩
theorem s6_1086_edges : next config 6 s6_1086 = [s7_728, s7_684] := by decide
theorem s6_1086_safe : Safe 7 6 s6_1086 := by
  apply safe_succ 6 6 s6_1086 [s7_728, s7_684] (by decide) s6_1086_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_728_safe
  · subst z; exact s7_684_safe
def s6_1087 : State := ⟨[35,4,104,145], 66902575877979152000836802574058178035646742, 1, 0, 1, 0⟩
theorem s6_1087_edges : next config 6 s6_1087 = [s7_729, s7_685] := by decide
theorem s6_1087_safe : Safe 7 6 s6_1087 := by
  apply safe_succ 6 6 s6_1087 [s7_729, s7_685] (by decide) s6_1087_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_729_safe
  · subst z; exact s7_685_safe
def s6_1088 : State := ⟨[35,4,104,171], 2993155353341141744800189360279219279870967437918494, 1, 0, 1, 0⟩
theorem s6_1088_edges : next config 6 s6_1088 = [] := by decide
theorem s6_1088_safe : Safe 7 6 s6_1088 := by
  apply safe_succ 6 6 s6_1088 [] (by decide) s6_1088_edges
  simp
def s6_1089 : State := ⟨[35,4,104,171], 2993155353341141744800189360279219279870976027853078, 1, 0, 1, 0⟩
theorem s6_1089_edges : next config 6 s6_1089 = [] := by decide
theorem s6_1089_safe : Safe 7 6 s6_1089 := by
  apply safe_succ 6 6 s6_1089 [] (by decide) s6_1089_edges
  simp
def s6_1090 : State := ⟨[35,4,104,171], 3004847366352676682214058592294325644525682236129566, 1, 0, 1, 0⟩
theorem s6_1090_edges : next config 6 s6_1090 = [] := by decide
theorem s6_1090_safe : Safe 7 6 s6_1090 := by
  apply safe_succ 6 6 s6_1090 [] (by decide) s6_1090_edges
  simp
def s6_1091 : State := ⟨[35,4,104,171], 3004847366352676682214058592294325644525690826064150, 1, 0, 1, 0⟩
theorem s6_1091_edges : next config 6 s6_1091 = [] := by decide
theorem s6_1091_safe : Safe 7 6 s6_1091 := by
  apply safe_succ 6 6 s6_1091 [] (by decide) s6_1091_edges
  simp
def s6_1092 : State := ⟨[35,12,64,145], 44601830679428167221534918366648267144630558, 3, 1, 1, 0⟩
theorem s6_1092_edges : next config 6 s6_1092 = [s7_609, s7_680] := by decide
theorem s6_1092_safe : Safe 7 6 s6_1092 := by
  apply safe_succ 6 6 s6_1092 [s7_609, s7_680] (by decide) s6_1092_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_609_safe
  · subst z; exact s7_680_safe
def s6_1093 : State := ⟨[35,12,64,145], 44601830679428167221534918366648275734565142, 3, 1, 1, 0⟩
theorem s6_1093_edges : next config 6 s6_1093 = [s7_611, s7_681] := by decide
theorem s6_1093_safe : Safe 7 6 s6_1093 := by
  apply safe_succ 6 6 s6_1093 [s7_611, s7_681] (by decide) s6_1093_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_611_safe
  · subst z; exact s7_681_safe
def s6_1094 : State := ⟨[35,12,67,129], 1020847100842043553070408856590889324830, 3, 0, 1, 0⟩
theorem s6_1094_edges : next config 6 s6_1094 = [s7_613, s7_676] := by decide
theorem s6_1094_safe : Safe 7 6 s6_1094 := by
  apply safe_succ 6 6 s6_1094 [s7_613, s7_676] (by decide) s6_1094_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_613_safe
  · subst z; exact s7_676_safe
def s6_1095 : State := ⟨[35,12,67,129], 1020847100842043553070408856599479259414, 3, 0, 1, 0⟩
theorem s6_1095_edges : next config 6 s6_1095 = [s7_614, s7_677] := by decide
theorem s6_1095_safe : Safe 7 6 s6_1095 := by
  apply safe_succ 6 6 s6_1095 [s7_614, s7_677] (by decide) s6_1095_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_614_safe
  · subst z; exact s7_677_safe
def s6_1096 : State := ⟨[35,12,67,130], 1701411834683920479997158071454425747742, 3, 0, 1, 0⟩
theorem s6_1096_edges : next config 6 s6_1096 = [s7_615] := by decide
theorem s6_1096_safe : Safe 7 6 s6_1096 := by
  apply safe_succ 6 6 s6_1096 [s7_615] (by decide) s6_1096_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_615_safe
def s6_1097 : State := ⟨[35,12,67,130], 1701411834683920479997158071463015682326, 3, 0, 1, 0⟩
theorem s6_1097_edges : next config 6 s6_1097 = [s7_616] := by decide
theorem s6_1097_safe : Safe 7 6 s6_1097 := by
  apply safe_succ 6 6 s6_1097 [s7_616] (by decide) s6_1097_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_616_safe
def s6_1098 : State := ⟨[35,12,67,131], 3062541302367674333850656501181498593566, 3, 0, 1, 0⟩
theorem s6_1098_edges : next config 6 s6_1098 = [s7_617] := by decide
theorem s6_1098_safe : Safe 7 6 s6_1098 := by
  apply safe_succ 6 6 s6_1098 [s7_617] (by decide) s6_1098_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_617_safe
def s6_1099 : State := ⟨[35,12,67,132], 5784800237735182041557653360635644285214, 3, 0, 1, 0⟩
theorem s6_1099_edges : next config 6 s6_1099 = [s7_618] := by decide
theorem s6_1099_safe : Safe 7 6 s6_1099 := by
  apply safe_succ 6 6 s6_1099 [s7_618] (by decide) s6_1099_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_618_safe
def s6_1100 : State := ⟨[35,12,67,132], 5784800237735182041557653360644234219798, 3, 0, 1, 0⟩
theorem s6_1100_edges : next config 6 s6_1100 = [s7_619] := by decide
theorem s6_1100_safe : Safe 7 6 s6_1100 := by
  apply safe_succ 6 6 s6_1100 [s7_619] (by decide) s6_1100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_619_safe
def s6_1101 : State := ⟨[35,12,67,136], 87452568298760413272767559144260015034654, 3, 0, 1, 0⟩
theorem s6_1101_edges : next config 6 s6_1101 = [s7_620] := by decide
theorem s6_1101_safe : Safe 7 6 s6_1101 := by
  apply safe_succ 6 6 s6_1101 [s7_620] (by decide) s6_1101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_620_safe
def s6_1102 : State := ⟨[35,12,67,136], 87452568298760413272767559144268604969238, 3, 0, 1, 0⟩
theorem s6_1102_edges : next config 6 s6_1102 = [s7_621] := by decide
theorem s6_1102_safe : Safe 7 6 s6_1102 := by
  apply safe_succ 6 6 s6_1102 [s7_621] (by decide) s6_1102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_621_safe
def s6_1103 : State := ⟨[35,12,67,140], 1394136857275164112972126051682249947025694, 3, 0, 1, 0⟩
theorem s6_1103_edges : next config 6 s6_1103 = [s7_624] := by decide
theorem s6_1103_safe : Safe 7 6 s6_1103 := by
  apply safe_succ 6 6 s6_1103 [s7_624] (by decide) s6_1103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_624_safe
def s6_1104 : State := ⟨[35,12,67,140], 1394136857275164112972126051682258536960278, 3, 0, 1, 0⟩
theorem s6_1104_edges : next config 6 s6_1104 = [s7_625] := by decide
theorem s6_1104_safe : Safe 7 6 s6_1104 := by
  apply safe_succ 6 6 s6_1104 [s7_625] (by decide) s6_1104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_625_safe
def s6_1105 : State := ⟨[35,12,67,144], 22301085480897623308161861932290088858882334, 3, 0, 1, 0⟩
theorem s6_1105_edges : next config 6 s6_1105 = [s7_626] := by decide
theorem s6_1105_safe : Safe 7 6 s6_1105 := by
  apply safe_succ 6 6 s6_1105 [s7_626] (by decide) s6_1105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_626_safe
def s6_1106 : State := ⟨[35,12,67,144], 22301085480897623308161861932290097448816918, 3, 0, 1, 0⟩
theorem s6_1106_edges : next config 6 s6_1106 = [s7_627] := by decide
theorem s6_1106_safe : Safe 7 6 s6_1106 := by
  apply safe_succ 6 6 s6_1106 [s7_627] (by decide) s6_1106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_627_safe
def s6_1107 : State := ⟨[35,12,67,145], 44602511244162009098461992689815720357335326, 3, 0, 1, 0⟩
theorem s6_1107_edges : next config 6 s6_1107 = [s7_837, s7_630] := by decide
theorem s6_1107_safe : Safe 7 6 s6_1107 := by
  apply safe_succ 6 6 s6_1107 [s7_837, s7_630] (by decide) s6_1107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_837_safe
  · subst z; exact s7_630_safe
def s6_1108 : State := ⟨[35,12,67,145], 66902575877958790363070784213249218326892830, 3, 0, 1, 0⟩
theorem s6_1108_edges : next config 6 s6_1108 = [s7_838, s7_631] := by decide
theorem s6_1108_safe : Safe 7 6 s6_1108 := by
  apply safe_succ 6 6 s6_1108 [s7_838, s7_631] (by decide) s6_1108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_838_safe
  · subst z; exact s7_631_safe
def s6_1109 : State := ⟨[35,12,67,160], 1461501637671185285203851458859942661383285444894, 3, 0, 1, 0⟩
theorem s6_1109_edges : next config 6 s6_1109 = [s7_632] := by decide
theorem s6_1109_safe : Safe 7 6 s6_1109 := by
  apply safe_succ 6 6 s6_1109 [s7_632] (by decide) s6_1109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_632_safe
def s6_1110 : State := ⟨[35,12,67,160], 1461501637671185285203851458859942661391875379478, 3, 0, 1, 0⟩
theorem s6_1110_edges : next config 6 s6_1110 = [s7_633] := by decide
theorem s6_1110_safe : Safe 7 6 s6_1110 := by
  apply safe_succ 6 6 s6_1110 [s7_633] (by decide) s6_1110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_633_safe
def s6_1111 : State := ⟨[35,12,67,161], 2923003275002088203407536291576225681047807922454, 3, 0, 1, 0⟩
theorem s6_1111_edges : next config 6 s6_1111 = [s7_634] := by decide
theorem s6_1111_safe : Safe 7 6 s6_1111 := by
  apply safe_succ 6 6 s6_1111 [s7_634] (by decide) s6_1111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_634_safe
def s6_1112 : State := ⟨[35,12,67,163], 11692013098987505712629645287873923798974813245726, 3, 0, 1, 0⟩
theorem s6_1112_edges : next config 6 s6_1112 = [s7_635] := by decide
theorem s6_1112_safe : Safe 7 6 s6_1112 := by
  apply safe_succ 6 6 s6_1112 [s7_635] (by decide) s6_1112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_635_safe
def s6_1113 : State := ⟨[35,12,67,163], 11692013098987505712629645287873923798983403180310, 3, 0, 1, 0⟩
theorem s6_1113_edges : next config 6 s6_1113 = [s7_636] := by decide
theorem s6_1113_safe : Safe 7 6 s6_1113 := by
  apply safe_succ 6 6 s6_1113 [s7_636] (by decide) s6_1113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_636_safe
def s6_1114 : State := ⟨[35,12,67,192], 6277101735386680764176071790207833042246015086191387414814, 3, 0, 1, 0⟩
theorem s6_1114_edges : next config 6 s6_1114 = [s7_637] := by decide
theorem s6_1114_safe : Safe 7 6 s6_1114 := by
  apply safe_succ 6 6 s6_1114 [s7_637] (by decide) s6_1114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_637_safe
def s6_1115 : State := ⟨[35,12,67,192], 6277101735386680764176071790207833042246015086199977349398, 3, 0, 1, 0⟩
theorem s6_1115_edges : next config 6 s6_1115 = [s7_638] := by decide
theorem s6_1115_safe : Safe 7 6 s6_1115 := by
  apply safe_succ 6 6 s6_1115 [s7_638] (by decide) s6_1115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_638_safe
def s6_1116 : State := ⟨[35,12,67,195], 50216813883093446111026597752661497954962503197439629005086, 3, 0, 1, 0⟩
theorem s6_1116_edges : next config 6 s6_1116 = [s7_639] := by decide
theorem s6_1116_safe : Safe 7 6 s6_1116 := by
  apply safe_succ 6 6 s6_1116 [s7_639] (by decide) s6_1116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_639_safe
def s6_1117 : State := ⟨[35,12,67,195], 50216813883093446111026597752661497954962503197448218939670, 3, 0, 1, 0⟩
theorem s6_1117_edges : next config 6 s6_1117 = [s7_640] := by decide
theorem s6_1117_safe : Safe 7 6 s6_1117 := by
  apply safe_succ 6 6 s6_1117 [s7_640] (by decide) s6_1117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_640_safe
def s6_1118 : State := ⟨[35,12,67,224], 26959946667150639794667015087359913040637311048684232122830963151134, 3, 0, 1, 0⟩
theorem s6_1118_edges : next config 6 s6_1118 = [s7_641] := by decide
theorem s6_1118_safe : Safe 7 6 s6_1118 := by
  apply safe_succ 6 6 s6_1118 [s7_641] (by decide) s6_1118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_641_safe
def s6_1119 : State := ⟨[35,12,67,224], 26959946667150639794667015087359913040637311048684232122839553085718, 3, 0, 1, 0⟩
theorem s6_1119_edges : next config 6 s6_1119 = [s7_642] := by decide
theorem s6_1119_safe : Safe 7 6 s6_1119 := by
  apply safe_succ 6 6 s6_1119 [s7_642] (by decide) s6_1119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_642_safe
def s6_1120 : State := ⟨[35,12,96,145], 44602511244162088326624359380200724224872734, 3, 0, 1, 0⟩
theorem s6_1120_edges : next config 6 s6_1120 = [s7_643, s7_676, s7_682] := by decide
theorem s6_1120_safe : Safe 7 6 s6_1120 := by
  apply safe_succ 6 6 s6_1120 [s7_643, s7_676, s7_682] (by decide) s6_1120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_643_safe
  · subst z; exact s7_676_safe
  · subst z; exact s7_682_safe
def s6_1121 : State := ⟨[35,12,96,145], 44602511244162088326624359380200732814807318, 3, 0, 1, 0⟩
theorem s6_1121_edges : next config 6 s6_1121 = [s7_644, s7_677, s7_683] := by decide
theorem s6_1121_safe : Safe 7 6 s6_1121 := by
  apply safe_succ 6 6 s6_1121 [s7_644, s7_677, s7_683] (by decide) s6_1121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_644_safe
  · subst z; exact s7_677_safe
  · subst z; exact s7_683_safe
def s6_1122 : State := ⟨[35,12,96,145], 66902575877958869591233150903634222194430238, 3, 0, 1, 0⟩
theorem s6_1122_edges : next config 6 s6_1122 = [s7_645, s7_678, s7_684] := by decide
theorem s6_1122_safe : Safe 7 6 s6_1122 := by
  apply safe_succ 6 6 s6_1122 [s7_645, s7_678, s7_684] (by decide) s6_1122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_645_safe
  · subst z; exact s7_678_safe
  · subst z; exact s7_684_safe
def s6_1123 : State := ⟨[35,12,96,145], 66902575877958869591233150903634230784364822, 3, 0, 1, 0⟩
theorem s6_1123_edges : next config 6 s6_1123 = [s7_646, s7_679, s7_685] := by decide
theorem s6_1123_safe : Safe 7 6 s6_1123 := by
  apply safe_succ 6 6 s6_1123 [s7_646, s7_679, s7_685] (by decide) s6_1123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_646_safe
  · subst z; exact s7_679_safe
  · subst z; exact s7_685_safe
def s6_1124 : State := ⟨[35,12,104,129], 1020847121124453156574505327948464197918, 3, 0, 1, 0⟩
theorem s6_1124_edges : next config 6 s6_1124 = [s7_647, s7_682] := by decide
theorem s6_1124_safe : Safe 7 6 s6_1124 := by
  apply safe_succ 6 6 s6_1124 [s7_647, s7_682] (by decide) s6_1124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_647_safe
  · subst z; exact s7_682_safe
def s6_1125 : State := ⟨[35,12,104,129], 1020847121124453156574505327957054132502, 3, 0, 1, 0⟩
theorem s6_1125_edges : next config 6 s6_1125 = [s7_648, s7_683] := by decide
theorem s6_1125_safe : Safe 7 6 s6_1125 := by
  apply safe_succ 6 6 s6_1125 [s7_648, s7_683] (by decide) s6_1125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_648_safe
  · subst z; exact s7_683_safe
def s6_1126 : State := ⟨[35,12,104,130], 1701411854966330083501254542812000620830, 3, 0, 1, 0⟩
theorem s6_1126_edges : next config 6 s6_1126 = [s7_649] := by decide
theorem s6_1126_safe : Safe 7 6 s6_1126 := by
  apply safe_succ 6 6 s6_1126 [s7_649] (by decide) s6_1126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_649_safe
def s6_1127 : State := ⟨[35,12,104,130], 1701411854966330083501254542820590555414, 3, 0, 1, 0⟩
theorem s6_1127_edges : next config 6 s6_1127 = [s7_650] := by decide
theorem s6_1127_safe : Safe 7 6 s6_1127 := by
  apply safe_succ 6 6 s6_1127 [s7_650] (by decide) s6_1127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_650_safe
def s6_1128 : State := ⟨[35,12,104,131], 3062541322650083937354752972539073466654, 3, 0, 1, 0⟩
theorem s6_1128_edges : next config 6 s6_1128 = [s7_651] := by decide
theorem s6_1128_safe : Safe 7 6 s6_1128 := by
  apply safe_succ 6 6 s6_1128 [s7_651] (by decide) s6_1128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_651_safe
def s6_1129 : State := ⟨[35,12,104,132], 5784800258017591645061749831993219158302, 3, 0, 1, 0⟩
theorem s6_1129_edges : next config 6 s6_1129 = [s7_652] := by decide
theorem s6_1129_safe : Safe 7 6 s6_1129 := by
  apply safe_succ 6 6 s6_1129 [s7_652] (by decide) s6_1129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_652_safe
def s6_1130 : State := ⟨[35,12,104,132], 5784800258017591645061749832001809092886, 3, 0, 1, 0⟩
theorem s6_1130_edges : next config 6 s6_1130 = [s7_653] := by decide
theorem s6_1130_safe : Safe 7 6 s6_1130 := by
  apply safe_succ 6 6 s6_1130 [s7_653] (by decide) s6_1130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_653_safe
def s6_1131 : State := ⟨[35,12,104,136], 87452568319042822876271655615617589907742, 3, 0, 1, 0⟩
theorem s6_1131_edges : next config 6 s6_1131 = [s7_654] := by decide
theorem s6_1131_safe : Safe 7 6 s6_1131 := by
  apply safe_succ 6 6 s6_1131 [s7_654] (by decide) s6_1131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_654_safe
def s6_1132 : State := ⟨[35,12,104,136], 87452568319042822876271655615626179842326, 3, 0, 1, 0⟩
theorem s6_1132_edges : next config 6 s6_1132 = [s7_655] := by decide
theorem s6_1132_safe : Safe 7 6 s6_1132 := by
  apply safe_succ 6 6 s6_1132 [s7_655] (by decide) s6_1132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_655_safe
def s6_1133 : State := ⟨[35,12,104,140], 1394136857295446522575630148153607521898782, 3, 0, 1, 0⟩
theorem s6_1133_edges : next config 6 s6_1133 = [s7_658] := by decide
theorem s6_1133_safe : Safe 7 6 s6_1133 := by
  apply safe_succ 6 6 s6_1133 [s7_658] (by decide) s6_1133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_658_safe
def s6_1134 : State := ⟨[35,12,104,140], 1394136857295446522575630148153616111833366, 3, 0, 1, 0⟩
theorem s6_1134_edges : next config 6 s6_1134 = [s7_659] := by decide
theorem s6_1134_safe : Safe 7 6 s6_1134 := by
  apply safe_succ 6 6 s6_1134 [s7_659] (by decide) s6_1134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_659_safe
def s6_1135 : State := ⟨[35,12,104,144], 22301085480917905717765366028761446433755422, 3, 0, 1, 0⟩
theorem s6_1135_edges : next config 6 s6_1135 = [s7_660] := by decide
theorem s6_1135_safe : Safe 7 6 s6_1135 := by
  apply safe_succ 6 6 s6_1135 [s7_660] (by decide) s6_1135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_660_safe
def s6_1136 : State := ⟨[35,12,104,144], 22301085480917905717765366028761455023690006, 3, 0, 1, 0⟩
theorem s6_1136_edges : next config 6 s6_1136 = [s7_661] := by decide
theorem s6_1136_safe : Safe 7 6 s6_1136 := by
  apply safe_succ 6 6 s6_1136 [s7_661] (by decide) s6_1136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_661_safe
def s6_1137 : State := ⟨[35,12,104,160], 1461501637671185305486261062364039132740860317982, 3, 0, 1, 0⟩
theorem s6_1137_edges : next config 6 s6_1137 = [s7_664] := by decide
theorem s6_1137_safe : Safe 7 6 s6_1137 := by
  apply safe_succ 6 6 s6_1137 [s7_664] (by decide) s6_1137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_664_safe
def s6_1138 : State := ⟨[35,12,104,160], 1461501637671185305486261062364039132749450252566, 3, 0, 1, 0⟩
theorem s6_1138_edges : next config 6 s6_1138 = [s7_665] := by decide
theorem s6_1138_safe : Safe 7 6 s6_1138 := by
  apply safe_succ 6 6 s6_1138 [s7_665] (by decide) s6_1138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_665_safe
def s6_1139 : State := ⟨[35,12,104,161], 2923003275002088223689945895080322152405382795542, 3, 0, 1, 0⟩
theorem s6_1139_edges : next config 6 s6_1139 = [s7_666] := by decide
theorem s6_1139_safe : Safe 7 6 s6_1139 := by
  apply safe_succ 6 6 s6_1139 [s7_666] (by decide) s6_1139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_666_safe
def s6_1140 : State := ⟨[35,12,104,163], 11692013098987505732912054891378020270332388118814, 3, 0, 1, 0⟩
theorem s6_1140_edges : next config 6 s6_1140 = [s7_667] := by decide
theorem s6_1140_safe : Safe 7 6 s6_1140 := by
  apply safe_succ 6 6 s6_1140 [s7_667] (by decide) s6_1140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_667_safe
def s6_1141 : State := ⟨[35,12,104,163], 11692013098987505732912054891378020270340978053398, 3, 0, 1, 0⟩
theorem s6_1141_edges : next config 6 s6_1141 = [s7_668] := by decide
theorem s6_1141_safe : Safe 7 6 s6_1141 := by
  apply safe_succ 6 6 s6_1141 [s7_668] (by decide) s6_1141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_668_safe
def s6_1142 : State := ⟨[35,12,104,192], 6277101735386680764176071810490242645750111557548962287902, 3, 0, 1, 0⟩
theorem s6_1142_edges : next config 6 s6_1142 = [s7_669] := by decide
theorem s6_1142_safe : Safe 7 6 s6_1142 := by
  apply safe_succ 6 6 s6_1142 [s7_669] (by decide) s6_1142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_669_safe
def s6_1143 : State := ⟨[35,12,104,192], 6277101735386680764176071810490242645750111557557552222486, 3, 0, 1, 0⟩
theorem s6_1143_edges : next config 6 s6_1143 = [s7_670] := by decide
theorem s6_1143_safe : Safe 7 6 s6_1143 := by
  apply safe_succ 6 6 s6_1143 [s7_670] (by decide) s6_1143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_670_safe
def s6_1144 : State := ⟨[35,12,104,224], 26959946667150639794667015087359913060919720652188328594188538024222, 3, 0, 1, 0⟩
theorem s6_1144_edges : next config 6 s6_1144 = [s7_671] := by decide
theorem s6_1144_safe : Safe 7 6 s6_1144 := by
  apply safe_succ 6 6 s6_1144 [s7_671] (by decide) s6_1144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_671_safe
def s6_1145 : State := ⟨[35,12,104,224], 26959946667150639794667015087359913060919720652188328594197127958806, 3, 0, 1, 0⟩
theorem s6_1145_edges : next config 6 s6_1145 = [s7_672] := by decide
theorem s6_1145_safe : Safe 7 6 s6_1145 := by
  apply safe_succ 6 6 s6_1145 [s7_672] (by decide) s6_1145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_672_safe
def s6_1146 : State := ⟨[35,12,104,232], 6901746346790563787434755862277365734838391548400034311275609151574302, 3, 0, 1, 0⟩
theorem s6_1146_edges : next config 6 s6_1146 = [s7_673] := by decide
theorem s6_1146_safe : Safe 7 6 s6_1146 := by
  apply safe_succ 6 6 s6_1146 [s7_673] (by decide) s6_1146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_673_safe
def s6_1147 : State := ⟨[35,12,104,232], 6901746346790563787434755862277365734838391548400034311275617741508886, 3, 0, 1, 0⟩
theorem s6_1147_edges : next config 6 s6_1147 = [s7_674] := by decide
theorem s6_1147_safe : Safe 7 6 s6_1147 := by
  apply safe_succ 6 6 s6_1147 [s7_674] (by decide) s6_1147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_674_safe
def s6_1148 : State := ⟨[35,21,64,145], 44601830679428167221534918366648267146723614, 3, 1, 1, 0⟩
theorem s6_1148_edges : next config 6 s6_1148 = [s7_748, s7_730, s7_691, s7_689, s7_687] := by decide
theorem s6_1148_safe : Safe 7 6 s6_1148 := by
  apply safe_succ 6 6 s6_1148 [s7_748, s7_730, s7_691, s7_689, s7_687] (by decide) s6_1148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_748_safe
  · subst z; exact s7_730_safe
  · subst z; exact s7_691_safe
  · subst z; exact s7_689_safe
  · subst z; exact s7_687_safe
def s6_1149 : State := ⟨[35,21,64,145], 44601830679428167221534918366648275736658198, 3, 1, 1, 0⟩
theorem s6_1149_edges : next config 6 s6_1149 = [s7_749, s7_731, s7_692, s7_690, s7_688] := by decide
theorem s6_1149_safe : Safe 7 6 s6_1149 := by
  apply safe_succ 6 6 s6_1149 [s7_749, s7_731, s7_692, s7_690, s7_688] (by decide) s6_1149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_749_safe
  · subst z; exact s7_731_safe
  · subst z; exact s7_692_safe
  · subst z; exact s7_690_safe
  · subst z; exact s7_688_safe
def s6_1150 : State := ⟨[35,140,67,136], 1481249143206924359618749951184782609154334, 3, 0, 1, 0⟩
theorem s6_1150_edges : next config 6 s6_1150 = [s7_622] := by decide
theorem s6_1150_safe : Safe 7 6 s6_1150 := by
  apply safe_succ 6 6 s6_1150 [s7_622] (by decide) s6_1150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_622_safe
def s6_1151 : State := ⟨[35,140,67,136], 1481249143206924359618749951184791199088918, 3, 0, 1, 0⟩
theorem s6_1151_edges : next config 6 s6_1151 = [s7_623] := by decide
theorem s6_1151_safe : Safe 7 6 s6_1151 := by
  apply safe_succ 6 6 s6_1151 [s7_623] (by decide) s6_1151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_623_safe
def s6_1152 : State := ⟨[35,140,104,136], 1481249143227206769222254047656140184027422, 3, 0, 1, 0⟩
theorem s6_1152_edges : next config 6 s6_1152 = [s7_656] := by decide
theorem s6_1152_safe : Safe 7 6 s6_1152 := by
  apply safe_succ 6 6 s6_1152 [s7_656] (by decide) s6_1152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_656_safe
def s6_1153 : State := ⟨[35,140,104,136], 1481249143227206769222254047656148773962006, 3, 0, 1, 0⟩
theorem s6_1153_edges : next config 6 s6_1153 = [s7_657] := by decide
theorem s6_1153_safe : Safe 7 6 s6_1153 := by
  apply safe_succ 6 6 s6_1153 [s7_657] (by decide) s6_1153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_657_safe
def s6_1154 : State := ⟨[43,4,64,145], 44601830679428167221534918366657063237648670, 1, 1, 1, 0⟩
theorem s6_1154_edges : next config 6 s6_1154 = [s7_724] := by decide
theorem s6_1154_safe : Safe 7 6 s6_1154 := by
  apply safe_succ 6 6 s6_1154 [s7_724] (by decide) s6_1154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_724_safe
def s6_1155 : State := ⟨[43,4,64,145], 44601830679428167221534918366657071827583254, 1, 1, 1, 0⟩
theorem s6_1155_edges : next config 6 s6_1155 = [s7_725] := by decide
theorem s6_1155_safe : Safe 7 6 s6_1155 := by
  apply safe_succ 6 6 s6_1155 [s7_725] (by decide) s6_1155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_725_safe
def s6_1156 : State := ⟨[43,4,67,128], 340282387282576229795330074470697206046, 1, 0, 0, 0⟩
theorem s6_1156_edges : next config 6 s6_1156 = [s7_714, s7_698, s7_718, s7_695, s7_700, s7_702, s7_709] := by decide
theorem s6_1156_safe : Safe 7 6 s6_1156 := by
  apply safe_succ 6 6 s6_1156 [s7_714, s7_698, s7_718, s7_695, s7_700, s7_702, s7_709] (by decide) s6_1156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_714_safe
  · subst z; exact s7_698_safe
  · subst z; exact s7_718_safe
  · subst z; exact s7_695_safe
  · subst z; exact s7_700_safe
  · subst z; exact s7_702_safe
  · subst z; exact s7_709_safe
def s6_1157 : State := ⟨[43,4,67,128], 340282387282576229795330074479287140630, 1, 0, 0, 0⟩
theorem s6_1157_edges : next config 6 s6_1157 = [s7_715, s7_699, s7_719, s7_696, s7_701, s7_703, s7_710] := by decide
theorem s6_1157_safe : Safe 7 6 s6_1157 := by
  apply safe_succ 6 6 s6_1157 [s7_715, s7_699, s7_719, s7_696, s7_701, s7_703, s7_710] (by decide) s6_1157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_715_safe
  · subst z; exact s7_699_safe
  · subst z; exact s7_719_safe
  · subst z; exact s7_696_safe
  · subst z; exact s7_701_safe
  · subst z; exact s7_703_safe
  · subst z; exact s7_710_safe
def s6_1158 : State := ⟨[43,4,67,129], 1020847100842043553070408865386982342942, 1, 0, 1, 0⟩
theorem s6_1158_edges : next config 6 s6_1158 = [s7_848, s7_705] := by decide
theorem s6_1158_safe : Safe 7 6 s6_1158 := by
  apply safe_succ 6 6 s6_1158 [s7_848, s7_705] (by decide) s6_1158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_848_safe
  · subst z; exact s7_705_safe
def s6_1159 : State := ⟨[43,4,67,129], 1020847100842043553070408865395572277526, 1, 0, 1, 0⟩
theorem s6_1159_edges : next config 6 s6_1159 = [s7_849, s7_706] := by decide
theorem s6_1159_safe : Safe 7 6 s6_1159 := by
  apply safe_succ 6 6 s6_1159 [s7_849, s7_706] (by decide) s6_1159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_849_safe
  · subst z; exact s7_706_safe
def s6_1160 : State := ⟨[43,4,67,130], 1701411834683920479997158080250518765854, 1, 0, 1, 0⟩
theorem s6_1160_edges : next config 6 s6_1160 = [s7_850] := by decide
theorem s6_1160_safe : Safe 7 6 s6_1160 := by
  apply safe_succ 6 6 s6_1160 [s7_850] (by decide) s6_1160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_850_safe
def s6_1161 : State := ⟨[43,4,67,130], 1701411834683920479997158080259108700438, 1, 0, 1, 0⟩
theorem s6_1161_edges : next config 6 s6_1161 = [s7_851] := by decide
theorem s6_1161_safe : Safe 7 6 s6_1161 := by
  apply safe_succ 6 6 s6_1161 [s7_851] (by decide) s6_1161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_851_safe
def s6_1162 : State := ⟨[43,4,67,131], 3062541302367674333850656509977591611678, 1, 0, 1, 0⟩
theorem s6_1162_edges : next config 6 s6_1162 = [s7_852] := by decide
theorem s6_1162_safe : Safe 7 6 s6_1162 := by
  apply safe_succ 6 6 s6_1162 [s7_852] (by decide) s6_1162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_852_safe
def s6_1163 : State := ⟨[43,4,67,132], 5784800237735182041557653369431737303326, 1, 0, 1, 0⟩
theorem s6_1163_edges : next config 6 s6_1163 = [s7_853] := by decide
theorem s6_1163_safe : Safe 7 6 s6_1163 := by
  apply safe_succ 6 6 s6_1163 [s7_853] (by decide) s6_1163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_853_safe
def s6_1164 : State := ⟨[43,4,67,132], 5784800237735182041557653369440327237910, 1, 0, 1, 0⟩
theorem s6_1164_edges : next config 6 s6_1164 = [s7_854] := by decide
theorem s6_1164_safe : Safe 7 6 s6_1164 := by
  apply safe_succ 6 6 s6_1164 [s7_854] (by decide) s6_1164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_854_safe
def s6_1165 : State := ⟨[43,4,67,136], 87452568298760413272767559153056108052766, 1, 0, 1, 0⟩
theorem s6_1165_edges : next config 6 s6_1165 = [s7_855] := by decide
theorem s6_1165_safe : Safe 7 6 s6_1165 := by
  apply safe_succ 6 6 s6_1165 [s7_855] (by decide) s6_1165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_855_safe
def s6_1166 : State := ⟨[43,4,67,136], 87452568298760413272767559153064697987350, 1, 0, 1, 0⟩
theorem s6_1166_edges : next config 6 s6_1166 = [s7_856] := by decide
theorem s6_1166_safe : Safe 7 6 s6_1166 := by
  apply safe_succ 6 6 s6_1166 [s7_856] (by decide) s6_1166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_856_safe
def s6_1167 : State := ⟨[43,4,67,144], 22301085480897623308161861932298884951900446, 1, 0, 1, 0⟩
theorem s6_1167_edges : next config 6 s6_1167 = [s7_859] := by decide
theorem s6_1167_safe : Safe 7 6 s6_1167 := by
  apply safe_succ 6 6 s6_1167 [s7_859] (by decide) s6_1167_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_859_safe
def s6_1168 : State := ⟨[43,4,67,144], 22301085480897623308161861932298893541835030, 1, 0, 1, 0⟩
theorem s6_1168_edges : next config 6 s6_1168 = [s7_860] := by decide
theorem s6_1168_safe : Safe 7 6 s6_1168 := by
  apply safe_succ 6 6 s6_1168 [s7_860] (by decide) s6_1168_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_860_safe
def s6_1169 : State := ⟨[43,4,67,145], 44602511244162009098461992689824516450353438, 1, 0, 1, 0⟩
theorem s6_1169_edges : next config 6 s6_1169 = [s7_861] := by decide
theorem s6_1169_safe : Safe 7 6 s6_1169 := by
  apply safe_succ 6 6 s6_1169 [s7_861] (by decide) s6_1169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_861_safe
def s6_1170 : State := ⟨[43,4,67,145], 66902575877958790363070784213258014419910942, 1, 0, 1, 0⟩
theorem s6_1170_edges : next config 6 s6_1170 = [s7_863] := by decide
theorem s6_1170_safe : Safe 7 6 s6_1170 := by
  apply safe_succ 6 6 s6_1170 [s7_863] (by decide) s6_1170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_863_safe
def s6_1171 : State := ⟨[43,4,67,160], 1461501637671185285203851458859942670179378463006, 1, 0, 1, 0⟩
theorem s6_1171_edges : next config 6 s6_1171 = [s7_865] := by decide
theorem s6_1171_safe : Safe 7 6 s6_1171 := by
  apply safe_succ 6 6 s6_1171 [s7_865] (by decide) s6_1171_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_865_safe
def s6_1172 : State := ⟨[43,4,67,160], 1461501637671185285203851458859942670187968397590, 1, 0, 1, 0⟩
theorem s6_1172_edges : next config 6 s6_1172 = [s7_866] := by decide
theorem s6_1172_safe : Safe 7 6 s6_1172 := by
  apply safe_succ 6 6 s6_1172 [s7_866] (by decide) s6_1172_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_866_safe
def s6_1173 : State := ⟨[43,4,67,161], 2923003275002088203407536291576225689843900940566, 1, 0, 1, 0⟩
theorem s6_1173_edges : next config 6 s6_1173 = [s7_867] := by decide
theorem s6_1173_safe : Safe 7 6 s6_1173 := by
  apply safe_succ 6 6 s6_1173 [s7_867] (by decide) s6_1173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_867_safe
def s6_1174 : State := ⟨[43,4,67,163], 11692013098987505712629645287873923807770906263838, 1, 0, 1, 0⟩
theorem s6_1174_edges : next config 6 s6_1174 = [s7_868] := by decide
theorem s6_1174_safe : Safe 7 6 s6_1174 := by
  apply safe_succ 6 6 s6_1174 [s7_868] (by decide) s6_1174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_868_safe
def s6_1175 : State := ⟨[43,4,67,163], 11692013098987505712629645287873923807779496198422, 1, 0, 1, 0⟩
theorem s6_1175_edges : next config 6 s6_1175 = [s7_869] := by decide
theorem s6_1175_safe : Safe 7 6 s6_1175 := by
  apply safe_succ 6 6 s6_1175 [s7_869] (by decide) s6_1175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_869_safe
def s6_1176 : State := ⟨[43,4,67,171], 2993155353254029458848146704029091283905873293934878, 1, 0, 1, 0⟩
theorem s6_1176_edges : next config 6 s6_1176 = [s7_870] := by decide
theorem s6_1176_safe : Safe 7 6 s6_1176 := by
  apply safe_succ 6 6 s6_1176 [s7_870] (by decide) s6_1176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_870_safe
def s6_1177 : State := ⟨[43,4,67,171], 2993155353254029458848146704029091283905881883869462, 1, 0, 1, 0⟩
theorem s6_1177_edges : next config 6 s6_1177 = [s7_871] := by decide
theorem s6_1177_safe : Safe 7 6 s6_1177 := by
  apply safe_succ 6 6 s6_1177 [s7_871] (by decide) s6_1177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_871_safe
def s6_1178 : State := ⟨[43,4,67,192], 6277101735386680764176071790207833042246015094987480432926, 1, 0, 1, 0⟩
theorem s6_1178_edges : next config 6 s6_1178 = [s7_876] := by decide
theorem s6_1178_safe : Safe 7 6 s6_1178 := by
  apply safe_succ 6 6 s6_1178 [s7_876] (by decide) s6_1178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_876_safe
def s6_1179 : State := ⟨[43,4,67,192], 6277101735386680764176071790207833042246015094996070367510, 1, 0, 1, 0⟩
theorem s6_1179_edges : next config 6 s6_1179 = [s7_877] := by decide
theorem s6_1179_safe : Safe 7 6 s6_1179 := by
  apply safe_succ 6 6 s6_1179 [s7_877] (by decide) s6_1179_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_877_safe
def s6_1180 : State := ⟨[43,4,67,195], 50216813883093446111026597752661497954962503206235722023198, 1, 0, 1, 0⟩
theorem s6_1180_edges : next config 6 s6_1180 = [s7_878] := by decide
theorem s6_1180_safe : Safe 7 6 s6_1180 := by
  apply safe_succ 6 6 s6_1180 [s7_878] (by decide) s6_1180_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_878_safe
def s6_1181 : State := ⟨[43,4,67,195], 50216813883093446111026597752661497954962503206244311957782, 1, 0, 1, 0⟩
theorem s6_1181_edges : next config 6 s6_1181 = [s7_879] := by decide
theorem s6_1181_safe : Safe 7 6 s6_1181 := by
  apply safe_succ 6 6 s6_1181 [s7_879] (by decide) s6_1181_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_879_safe
def s6_1182 : State := ⟨[43,4,67,224], 26959946667150639794667015087359913040637311048684232131627056169246, 1, 0, 1, 0⟩
theorem s6_1182_edges : next config 6 s6_1182 = [s7_880] := by decide
theorem s6_1182_safe : Safe 7 6 s6_1182 := by
  apply safe_succ 6 6 s6_1182 [s7_880] (by decide) s6_1182_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_880_safe
def s6_1183 : State := ⟨[43,4,67,224], 26959946667150639794667015087359913040637311048684232131635646103830, 1, 0, 1, 0⟩
theorem s6_1183_edges : next config 6 s6_1183 = [s7_881] := by decide
theorem s6_1183_safe : Safe 7 6 s6_1183 := by
  apply safe_succ 6 6 s6_1183 [s7_881] (by decide) s6_1183_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_881_safe
def s6_1184 : State := ⟨[43,4,96,145], 44602511244162088326624359380209520317890846, 1, 0, 1, 0⟩
theorem s6_1184_edges : next config 6 s6_1184 = [s7_726] := by decide
theorem s6_1184_safe : Safe 7 6 s6_1184 := by
  apply safe_succ 6 6 s6_1184 [s7_726] (by decide) s6_1184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_726_safe
def s6_1185 : State := ⟨[43,4,96,145], 44602511244162088326624359380209528907825430, 1, 0, 1, 0⟩
theorem s6_1185_edges : next config 6 s6_1185 = [s7_727] := by decide
theorem s6_1185_safe : Safe 7 6 s6_1185 := by
  apply safe_succ 6 6 s6_1185 [s7_727] (by decide) s6_1185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_727_safe
def s6_1186 : State := ⟨[43,4,96,145], 66902575877958869591233150903643018287448350, 1, 0, 1, 0⟩
theorem s6_1186_edges : next config 6 s6_1186 = [s7_728] := by decide
theorem s6_1186_safe : Safe 7 6 s6_1186 := by
  apply safe_succ 6 6 s6_1186 [s7_728] (by decide) s6_1186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_728_safe
def s6_1187 : State := ⟨[43,4,96,145], 66902575877958869591233150903643026877382934, 1, 0, 1, 0⟩
theorem s6_1187_edges : next config 6 s6_1187 = [s7_729] := by decide
theorem s6_1187_safe : Safe 7 6 s6_1187 := by
  apply safe_succ 6 6 s6_1187 [s7_729] (by decide) s6_1187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_729_safe
def s6_1188 : State := ⟨[43,4,104,129], 1020847121124453156574505336744557216030, 1, 0, 1, 0⟩
theorem s6_1188_edges : next config 6 s6_1188 = [s7_693, s7_726] := by decide
theorem s6_1188_safe : Safe 7 6 s6_1188 := by
  apply safe_succ 6 6 s6_1188 [s7_693, s7_726] (by decide) s6_1188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_693_safe
  · subst z; exact s7_726_safe
def s6_1189 : State := ⟨[43,4,104,129], 1020847121124453156574505336753147150614, 1, 0, 1, 0⟩
theorem s6_1189_edges : next config 6 s6_1189 = [s7_694, s7_727] := by decide
theorem s6_1189_safe : Safe 7 6 s6_1189 := by
  apply safe_succ 6 6 s6_1189 [s7_694, s7_727] (by decide) s6_1189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_694_safe
  · subst z; exact s7_727_safe
def s6_1190 : State := ⟨[43,4,104,130], 1701411854966330083501254551608093638942, 1, 0, 1, 0⟩
theorem s6_1190_edges : next config 6 s6_1190 = [s7_695] := by decide
theorem s6_1190_safe : Safe 7 6 s6_1190 := by
  apply safe_succ 6 6 s6_1190 [s7_695] (by decide) s6_1190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_695_safe
def s6_1191 : State := ⟨[43,4,104,130], 1701411854966330083501254551616683573526, 1, 0, 1, 0⟩
theorem s6_1191_edges : next config 6 s6_1191 = [s7_696] := by decide
theorem s6_1191_safe : Safe 7 6 s6_1191 := by
  apply safe_succ 6 6 s6_1191 [s7_696] (by decide) s6_1191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_696_safe
def s6_1192 : State := ⟨[43,4,104,131], 3062541322650083937354752981335166484766, 1, 0, 1, 0⟩
theorem s6_1192_edges : next config 6 s6_1192 = [s7_697] := by decide
theorem s6_1192_safe : Safe 7 6 s6_1192 := by
  apply safe_succ 6 6 s6_1192 [s7_697] (by decide) s6_1192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_697_safe
def s6_1193 : State := ⟨[43,4,104,132], 5784800258017591645061749840789312176414, 1, 0, 1, 0⟩
theorem s6_1193_edges : next config 6 s6_1193 = [s7_698] := by decide
theorem s6_1193_safe : Safe 7 6 s6_1193 := by
  apply safe_succ 6 6 s6_1193 [s7_698] (by decide) s6_1193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_698_safe
def s6_1194 : State := ⟨[43,4,104,132], 5784800258017591645061749840797902110998, 1, 0, 1, 0⟩
theorem s6_1194_edges : next config 6 s6_1194 = [s7_699] := by decide
theorem s6_1194_safe : Safe 7 6 s6_1194 := by
  apply safe_succ 6 6 s6_1194 [s7_699] (by decide) s6_1194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_699_safe
def s6_1195 : State := ⟨[43,4,104,136], 87452568319042822876271655624413682925854, 1, 0, 1, 0⟩
theorem s6_1195_edges : next config 6 s6_1195 = [s7_700] := by decide
theorem s6_1195_safe : Safe 7 6 s6_1195 := by
  apply safe_succ 6 6 s6_1195 [s7_700] (by decide) s6_1195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_700_safe
def s6_1196 : State := ⟨[43,4,104,136], 87452568319042822876271655624422272860438, 1, 0, 1, 0⟩
theorem s6_1196_edges : next config 6 s6_1196 = [s7_701] := by decide
theorem s6_1196_safe : Safe 7 6 s6_1196 := by
  apply safe_succ 6 6 s6_1196 [s7_701] (by decide) s6_1196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_701_safe
def s6_1197 : State := ⟨[43,4,104,144], 22301085480917905717765366028770242526773534, 1, 0, 1, 0⟩
theorem s6_1197_edges : next config 6 s6_1197 = [s7_702] := by decide
theorem s6_1197_safe : Safe 7 6 s6_1197 := by
  apply safe_succ 6 6 s6_1197 [s7_702] (by decide) s6_1197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_702_safe
def s6_1198 : State := ⟨[43,4,104,144], 22301085480917905717765366028770251116708118, 1, 0, 1, 0⟩
theorem s6_1198_edges : next config 6 s6_1198 = [s7_703] := by decide
theorem s6_1198_safe : Safe 7 6 s6_1198 := by
  apply safe_succ 6 6 s6_1198 [s7_703] (by decide) s6_1198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_703_safe
def s6_1199 : State := ⟨[43,4,104,160], 1461501637671185305486261062364039141536953336094, 1, 0, 1, 0⟩
theorem s6_1199_edges : next config 6 s6_1199 = [s7_709] := by decide
theorem s6_1199_safe : Safe 7 6 s6_1199 := by
  apply safe_succ 6 6 s6_1199 [s7_709] (by decide) s6_1199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_709_safe
def s6_1200 : State := ⟨[43,4,104,160], 1461501637671185305486261062364039141545543270678, 1, 0, 1, 0⟩
theorem s6_1200_edges : next config 6 s6_1200 = [s7_710] := by decide
theorem s6_1200_safe : Safe 7 6 s6_1200 := by
  apply safe_succ 6 6 s6_1200 [s7_710] (by decide) s6_1200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_710_safe
def s6_1201 : State := ⟨[43,4,104,161], 2923003275002088223689945895080322161201475813654, 1, 0, 1, 0⟩
theorem s6_1201_edges : next config 6 s6_1201 = [s7_711] := by decide
theorem s6_1201_safe : Safe 7 6 s6_1201 := by
  apply safe_succ 6 6 s6_1201 [s7_711] (by decide) s6_1201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_711_safe
def s6_1202 : State := ⟨[43,4,104,163], 11692013098987505732912054891378020279128481136926, 1, 0, 1, 0⟩
theorem s6_1202_edges : next config 6 s6_1202 = [s7_712] := by decide
theorem s6_1202_safe : Safe 7 6 s6_1202 := by
  apply safe_succ 6 6 s6_1202 [s7_712] (by decide) s6_1202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_712_safe
def s6_1203 : State := ⟨[43,4,104,163], 11692013098987505732912054891378020279137071071510, 1, 0, 1, 0⟩
theorem s6_1203_edges : next config 6 s6_1203 = [s7_713] := by decide
theorem s6_1203_safe : Safe 7 6 s6_1203 := by
  apply safe_succ 6 6 s6_1203 [s7_713] (by decide) s6_1203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_713_safe
def s6_1204 : State := ⟨[43,4,104,171], 2993155353254029458868429113632595380377230868807966, 1, 0, 1, 0⟩
theorem s6_1204_edges : next config 6 s6_1204 = [s7_714] := by decide
theorem s6_1204_safe : Safe 7 6 s6_1204 := by
  apply safe_succ 6 6 s6_1204 [s7_714] (by decide) s6_1204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_714_safe
def s6_1205 : State := ⟨[43,4,104,171], 2993155353254029458868429113632595380377239458742550, 1, 0, 1, 0⟩
theorem s6_1205_edges : next config 6 s6_1205 = [s7_715] := by decide
theorem s6_1205_safe : Safe 7 6 s6_1205 := by
  apply safe_succ 6 6 s6_1205 [s7_715] (by decide) s6_1205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_715_safe
def s6_1206 : State := ⟨[43,4,104,192], 6277101735386680764176071810490242645750111566345055306014, 1, 0, 1, 0⟩
theorem s6_1206_edges : next config 6 s6_1206 = [s7_716] := by decide
theorem s6_1206_safe : Safe 7 6 s6_1206 := by
  apply safe_succ 6 6 s6_1206 [s7_716] (by decide) s6_1206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_716_safe
def s6_1207 : State := ⟨[43,4,104,192], 6277101735386680764176071810490242645750111566353645240598, 1, 0, 1, 0⟩
theorem s6_1207_edges : next config 6 s6_1207 = [s7_717] := by decide
theorem s6_1207_safe : Safe 7 6 s6_1207 := by
  apply safe_succ 6 6 s6_1207 [s7_717] (by decide) s6_1207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_717_safe
def s6_1208 : State := ⟨[43,4,104,224], 26959946667150639794667015087359913060919720652188328602984631042334, 1, 0, 1, 0⟩
theorem s6_1208_edges : next config 6 s6_1208 = [s7_720] := by decide
theorem s6_1208_safe : Safe 7 6 s6_1208 := by
  apply safe_succ 6 6 s6_1208 [s7_720] (by decide) s6_1208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_720_safe
def s6_1209 : State := ⟨[43,4,104,224], 26959946667150639794667015087359913060919720652188328602993220976918, 1, 0, 1, 0⟩
theorem s6_1209_edges : next config 6 s6_1209 = [s7_721] := by decide
theorem s6_1209_safe : Safe 7 6 s6_1209 := by
  apply safe_succ 6 6 s6_1209 [s7_721] (by decide) s6_1209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_721_safe
def s6_1210 : State := ⟨[43,4,104,232], 6901746346790563787434755862277365734838391548400034311284405244592414, 1, 0, 1, 0⟩
theorem s6_1210_edges : next config 6 s6_1210 = [s7_722] := by decide
theorem s6_1210_safe : Safe 7 6 s6_1210 := by
  apply safe_succ 6 6 s6_1210 [s7_722] (by decide) s6_1210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_722_safe
def s6_1211 : State := ⟨[43,4,104,232], 6901746346790563787434755862277365734838391548400034311284413834526998, 1, 0, 1, 0⟩
theorem s6_1211_edges : next config 6 s6_1211 = [s7_723] := by decide
theorem s6_1211_safe : Safe 7 6 s6_1211 := by
  apply safe_succ 6 6 s6_1211 [s7_723] (by decide) s6_1211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_723_safe
def s6_1212 : State := ⟨[49,4,67,145], 44601830679428167221535065941163772414722334, 1, 1, 1, 0⟩
theorem s6_1212_edges : next config 6 s6_1212 = [s7_737] := by decide
theorem s6_1212_safe : Safe 7 6 s6_1212 := by
  apply safe_succ 6 6 s6_1212 [s7_737] (by decide) s6_1212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_737_safe
def s6_1213 : State := ⟨[49,4,96,145], 44601830679428246449697432631548776282259742, 1, 1, 1, 0⟩
theorem s6_1213_edges : next config 6 s6_1213 = [s7_738, s7_734] := by decide
theorem s6_1213_safe : Safe 7 6 s6_1213 := by
  apply safe_succ 6 6 s6_1213 [s7_738, s7_734] (by decide) s6_1213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_738_safe
  · subst z; exact s7_734_safe
def s6_1214 : State := ⟨[49,4,96,145], 44601830679428246449697432631548776282263830, 3, 2, 1, 0⟩
theorem s6_1214_edges : next config 6 s6_1214 = [s7_735] := by decide
theorem s6_1214_safe : Safe 7 6 s6_1214 := by
  apply safe_succ 6 6 s6_1214 [s7_735] (by decide) s6_1214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_735_safe
def s6_1215 : State := ⟨[49,4,96,145], 44601830679428246449697432631548776284356886, 3, 2, 1, 0⟩
theorem s6_1215_edges : next config 6 s6_1215 = [s7_739, s7_736] := by decide
theorem s6_1215_safe : Safe 7 6 s6_1215 := by
  apply safe_succ 6 6 s6_1215 [s7_739, s7_736] (by decide) s6_1215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_739_safe
  · subst z; exact s7_736_safe
def s6_1216 : State := ⟨[49,12,64,145], 44601830679428167221534918367211182738313502, 3, 1, 1, 0⟩
theorem s6_1216_edges : next config 6 s6_1216 = [s7_732, s7_738] := by decide
theorem s6_1216_safe : Safe 7 6 s6_1216 := by
  apply safe_succ 6 6 s6_1216 [s7_732, s7_738] (by decide) s6_1216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_732_safe
  · subst z; exact s7_738_safe
def s6_1217 : State := ⟨[49,12,64,145], 44601830679428167221534918367211182740410646, 3, 2, 1, 0⟩
theorem s6_1217_edges : next config 6 s6_1217 = [s7_739] := by decide
theorem s6_1217_safe : Safe 7 6 s6_1217 := by
  apply safe_succ 6 6 s6_1217 [s7_739] (by decide) s6_1217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_739_safe
def s6_1218 : State := ⟨[49,12,104,145], 44601830679448528859301084301972723533549846, 3, 0, 1, 0⟩
theorem s6_1218_edges : next config 6 s6_1218 = [s7_735] := by decide
theorem s6_1218_safe : Safe 7 6 s6_1218 := by
  apply safe_succ 6 6 s6_1218 [s7_735] (by decide) s6_1218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_735_safe
def s6_1219 : State := ⟨[49,21,64,145], 44601830679428167221534918367211182740406558, 3, 1, 1, 0⟩
theorem s6_1219_edges : next config 6 s6_1219 = [s7_741] := by decide
theorem s6_1219_safe : Safe 7 6 s6_1219 := by
  apply safe_succ 6 6 s6_1219 [s7_741] (by decide) s6_1219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_741_safe
def s6_1220 : State := ⟨[49,21,64,145], 44601830679428167221534918367211182740410646, 3, 2, 1, 0⟩
theorem s6_1220_edges : next config 6 s6_1220 = [s7_742] := by decide
theorem s6_1220_safe : Safe 7 6 s6_1220 := by
  apply safe_succ 6 6 s6_1220 [s7_742] (by decide) s6_1220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_742_safe
def s6_1221 : State := ⟨[49,21,104,145], 44601830679448528859301084301972723535642902, 3, 0, 1, 0⟩
theorem s6_1221_edges : next config 6 s6_1221 = [s7_744, s7_743] := by decide
theorem s6_1221_safe : Safe 7 6 s6_1221 := by
  apply safe_succ 6 6 s6_1221 [s7_744, s7_743] (by decide) s6_1221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_744_safe
  · subst z; exact s7_743_safe
def s6_1222 : State := ⟨[53,4,64,145], 44601830679428167221534918375655432041726238, 1, 1, 1, 0⟩
theorem s6_1222_edges : next config 6 s6_1222 = [s7_746] := by decide
theorem s6_1222_safe : Safe 7 6 s6_1222 := by
  apply safe_succ 6 6 s6_1222 [s7_746] (by decide) s6_1222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_746_safe
def s6_1223 : State := ⟨[53,4,104,145], 44601830679448528859301084310416972836962582, 1, 0, 1, 0⟩
theorem s6_1223_edges : next config 6 s6_1223 = [] := by decide
theorem s6_1223_safe : Safe 7 6 s6_1223 := by
  apply safe_succ 6 6 s6_1223 [] (by decide) s6_1223_edges
  simp
def s6_1224 : State := ⟨[65,4,64,145], 44601830679428167221534955260136380203995414, 3, 3, 1, 0⟩
theorem s6_1224_edges : next config 6 s6_1224 = [s7_751] := by decide
theorem s6_1224_safe : Safe 7 6 s6_1224 := by
  apply safe_succ 6 6 s6_1224 [s7_751] (by decide) s6_1224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_751_safe
def s6_1225 : State := ⟨[65,4,64,145], 44601830679428167221534955260136380206088470, 3, 3, 1, 0⟩
theorem s6_1225_edges : next config 6 s6_1225 = [s7_770, s7_752] := by decide
theorem s6_1225_safe : Safe 7 6 s6_1225 := by
  apply safe_succ 6 6 s6_1225 [s7_770, s7_752] (by decide) s6_1225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_770_safe
  · subst z; exact s7_752_safe
def s6_1226 : State := ⟨[65,4,96,145], 44602511244162088326624396273688837284237590, 3, 2, 1, 0⟩
theorem s6_1226_edges : next config 6 s6_1226 = [s7_767, s7_754] := by decide
theorem s6_1226_safe : Safe 7 6 s6_1226 := by
  apply safe_succ 6 6 s6_1226 [s7_767, s7_754] (by decide) s6_1226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_767_safe
  · subst z; exact s7_754_safe
def s6_1227 : State := ⟨[65,4,96,145], 44602511244163355977224624503090333987438870, 3, 2, 1, 0⟩
theorem s6_1227_edges : next config 6 s6_1227 = [s7_755] := by decide
theorem s6_1227_safe : Safe 7 6 s6_1227 := by
  apply safe_succ 6 6 s6_1227 [s7_755] (by decide) s6_1227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_755_safe
def s6_1228 : State := ⟨[65,4,96,145], 66902575877958869591233187797122335253795094, 3, 2, 1, 0⟩
theorem s6_1228_edges : next config 6 s6_1228 = [s7_768, s7_757] := by decide
theorem s6_1228_safe : Safe 7 6 s6_1228 := by
  apply safe_succ 6 6 s6_1228 [s7_768, s7_757] (by decide) s6_1228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_768_safe
  · subst z; exact s7_757_safe
def s6_1229 : State := ⟨[65,4,96,145], 66902575877960137241833416026523831956996374, 3, 2, 1, 0⟩
theorem s6_1229_edges : next config 6 s6_1229 = [s7_758] := by decide
theorem s6_1229_safe : Safe 7 6 s6_1229 := by
  apply safe_succ 6 6 s6_1229 [s7_758] (by decide) s6_1229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_758_safe
def s6_1230 : State := ⟨[65,4,96,146], 89204682205957176486622759568200423832621334, 3, 2, 1, 0⟩
theorem s6_1230_edges : next config 6 s6_1230 = [s7_760] := by decide
theorem s6_1230_safe : Safe 7 6 s6_1230 := by
  apply safe_succ 6 6 s6_1230 [s7_760] (by decide) s6_1230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_760_safe
def s6_1231 : State := ⟨[65,4,96,146], 111504066275020115874304624342419058265755926, 3, 2, 1, 0⟩
theorem s6_1231_edges : next config 6 s6_1231 = [s7_761] := by decide
theorem s6_1231_safe : Safe 7 6 s6_1231 := by
  apply safe_succ 6 6 s6_1231 [s7_761] (by decide) s6_1231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_761_safe
def s6_1232 : State := ⟨[65,4,96,162], 5846006551025023507498659810751609685601538871574, 3, 2, 1, 0⟩
theorem s6_1232_edges : next config 6 s6_1232 = [s7_762] := by decide
theorem s6_1232_safe : Safe 7 6 s6_1232 := by
  apply safe_succ 6 6 s6_1232 [s7_762] (by decide) s6_1232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_762_safe
def s6_1233 : State := ⟨[65,4,96,162], 7307508186994796958018590789614394275530398568726, 3, 2, 1, 0⟩
theorem s6_1233_edges : next config 6 s6_1233 = [s7_763] := by decide
theorem s6_1233_safe : Safe 7 6 s6_1233 := by
  apply safe_succ 6 6 s6_1233 [s7_763] (by decide) s6_1233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_763_safe
def s6_1234 : State := ⟨[65,4,96,176], 95780971326419139128294312505056075227996807378309398, 3, 2, 1, 0⟩
theorem s6_1234_edges : next config 6 s6_1234 = [s7_764] := by decide
theorem s6_1234_safe : Safe 7 6 s6_1234 := by
  apply safe_succ 6 6 s6_1234 [s7_764] (by decide) s6_1234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_764_safe
def s6_1235 : State := ⟨[65,4,96,176], 95782432805755724832681893048353073238368101804871958, 3, 2, 1, 0⟩
theorem s6_1235_edges : next config 6 s6_1235 = [s7_765] := by decide
theorem s6_1235_safe : Safe 7 6 s6_1235 := by
  apply safe_succ 6 6 s6_1235 [s7_765] (by decide) s6_1235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_765_safe
def s6_1236 : State := ⟨[65,4,100,145], 44601830679429514100297697753875470451147030, 1, 1, 1, 0⟩
theorem s6_1236_edges : next config 6 s6_1236 = [] := by decide
theorem s6_1236_safe : Safe 7 6 s6_1236 := by
  apply safe_succ 6 6 s6_1236 [] (by decide) s6_1236_edges
  simp
def s6_1237 : State := ⟨[65,4,104,129], 1020847121124453156611398816061523562774, 3, 2, 1, 0⟩
theorem s6_1237_edges : next config 6 s6_1237 = [s7_754] := by decide
theorem s6_1237_safe : Safe 7 6 s6_1237 := by
  apply safe_succ 6 6 s6_1237 [s7_754] (by decide) s6_1237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_754_safe
def s6_1238 : State := ⟨[65,4,104,129], 1020847122392103756839628217558226764054, 3, 2, 1, 0⟩
theorem s6_1238_edges : next config 6 s6_1238 = [s7_755] := by decide
theorem s6_1238_safe : Safe 7 6 s6_1238 := by
  apply safe_succ 6 6 s6_1238 [s7_755] (by decide) s6_1238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_755_safe
def s6_1239 : State := ⟨[65,4,104,129], 1020847445643006815038125599217544134934, 3, 2, 1, 0⟩
theorem s6_1239_edges : next config 6 s6_1239 = [s7_756] := by decide
theorem s6_1239_safe : Safe 7 6 s6_1239 := by
  apply safe_succ 6 6 s6_1239 [s7_756] (by decide) s6_1239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_756_safe
def s6_1240 : State := ⟨[65,4,104,130], 1701411854966330083538148030925059985686, 3, 2, 1, 0⟩
theorem s6_1240_edges : next config 6 s6_1240 = [s7_760, s7_762] := by decide
theorem s6_1240_safe : Safe 7 6 s6_1240 := by
  apply safe_succ 6 6 s6_1240 [s7_760, s7_762] (by decide) s6_1240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_760_safe
  · subst z; exact s7_762_safe
def s6_1241 : State := ⟨[65,4,104,130], 1701411856233980683766377432421763186966, 3, 2, 1, 0⟩
theorem s6_1241_edges : next config 6 s6_1241 = [] := by decide
theorem s6_1241_safe : Safe 7 6 s6_1241 := by
  apply safe_succ 6 6 s6_1241 [] (by decide) s6_1241_edges
  simp
def s6_1242 : State := ⟨[65,4,104,130], 1701412179484883741964874814081080557846, 3, 2, 1, 0⟩
theorem s6_1242_edges : next config 6 s6_1242 = [] := by decide
theorem s6_1242_safe : Safe 7 6 s6_1242 := by
  apply safe_succ 6 6 s6_1242 [] (by decide) s6_1242_edges
  simp
def s6_1243 : State := ⟨[65,4,104,132], 5784800258017591645098643320106278523158, 3, 2, 1, 0⟩
theorem s6_1243_edges : next config 6 s6_1243 = [] := by decide
theorem s6_1243_safe : Safe 7 6 s6_1243 := by
  apply safe_succ 6 6 s6_1243 [] (by decide) s6_1243_edges
  simp
def s6_1244 : State := ⟨[65,4,104,132], 5784800259285242245326872721602981724438, 3, 2, 1, 0⟩
theorem s6_1244_edges : next config 6 s6_1244 = [] := by decide
theorem s6_1244_safe : Safe 7 6 s6_1244 := by
  apply safe_succ 6 6 s6_1244 [] (by decide) s6_1244_edges
  simp
def s6_1245 : State := ⟨[65,4,104,132], 5784800582536145303525370103262299095318, 3, 2, 1, 0⟩
theorem s6_1245_edges : next config 6 s6_1245 = [] := by decide
theorem s6_1245_safe : Safe 7 6 s6_1245 := by
  apply safe_succ 6 6 s6_1245 [] (by decide) s6_1245_edges
  simp
def s6_1246 : State := ⟨[65,4,104,136], 87452568319042822876308549103730649272598, 3, 2, 1, 0⟩
theorem s6_1246_edges : next config 6 s6_1246 = [] := by decide
theorem s6_1246_safe : Safe 7 6 s6_1246 := by
  apply safe_succ 6 6 s6_1246 [] (by decide) s6_1246_edges
  simp
def s6_1247 : State := ⟨[65,4,104,136], 87452568320310473476536778505227352473878, 3, 2, 1, 0⟩
theorem s6_1247_edges : next config 6 s6_1247 = [] := by decide
theorem s6_1247_safe : Safe 7 6 s6_1247 := by
  apply safe_succ 6 6 s6_1247 [] (by decide) s6_1247_edges
  simp
def s6_1248 : State := ⟨[65,4,104,136], 87452568643561376534735275886886669844758, 3, 2, 1, 0⟩
theorem s6_1248_edges : next config 6 s6_1248 = [] := by decide
theorem s6_1248_safe : Safe 7 6 s6_1248 := by
  apply safe_succ 6 6 s6_1248 [] (by decide) s6_1248_edges
  simp
def s6_1249 : State := ⟨[65,4,104,136], 1481249143227206769222290941144253243392278, 3, 2, 1, 0⟩
theorem s6_1249_edges : next config 6 s6_1249 = [] := by decide
theorem s6_1249_safe : Safe 7 6 s6_1249 := by
  apply safe_succ 6 6 s6_1249 [] (by decide) s6_1249_edges
  simp
def s6_1250 : State := ⟨[65,4,104,140], 1394136857295446522575667041641720581263638, 3, 2, 1, 0⟩
theorem s6_1250_edges : next config 6 s6_1250 = [] := by decide
theorem s6_1250_safe : Safe 7 6 s6_1250 := by
  apply safe_succ 6 6 s6_1250 [] (by decide) s6_1250_edges
  simp
def s6_1251 : State := ⟨[65,4,104,144], 22301085480917905717765402922249559493120278, 3, 2, 1, 0⟩
theorem s6_1251_edges : next config 6 s6_1251 = [s7_761, s7_764] := by decide
theorem s6_1251_safe : Safe 7 6 s6_1251 := by
  apply safe_succ 6 6 s6_1251 [s7_761, s7_764] (by decide) s6_1251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_761_safe
  · subst z; exact s7_764_safe
def s6_1252 : State := ⟨[65,4,104,144], 22301085480919173368365631151651056196321558, 3, 2, 1, 0⟩
theorem s6_1252_edges : next config 6 s6_1252 = [] := by decide
theorem s6_1252_safe : Safe 7 6 s6_1252 := by
  apply safe_succ 6 6 s6_1252 [] (by decide) s6_1252_edges
  simp
def s6_1253 : State := ⟨[65,4,104,144], 22301085481242424271423829649032715513692438, 3, 2, 1, 0⟩
theorem s6_1253_edges : next config 6 s6_1253 = [] := by decide
theorem s6_1253_safe : Safe 7 6 s6_1253 := by
  apply safe_succ 6 6 s6_1253 [] (by decide) s6_1253_edges
  simp
def s6_1254 : State := ⟨[65,4,104,145], 44601830679448528859301121194897920999227670, 1, 1, 1, 0⟩
theorem s6_1254_edges : next config 6 s6_1254 = [s7_779, s7_771, s7_766, s7_769] := by decide
theorem s6_1254_safe : Safe 7 6 s6_1254 := by
  apply safe_succ 6 6 s6_1254 [s7_779, s7_771, s7_766, s7_769] (by decide) s6_1254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_779_safe
  · subst z; exact s7_771_safe
  · subst z; exact s7_766_safe
  · subst z; exact s7_769_safe
def s6_1255 : State := ⟨[65,4,104,160], 1461501637671185305486261062400932620853919682838, 3, 2, 1, 0⟩
theorem s6_1255_edges : next config 6 s6_1255 = [s7_763, s7_765] := by decide
theorem s6_1255_safe : Safe 7 6 s6_1255 := by
  apply safe_succ 6 6 s6_1255 [s7_763, s7_765] (by decide) s6_1255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_763_safe
  · subst z; exact s7_765_safe
def s6_1256 : State := ⟨[65,4,104,160], 1461501637671185306753911662629162022350622884118, 3, 2, 1, 0⟩
theorem s6_1256_edges : next config 6 s6_1256 = [] := by decide
theorem s6_1256_safe : Safe 7 6 s6_1256 := by
  apply safe_succ 6 6 s6_1256 [] (by decide) s6_1256_edges
  simp
def s6_1257 : State := ⟨[65,4,104,160], 1461501637671185630004814720827659404009940254998, 3, 2, 1, 0⟩
theorem s6_1257_edges : next config 6 s6_1257 = [] := by decide
theorem s6_1257_safe : Safe 7 6 s6_1257 := by
  apply safe_succ 6 6 s6_1257 [] (by decide) s6_1257_edges
  simp
def s6_1258 : State := ⟨[65,4,104,192], 6277101735386680764176071810490242645787005045662021652758, 3, 2, 1, 0⟩
theorem s6_1258_edges : next config 6 s6_1258 = [] := by decide
theorem s6_1258_safe : Safe 7 6 s6_1258 := by
  apply safe_succ 6 6 s6_1258 [] (by decide) s6_1258_edges
  simp
def s6_1259 : State := ⟨[65,4,104,192], 6277101735386680764176071811757893246015234447158724854038, 3, 2, 1, 0⟩
theorem s6_1259_edges : next config 6 s6_1259 = [] := by decide
theorem s6_1259_safe : Safe 7 6 s6_1259 := by
  apply safe_succ 6 6 s6_1259 [] (by decide) s6_1259_edges
  simp
def s6_1260 : State := ⟨[65,4,104,192], 6277101735386680764176072135008796304213731828818042224918, 3, 2, 1, 0⟩
theorem s6_1260_edges : next config 6 s6_1260 = [] := by decide
theorem s6_1260_safe : Safe 7 6 s6_1260 := by
  apply safe_succ 6 6 s6_1260 [] (by decide) s6_1260_edges
  simp
def s6_1261 : State := ⟨[65,4,104,193], 12554203470773361528011861233697909061889360490126056165654, 3, 2, 1, 0⟩
theorem s6_1261_edges : next config 6 s6_1261 = [] := by decide
theorem s6_1261_safe : Safe 7 6 s6_1261 := by
  apply safe_succ 6 6 s6_1261 [] (by decide) s6_1261_edges
  simp
def s6_1262 : State := ⟨[65,4,104,193], 12554203470773361528011861234965559662117589891622759366934, 3, 2, 1, 0⟩
theorem s6_1262_edges : next config 6 s6_1262 = [] := by decide
theorem s6_1262_safe : Safe 7 6 s6_1262 := by
  apply safe_succ 6 6 s6_1262 [] (by decide) s6_1262_edges
  simp
def s6_1263 : State := ⟨[65,4,104,193], 12554203470773361528011861558216462720316087273282076737814, 3, 2, 1, 0⟩
theorem s6_1263_edges : next config 6 s6_1263 = [] := by decide
theorem s6_1263_safe : Safe 7 6 s6_1263 := by
  apply safe_succ 6 6 s6_1263 [] (by decide) s6_1263_edges
  simp
def s6_1264 : State := ⟨[65,4,104,224], 26959946667150639794667015087359913060919720652225222082301597389078, 3, 2, 1, 0⟩
theorem s6_1264_edges : next config 6 s6_1264 = [] := by decide
theorem s6_1264_safe : Safe 7 6 s6_1264 := by
  apply safe_succ 6 6 s6_1264 [] (by decide) s6_1264_edges
  simp
def s6_1265 : State := ⟨[65,4,104,224], 26959946667150639794667015087359913062187371252453451483798300590358, 3, 2, 1, 0⟩
theorem s6_1265_edges : next config 6 s6_1265 = [] := by decide
theorem s6_1265_safe : Safe 7 6 s6_1265 := by
  apply safe_succ 6 6 s6_1265 [] (by decide) s6_1265_edges
  simp
def s6_1266 : State := ⟨[65,4,104,224], 26959946667150639794667015087359913385438274310651948865457617961238, 3, 2, 1, 0⟩
theorem s6_1266_edges : next config 6 s6_1266 = [] := by decide
theorem s6_1266_safe : Safe 7 6 s6_1266 := by
  apply safe_succ 6 6 s6_1266 [] (by decide) s6_1266_edges
  simp
def s6_1267 : State := ⟨[65,4,104,224], 458319093341560876509339256479674003839114031412874381779959361372438, 3, 2, 1, 0⟩
theorem s6_1267_edges : next config 6 s6_1267 = [] := by decide
theorem s6_1267_safe : Safe 7 6 s6_1267 := by
  apply safe_succ 6 6 s6_1267 [] (by decide) s6_1267_edges
  simp
def s6_1268 : State := ⟨[65,4,104,228], 431359146674410236714672241392654373166744537590562038700352454328598, 3, 2, 1, 0⟩
theorem s6_1268_edges : next config 6 s6_1268 = [] := by decide
theorem s6_1268_safe : Safe 7 6 s6_1268 := by
  apply safe_succ 6 6 s6_1268 [] (by decide) s6_1268_edges
  simp
def s6_1269 : State := ⟨[65,4,104,232], 6901746346790563787434755862277365734838391548400071204763722210939158, 3, 2, 1, 0⟩
theorem s6_1269_edges : next config 6 s6_1269 = [] := by decide
theorem s6_1269_safe : Safe 7 6 s6_1269 := by
  apply safe_succ 6 6 s6_1269 [] (by decide) s6_1269_edges
  simp
def s6_1270 : State := ⟨[65,4,104,232], 6901746346790563787434755862277365734839659199000299434165218914140438, 3, 2, 1, 0⟩
theorem s6_1270_edges : next config 6 s6_1270 = [] := by decide
theorem s6_1270_safe : Safe 7 6 s6_1270 := by
  apply safe_succ 6 6 s6_1270 [] (by decide) s6_1270_edges
  simp
def s6_1271 : State := ⟨[65,4,104,232], 6901746346790563787434755862277365735162910102058497931546878231511318, 3, 2, 1, 0⟩
theorem s6_1271_edges : next config 6 s6_1271 = [] := by decide
theorem s6_1271_safe : Safe 7 6 s6_1271 := by
  apply safe_succ 6 6 s6_1271 [] (by decide) s6_1271_edges
  simp
def s6_1272 : State := ⟨[65,4,104,232], 117329687895439584386390849658709772974056135103126256087364109791723798, 3, 2, 1, 0⟩
theorem s6_1272_edges : next config 6 s6_1272 = [] := by decide
theorem s6_1272_safe : Safe 7 6 s6_1272 := by
  apply safe_succ 6 6 s6_1272 [] (by decide) s6_1272_edges
  simp
def s6_1273 : State := ⟨[65,4,104,236], 110427941548649020598956093796432747521929544684614296258984741588500758, 3, 2, 1, 0⟩
theorem s6_1273_edges : next config 6 s6_1273 = [] := by decide
theorem s6_1273_safe : Safe 7 6 s6_1273 := by
  apply safe_succ 6 6 s6_1273 [] (by decide) s6_1273_edges
  simp
def s6_1274 : State := ⟨[65,4,108,145], 44602511244506889289886474670895940556095766, 1, 0, 1, 0⟩
theorem s6_1274_edges : next config 6 s6_1274 = [] := by decide
theorem s6_1274_safe : Safe 7 6 s6_1274 := by
  apply safe_succ 6 6 s6_1274 [] (by decide) s6_1274_edges
  simp
def s6_1275 : State := ⟨[65,4,108,145], 66902575878303670554495266194329438525653270, 1, 0, 1, 0⟩
theorem s6_1275_edges : next config 6 s6_1275 = [] := by decide
theorem s6_1275_safe : Safe 7 6 s6_1275 := by
  apply safe_succ 6 6 s6_1275 [] (by decide) s6_1275_edges
  simp
def s6_1276 : State := ⟨[65,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376333181206, 1, 1, 1, 0⟩
theorem s6_1276_edges : next config 6 s6_1276 = [s7_772] := by decide
theorem s6_1276_safe : Safe 7 6 s6_1276 := by
  apply safe_succ 6 6 s6_1276 [s7_772] (by decide) s6_1276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_772_safe
def s6_1277 : State := ⟨[65,4,249,145], 904625697166532776746648320380418882614915937571053134606206487846356844822, 1, 0, 1, 0⟩
theorem s6_1277_edges : next config 6 s6_1277 = [] := by decide
theorem s6_1277_safe : Safe 7 6 s6_1277 := by
  apply safe_succ 6 6 s6_1277 [] (by decide) s6_1277_edges
  simp
def s6_1278 : State := ⟨[65,4,249,145], 904625697166532776746648320380441182679549734352317743397729921344326402326, 1, 0, 1, 0⟩
theorem s6_1278_edges : next config 6 s6_1278 = [] := by decide
theorem s6_1278_safe : Safe 7 6 s6_1278 := by
  apply safe_succ 6 6 s6_1278 [] (by decide) s6_1278_edges
  simp
def s6_1279 : State := ⟨[65,12,96,145], 44601830679428246449697469524473973747945750, 3, 1, 1, 0⟩
theorem s6_1279_edges : next config 6 s6_1279 = [s7_751, s7_772, s7_771] := by decide
theorem s6_1279_safe : Safe 7 6 s6_1279 := by
  apply safe_succ 6 6 s6_1279 [s7_751, s7_772, s7_771] (by decide) s6_1279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_751_safe
  · subst z; exact s7_772_safe
  · subst z; exact s7_771_safe
def s6_1280 : State := ⟨[65,12,104,145], 44602511244182370736228047944112784535523606, 3, 0, 1, 0⟩
theorem s6_1280_edges : next config 6 s6_1280 = [s7_754] := by decide
theorem s6_1280_safe : Safe 7 6 s6_1280 := by
  apply safe_succ 6 6 s6_1280 [s7_754] (by decide) s6_1280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_754_safe
def s6_1281 : State := ⟨[65,12,104,145], 66902575877979152000836839467546282505081110, 3, 0, 1, 0⟩
theorem s6_1281_edges : next config 6 s6_1281 = [s7_757] := by decide
theorem s6_1281_safe : Safe 7 6 s6_1281 := by
  apply safe_succ 6 6 s6_1281 [s7_757] (by decide) s6_1281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_757_safe
def s6_1282 : State := ⟨[65,12,104,146], 89204682205977458896226411238624371083907350, 3, 0, 1, 0⟩
theorem s6_1282_edges : next config 6 s6_1282 = [s7_760] := by decide
theorem s6_1282_safe : Safe 7 6 s6_1282 := by
  apply safe_succ 6 6 s6_1282 [s7_760] (by decide) s6_1282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_760_safe
def s6_1283 : State := ⟨[65,12,104,146], 111504066275040398283908276012843005517041942, 3, 0, 1, 0⟩
theorem s6_1283_edges : next config 6 s6_1283 = [s7_761] := by decide
theorem s6_1283_safe : Safe 7 6 s6_1283 := by
  apply safe_succ 6 6 s6_1283 [s7_761] (by decide) s6_1283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_761_safe
def s6_1284 : State := ⟨[65,12,104,162], 5846006551025023527781069414403280109548790157590, 3, 0, 1, 0⟩
theorem s6_1284_edges : next config 6 s6_1284 = [s7_762] := by decide
theorem s6_1284_safe : Safe 7 6 s6_1284 := by
  apply safe_succ 6 6 s6_1284 [s7_762] (by decide) s6_1284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_762_safe
def s6_1285 : State := ⟨[65,12,104,162], 7307508186994796978301000393266064699477649854742, 3, 0, 1, 0⟩
theorem s6_1285_edges : next config 6 s6_1285 = [s7_763] := by decide
theorem s6_1285_safe : Safe 7 6 s6_1285 := by
  apply safe_succ 6 6 s6_1285 [s7_763] (by decide) s6_1285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_763_safe
def s6_1286 : State := ⟨[65,12,104,176], 95780971326419139128314594914659726898420754629595414, 3, 0, 1, 0⟩
theorem s6_1286_edges : next config 6 s6_1286 = [s7_764] := by decide
theorem s6_1286_safe : Safe 7 6 s6_1286 := by
  apply safe_succ 6 6 s6_1286 [s7_764] (by decide) s6_1286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_764_safe
def s6_1287 : State := ⟨[65,12,104,176], 95782432805755724832702175457956724908792049056157974, 3, 0, 1, 0⟩
theorem s6_1287_edges : next config 6 s6_1287 = [s7_765] := by decide
theorem s6_1287_safe : Safe 7 6 s6_1287 := by
  apply safe_succ 6 6 s6_1287 [s7_765] (by decide) s6_1287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_765_safe
def s6_1288 : State := ⟨[65,12,241,145], 3533694129556768659166595001530439542899129882077862312516901239869477142, 3, 0, 1, 0⟩
theorem s6_1288_edges : next config 6 s6_1288 = [s7_767] := by decide
theorem s6_1288_safe : Safe 7 6 s6_1288 := by
  apply safe_succ 6 6 s6_1288 [s7_767] (by decide) s6_1288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_767_safe
def s6_1289 : State := ⟨[65,12,241,145], 3533694129556768659166595001552739607532926663342471104040334737839034646, 3, 0, 1, 0⟩
theorem s6_1289_edges : next config 6 s6_1289 = [s7_768] := by decide
theorem s6_1289_safe : Safe 7 6 s6_1289 := by
  apply safe_succ 6 6 s6_1289 [s7_768] (by decide) s6_1289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_768_safe
def s6_1290 : State := ⟨[65,21,96,145], 44601830679428246449697469524473973750038806, 3, 1, 1, 0⟩
theorem s6_1290_edges : next config 6 s6_1290 = [s7_780, s7_777, s7_775, s7_776, s7_774] := by decide
theorem s6_1290_safe : Safe 7 6 s6_1290 := by
  apply safe_succ 6 6 s6_1290 [s7_780, s7_777, s7_775, s7_776, s7_774] (by decide) s6_1290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s7_780_safe
  · subst z; exact s7_777_safe
  · subst z; exact s7_775_safe
  · subst z; exact s7_776_safe
  · subst z; exact s7_774_safe
def s6_1291 : State := ⟨[65,29,64,145], 44601830679428167221534955260136380742959382, 3, 1, 1, 0⟩
theorem s6_1291_edges : next config 6 s6_1291 = [s7_777] := by decide
theorem s6_1291_safe : Safe 7 6 s6_1291 := by
  apply safe_succ 6 6 s6_1291 [s7_777] (by decide) s6_1291_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_777_safe
def s6_1292 : State := ⟨[65,100,96,145], 44601830679429514100297697753875470451147030, 3, 1, 1, 0⟩
theorem s6_1292_edges : next config 6 s6_1292 = [s7_753, s7_778] := by decide
theorem s6_1292_safe : Safe 7 6 s6_1292 := by
  apply safe_succ 6 6 s6_1292 [s7_753, s7_778] (by decide) s6_1292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_753_safe
  · subst z; exact s7_778_safe
def s6_1293 : State := ⟨[65,100,104,145], 44602511244183638386828276173514281238724886, 3, 0, 1, 0⟩
theorem s6_1293_edges : next config 6 s6_1293 = [] := by decide
theorem s6_1293_safe : Safe 7 6 s6_1293 := by
  apply safe_succ 6 6 s6_1293 [] (by decide) s6_1293_edges
  simp
def s6_1294 : State := ⟨[65,100,104,145], 66902575877980419651437067696947779208282390, 3, 0, 1, 0⟩
theorem s6_1294_edges : next config 6 s6_1294 = [] := by decide
theorem s6_1294_safe : Safe 7 6 s6_1294 := by
  apply safe_succ 6 6 s6_1294 [] (by decide) s6_1294_edges
  simp
def s6_1295 : State := ⟨[65,108,104,145], 44602511244506889289886474670895940556095766, 3, 0, 1, 0⟩
theorem s6_1295_edges : next config 6 s6_1295 = [s7_756] := by decide
theorem s6_1295_safe : Safe 7 6 s6_1295 := by
  apply safe_succ 6 6 s6_1295 [s7_756] (by decide) s6_1295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_756_safe
def s6_1296 : State := ⟨[65,108,104,145], 66902575878303670554495266194329438525653270, 3, 0, 1, 0⟩
theorem s6_1296_edges : next config 6 s6_1296 = [s7_759] := by decide
theorem s6_1296_safe : Safe 7 6 s6_1296 := by
  apply safe_succ 6 6 s6_1296 [s7_759] (by decide) s6_1296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_759_safe
def s6_1297 : State := ⟨[81,4,96,145], 44601830679428246452115284270215084678254870, 3, 2, 1, 0⟩
theorem s6_1297_edges : next config 6 s6_1297 = [s7_781] := by decide
theorem s6_1297_safe : Safe 7 6 s6_1297 := by
  apply safe_succ 6 6 s6_1297 [s7_781] (by decide) s6_1297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_781_safe
def s6_1298 : State := ⟨[81,4,96,145], 44601830679428246452115284270215084680347926, 3, 2, 1, 0⟩
theorem s6_1298_edges : next config 6 s6_1298 = [s7_783, s7_782] := by decide
theorem s6_1298_safe : Safe 7 6 s6_1298 := by
  apply safe_succ 6 6 s6_1298 [s7_783, s7_782] (by decide) s6_1298_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_783_safe
  · subst z; exact s7_782_safe
def s6_1299 : State := ⟨[81,12,64,145], 44601830679428167223952770005877491136401686, 3, 2, 1, 0⟩
theorem s6_1299_edges : next config 6 s6_1299 = [s7_783] := by decide
theorem s6_1299_safe : Safe 7 6 s6_1299 := by
  apply safe_succ 6 6 s6_1299 [s7_783] (by decide) s6_1299_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_783_safe
def s6_1300 : State := ⟨[81,12,104,145], 44601830679448528861718935940639031929540886, 3, 0, 1, 0⟩
theorem s6_1300_edges : next config 6 s6_1300 = [s7_781] := by decide
theorem s6_1300_safe : Safe 7 6 s6_1300 := by
  apply safe_succ 6 6 s6_1300 [s7_781] (by decide) s6_1300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_781_safe
def s6_1301 : State := ⟨[81,21,64,145], 44601830679428167223952770005877491136401686, 3, 2, 1, 0⟩
theorem s6_1301_edges : next config 6 s6_1301 = [s7_784] := by decide
theorem s6_1301_safe : Safe 7 6 s6_1301 := by
  apply safe_succ 6 6 s6_1301 [s7_784] (by decide) s6_1301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_784_safe
def s6_1302 : State := ⟨[81,21,104,145], 44601830679448528861718935940639031931633942, 3, 0, 1, 0⟩
theorem s6_1302_edges : next config 6 s6_1302 = [s7_786, s7_785] := by decide
theorem s6_1302_safe : Safe 7 6 s6_1302 := by
  apply safe_succ 6 6 s6_1302 [s7_786, s7_785] (by decide) s6_1302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_786_safe
  · subst z; exact s7_785_safe
def s6_1303 : State := ⟨[82,4,67,145], 44601830679428167226370769219059339160125726, 1, 1, 1, 0⟩
theorem s6_1303_edges : next config 6 s6_1303 = [s7_803, s7_799, s7_795] := by decide
theorem s6_1303_safe : Safe 7 6 s6_1303 := by
  apply safe_succ 6 6 s6_1303 [s7_803, s7_799, s7_795] (by decide) s6_1303_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_803_safe
  · subst z; exact s7_799_safe
  · subst z; exact s7_795_safe
def s6_1304 : State := ⟨[82,12,67,145], 44601830679428167226370806112547486579233046, 3, 0, 1, 0⟩
theorem s6_1304_edges : next config 6 s6_1304 = [s7_787] := by decide
theorem s6_1304_safe : Safe 7 6 s6_1304 := by
  apply safe_succ 6 6 s6_1304 [s7_787] (by decide) s6_1304_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_787_safe
def s6_1305 : State := ⟨[82,12,67,145], 44601830679428167226370843006035633998336278, 3, 0, 1, 0⟩
theorem s6_1305_edges : next config 6 s6_1305 = [s7_789] := by decide
theorem s6_1305_safe : Safe 7 6 s6_1305 := by
  apply safe_succ 6 6 s6_1305 [s7_789] (by decide) s6_1305_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_789_safe
def s6_1306 : State := ⟨[82,21,67,145], 44601830679428167226370806112547486581326102, 3, 0, 1, 0⟩
theorem s6_1306_edges : next config 6 s6_1306 = [s7_800] := by decide
theorem s6_1306_safe : Safe 7 6 s6_1306 := by
  apply safe_succ 6 6 s6_1306 [s7_800] (by decide) s6_1306_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_800_safe
def s6_1307 : State := ⟨[82,21,67,145], 44601830679428167226370843006035634000429334, 3, 0, 1, 0⟩
theorem s6_1307_edges : next config 6 s6_1307 = [s7_801] := by decide
theorem s6_1307_safe : Safe 7 6 s6_1307 := by
  apply safe_succ 6 6 s6_1307 [s7_801] (by decide) s6_1307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_801_safe
def s6_1308 : State := ⟨[82,86,67,145], 44601830679428167303742058567883753760424214, 3, 0, 1, 0⟩
theorem s6_1308_edges : next config 6 s6_1308 = [s7_791, s7_797] := by decide
theorem s6_1308_safe : Safe 7 6 s6_1308 := by
  apply safe_succ 6 6 s6_1308 [s7_791, s7_797] (by decide) s6_1308_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_791_safe
  · subst z; exact s7_797_safe
def s6_1309 : State := ⟨[82,86,67,145], 44601830679428167303742095461371901179527446, 3, 0, 1, 0⟩
theorem s6_1309_edges : next config 6 s6_1309 = [s7_793, s7_798] := by decide
theorem s6_1309_safe : Safe 7 6 s6_1309 := by
  apply safe_succ 6 6 s6_1309 [s7_793, s7_798] (by decide) s6_1309_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_793_safe
  · subst z; exact s7_798_safe
def s6_1310 : State := ⟨[86,4,67,145], 44601830679428167298906355289425237063696662, 1, 0, 1, 0⟩
theorem s6_1310_edges : next config 6 s6_1310 = [s7_792, s7_808, s7_806] := by decide
theorem s6_1310_safe : Safe 7 6 s6_1310 := by
  apply safe_succ 6 6 s6_1310 [s7_792, s7_808, s7_806] (by decide) s6_1310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_792_safe
  · subst z; exact s7_808_safe
  · subst z; exact s7_806_safe
def s6_1311 : State := ⟨[86,4,67,145], 44601830679428167298906392182913384482799894, 1, 0, 1, 0⟩
theorem s6_1311_edges : next config 6 s6_1311 = [s7_794, s7_809, s7_807] := by decide
theorem s6_1311_safe : Safe 7 6 s6_1311 := by
  apply safe_succ 6 6 s6_1311 [s7_794, s7_809, s7_807] (by decide) s6_1311_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_794_safe
  · subst z; exact s7_809_safe
  · subst z; exact s7_807_safe
def s6_1312 : State := ⟨[86,4,67,145], 44601830679428167303742058567883753760424214, 1, 0, 1, 0⟩
theorem s6_1312_edges : next config 6 s6_1312 = [s7_544] := by decide
theorem s6_1312_safe : Safe 7 6 s6_1312 := by
  apply safe_succ 6 6 s6_1312 [s7_544] (by decide) s6_1312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_544_safe
def s6_1313 : State := ⟨[86,4,67,145], 44601830679428167303742095461371901179527446, 1, 0, 1, 0⟩
theorem s6_1313_edges : next config 6 s6_1313 = [s7_545] := by decide
theorem s6_1313_safe : Safe 7 6 s6_1313 := by
  apply safe_succ 6 6 s6_1313 [s7_545] (by decide) s6_1313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_545_safe
def s6_1314 : State := ⟨[96,4,67,128], 340282367000166626143659641727352901918, 3, 2, 0, 0⟩
theorem s6_1314_edges : next config 6 s6_1314 = [s7_847, s7_834, s7_816, s7_832, s7_812, s7_818, s7_822, s7_825] := by decide
theorem s6_1314_safe : Safe 7 6 s6_1314 := by
  apply safe_succ 6 6 s6_1314 [s7_847, s7_834, s7_816, s7_832, s7_812, s7_818, s7_822, s7_825] (by decide) s6_1314_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_847_safe
  · subst z; exact s7_834_safe
  · subst z; exact s7_816_safe
  · subst z; exact s7_832_safe
  · subst z; exact s7_812_safe
  · subst z; exact s7_818_safe
  · subst z; exact s7_822_safe
  · subst z; exact s7_825_safe
def s6_1315 : State := ⟨[96,4,67,128], 340282387282576229795330074470697206046, 1, 0, 0, 0⟩
theorem s6_1315_edges : next config 6 s6_1315 = [s7_835, s7_817, s7_833, s7_813, s7_819, s7_823, s7_826] := by decide
theorem s6_1315_safe : Safe 7 6 s6_1315 := by
  apply safe_succ 6 6 s6_1315 [s7_835, s7_817, s7_833, s7_813, s7_819, s7_823, s7_826] (by decide) s6_1315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_835_safe
  · subst z; exact s7_817_safe
  · subst z; exact s7_833_safe
  · subst z; exact s7_813_safe
  · subst z; exact s7_819_safe
  · subst z; exact s7_823_safe
  · subst z; exact s7_826_safe
def s6_1316 : State := ⟨[96,4,67,140], 1399581375145899128387540045401158238404894, 1, 0, 1, 0⟩
theorem s6_1316_edges : next config 6 s6_1316 = [s7_857] := by decide
theorem s6_1316_safe : Safe 7 6 s6_1316 := by
  apply safe_succ 6 6 s6_1316 [s7_857] (by decide) s6_1316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_857_safe
def s6_1317 : State := ⟨[96,4,67,140], 1481249143206924359618749951184782609154334, 1, 0, 1, 0⟩
theorem s6_1317_edges : next config 6 s6_1317 = [s7_858] := by decide
theorem s6_1317_safe : Safe 7 6 s6_1317 := by
  apply safe_succ 6 6 s6_1317 [s7_858] (by decide) s6_1317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_858_safe
def s6_1318 : State := ⟨[96,4,67,145], 44602511244162088326624506954153313901281566, 1, 0, 1, 0⟩
theorem s6_1318_edges : next config 6 s6_1318 = [s7_862, s7_837] := by decide
theorem s6_1318_safe : Safe 7 6 s6_1318 := by
  apply safe_succ 6 6 s6_1318 [s7_862, s7_837] (by decide) s6_1318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_862_safe
  · subst z; exact s7_837_safe
def s6_1319 : State := ⟨[96,4,67,145], 66902575877958869591233298477586811870839070, 1, 0, 1, 0⟩
theorem s6_1319_edges : next config 6 s6_1319 = [s7_864, s7_838] := by decide
theorem s6_1319_safe : Safe 7 6 s6_1319 := by
  apply safe_succ 6 6 s6_1319 [s7_864, s7_838] (by decide) s6_1319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_864_safe
  · subst z; exact s7_838_safe
def s6_1320 : State := ⟨[96,4,67,171], 2993155353341141744779906950675715183399609863045406, 1, 0, 1, 0⟩
theorem s6_1320_edges : next config 6 s6_1320 = [s7_872] := by decide
theorem s6_1320_safe : Safe 7 6 s6_1320 := by
  apply safe_succ 6 6 s6_1320 [s7_872] (by decide) s6_1320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_872_safe
def s6_1321 : State := ⟨[96,4,67,171], 3004847366352676682193776182690821548054324661256478, 1, 0, 1, 0⟩
theorem s6_1321_edges : next config 6 s6_1321 = [s7_873] := by decide
theorem s6_1321_safe : Safe 7 6 s6_1321 := by
  apply safe_succ 6 6 s6_1321 [s7_873] (by decide) s6_1321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_873_safe
def s6_1322 : State := ⟨[96,12,67,129], 1020847100842043553070408856590889324830, 3, 0, 1, 0⟩
theorem s6_1322_edges : next config 6 s6_1322 = [s7_884, s7_810, s7_837] := by decide
theorem s6_1322_safe : Safe 7 6 s6_1322 := by
  apply safe_succ 6 6 s6_1322 [s7_884, s7_810, s7_837] (by decide) s6_1322_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_884_safe
  · subst z; exact s7_810_safe
  · subst z; exact s7_837_safe
def s6_1323 : State := ⟨[96,12,67,130], 1701411834683920479997158071454425747742, 3, 0, 1, 0⟩
theorem s6_1323_edges : next config 6 s6_1323 = [s7_885, s7_812] := by decide
theorem s6_1323_safe : Safe 7 6 s6_1323 := by
  apply safe_succ 6 6 s6_1323 [s7_885, s7_812] (by decide) s6_1323_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_885_safe
  · subst z; exact s7_812_safe
def s6_1324 : State := ⟨[96,12,67,131], 3062541302367674333850656501181498593566, 3, 0, 1, 0⟩
theorem s6_1324_edges : next config 6 s6_1324 = [s7_886, s7_814] := by decide
theorem s6_1324_safe : Safe 7 6 s6_1324 := by
  apply safe_succ 6 6 s6_1324 [s7_886, s7_814] (by decide) s6_1324_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_886_safe
  · subst z; exact s7_814_safe
def s6_1325 : State := ⟨[96,12,67,132], 5784800237735182041557653360635644285214, 3, 0, 1, 0⟩
theorem s6_1325_edges : next config 6 s6_1325 = [s7_887, s7_816] := by decide
theorem s6_1325_safe : Safe 7 6 s6_1325 := by
  apply safe_succ 6 6 s6_1325 [s7_887, s7_816] (by decide) s6_1325_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_887_safe
  · subst z; exact s7_816_safe
def s6_1326 : State := ⟨[96,12,67,136], 87452568298760413272767559144260015034654, 3, 0, 1, 0⟩
theorem s6_1326_edges : next config 6 s6_1326 = [s7_888, s7_818] := by decide
theorem s6_1326_safe : Safe 7 6 s6_1326 := by
  apply safe_succ 6 6 s6_1326 [s7_888, s7_818] (by decide) s6_1326_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_888_safe
  · subst z; exact s7_818_safe
def s6_1327 : State := ⟨[96,12,67,140], 1394136857275164112972126051682249947025694, 3, 0, 1, 0⟩
theorem s6_1327_edges : next config 6 s6_1327 = [s7_889, s7_821] := by decide
theorem s6_1327_safe : Safe 7 6 s6_1327 := by
  apply safe_succ 6 6 s6_1327 [s7_889, s7_821] (by decide) s6_1327_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_889_safe
  · subst z; exact s7_821_safe
def s6_1328 : State := ⟨[96,12,67,144], 22301085480897623308161861932290088858882334, 3, 0, 1, 0⟩
theorem s6_1328_edges : next config 6 s6_1328 = [s7_890, s7_822] := by decide
theorem s6_1328_safe : Safe 7 6 s6_1328 := by
  apply safe_succ 6 6 s6_1328 [s7_890, s7_822] (by decide) s6_1328_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_890_safe
  · subst z; exact s7_822_safe
def s6_1329 : State := ⟨[96,12,67,160], 1461501637671185285203851458859942661383285444894, 3, 0, 1, 0⟩
theorem s6_1329_edges : next config 6 s6_1329 = [s7_891, s7_825] := by decide
theorem s6_1329_safe : Safe 7 6 s6_1329 := by
  apply safe_succ 6 6 s6_1329 [s7_891, s7_825] (by decide) s6_1329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_891_safe
  · subst z; exact s7_825_safe
def s6_1330 : State := ⟨[96,12,67,163], 11692013098987505712629645287873923798974813245726, 3, 0, 1, 0⟩
theorem s6_1330_edges : next config 6 s6_1330 = [s7_892, s7_827] := by decide
theorem s6_1330_safe : Safe 7 6 s6_1330 := by
  apply safe_succ 6 6 s6_1330 [s7_892, s7_827] (by decide) s6_1330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_892_safe
  · subst z; exact s7_827_safe
def s6_1331 : State := ⟨[96,12,67,192], 6277101735386680764176071790207833042246015086191387414814, 3, 0, 1, 0⟩
theorem s6_1331_edges : next config 6 s6_1331 = [s7_893, s7_830] := by decide
theorem s6_1331_safe : Safe 7 6 s6_1331 := by
  apply safe_succ 6 6 s6_1331 [s7_893, s7_830] (by decide) s6_1331_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_893_safe
  · subst z; exact s7_830_safe
def s6_1332 : State := ⟨[96,12,67,195], 50216813883093446111026597752661497954962503197439629005086, 3, 0, 1, 0⟩
theorem s6_1332_edges : next config 6 s6_1332 = [s7_894, s7_832] := by decide
theorem s6_1332_safe : Safe 7 6 s6_1332 := by
  apply safe_succ 6 6 s6_1332 [s7_894, s7_832] (by decide) s6_1332_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_894_safe
  · subst z; exact s7_832_safe
def s6_1333 : State := ⟨[96,12,67,224], 26959946667150639794667015087359913040637311048684232122830963151134, 3, 0, 1, 0⟩
theorem s6_1333_edges : next config 6 s6_1333 = [s7_895, s7_834] := by decide
theorem s6_1333_safe : Safe 7 6 s6_1333 := by
  apply safe_succ 6 6 s6_1333 [s7_895, s7_834] (by decide) s6_1333_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_895_safe
  · subst z; exact s7_834_safe
def s6_1334 : State := ⟨[96,140,67,136], 1481249143206924359618749951184782609154334, 3, 0, 1, 0⟩
theorem s6_1334_edges : next config 6 s6_1334 = [s7_897, s7_820] := by decide
theorem s6_1334_safe : Safe 7 6 s6_1334 := by
  apply safe_succ 6 6 s6_1334 [s7_897, s7_820] (by decide) s6_1334_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_897_safe
  · subst z; exact s7_820_safe
def s6_1335 : State := ⟨[97,4,96,145], 44602511244162246782949387908875876953035030, 3, 2, 1, 0⟩
theorem s6_1335_edges : next config 6 s6_1335 = [s7_31, s7_841] := by decide
theorem s6_1335_safe : Safe 7 6 s6_1335 := by
  apply safe_succ 6 6 s6_1335 [s7_31, s7_841] (by decide) s6_1335_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_31_safe
  · subst z; exact s7_841_safe
def s6_1336 : State := ⟨[97,4,96,145], 66902575877959028047558179432309374922592534, 3, 2, 1, 0⟩
theorem s6_1336_edges : next config 6 s6_1336 = [s7_37, s7_842] := by decide
theorem s6_1336_safe : Safe 7 6 s6_1336 := by
  apply safe_succ 6 6 s6_1336 [s7_37, s7_842] (by decide) s6_1336_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_37_safe
  · subst z; exact s7_842_safe
def s6_1337 : State := ⟨[97,4,96,162], 5846006551025023507657116135743244872641207669014, 3, 2, 1, 0⟩
theorem s6_1337_edges : next config 6 s6_1337 = [s7_47, s7_843] := by decide
theorem s6_1337_safe : Safe 7 6 s6_1337 := by
  apply safe_succ 6 6 s6_1337 [s7_47, s7_843] (by decide) s6_1337_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_47_safe
  · subst z; exact s7_843_safe
def s6_1338 : State := ⟨[97,4,96,162], 7307508186994796958177047114606029462570067366166, 3, 2, 1, 0⟩
theorem s6_1338_edges : next config 6 s6_1338 = [s7_51, s7_844] := by decide
theorem s6_1338_safe : Safe 7 6 s6_1338 := by
  apply safe_succ 6 6 s6_1338 [s7_51, s7_844] (by decide) s6_1338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_51_safe
  · subst z; exact s7_844_safe
def s6_1339 : State := ⟨[97,4,104,129], 1020847121282909481603034003101192360214, 3, 2, 1, 0⟩
theorem s6_1339_edges : next config 6 s6_1339 = [s7_841] := by decide
theorem s6_1339_safe : Safe 7 6 s6_1339 := by
  apply safe_succ 6 6 s6_1339 [s7_841] (by decide) s6_1339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_841_safe
def s6_1340 : State := ⟨[97,4,104,130], 1701411855124786408529783217964728783126, 3, 2, 1, 0⟩
theorem s6_1340_edges : next config 6 s6_1340 = [s7_843] := by decide
theorem s6_1340_safe : Safe 7 6 s6_1340 := by
  apply safe_succ 6 6 s6_1340 [s7_843] (by decide) s6_1340_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_843_safe
def s6_1341 : State := ⟨[97,4,104,132], 5784800258176047970090278507145947320598, 3, 2, 1, 0⟩
theorem s6_1341_edges : next config 6 s6_1341 = [] := by decide
theorem s6_1341_safe : Safe 7 6 s6_1341 := by
  apply safe_succ 6 6 s6_1341 [] (by decide) s6_1341_edges
  simp
def s6_1342 : State := ⟨[97,4,104,136], 87452568319201279201300184290770318070038, 3, 2, 1, 0⟩
theorem s6_1342_edges : next config 6 s6_1342 = [] := by decide
theorem s6_1342_safe : Safe 7 6 s6_1342 := by
  apply safe_succ 6 6 s6_1342 [] (by decide) s6_1342_edges
  simp
def s6_1343 : State := ⟨[97,4,104,136], 1481249143227365225547282576331292912189718, 3, 2, 1, 0⟩
theorem s6_1343_edges : next config 6 s6_1343 = [] := by decide
theorem s6_1343_safe : Safe 7 6 s6_1343 := by
  apply safe_succ 6 6 s6_1343 [] (by decide) s6_1343_edges
  simp
def s6_1344 : State := ⟨[97,4,104,140], 1394136857295604978900658676828760250061078, 3, 2, 1, 0⟩
theorem s6_1344_edges : next config 6 s6_1344 = [] := by decide
theorem s6_1344_safe : Safe 7 6 s6_1344 := by
  apply safe_succ 6 6 s6_1344 [] (by decide) s6_1344_edges
  simp
def s6_1345 : State := ⟨[97,4,104,144], 22301085480918064174090394557436599161917718, 3, 2, 1, 0⟩
theorem s6_1345_edges : next config 6 s6_1345 = [] := by decide
theorem s6_1345_safe : Safe 7 6 s6_1345 := by
  apply safe_succ 6 6 s6_1345 [] (by decide) s6_1345_edges
  simp
def s6_1346 : State := ⟨[97,4,104,145], 44601830679448687315626112830084960668025110, 1, 1, 1, 0⟩
theorem s6_1346_edges : next config 6 s6_1346 = [s7_845] := by decide
theorem s6_1346_safe : Safe 7 6 s6_1346 := by
  apply safe_succ 6 6 s6_1346 [s7_845] (by decide) s6_1346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_845_safe
def s6_1347 : State := ⟨[97,4,104,160], 1461501637671185305644717387392567807893588480278, 3, 2, 1, 0⟩
theorem s6_1347_edges : next config 6 s6_1347 = [s7_844] := by decide
theorem s6_1347_safe : Safe 7 6 s6_1347 := by
  apply safe_succ 6 6 s6_1347 [s7_844] (by decide) s6_1347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_844_safe
def s6_1348 : State := ⟨[97,4,104,192], 6277101735386680764176071810648698970778640232701690450198, 3, 2, 1, 0⟩
theorem s6_1348_edges : next config 6 s6_1348 = [] := by decide
theorem s6_1348_safe : Safe 7 6 s6_1348 := by
  apply safe_succ 6 6 s6_1348 [] (by decide) s6_1348_edges
  simp
def s6_1349 : State := ⟨[97,4,104,224], 26959946667150639794667015087359913061078176977216857269341266186518, 3, 2, 1, 0⟩
theorem s6_1349_edges : next config 6 s6_1349 = [] := by decide
theorem s6_1349_safe : Safe 7 6 s6_1349 := by
  apply safe_succ 6 6 s6_1349 [] (by decide) s6_1349_edges
  simp
def s6_1350 : State := ⟨[97,4,104,225], 53919893334301279589334030174379543734715321399757429750444876435734, 3, 2, 1, 0⟩
theorem s6_1350_edges : next config 6 s6_1350 = [] := by decide
theorem s6_1350_safe : Safe 7 6 s6_1350 := by
  apply safe_succ 6 6 s6_1350 [] (by decide) s6_1350_edges
  simp
def s6_1351 : State := ⟨[97,4,104,232], 6901746346790563787434755862277365734838550004725062839950761879736598, 3, 2, 1, 0⟩
theorem s6_1351_edges : next config 6 s6_1351 = [] := by decide
theorem s6_1351_safe : Safe 7 6 s6_1351 := by
  apply safe_succ 6 6 s6_1351 [] (by decide) s6_1351_edges
  simp
def s6_1352 : State := ⟨[97,12,96,145], 44601830679428404906022461159661013416743190, 3, 1, 1, 0⟩
theorem s6_1352_edges : next config 6 s6_1352 = [s7_839, s7_845] := by decide
theorem s6_1352_safe : Safe 7 6 s6_1352 := by
  apply safe_succ 6 6 s6_1352 [s7_839, s7_845] (by decide) s6_1352_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_839_safe
  · subst z; exact s7_845_safe
def s6_1353 : State := ⟨[97,12,104,145], 44602511244182529192553039579299824204321046, 3, 0, 1, 0⟩
theorem s6_1353_edges : next config 6 s6_1353 = [s7_841] := by decide
theorem s6_1353_safe : Safe 7 6 s6_1353 := by
  apply safe_succ 6 6 s6_1353 [s7_841] (by decide) s6_1353_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_841_safe
def s6_1354 : State := ⟨[97,12,104,145], 66902575877979310457161831102733322173878550, 3, 0, 1, 0⟩
theorem s6_1354_edges : next config 6 s6_1354 = [s7_842] := by decide
theorem s6_1354_safe : Safe 7 6 s6_1354 := by
  apply safe_succ 6 6 s6_1354 [s7_842] (by decide) s6_1354_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_842_safe
def s6_1355 : State := ⟨[97,12,104,162], 5846006551025023527939525739394915296588458955030, 3, 0, 1, 0⟩
theorem s6_1355_edges : next config 6 s6_1355 = [s7_843] := by decide
theorem s6_1355_safe : Safe 7 6 s6_1355 := by
  apply safe_succ 6 6 s6_1355 [s7_843] (by decide) s6_1355_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_843_safe
def s6_1356 : State := ⟨[97,12,104,162], 7307508186994796978459456718257699886517318652182, 3, 0, 1, 0⟩
theorem s6_1356_edges : next config 6 s6_1356 = [s7_844] := by decide
theorem s6_1356_safe : Safe 7 6 s6_1356 := by
  apply safe_succ 6 6 s6_1356 [s7_844] (by decide) s6_1356_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_844_safe
def s6_1357 : State := ⟨[97,21,96,145], 44601830679428404906022461159661013418836246, 3, 1, 1, 0⟩
theorem s6_1357_edges : next config 6 s6_1357 = [s7_846] := by decide
theorem s6_1357_safe : Safe 7 6 s6_1357 := by
  apply safe_succ 6 6 s6_1357 [s7_846] (by decide) s6_1357_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_846_safe
def s6_1358 : State := ⟨[104,4,67,128], 340282387282576229795330074470697206046, 1, 0, 0, 0⟩
theorem s6_1358_edges : next config 6 s6_1358 = [s7_882, s7_853, s7_878, s7_850, s7_855, s7_859, s7_865] := by decide
theorem s6_1358_safe : Safe 7 6 s6_1358 := by
  apply safe_succ 6 6 s6_1358 [s7_882, s7_853, s7_878, s7_850, s7_855, s7_859, s7_865] (by decide) s6_1358_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_882_safe
  · subst z; exact s7_853_safe
  · subst z; exact s7_878_safe
  · subst z; exact s7_850_safe
  · subst z; exact s7_855_safe
  · subst z; exact s7_859_safe
  · subst z; exact s7_865_safe
def s6_1359 : State := ⟨[104,4,67,128], 340282387282576229795330074479287140630, 1, 0, 0, 0⟩
theorem s6_1359_edges : next config 6 s6_1359 = [s7_883, s7_854, s7_879, s7_851, s7_856, s7_860, s7_866] := by decide
theorem s6_1359_safe : Safe 7 6 s6_1359 := by
  apply safe_succ 6 6 s6_1359 [s7_883, s7_854, s7_879, s7_851, s7_856, s7_860, s7_866] (by decide) s6_1359_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s7_883_safe
  · subst z; exact s7_854_safe
  · subst z; exact s7_879_safe
  · subst z; exact s7_851_safe
  · subst z; exact s7_856_safe
  · subst z; exact s7_860_safe
  · subst z; exact s7_866_safe
def s6_1360 : State := ⟨[104,4,67,129], 1020847121045224994207814951740689678622, 1, 0, 1, 0⟩
theorem s6_1360_edges : next config 6 s6_1360 = [s7_811, s7_861] := by decide
theorem s6_1360_safe : Safe 7 6 s6_1360 := by
  apply safe_succ 6 6 s6_1360 [s7_811, s7_861] (by decide) s6_1360_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_811_safe
  · subst z; exact s7_861_safe
def s6_1361 : State := ⟨[104,4,67,129], 1020847121124453156722079280538140606750, 1, 0, 1, 0⟩
theorem s6_1361_edges : next config 6 s6_1361 = [s7_693, s7_884, s7_862] := by decide
theorem s6_1361_safe : Safe 7 6 s6_1361 := by
  apply safe_succ 6 6 s6_1361 [s7_693, s7_884, s7_862] (by decide) s6_1361_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_693_safe
  · subst z; exact s7_884_safe
  · subst z; exact s7_862_safe
def s6_1362 : State := ⟨[104,4,67,130], 1701411854887101921134564166604226101534, 1, 0, 1, 0⟩
theorem s6_1362_edges : next config 6 s6_1362 = [s7_813] := by decide
theorem s6_1362_safe : Safe 7 6 s6_1362 := by
  apply safe_succ 6 6 s6_1362 [s7_813] (by decide) s6_1362_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_813_safe
def s6_1363 : State := ⟨[104,4,67,130], 1701411854966330083648828495401677029662, 1, 0, 1, 0⟩
theorem s6_1363_edges : next config 6 s6_1363 = [s7_695, s7_885] := by decide
theorem s6_1363_safe : Safe 7 6 s6_1363 := by
  apply safe_succ 6 6 s6_1363 [s7_695, s7_885] (by decide) s6_1363_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_695_safe
  · subst z; exact s7_885_safe
def s6_1364 : State := ⟨[104,4,67,131], 3062541322570855774988062596331298947358, 1, 0, 1, 0⟩
theorem s6_1364_edges : next config 6 s6_1364 = [s7_815] := by decide
theorem s6_1364_safe : Safe 7 6 s6_1364 := by
  apply safe_succ 6 6 s6_1364 [s7_815] (by decide) s6_1364_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_815_safe
def s6_1365 : State := ⟨[104,4,67,131], 3062541322650083937502326925128749875486, 1, 0, 1, 0⟩
theorem s6_1365_edges : next config 6 s6_1365 = [s7_697, s7_886] := by decide
theorem s6_1365_safe : Safe 7 6 s6_1365 := by
  apply safe_succ 6 6 s6_1365 [s7_697, s7_886] (by decide) s6_1365_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_697_safe
  · subst z; exact s7_886_safe
def s6_1366 : State := ⟨[104,4,67,132], 5784800257938363482695059455785444639006, 1, 0, 1, 0⟩
theorem s6_1366_edges : next config 6 s6_1366 = [s7_817] := by decide
theorem s6_1366_safe : Safe 7 6 s6_1366 := by
  apply safe_succ 6 6 s6_1366 [s7_817] (by decide) s6_1366_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_817_safe
def s6_1367 : State := ⟨[104,4,67,132], 5784800258017591645209323784582895567134, 1, 0, 1, 0⟩
theorem s6_1367_edges : next config 6 s6_1367 = [s7_698, s7_887, s7_857] := by decide
theorem s6_1367_safe : Safe 7 6 s6_1367 := by
  apply safe_succ 6 6 s6_1367 [s7_698, s7_887, s7_857] (by decide) s6_1367_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_698_safe
  · subst z; exact s7_887_safe
  · subst z; exact s7_857_safe
def s6_1368 : State := ⟨[104,4,67,136], 87452568318963594713904965239409815388446, 1, 0, 1, 0⟩
theorem s6_1368_edges : next config 6 s6_1368 = [s7_819] := by decide
theorem s6_1368_safe : Safe 7 6 s6_1368 := by
  apply safe_succ 6 6 s6_1368 [s7_819] (by decide) s6_1368_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_819_safe
def s6_1369 : State := ⟨[104,4,67,136], 87452568319042822876419229568207266316574, 1, 0, 1, 0⟩
theorem s6_1369_edges : next config 6 s6_1369 = [s7_700, s7_897, s7_888, s7_858] := by decide
theorem s6_1369_safe : Safe 7 6 s6_1369 := by
  apply safe_succ 6 6 s6_1369 [s7_700, s7_897, s7_888, s7_858] (by decide) s6_1369_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_700_safe
  · subst z; exact s7_897_safe
  · subst z; exact s7_888_safe
  · subst z; exact s7_858_safe
def s6_1370 : State := ⟨[104,4,67,144], 22301085480917826489602999338385238659236126, 1, 0, 1, 0⟩
theorem s6_1370_edges : next config 6 s6_1370 = [s7_823] := by decide
theorem s6_1370_safe : Safe 7 6 s6_1370 := by
  apply safe_succ 6 6 s6_1370 [s7_823] (by decide) s6_1370_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_823_safe
def s6_1371 : State := ⟨[104,4,67,144], 22301085480917905717765513602714036110164254, 1, 0, 1, 0⟩
theorem s6_1371_edges : next config 6 s6_1371 = [s7_702, s7_890] := by decide
theorem s6_1371_safe : Safe 7 6 s6_1371 := by
  apply safe_succ 6 6 s6_1371 [s7_702, s7_890] (by decide) s6_1371_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_702_safe
  · subst z; exact s7_890_safe
def s6_1372 : State := ⟨[104,4,67,160], 1461501637671185305407032899997348756533085798686, 1, 0, 1, 0⟩
theorem s6_1372_edges : next config 6 s6_1372 = [s7_826] := by decide
theorem s6_1372_safe : Safe 7 6 s6_1372 := by
  apply safe_succ 6 6 s6_1372 [s7_826] (by decide) s6_1372_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_826_safe
def s6_1373 : State := ⟨[104,4,67,160], 1461501637671185305486261062511613085330536726814, 1, 0, 1, 0⟩
theorem s6_1373_edges : next config 6 s6_1373 = [s7_709, s7_891] := by decide
theorem s6_1373_safe : Safe 7 6 s6_1373 := by
  apply safe_succ 6 6 s6_1373 [s7_709, s7_891] (by decide) s6_1373_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_709_safe
  · subst z; exact s7_891_safe
def s6_1374 : State := ⟨[104,4,67,163], 11692013098987505732832826729011329894124613599518, 1, 0, 1, 0⟩
theorem s6_1374_edges : next config 6 s6_1374 = [s7_828] := by decide
theorem s6_1374_safe : Safe 7 6 s6_1374 := by
  apply safe_succ 6 6 s6_1374 [s7_828] (by decide) s6_1374_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_828_safe
def s6_1375 : State := ⟨[104,4,67,163], 11692013098987505732912054891525594222922064527646, 1, 0, 1, 0⟩
theorem s6_1375_edges : next config 6 s6_1375 = [s7_712, s7_892, s7_873] := by decide
theorem s6_1375_safe : Safe 7 6 s6_1375 := by
  apply safe_succ 6 6 s6_1375 [s7_712, s7_892, s7_873] (by decide) s6_1375_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_712_safe
  · subst z; exact s7_892_safe
  · subst z; exact s7_873_safe
def s6_1376 : State := ⟨[104,4,67,171], 2993155353254029458868349885470228689992227001270558, 1, 0, 1, 0⟩
theorem s6_1376_edges : next config 6 s6_1376 = [s7_829] := by decide
theorem s6_1376_safe : Safe 7 6 s6_1376 := by
  apply safe_succ 6 6 s6_1376 [s7_829] (by decide) s6_1376_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_829_safe
def s6_1377 : State := ⟨[104,4,67,192], 6277101735386680764176071810411014483383421181341187768606, 1, 0, 1, 0⟩
theorem s6_1377_edges : next config 6 s6_1377 = [s7_831] := by decide
theorem s6_1377_safe : Safe 7 6 s6_1377 := by
  apply safe_succ 6 6 s6_1377 [s7_831] (by decide) s6_1377_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_831_safe
def s6_1378 : State := ⟨[104,4,67,192], 6277101735386680764176071810490242645897685510138638696734, 1, 0, 1, 0⟩
theorem s6_1378_edges : next config 6 s6_1378 = [s7_716, s7_893] := by decide
theorem s6_1378_safe : Safe 7 6 s6_1378 := by
  apply safe_succ 6 6 s6_1378 [s7_716, s7_893] (by decide) s6_1378_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_716_safe
  · subst z; exact s7_893_safe
def s6_1379 : State := ⟨[104,4,67,195], 50216813883093446111026597772864679396099909292589429358878, 1, 0, 1, 0⟩
theorem s6_1379_edges : next config 6 s6_1379 = [s7_833] := by decide
theorem s6_1379_safe : Safe 7 6 s6_1379 := by
  apply safe_succ 6 6 s6_1379 [s7_833] (by decide) s6_1379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_833_safe
def s6_1380 : State := ⟨[104,4,67,195], 50216813883093446111026597772943907558614173621386880287006, 1, 0, 1, 0⟩
theorem s6_1380_edges : next config 6 s6_1380 = [s7_718, s7_937, s7_894, s7_874] := by decide
theorem s6_1380_safe : Safe 7 6 s6_1380 := by
  apply safe_succ 6 6 s6_1380 [s7_718, s7_937, s7_894, s7_874] (by decide) s6_1380_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_718_safe
  · subst z; exact s7_937_safe
  · subst z; exact s7_894_safe
  · subst z; exact s7_874_safe
def s6_1381 : State := ⟨[104,4,67,224], 26959946667150639794667015087359913060919720652335902546778214433054, 1, 0, 1, 0⟩
theorem s6_1381_edges : next config 6 s6_1381 = [s7_720, s7_895] := by decide
theorem s6_1381_safe : Safe 7 6 s6_1381 := by
  apply safe_succ 6 6 s6_1381 [s7_720, s7_895] (by decide) s6_1381_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_720_safe
  · subst z; exact s7_895_safe
def s6_1382 : State := ⟨[104,4,67,232], 6901746346790563787434755862277365734838312320237667620899401377055006, 1, 0, 1, 0⟩
theorem s6_1382_edges : next config 6 s6_1382 = [s7_836] := by decide
theorem s6_1382_safe : Safe 7 6 s6_1382 := by
  apply safe_succ 6 6 s6_1382 [s7_836] (by decide) s6_1382_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_836_safe
def s6_1383 : State := ⟨[104,4,67,232], 6901746346790563787434755862277365734838391548400181885228198827983134, 1, 0, 1, 0⟩
theorem s6_1383_edges : next config 6 s6_1383 = [s7_722, s7_896, s7_875] := by decide
theorem s6_1383_safe : Safe 7 6 s6_1383 := by
  apply safe_succ 6 6 s6_1383 [s7_722, s7_896, s7_875] (by decide) s6_1383_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s7_722_safe
  · subst z; exact s7_896_safe
  · subst z; exact s7_875_safe
def s6_1384 : State := ⟨[104,12,67,128], 340282387282576229795330065674604187934, 3, 0, 0, 0⟩
theorem s6_1384_edges : next config 6 s6_1384 = [s7_847, s7_896, s7_889, s7_894, s7_885, s7_888, s7_890, s7_891] := by decide
theorem s6_1384_safe : Safe 7 6 s6_1384 := by
  apply safe_succ 6 6 s6_1384 [s7_847, s7_896, s7_889, s7_894, s7_885, s7_888, s7_890, s7_891] (by decide) s6_1384_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s7_847_safe
  · subst z; exact s7_896_safe
  · subst z; exact s7_889_safe
  · subst z; exact s7_894_safe
  · subst z; exact s7_885_safe
  · subst z; exact s7_888_safe
  · subst z; exact s7_890_safe
  · subst z; exact s7_891_safe
def s6_1385 : State := ⟨[113,4,96,145], 44601830689812840166767087888046818987278622, 1, 1, 1, 0⟩
theorem s6_1385_edges : next config 6 s6_1385 = [s7_902, s7_898] := by decide
theorem s6_1385_safe : Safe 7 6 s6_1385 := by
  apply safe_succ 6 6 s6_1385 [s7_902, s7_898] (by decide) s6_1385_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_902_safe
  · subst z; exact s7_898_safe
def s6_1386 : State := ⟨[113,4,96,145], 44601830689812840166767087888046818987282710, 3, 2, 1, 0⟩
theorem s6_1386_edges : next config 6 s6_1386 = [s7_899] := by decide
theorem s6_1386_safe : Safe 7 6 s6_1386 := by
  apply safe_succ 6 6 s6_1386 [s7_899] (by decide) s6_1386_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_899_safe
def s6_1387 : State := ⟨[113,4,96,145], 44601830689812840166767087888046818989375766, 3, 2, 1, 0⟩
theorem s6_1387_edges : next config 6 s6_1387 = [s7_903, s7_900] := by decide
theorem s6_1387_safe : Safe 7 6 s6_1387 := by
  apply safe_succ 6 6 s6_1387 [s7_903, s7_900] (by decide) s6_1387_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_903_safe
  · subst z; exact s7_900_safe
def s6_1388 : State := ⟨[113,4,96,145], 44601830689812840166767124781534966406381846, 1, 1, 1, 0⟩
theorem s6_1388_edges : next config 6 s6_1388 = [s7_904, s7_901] := by decide
theorem s6_1388_safe : Safe 7 6 s6_1388 := by
  apply safe_succ 6 6 s6_1388 [s7_904, s7_901] (by decide) s6_1388_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_904_safe
  · subst z; exact s7_901_safe
def s6_1389 : State := ⟨[113,12,104,145], 44601830689833122576370739558470766238568726, 3, 0, 1, 0⟩
theorem s6_1389_edges : next config 6 s6_1389 = [s7_899] := by decide
theorem s6_1389_safe : Safe 7 6 s6_1389 := by
  apply safe_succ 6 6 s6_1389 [s7_899] (by decide) s6_1389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_899_safe
def s6_1390 : State := ⟨[113,21,104,145], 44601830689833122576370739558470766240661782, 3, 0, 1, 0⟩
theorem s6_1390_edges : next config 6 s6_1390 = [s7_909, s7_908] := by decide
theorem s6_1390_safe : Safe 7 6 s6_1390 := by
  apply safe_succ 6 6 s6_1390 [s7_909, s7_908] (by decide) s6_1390_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_909_safe
  · subst z; exact s7_908_safe
def s6_1391 : State := ⟨[117,4,104,145], 44601830845602028332415568414385656117264662, 1, 0, 1, 0⟩
theorem s6_1391_edges : next config 6 s6_1391 = [] := by decide
theorem s6_1391_safe : Safe 7 6 s6_1391 := by
  apply safe_succ 6 6 s6_1391 [] (by decide) s6_1391_edges
  simp
def s6_1392 : State := ⟨[121,21,104,145], 44601833337904520429132830109023894142910742, 3, 0, 1, 0⟩
theorem s6_1392_edges : next config 6 s6_1392 = [] := by decide
theorem s6_1392_safe : Safe 7 6 s6_1392 := by
  apply safe_succ 6 6 s6_1392 [] (by decide) s6_1392_edges
  simp
def s6_1393 : State := ⟨[125,4,104,145], 44601873214744393976609017223235702553248022, 1, 0, 1, 0⟩
theorem s6_1393_edges : next config 6 s6_1393 = [s7_915] := by decide
theorem s6_1393_safe : Safe 7 6 s6_1393 := by
  apply safe_succ 6 6 s6_1393 [s7_915] (by decide) s6_1393_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_915_safe
def s6_1394 : State := ⟨[131,4,96,146], 89207404464892543994330429671571730559209750, 3, 2, 1, 0⟩
theorem s6_1394_edges : next config 6 s6_1394 = [s7_916] := by decide
theorem s6_1394_safe : Safe 7 6 s6_1394 := by
  apply safe_succ 6 6 s6_1394 [s7_916] (by decide) s6_1394_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_916_safe
def s6_1395 : State := ⟨[131,4,96,162], 5846006553747282442866167518421713056908265459990, 3, 2, 1, 0⟩
theorem s6_1395_edges : next config 6 s6_1395 = [s7_917] := by decide
theorem s6_1395_safe : Safe 7 6 s6_1395 := by
  apply safe_succ 6 6 s6_1395 [s7_917] (by decide) s6_1395_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_917_safe
def s6_1396 : State := ⟨[131,4,104,130], 4423670790333837791208251402231786574102, 3, 2, 1, 0⟩
theorem s6_1396_edges : next config 6 s6_1396 = [s7_81, s7_932, s7_916, s7_917] := by decide
theorem s6_1396_safe : Safe 7 6 s6_1396 := by
  apply safe_succ 6 6 s6_1396 [s7_81, s7_932, s7_916, s7_917] (by decide) s6_1396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s7_81_safe
  · subst z; exact s7_932_safe
  · subst z; exact s7_916_safe
  · subst z; exact s7_917_safe
def s6_1397 : State := ⟨[131,4,104,130], 4423670791601488391436480803728489775382, 3, 2, 1, 0⟩
theorem s6_1397_edges : next config 6 s6_1397 = [s7_82] := by decide
theorem s6_1397_safe : Safe 7 6 s6_1397 := by
  apply safe_succ 6 6 s6_1397 [s7_82] (by decide) s6_1397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_82_safe
def s6_1398 : State := ⟨[131,4,104,130], 4423671114852391449634978185387807146262, 3, 2, 1, 0⟩
theorem s6_1398_edges : next config 6 s6_1398 = [s7_83] := by decide
theorem s6_1398_safe : Safe 7 6 s6_1398 := by
  apply safe_succ 6 6 s6_1398 [s7_83] (by decide) s6_1398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_83_safe
def s6_1399 : State := ⟨[131,12,104,146], 89207404464912826403934081341995677810495766, 3, 0, 1, 0⟩
theorem s6_1399_edges : next config 6 s6_1399 = [s7_916] := by decide
theorem s6_1399_safe : Safe 7 6 s6_1399 := by
  apply safe_succ 6 6 s6_1399 [s7_916] (by decide) s6_1399_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_916_safe
def s6_1400 : State := ⟨[131,12,104,162], 5846006553747282463148577122073383480855516746006, 3, 0, 1, 0⟩
theorem s6_1400_edges : next config 6 s6_1400 = [s7_917] := by decide
theorem s6_1400_safe : Safe 7 6 s6_1400 := by
  apply safe_succ 6 6 s6_1400 [s7_917] (by decide) s6_1400_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_917_safe
def s6_1401 : State := ⟨[146,4,64,145], 133805492038284501664604718206456542345105694, 3, 2, 1, 0⟩
theorem s6_1401_edges : next config 6 s6_1401 = [s7_922] := by decide
theorem s6_1401_safe : Safe 7 6 s6_1401 := by
  apply safe_succ 6 6 s6_1401 [s7_922] (by decide) s6_1401_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_922_safe
def s6_1402 : State := ⟨[146,4,64,145], 156105556672081282929213509729890040314663198, 3, 2, 1, 0⟩
theorem s6_1402_edges : next config 6 s6_1402 = [s7_923] := by decide
theorem s6_1402_safe : Safe 7 6 s6_1402 := by
  apply safe_succ 6 6 s6_1402 [s7_923] (by decide) s6_1402_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_923_safe
def s6_1403 : State := ⟨[146,4,67,145], 133804811473550659787677939031194268485222686, 1, 1, 1, 0⟩
theorem s6_1403_edges : next config 6 s6_1403 = [s7_925] := by decide
theorem s6_1403_safe : Safe 7 6 s6_1403 := by
  apply safe_succ 6 6 s6_1403 [s7_925] (by decide) s6_1403_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_925_safe
def s6_1404 : State := ⟨[146,4,96,145], 133804811473550739015840305721579272352760094, 1, 1, 1, 0⟩
theorem s6_1404_edges : next config 6 s6_1404 = [s7_926, s7_924] := by decide
theorem s6_1404_safe : Safe 7 6 s6_1404 := by
  apply safe_succ 6 6 s6_1404 [s7_926, s7_924] (by decide) s6_1404_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_926_safe
  · subst z; exact s7_924_safe
def s6_1405 : State := ⟨[146,4,104,145], 133805492038304863302370884141218083140337950, 1, 0, 1, 0⟩
theorem s6_1405_edges : next config 6 s6_1405 = [s7_927] := by decide
theorem s6_1405_safe : Safe 7 6 s6_1405 := by
  apply safe_succ 6 6 s6_1405 [s7_927] (by decide) s6_1405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_927_safe
def s6_1406 : State := ⟨[146,4,104,145], 156105556672101644566979675664651581109895454, 1, 0, 1, 0⟩
theorem s6_1406_edges : next config 6 s6_1406 = [s7_928] := by decide
theorem s6_1406_safe : Safe 7 6 s6_1406 := by
  apply safe_succ 6 6 s6_1406 [s7_928] (by decide) s6_1406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_928_safe
def s6_1407 : State := ⟨[146,12,64,145], 133804811473550659787677791457241678808813854, 3, 1, 1, 0⟩
theorem s6_1407_edges : next config 6 s6_1407 = [s7_918, s7_926] := by decide
theorem s6_1407_safe : Safe 7 6 s6_1407 := by
  apply safe_succ 6 6 s6_1407 [s7_918, s7_926] (by decide) s6_1407_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_918_safe
  · subst z; exact s7_926_safe
def s6_1408 : State := ⟨[146,12,67,145], 133805492038284501664604865780409132021518622, 3, 0, 1, 0⟩
theorem s6_1408_edges : next config 6 s6_1408 = [s7_920] := by decide
theorem s6_1408_safe : Safe 7 6 s6_1408 := by
  apply safe_succ 6 6 s6_1408 [s7_920] (by decide) s6_1408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_920_safe
def s6_1409 : State := ⟨[146,12,67,145], 156105556672081282929213657303842629991076126, 3, 0, 1, 0⟩
theorem s6_1409_edges : next config 6 s6_1409 = [s7_921] := by decide
theorem s6_1409_safe : Safe 7 6 s6_1409 := by
  apply safe_succ 6 6 s6_1409 [s7_921] (by decide) s6_1409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_921_safe
def s6_1410 : State := ⟨[146,12,96,145], 133805492038284580892767232470794135889056030, 3, 0, 1, 0⟩
theorem s6_1410_edges : next config 6 s6_1410 = [s7_922, s7_927] := by decide
theorem s6_1410_safe : Safe 7 6 s6_1410 := by
  apply safe_succ 6 6 s6_1410 [s7_922, s7_927] (by decide) s6_1410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_922_safe
  · subst z; exact s7_927_safe
def s6_1411 : State := ⟨[146,12,96,145], 156105556672081362157376023994227633858613534, 3, 0, 1, 0⟩
theorem s6_1411_edges : next config 6 s6_1411 = [s7_923, s7_928] := by decide
theorem s6_1411_safe : Safe 7 6 s6_1411 := by
  apply safe_succ 6 6 s6_1411 [s7_923, s7_928] (by decide) s6_1411_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_923_safe
  · subst z; exact s7_928_safe
def s6_1412 : State := ⟨[146,21,64,145], 133804811473550659787677791457241678810906910, 3, 1, 1, 0⟩
theorem s6_1412_edges : next config 6 s6_1412 = [s7_930] := by decide
theorem s6_1412_safe : Safe 7 6 s6_1412 := by
  apply safe_succ 6 6 s6_1412 [s7_930] (by decide) s6_1412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_930_safe
def s6_1413 : State := ⟨[161,4,104,160], 4384504912332991141893630727796605172018365665558, 3, 2, 1, 0⟩
theorem s6_1413_edges : next config 6 s6_1413 = [s7_134, s7_934] := by decide
theorem s6_1413_safe : Safe 7 6 s6_1413 := by
  apply safe_succ 6 6 s6_1413 [s7_134, s7_934] (by decide) s6_1413_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_134_safe
  · subst z; exact s7_934_safe
def s6_1414 : State := ⟨[163,4,67,160], 13153514736318408630754101958075942481002842099998, 3, 2, 1, 0⟩
theorem s6_1414_edges : next config 6 s6_1414 = [] := by decide
theorem s6_1414_safe : Safe 7 6 s6_1414 := by
  apply safe_succ 6 6 s6_1414 [] (by decide) s6_1414_edges
  simp
def s6_1415 : State := ⟨[163,4,96,130], 11692013100348635180313399141579848276086439874838, 3, 2, 1, 0⟩
theorem s6_1415_edges : next config 6 s6_1415 = [s7_931] := by decide
theorem s6_1415_safe : Safe 7 6 s6_1415 := by
  apply safe_succ 6 6 s6_1415 [s7_931] (by decide) s6_1415_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_931_safe
def s6_1416 : State := ⟨[163,4,96,130], 11692013103070894115680906849286845135531995631894, 3, 2, 1, 0⟩
theorem s6_1416_edges : next config 6 s6_1416 = [s7_932] := by decide
theorem s6_1416_safe : Safe 7 6 s6_1416 := by
  apply safe_succ 6 6 s6_1416 [s7_932] (by decide) s6_1416_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_932_safe
def s6_1417 : State := ⟨[163,4,96,160], 13153514736318408630833330120442632866006709637406, 3, 2, 1, 0⟩
theorem s6_1417_edges : next config 6 s6_1417 = [s7_933] := by decide
theorem s6_1417_safe : Safe 7 6 s6_1417 := by
  apply safe_succ 6 6 s6_1417 [s7_933] (by decide) s6_1417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_933_safe
def s6_1418 : State := ⟨[163,4,96,160], 16076518010980214467240699785875198905318574723350, 3, 2, 1, 0⟩
theorem s6_1418_edges : next config 6 s6_1418 = [s7_934] := by decide
theorem s6_1418_safe : Safe 7 6 s6_1418 := by
  apply safe_succ 6 6 s6_1418 [s7_934] (by decide) s6_1418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_934_safe
def s6_1419 : State := ⟨[163,4,96,162], 17538019649672246853128138472444980354701580112150, 3, 2, 1, 0⟩
theorem s6_1419_edges : next config 6 s6_1419 = [s7_52, s7_935] := by decide
theorem s6_1419_safe : Safe 7 6 s6_1419 := by
  apply safe_succ 6 6 s6_1419 [s7_52, s7_935] (by decide) s6_1419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_52_safe
  · subst z; exact s7_935_safe
def s6_1420 : State := ⟨[163,4,96,162], 18999521285642020303648069451307764944630439809302, 3, 2, 1, 0⟩
theorem s6_1420_edges : next config 6 s6_1420 = [s7_53, s7_936] := by decide
theorem s6_1420_safe : Safe 7 6 s6_1420 := by
  apply safe_succ 6 6 s6_1420 [s7_53, s7_936] (by decide) s6_1420_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_53_safe
  · subst z; exact s7_936_safe
def s6_1421 : State := ⟨[163,12,104,130], 11692013100348635200595808745231518700033691160854, 3, 0, 1, 0⟩
theorem s6_1421_edges : next config 6 s6_1421 = [s7_931] := by decide
theorem s6_1421_safe : Safe 7 6 s6_1421 := by
  apply safe_succ 6 6 s6_1421 [s7_931] (by decide) s6_1421_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_931_safe
def s6_1422 : State := ⟨[163,12,104,130], 11692013103070894135963316452938515559479246917910, 3, 0, 1, 0⟩
theorem s6_1422_edges : next config 6 s6_1422 = [s7_932] := by decide
theorem s6_1422_safe : Safe 7 6 s6_1422 := by
  apply safe_succ 6 6 s6_1422 [s7_932] (by decide) s6_1422_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_932_safe
def s6_1423 : State := ⟨[163,12,104,160], 13153514736318408651115739724094303289953960923422, 3, 0, 1, 0⟩
theorem s6_1423_edges : next config 6 s6_1423 = [s7_933] := by decide
theorem s6_1423_safe : Safe 7 6 s6_1423 := by
  apply safe_succ 6 6 s6_1423 [s7_933] (by decide) s6_1423_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_933_safe
def s6_1424 : State := ⟨[163,12,104,160], 16076518010980214487523109389526869329265826009366, 3, 0, 1, 0⟩
theorem s6_1424_edges : next config 6 s6_1424 = [s7_934] := by decide
theorem s6_1424_safe : Safe 7 6 s6_1424 := by
  apply safe_succ 6 6 s6_1424 [s7_934] (by decide) s6_1424_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_934_safe
def s6_1425 : State := ⟨[163,12,104,162], 17538019649672246873410548076096650778648831398166, 3, 0, 1, 0⟩
theorem s6_1425_edges : next config 6 s6_1425 = [s7_261, s7_935] := by decide
theorem s6_1425_safe : Safe 7 6 s6_1425 := by
  apply safe_succ 6 6 s6_1425 [s7_261, s7_935] (by decide) s6_1425_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_261_safe
  · subst z; exact s7_935_safe
def s6_1426 : State := ⟨[163,12,104,162], 18999521285642020323930479054959435368577691095318, 3, 0, 1, 0⟩
theorem s6_1426_edges : next config 6 s6_1426 = [s7_262, s7_936] := by decide
theorem s6_1426_safe : Safe 7 6 s6_1426 := by
  apply safe_succ 6 6 s6_1426 [s7_262, s7_936] (by decide) s6_1426_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_262_safe
  · subst z; exact s7_936_safe
def s6_1427 : State := ⟨[171,4,67,136], 2993155353341141744779906950675715183399609863045406, 1, 0, 1, 0⟩
theorem s6_1427_edges : next config 6 s6_1427 = [] := by decide
theorem s6_1427_safe : Safe 7 6 s6_1427 := by
  apply safe_succ 6 6 s6_1427 [] (by decide) s6_1427_edges
  simp
def s6_1428 : State := ⟨[171,4,67,136], 2993155353341141744779906950675715183399618452979990, 1, 0, 1, 0⟩
theorem s6_1428_edges : next config 6 s6_1428 = [] := by decide
theorem s6_1428_safe : Safe 7 6 s6_1428 := by
  apply safe_succ 6 6 s6_1428 [] (by decide) s6_1428_edges
  simp
def s6_1429 : State := ⟨[171,4,104,130], 3004847366354037811681742346148179142955383539171606, 1, 0, 1, 0⟩
theorem s6_1429_edges : next config 6 s6_1429 = [] := by decide
theorem s6_1429_safe : Safe 7 6 s6_1429 := by
  apply safe_succ 6 6 s6_1429 [] (by decide) s6_1429_edges
  simp
def s6_1430 : State := ⟨[171,4,104,130], 3004847366356760070617109853855886139814829094928662, 1, 0, 1, 0⟩
theorem s6_1430_edges : next config 6 s6_1430 = [] := by decide
theorem s6_1430_safe : Safe 7 6 s6_1430 := by
  apply safe_succ 6 6 s6_1430 [] (by decide) s6_1430_edges
  simp
def s6_1431 : State := ⟨[171,4,104,136], 2993155353341141744800189360279219279870967437918494, 1, 0, 1, 0⟩
theorem s6_1431_edges : next config 6 s6_1431 = [] := by decide
theorem s6_1431_safe : Safe 7 6 s6_1431 := by
  apply safe_succ 6 6 s6_1431 [] (by decide) s6_1431_edges
  simp
def s6_1432 : State := ⟨[171,4,104,136], 2993155353341141744800189360279219279870976027853078, 1, 0, 1, 0⟩
theorem s6_1432_edges : next config 6 s6_1432 = [] := by decide
theorem s6_1432_safe : Safe 7 6 s6_1432 := by
  apply safe_succ 6 6 s6_1432 [] (by decide) s6_1432_edges
  simp
def s6_1433 : State := ⟨[171,4,104,160], 3006308867990007585132262277127041927545303808934174, 1, 0, 1, 0⟩
theorem s6_1433_edges : next config 6 s6_1433 = [] := by decide
theorem s6_1433_safe : Safe 7 6 s6_1433 := by
  apply safe_succ 6 6 s6_1433 [] (by decide) s6_1433_edges
  simp
def s6_1434 : State := ⟨[171,4,104,160], 3009231871264669390968669646792474493584615674020118, 1, 0, 1, 0⟩
theorem s6_1434_edges : next config 6 s6_1434 = [] := by decide
theorem s6_1434_safe : Safe 7 6 s6_1434 := by
  apply safe_succ 6 6 s6_1434 [] (by decide) s6_1434_edges
  simp
def s6_1435 : State := ⟨[171,4,104,162], 2999001359804714200008927606817314010876751219065622, 1, 0, 1, 0⟩
theorem s6_1435_edges : next config 6 s6_1435 = [] := by decide
theorem s6_1435_safe : Safe 7 6 s6_1435 := by
  apply safe_succ 6 6 s6_1435 [] (by decide) s6_1435_edges
  simp
def s6_1436 : State := ⟨[171,4,104,162], 3000462861440683973459447537796176795466680078762774, 1, 0, 1, 0⟩
theorem s6_1436_edges : next config 6 s6_1436 = [] := by decide
theorem s6_1436_safe : Safe 7 6 s6_1436 := by
  apply safe_succ 6 6 s6_1436 [] (by decide) s6_1436_edges
  simp
def s6_1437 : State := ⟨[171,4,104,162], 3010693372903361423354557085479044275033998679408918, 1, 0, 1, 0⟩
theorem s6_1437_edges : next config 6 s6_1437 = [] := by decide
theorem s6_1437_safe : Safe 7 6 s6_1437 := by
  apply safe_succ 6 6 s6_1437 [] (by decide) s6_1437_edges
  simp
def s6_1438 : State := ⟨[171,4,104,162], 3012154874539331196805077016457907059623927539106070, 1, 0, 1, 0⟩
theorem s6_1438_edges : next config 6 s6_1438 = [] := by decide
theorem s6_1438_safe : Safe 7 6 s6_1438 := by
  apply safe_succ 6 6 s6_1438 [] (by decide) s6_1438_edges
  simp
def s6_1439 : State := ⟨[171,4,104,170], 4495579036431558788249500875518787823004426143072534, 1, 0, 1, 0⟩
theorem s6_1439_edges : next config 6 s6_1439 = [s7_144] := by decide
theorem s6_1439_safe : Safe 7 6 s6_1439 := by
  apply safe_succ 6 6 s6_1439 [s7_144] (by decide) s6_1439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_144_safe
def s6_1440 : State := ⟨[171,4,104,170], 4497040538067528561700020806497650607594355002769686, 1, 0, 1, 0⟩
theorem s6_1440_edges : next config 6 s6_1440 = [s7_145] := by decide
theorem s6_1440_safe : Safe 7 6 s6_1440 := by
  apply safe_succ 6 6 s6_1440 [s7_145] (by decide) s6_1440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_145_safe
def s6_1441 : State := ⟨[193,4,104,192], 18831305206160042291847650656905575477954822446442671575318, 3, 2, 1, 0⟩
theorem s6_1441_edges : next config 6 s6_1441 = [s7_160] := by decide
theorem s6_1441_safe : Safe 7 6 s6_1441 := by
  apply safe_succ 6 6 s6_1441 [s7_160] (by decide) s6_1441_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_160_safe
def s6_1442 : State := ⟨[193,4,104,192], 18831305206160042291847650658173226078183051847939374776598, 3, 2, 1, 0⟩
theorem s6_1442_edges : next config 6 s6_1442 = [s7_161] := by decide
theorem s6_1442_safe : Safe 7 6 s6_1442 := by
  apply safe_succ 6 6 s6_1442 [s7_161] (by decide) s6_1442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_161_safe
def s6_1443 : State := ⟨[193,4,104,192], 18831305206160042291847650981424129136381549229598692147478, 3, 2, 1, 0⟩
theorem s6_1443_edges : next config 6 s6_1443 = [s7_162] := by decide
theorem s6_1443_safe : Safe 7 6 s6_1443 := by
  apply safe_succ 6 6 s6_1443 [s7_162] (by decide) s6_1443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_162_safe
def s6_1444 : State := ⟨[225,4,104,224], 80879840001451919384001045261399174408194009497269473556361398784278, 3, 2, 1, 0⟩
theorem s6_1444_edges : next config 6 s6_1444 = [s7_196] := by decide
theorem s6_1444_safe : Safe 7 6 s6_1444 := by
  apply safe_succ 6 6 s6_1444 [s7_196] (by decide) s6_1444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_196_safe
end HGP13.SectorGraph234
