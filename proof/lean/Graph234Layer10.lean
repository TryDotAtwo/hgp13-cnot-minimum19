import Graph234Layer11
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s10_0 : State := ⟨[21,4,125,145], 44601873214744393976609017223235702553252126, 3, 3, 1, 0⟩
theorem s10_0_edges : next config 10 s10_0 = [] := by decide
theorem s10_0_safe : Safe 3 10 s10_0 := by
  apply safe_succ 2 10 s10_0 [] (by decide) s10_0_edges
  simp
def s10_1 : State := ⟨[21,4,125,145], 44601873214744393976609054116723849972355350, 3, 3, 1, 0⟩
theorem s10_1_edges : next config 10 s10_1 = [] := by decide
theorem s10_1_safe : Safe 3 10 s10_1 := by
  apply safe_succ 2 10 s10_1 [] (by decide) s10_1_edges
  simp
def s10_2 : State := ⟨[35,4,125,145], 44601873214744393976609017223235736912986398, 3, 3, 1, 0⟩
theorem s10_2_edges : next config 10 s10_2 = [] := by decide
theorem s10_2_safe : Safe 3 10 s10_2 := by
  apply safe_succ 2 10 s10_2 [] (by decide) s10_2_edges
  simp
def s10_3 : State := ⟨[35,4,125,145], 44601873214744393976609017223235745502920982, 3, 3, 1, 0⟩
theorem s10_3_edges : next config 10 s10_3 = [] := by decide
theorem s10_3_safe : Safe 3 10 s10_3 := by
  apply safe_succ 2 10 s10_3 [] (by decide) s10_3_edges
  simp
def s10_4 : State := ⟨[35,12,67,145], 44601830679428246449697580204938450367090974, 3, 3, 1, 0⟩
theorem s10_4_edges : next config 10 s10_4 = [] := by decide
theorem s10_4_safe : Safe 3 10 s10_4 := by
  apply safe_succ 2 10 s10_4 [] (by decide) s10_4_edges
  simp
def s10_5 : State := ⟨[35,12,67,145], 44601830679428246449697580204938458957025558, 3, 3, 1, 0⟩
theorem s10_5_edges : next config 10 s10_5 = [] := by decide
theorem s10_5_safe : Safe 3 10 s10_5 := by
  apply safe_succ 2 10 s10_5 [] (by decide) s10_5_edges
  simp
def s10_6 : State := ⟨[35,21,67,145], 44601830679428246449697580204938450367090974, 3, 3, 1, 0⟩
theorem s10_6_edges : next config 10 s10_6 = [] := by decide
theorem s10_6_safe : Safe 3 10 s10_6 := by
  apply safe_succ 2 10 s10_6 [] (by decide) s10_6_edges
  simp
def s10_7 : State := ⟨[35,21,67,145], 44601830679428246449697580204938458957025558, 3, 3, 1, 0⟩
theorem s10_7_edges : next config 10 s10_7 = [] := by decide
theorem s10_7_safe : Safe 3 10 s10_7 := by
  apply safe_succ 2 10 s10_7 [] (by decide) s10_7_edges
  simp
def s10_8 : State := ⟨[35,62,67,145], 44601830679428246449697584816624469331345694, 3, 1, 1, 0⟩
theorem s10_8_edges : next config 10 s10_8 = [] := by decide
theorem s10_8_safe : Safe 3 10 s10_8 := by
  apply safe_succ 2 10 s10_8 [] (by decide) s10_8_edges
  simp
def s10_9 : State := ⟨[35,62,67,145], 44601830679428246449697584816624477921280278, 3, 1, 1, 0⟩
theorem s10_9_edges : next config 10 s10_9 = [] := by decide
theorem s10_9_safe : Safe 3 10 s10_9 := by
  apply safe_succ 2 10 s10_9 [] (by decide) s10_9_edges
  simp
def s10_10 : State := ⟨[35,62,67,145], 44601830679428246449697584834638867303956766, 3, 1, 1, 0⟩
theorem s10_10_edges : next config 10 s10_10 = [] := by decide
theorem s10_10_safe : Safe 3 10 s10_10 := by
  apply safe_succ 2 10 s10_10 [] (by decide) s10_10_edges
  simp
def s10_11 : State := ⟨[35,62,67,145], 44601830679428246449697584834638875893891350, 3, 1, 1, 0⟩
theorem s10_11_edges : next config 10 s10_11 = [] := by decide
theorem s10_11_safe : Safe 3 10 s10_11 := by
  apply safe_succ 2 10 s10_11 [] (by decide) s10_11_edges
  simp
def s10_12 : State := ⟨[43,4,67,145], 44601830679428246449697580204947246460109086, 3, 3, 1, 0⟩
theorem s10_12_edges : next config 10 s10_12 = [s11_3] := by decide
theorem s10_12_safe : Safe 3 10 s10_12 := by
  apply safe_succ 2 10 s10_12 [s11_3] (by decide) s10_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s11_3_safe
def s10_13 : State := ⟨[43,4,67,145], 44601830679428246449697580204947255050043670, 3, 3, 1, 0⟩
theorem s10_13_edges : next config 10 s10_13 = [s11_4] := by decide
theorem s10_13_safe : Safe 3 10 s10_13 := by
  apply safe_succ 2 10 s10_13 [s11_4] (by decide) s10_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s11_4_safe
def s10_14 : State := ⟨[43,4,104,145], 44601830679448528859301084301418604034982174, 3, 3, 1, 0⟩
theorem s10_14_edges : next config 10 s10_14 = [s11_0] := by decide
theorem s10_14_safe : Safe 3 10 s10_14 := by
  apply safe_succ 2 10 s10_14 [s11_0] (by decide) s10_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s11_0_safe
def s10_15 : State := ⟨[43,4,104,145], 44601830679448528859301084301418612624916758, 3, 3, 1, 0⟩
theorem s10_15_edges : next config 10 s10_15 = [s11_1] := by decide
theorem s10_15_safe : Safe 3 10 s10_15 := by
  apply safe_succ 2 10 s10_15 [s11_1] (by decide) s10_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s11_1_safe
def s10_16 : State := ⟨[43,21,67,145], 44601830679448528859301231875371193711395102, 3, 1, 1, 0⟩
theorem s10_16_edges : next config 10 s10_16 = [] := by decide
theorem s10_16_safe : Safe 3 10 s10_16 := by
  apply safe_succ 2 10 s10_16 [] (by decide) s10_16_edges
  simp
def s10_17 : State := ⟨[43,21,67,145], 44601830679448528859301231875371202301329686, 3, 1, 1, 0⟩
theorem s10_17_edges : next config 10 s10_17 = [] := by decide
theorem s10_17_safe : Safe 3 10 s10_17 := by
  apply safe_succ 2 10 s10_17 [] (by decide) s10_17_edges
  simp
def s10_18 : State := ⟨[43,62,67,145], 44601830679428246449697584816633264887496990, 3, 1, 1, 0⟩
theorem s10_18_edges : next config 10 s10_18 = [] := by decide
theorem s10_18_safe : Safe 3 10 s10_18 := by
  apply safe_succ 2 10 s10_18 [] (by decide) s10_18_edges
  simp
def s10_19 : State := ⟨[43,62,67,145], 44601830679428246449697584816633273477431574, 3, 1, 1, 0⟩
theorem s10_19_edges : next config 10 s10_19 = [] := by decide
theorem s10_19_safe : Safe 3 10 s10_19 := by
  apply safe_succ 2 10 s10_19 [] (by decide) s10_19_edges
  simp
def s10_20 : State := ⟨[49,4,125,145], 44601873214744393976609017223798652506669342, 3, 3, 1, 0⟩
theorem s10_20_edges : next config 10 s10_20 = [] := by decide
theorem s10_20_safe : Safe 3 10 s10_20 := by
  apply safe_succ 2 10 s10_20 [] (by decide) s10_20_edges
  simp
def s10_21 : State := ⟨[62,21,67,145], 44601830679428246449697584816633264887496990, 3, 1, 1, 0⟩
theorem s10_21_edges : next config 10 s10_21 = [] := by decide
theorem s10_21_safe : Safe 3 10 s10_21 := by
  apply safe_succ 2 10 s10_21 [] (by decide) s10_21_edges
  simp
def s10_22 : State := ⟨[62,21,67,145], 44601830679428246449697584816633273477431574, 3, 1, 1, 0⟩
theorem s10_22_edges : next config 10 s10_22 = [] := by decide
theorem s10_22_safe : Safe 3 10 s10_22 := by
  apply safe_succ 2 10 s10_22 [] (by decide) s10_22_edges
  simp
def s10_23 : State := ⟨[62,21,67,145], 44601830679428246449697584834638867303956766, 3, 1, 1, 0⟩
theorem s10_23_edges : next config 10 s10_23 = [] := by decide
theorem s10_23_safe : Safe 3 10 s10_23 := by
  apply safe_succ 2 10 s10_23 [] (by decide) s10_23_edges
  simp
def s10_24 : State := ⟨[62,21,67,145], 44601830679428246449697584834638875893891350, 3, 1, 1, 0⟩
theorem s10_24_edges : next config 10 s10_24 = [] := by decide
theorem s10_24_safe : Safe 3 10 s10_24 := by
  apply safe_succ 2 10 s10_24 [] (by decide) s10_24_edges
  simp
def s10_25 : State := ⟨[62,29,67,145], 44601830679428246449697584816624469331345694, 3, 1, 1, 0⟩
theorem s10_25_edges : next config 10 s10_25 = [] := by decide
theorem s10_25_safe : Safe 3 10 s10_25 := by
  apply safe_succ 2 10 s10_25 [] (by decide) s10_25_edges
  simp
def s10_26 : State := ⟨[62,29,67,145], 44601830679428246449697584816624477921280278, 3, 1, 1, 0⟩
theorem s10_26_edges : next config 10 s10_26 = [] := by decide
theorem s10_26_safe : Safe 3 10 s10_26 := by
  apply safe_succ 2 10 s10_26 [] (by decide) s10_26_edges
  simp
def s10_27 : State := ⟨[96,12,67,145], 44601830679428246449697580204938450367090974, 3, 3, 1, 0⟩
theorem s10_27_edges : next config 10 s10_27 = [] := by decide
theorem s10_27_safe : Safe 3 10 s10_27 := by
  apply safe_succ 2 10 s10_27 [] (by decide) s10_27_edges
  simp
def s10_28 : State := ⟨[96,21,67,145], 44601830679428246449697580204938450367090974, 3, 3, 1, 0⟩
theorem s10_28_edges : next config 10 s10_28 = [] := by decide
theorem s10_28_safe : Safe 3 10 s10_28 := by
  apply safe_succ 2 10 s10_28 [] (by decide) s10_28_edges
  simp
def s10_29 : State := ⟨[96,21,67,145], 44601830679448528859301231875371193711395102, 3, 1, 1, 0⟩
theorem s10_29_edges : next config 10 s10_29 = [] := by decide
theorem s10_29_safe : Safe 3 10 s10_29 := by
  apply safe_succ 2 10 s10_29 [] (by decide) s10_29_edges
  simp
def s10_30 : State := ⟨[96,62,67,145], 44601830679428246449697584816624469331345694, 3, 1, 1, 0⟩
theorem s10_30_edges : next config 10 s10_30 = [] := by decide
theorem s10_30_safe : Safe 3 10 s10_30 := by
  apply safe_succ 2 10 s10_30 [] (by decide) s10_30_edges
  simp
def s10_31 : State := ⟨[96,62,67,145], 44601830679428246449697584834638867303956766, 3, 1, 1, 0⟩
theorem s10_31_edges : next config 10 s10_31 = [] := by decide
theorem s10_31_safe : Safe 3 10 s10_31 := by
  apply safe_succ 2 10 s10_31 [] (by decide) s10_31_edges
  simp
def s10_32 : State := ⟨[104,4,67,145], 44601830679448449631138717611033600167444766, 3, 3, 1, 0⟩
theorem s10_32_edges : next config 10 s10_32 = [s11_2] := by decide
theorem s10_32_safe : Safe 3 10 s10_32 := by
  apply safe_succ 2 10 s10_32 [s11_2] (by decide) s10_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s11_2_safe
def s10_33 : State := ⟨[104,4,67,145], 44601830679448528859301231875362397616279838, 3, 3, 1, 0⟩
theorem s10_33_edges : next config 10 s10_33 = [] := by decide
theorem s10_33_safe : Safe 3 10 s10_33 := by
  apply safe_succ 2 10 s10_33 [] (by decide) s10_33_edges
  simp
def s10_34 : State := ⟨[104,4,67,145], 44601830679448528859301231875362397618372894, 3, 3, 1, 0⟩
theorem s10_34_edges : next config 10 s10_34 = [s11_0] := by decide
theorem s10_34_safe : Safe 3 10 s10_34 := by
  apply safe_succ 2 10 s10_34 [s11_0] (by decide) s10_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s11_0_safe
def s10_35 : State := ⟨[104,21,67,145], 44601830679448528859301231875371193711395102, 3, 1, 1, 0⟩
theorem s10_35_edges : next config 10 s10_35 = [] := by decide
theorem s10_35_safe : Safe 3 10 s10_35 := by
  apply safe_succ 2 10 s10_35 [] (by decide) s10_35_edges
  simp
def s10_36 : State := ⟨[104,21,67,145], 44601830679448528859301231875371202301329686, 3, 1, 1, 0⟩
theorem s10_36_edges : next config 10 s10_36 = [] := by decide
theorem s10_36_safe : Safe 3 10 s10_36 := by
  apply safe_succ 2 10 s10_36 [] (by decide) s10_36_edges
  simp
def s10_37 : State := ⟨[104,29,67,145], 44601830679448528859301231875362398155243806, 3, 1, 1, 0⟩
theorem s10_37_edges : next config 10 s10_37 = [] := by decide
theorem s10_37_safe : Safe 3 10 s10_37 := by
  apply safe_succ 2 10 s10_37 [] (by decide) s10_37_edges
  simp
def s10_38 : State := ⟨[104,54,67,145], 44601830679448528859301231893376796127854878, 3, 1, 1, 0⟩
theorem s10_38_edges : next config 10 s10_38 = [] := by decide
theorem s10_38_safe : Safe 3 10 s10_38 := by
  apply safe_succ 2 10 s10_38 [] (by decide) s10_38_edges
  simp
def s10_39 : State := ⟨[104,62,67,145], 44601830679448449631138722222719618594832670, 3, 1, 1, 0⟩
theorem s10_39_edges : next config 10 s10_39 = [] := by decide
theorem s10_39_safe : Safe 3 10 s10_39 := by
  apply safe_succ 2 10 s10_39 [] (by decide) s10_39_edges
  simp
def s10_40 : State := ⟨[104,86,67,145], 44601830679448528936672484330698664799568158, 3, 1, 1, 0⟩
theorem s10_40_edges : next config 10 s10_40 = [] := by decide
theorem s10_40_safe : Safe 3 10 s10_40 := by
  apply safe_succ 2 10 s10_40 [] (by decide) s10_40_edges
  simp
def s10_41 : State := ⟨[104,125,67,145], 44601873214744393976609164797188326589399326, 3, 1, 1, 0⟩
theorem s10_41_edges : next config 10 s10_41 = [] := by decide
theorem s10_41_safe : Safe 3 10 s10_41 := by
  apply safe_succ 2 10 s10_41 [] (by decide) s10_41_edges
  simp
def s10_42 : State := ⟨[125,4,104,145], 44601873214744393976609017223235702553252126, 3, 3, 1, 0⟩
theorem s10_42_edges : next config 10 s10_42 = [] := by decide
theorem s10_42_safe : Safe 3 10 s10_42 := by
  apply safe_succ 2 10 s10_42 [] (by decide) s10_42_edges
  simp
def s10_43 : State := ⟨[125,4,104,145], 44601873214744393976609054116723849972355350, 3, 3, 1, 0⟩
theorem s10_43_edges : next config 10 s10_43 = [] := by decide
theorem s10_43_safe : Safe 3 10 s10_43 := by
  apply safe_succ 2 10 s10_43 [] (by decide) s10_43_edges
  simp
def s10_44 : State := ⟨[125,21,67,145], 44601873214744393976609164797188326589399326, 3, 1, 1, 0⟩
theorem s10_44_edges : next config 10 s10_44 = [] := by decide
theorem s10_44_safe : Safe 3 10 s10_44 := by
  apply safe_succ 2 10 s10_44 [] (by decide) s10_44_edges
  simp
def s10_45 : State := ⟨[146,4,125,145], 133804854008866886542751890313829148577169694, 3, 3, 1, 0⟩
theorem s10_45_edges : next config 10 s10_45 = [] := by decide
theorem s10_45_safe : Safe 3 10 s10_45 := by
  apply safe_succ 2 10 s10_45 [] (by decide) s10_45_edges
  simp
end HGP13.SectorGraph234
