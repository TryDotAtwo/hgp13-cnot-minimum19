import Graph234Layer9
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s8_0 : State := ⟨[1,4,67,145], 44601830679428167226370843006035633998336278, 3, 3, 1, 0⟩
theorem s8_0_edges : next config 8 s8_0 = [] := by decide
theorem s8_0_safe : Safe 5 8 s8_0 := by
  apply safe_succ 4 8 s8_0 [] (by decide) s8_0_edges
  simp
def s8_1 : State := ⟨[1,4,67,145], 44601830679428167226370843006035634000429334, 3, 3, 1, 0⟩
theorem s8_1_edges : next config 8 s8_1 = [s9_4] := by decide
theorem s8_1_safe : Safe 5 8 s8_1 := by
  apply safe_succ 4 8 s8_1 [s9_4] (by decide) s8_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_4_safe
def s8_2 : State := ⟨[1,4,67,145], 44601830679428167227579695038673968334835990, 3, 3, 1, 0⟩
theorem s8_2_edges : next config 8 s8_2 = [] := by decide
theorem s8_2_safe : Safe 5 8 s8_2 := by
  apply safe_succ 4 8 s8_2 [] (by decide) s8_2_edges
  simp
def s8_3 : State := ⟨[1,4,67,145], 44601830679428167227579695038673968336929046, 3, 3, 1, 0⟩
theorem s8_3_edges : next config 8 s8_3 = [s9_5] := by decide
theorem s8_3_safe : Safe 5 8 s8_3 := by
  apply safe_succ 4 8 s8_3 [s9_5] (by decide) s8_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_5_safe
def s8_4 : State := ⟨[1,4,67,145], 44601830679428167303742095461371901179527446, 3, 3, 1, 0⟩
theorem s8_4_edges : next config 8 s8_4 = [] := by decide
theorem s8_4_safe : Safe 5 8 s8_4 := by
  apply safe_succ 4 8 s8_4 [] (by decide) s8_4_edges
  simp
def s8_5 : State := ⟨[1,4,67,145], 44601830679428167304950947494010235516027158, 3, 3, 1, 0⟩
theorem s8_5_edges : next config 8 s8_5 = [] := by decide
theorem s8_5_safe : Safe 5 8 s8_5 := by
  apply safe_succ 4 8 s8_5 [] (by decide) s8_5_edges
  simp
def s8_6 : State := ⟨[1,4,67,145], 133806172603018343541531792529623995557941534, 3, 3, 1, 0⟩
theorem s8_6_edges : next config 8 s8_6 = [] := by decide
theorem s8_6_safe : Safe 5 8 s8_6 := by
  apply safe_succ 4 8 s8_6 [] (by decide) s8_6_edges
  simp
def s8_7 : State := ⟨[1,4,67,145], 156105556672081282929213657303842629991076126, 3, 3, 1, 0⟩
theorem s8_7_edges : next config 8 s8_7 = [] := by decide
theorem s8_7_safe : Safe 5 8 s8_7 := by
  apply safe_succ 4 8 s8_7 [] (by decide) s8_7_edges
  simp
def s8_8 : State := ⟨[1,4,86,145], 44601830679428167303741947887419311505211670, 3, 3, 1, 0⟩
theorem s8_8_edges : next config 8 s8_8 = [] := by decide
theorem s8_8_safe : Safe 5 8 s8_8 := by
  apply safe_succ 4 8 s8_8 [] (by decide) s8_8_edges
  simp
def s8_9 : State := ⟨[1,4,86,145], 44601830679428167304950799920057645841711382, 3, 3, 1, 0⟩
theorem s8_9_edges : next config 8 s8_9 = [] := by decide
theorem s8_9_safe : Safe 5 8 s8_9 := by
  apply safe_succ 4 8 s8_9 [] (by decide) s8_9_edges
  simp
def s8_10 : State := ⟨[1,4,96,145], 133806172603018422769694159220008999425478942, 3, 3, 1, 0⟩
theorem s8_10_edges : next config 8 s8_10 = [s9_2] := by decide
theorem s8_10_safe : Safe 5 8 s8_10 := by
  apply safe_succ 4 8 s8_10 [s9_2] (by decide) s8_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_2_safe
def s8_11 : State := ⟨[1,4,96,145], 156105556672081362157376023994227633858613534, 3, 3, 1, 0⟩
theorem s8_11_edges : next config 8 s8_11 = [s9_3] := by decide
theorem s8_11_safe : Safe 5 8 s8_11 := by
  apply safe_succ 4 8 s8_11 [s9_3] (by decide) s8_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_3_safe
def s8_12 : State := ⟨[1,4,104,145], 44602511244182370736228011050624637116420382, 3, 3, 1, 0⟩
theorem s8_12_edges : next config 8 s8_12 = [] := by decide
theorem s8_12_safe : Safe 5 8 s8_12 := by
  apply safe_succ 4 8 s8_12 [] (by decide) s8_12_edges
  simp
def s8_13 : State := ⟨[1,4,104,145], 44602511244182370736228011050624645706354966, 3, 3, 1, 0⟩
theorem s8_13_edges : next config 8 s8_13 = [] := by decide
theorem s8_13_safe : Safe 5 8 s8_13 := by
  apply safe_succ 4 8 s8_13 [] (by decide) s8_13_edges
  simp
def s8_14 : State := ⟨[1,4,104,145], 44602511244182370736228047944112784535523606, 3, 3, 1, 0⟩
theorem s8_14_edges : next config 8 s8_14 = [] := by decide
theorem s8_14_safe : Safe 5 8 s8_14 := by
  apply safe_succ 4 8 s8_14 [] (by decide) s8_14_edges
  simp
def s8_15 : State := ⟨[1,4,104,145], 44602511244182529192553039579299824204321046, 3, 3, 1, 0⟩
theorem s8_15_edges : next config 8 s8_15 = [] := by decide
theorem s8_15_safe : Safe 5 8 s8_15 := by
  apply safe_succ 4 8 s8_15 [] (by decide) s8_15_edges
  simp
def s8_16 : State := ⟨[1,4,104,145], 44602511244183638386828239280026133819621662, 3, 3, 1, 0⟩
theorem s8_16_edges : next config 8 s8_16 = [] := by decide
theorem s8_16_safe : Safe 5 8 s8_16 := by
  apply safe_succ 4 8 s8_16 [] (by decide) s8_16_edges
  simp
def s8_17 : State := ⟨[1,4,104,145], 44602511244183638386828276173514281238724886, 3, 3, 1, 0⟩
theorem s8_17_edges : next config 8 s8_17 = [] := by decide
theorem s8_17_safe : Safe 5 8 s8_17 := by
  apply safe_succ 4 8 s8_17 [] (by decide) s8_17_edges
  simp
def s8_18 : State := ⟨[1,4,104,145], 44602511244506889289886437777407793136992542, 3, 3, 1, 0⟩
theorem s8_18_edges : next config 8 s8_18 = [] := by decide
theorem s8_18_safe : Safe 5 8 s8_18 := by
  apply safe_succ 4 8 s8_18 [] (by decide) s8_18_edges
  simp
def s8_19 : State := ⟨[1,4,104,145], 44602511244506889289886474670895940556095766, 3, 3, 1, 0⟩
theorem s8_19_edges : next config 8 s8_19 = [] := by decide
theorem s8_19_safe : Safe 5 8 s8_19 := by
  apply safe_succ 4 8 s8_19 [] (by decide) s8_19_edges
  simp
def s8_20 : State := ⟨[1,4,104,145], 66902575877979152000836802574058135085977886, 3, 3, 1, 0⟩
theorem s8_20_edges : next config 8 s8_20 = [] := by decide
theorem s8_20_safe : Safe 5 8 s8_20 := by
  apply safe_succ 4 8 s8_20 [] (by decide) s8_20_edges
  simp
def s8_21 : State := ⟨[1,4,104,145], 66902575877979152000836802574058143675912470, 3, 3, 1, 0⟩
theorem s8_21_edges : next config 8 s8_21 = [] := by decide
theorem s8_21_safe : Safe 5 8 s8_21 := by
  apply safe_succ 4 8 s8_21 [] (by decide) s8_21_edges
  simp
def s8_22 : State := ⟨[1,4,104,145], 66902575877979152000836839467546282505081110, 3, 3, 1, 0⟩
theorem s8_22_edges : next config 8 s8_22 = [] := by decide
theorem s8_22_safe : Safe 5 8 s8_22 := by
  apply safe_succ 4 8 s8_22 [] (by decide) s8_22_edges
  simp
def s8_23 : State := ⟨[1,4,104,145], 66902575877979310457161831102733322173878550, 3, 3, 1, 0⟩
theorem s8_23_edges : next config 8 s8_23 = [] := by decide
theorem s8_23_safe : Safe 5 8 s8_23 := by
  apply safe_succ 4 8 s8_23 [] (by decide) s8_23_edges
  simp
def s8_24 : State := ⟨[1,4,104,145], 66902575877980419651437030803459631789179166, 3, 3, 1, 0⟩
theorem s8_24_edges : next config 8 s8_24 = [] := by decide
theorem s8_24_safe : Safe 5 8 s8_24 := by
  apply safe_succ 4 8 s8_24 [] (by decide) s8_24_edges
  simp
def s8_25 : State := ⟨[1,4,104,145], 66902575877980419651437067696947779208282390, 3, 3, 1, 0⟩
theorem s8_25_edges : next config 8 s8_25 = [] := by decide
theorem s8_25_safe : Safe 5 8 s8_25 := by
  apply safe_succ 4 8 s8_25 [] (by decide) s8_25_edges
  simp
def s8_26 : State := ⟨[1,4,104,145], 66902575878303670554495229300841291106550046, 3, 3, 1, 0⟩
theorem s8_26_edges : next config 8 s8_26 = [] := by decide
theorem s8_26_safe : Safe 5 8 s8_26 := by
  apply safe_succ 4 8 s8_26 [] (by decide) s8_26_edges
  simp
def s8_27 : State := ⟨[1,4,104,145], 66902575878303670554495266194329438525653270, 3, 3, 1, 0⟩
theorem s8_27_edges : next config 8 s8_27 = [] := by decide
theorem s8_27_safe : Safe 5 8 s8_27 := by
  apply safe_succ 4 8 s8_27 [] (by decide) s8_27_edges
  simp
def s8_28 : State := ⟨[1,4,104,146], 89204682205977458896226374345136223664804126, 3, 3, 1, 0⟩
theorem s8_28_edges : next config 8 s8_28 = [] := by decide
theorem s8_28_safe : Safe 5 8 s8_28 := by
  apply safe_succ 4 8 s8_28 [] (by decide) s8_28_edges
  simp
def s8_29 : State := ⟨[1,4,104,146], 89204682205977458896226411238624371083907350, 3, 3, 1, 0⟩
theorem s8_29_edges : next config 8 s8_29 = [] := by decide
theorem s8_29_safe : Safe 5 8 s8_29 := by
  apply safe_succ 4 8 s8_29 [] (by decide) s8_29_edges
  simp
def s8_30 : State := ⟨[1,4,104,146], 89207404464912826403934081341995677810495766, 3, 3, 1, 0⟩
theorem s8_30_edges : next config 8 s8_30 = [] := by decide
theorem s8_30_safe : Safe 5 8 s8_30 := by
  apply safe_succ 4 8 s8_30 [] (by decide) s8_30_edges
  simp
def s8_31 : State := ⟨[1,4,104,146], 111504066275040398283908239119354858097938718, 3, 3, 1, 0⟩
theorem s8_31_edges : next config 8 s8_31 = [] := by decide
theorem s8_31_safe : Safe 5 8 s8_31 := by
  apply safe_succ 4 8 s8_31 [] (by decide) s8_31_edges
  simp
def s8_32 : State := ⟨[1,4,104,146], 111504066275040398283908276012843005517041942, 3, 3, 1, 0⟩
theorem s8_32_edges : next config 8 s8_32 = [] := by decide
theorem s8_32_safe : Safe 5 8 s8_32 := by
  apply safe_succ 4 8 s8_32 [] (by decide) s8_32_edges
  simp
def s8_33 : State := ⟨[1,4,104,162], 5846006551025023527781069414366386621401371054366, 3, 3, 1, 0⟩
theorem s8_33_edges : next config 8 s8_33 = [] := by decide
theorem s8_33_safe : Safe 5 8 s8_33 := by
  apply safe_succ 4 8 s8_33 [] (by decide) s8_33_edges
  simp
def s8_34 : State := ⟨[1,4,104,162], 5846006551025023527781069414403280109548790157590, 3, 3, 1, 0⟩
theorem s8_34_edges : next config 8 s8_34 = [] := by decide
theorem s8_34_safe : Safe 5 8 s8_34 := by
  apply safe_succ 4 8 s8_34 [] (by decide) s8_34_edges
  simp
def s8_35 : State := ⟨[1,4,104,162], 5846006551025023527939525739394915296588458955030, 3, 3, 1, 0⟩
theorem s8_35_edges : next config 8 s8_35 = [] := by decide
theorem s8_35_safe : Safe 5 8 s8_35 := by
  apply safe_succ 4 8 s8_35 [] (by decide) s8_35_edges
  simp
def s8_36 : State := ⟨[1,4,104,162], 5846006553747282463148577122073383480855516746006, 3, 3, 1, 0⟩
theorem s8_36_edges : next config 8 s8_36 = [] := by decide
theorem s8_36_safe : Safe 5 8 s8_36 := by
  apply safe_succ 4 8 s8_36 [] (by decide) s8_36_edges
  simp
def s8_37 : State := ⟨[1,4,104,162], 7307508186994796978301000393229171211330230751518, 3, 3, 1, 0⟩
theorem s8_37_edges : next config 8 s8_37 = [] := by decide
theorem s8_37_safe : Safe 5 8 s8_37 := by
  apply safe_succ 4 8 s8_37 [] (by decide) s8_37_edges
  simp
def s8_38 : State := ⟨[1,4,104,162], 7307508186994796978301000393266064699477649854742, 3, 3, 1, 0⟩
theorem s8_38_edges : next config 8 s8_38 = [] := by decide
theorem s8_38_safe : Safe 5 8 s8_38 := by
  apply safe_succ 4 8 s8_38 [] (by decide) s8_38_edges
  simp
def s8_39 : State := ⟨[1,4,104,162], 7307508186994796978459456718257699886517318652182, 3, 3, 1, 0⟩
theorem s8_39_edges : next config 8 s8_39 = [] := by decide
theorem s8_39_safe : Safe 5 8 s8_39 := by
  apply safe_succ 4 8 s8_39 [] (by decide) s8_39_edges
  simp
def s8_40 : State := ⟨[1,4,104,162], 17538019649672246873410548076096650778648831398166, 3, 3, 1, 0⟩
theorem s8_40_edges : next config 8 s8_40 = [] := by decide
theorem s8_40_safe : Safe 5 8 s8_40 := by
  apply safe_succ 4 8 s8_40 [] (by decide) s8_40_edges
  simp
def s8_41 : State := ⟨[1,4,104,162], 18999521285642020323930479054959435368577691095318, 3, 3, 1, 0⟩
theorem s8_41_edges : next config 8 s8_41 = [] := by decide
theorem s8_41_safe : Safe 5 8 s8_41 := by
  apply safe_succ 4 8 s8_41 [] (by decide) s8_41_edges
  simp
def s8_42 : State := ⟨[1,4,104,163], 11692013100348635200595808745231518700033691160854, 3, 3, 1, 0⟩
theorem s8_42_edges : next config 8 s8_42 = [] := by decide
theorem s8_42_safe : Safe 5 8 s8_42 := by
  apply safe_succ 4 8 s8_42 [] (by decide) s8_42_edges
  simp
def s8_43 : State := ⟨[1,4,104,163], 11692013101709764668279562599085017129752174072094, 3, 3, 1, 0⟩
theorem s8_43_edges : next config 8 s8_43 = [] := by decide
theorem s8_43_safe : Safe 5 8 s8_43 := by
  apply safe_succ 4 8 s8_43 [] (by decide) s8_43_edges
  simp
def s8_44 : State := ⟨[1,4,104,163], 13153514736318408651115739724094303289953960923422, 3, 3, 1, 0⟩
theorem s8_44_edges : next config 8 s8_44 = [] := by decide
theorem s8_44_safe : Safe 5 8 s8_44 := by
  apply safe_succ 4 8 s8_44 [] (by decide) s8_44_edges
  simp
def s8_45 : State := ⟨[1,4,104,163], 14615016373649311569319424556810586309618483400982, 3, 3, 1, 0⟩
theorem s8_45_edges : next config 8 s8_45 = [] := by decide
theorem s8_45_safe : Safe 5 8 s8_45 := by
  apply safe_succ 4 8 s8_45 [] (by decide) s8_45_edges
  simp
def s8_46 : State := ⟨[1,4,104,176], 95780971326419139128314594914659690004932607210492190, 3, 3, 1, 0⟩
theorem s8_46_edges : next config 8 s8_46 = [] := by decide
theorem s8_46_safe : Safe 5 8 s8_46 := by
  apply safe_succ 4 8 s8_46 [] (by decide) s8_46_edges
  simp
def s8_47 : State := ⟨[1,4,104,176], 95780971326419139128314594914659726898420754629595414, 3, 3, 1, 0⟩
theorem s8_47_edges : next config 8 s8_47 = [] := by decide
theorem s8_47_safe : Safe 5 8 s8_47 := by
  apply safe_succ 4 8 s8_47 [] (by decide) s8_47_edges
  simp
def s8_48 : State := ⟨[1,4,104,176], 95782432805755724832702175457956688015303901637054750, 3, 3, 1, 0⟩
theorem s8_48_edges : next config 8 s8_48 = [] := by decide
theorem s8_48_safe : Safe 5 8 s8_48 := by
  apply safe_succ 4 8 s8_48 [] (by decide) s8_48_edges
  simp
def s8_49 : State := ⟨[1,4,104,176], 95782432805755724832702175457956724908792049056157974, 3, 3, 1, 0⟩
theorem s8_49_edges : next config 8 s8_49 = [] := by decide
theorem s8_49_safe : Safe 5 8 s8_49 := by
  apply safe_succ 4 8 s8_49 [] (by decide) s8_49_edges
  simp
def s8_50 : State := ⟨[1,4,108,145], 44601830679773047412959511028192929602797846, 3, 3, 1, 0⟩
theorem s8_50_edges : next config 8 s8_50 = [s9_17] := by decide
theorem s8_50_safe : Safe 5 8 s8_50 := by
  apply safe_succ 4 8 s8_50 [s9_17] (by decide) s8_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_17_safe
def s8_51 : State := ⟨[1,4,120,145], 44601832008676524644216957205216833862566166, 3, 3, 1, 0⟩
theorem s8_51_edges : next config 8 s8_51 = [] := by decide
theorem s8_51_safe : Safe 5 8 s8_51 := by
  apply safe_succ 4 8 s8_51 [] (by decide) s8_51_edges
  simp
def s8_52 : State := ⟨[1,4,121,145], 44601833337904520429132830109023894142910742, 3, 3, 1, 0⟩
theorem s8_52_edges : next config 8 s8_52 = [s9_18] := by decide
theorem s8_52_safe : Safe 5 8 s8_52 := by
  apply safe_succ 4 8 s8_52 [s9_18] (by decide) s8_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_18_safe
def s8_53 : State := ⟨[1,4,125,145], 44601873214744393976609017223235702553248022, 3, 3, 1, 0⟩
theorem s8_53_edges : next config 8 s8_53 = [s9_19, s9_89, s9_6] := by decide
theorem s8_53_safe : Safe 5 8 s8_53 := by
  apply safe_succ 4 8 s8_53 [s9_19, s9_89, s9_6] (by decide) s8_53_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_19_safe
  · subst z; exact s9_89_safe
  · subst z; exact s9_6_safe
def s8_54 : State := ⟨[1,4,241,145], 3533694129556768659166595001530439542899129882077862275623413092450373918, 3, 3, 1, 0⟩
theorem s8_54_edges : next config 8 s8_54 = [] := by decide
theorem s8_54_safe : Safe 5 8 s8_54 := by
  apply safe_succ 4 8 s8_54 [] (by decide) s8_54_edges
  simp
def s8_55 : State := ⟨[1,4,241,145], 3533694129556768659166595001530439542899129882077862312516901239869477142, 3, 3, 1, 0⟩
theorem s8_55_edges : next config 8 s8_55 = [] := by decide
theorem s8_55_safe : Safe 5 8 s8_55 := by
  apply safe_succ 4 8 s8_55 [] (by decide) s8_55_edges
  simp
def s8_56 : State := ⟨[1,4,241,145], 3533694129556768659166595001552739607532926663342471067146846590419931422, 3, 3, 1, 0⟩
theorem s8_56_edges : next config 8 s8_56 = [] := by decide
theorem s8_56_safe : Safe 5 8 s8_56 := by
  apply safe_succ 4 8 s8_56 [] (by decide) s8_56_edges
  simp
def s8_57 : State := ⟨[1,4,241,145], 3533694129556768659166595001552739607532926663342471104040334737839034646, 3, 3, 1, 0⟩
theorem s8_57_edges : next config 8 s8_57 = [] := by decide
theorem s8_57_safe : Safe 5 8 s8_57 := by
  apply safe_succ 4 8 s8_57 [] (by decide) s8_57_edges
  simp
def s8_58 : State := ⟨[1,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546902, 3, 3, 1, 0⟩
theorem s8_58_edges : next config 8 s8_58 = [s9_20] := by decide
theorem s8_58_safe : Safe 5 8 s8_58 := by
  apply safe_succ 4 8 s8_58 [s9_20] (by decide) s8_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_20_safe
def s8_59 : State := ⟨[1,12,67,145], 44601830679428167221535102834088969882505494, 3, 3, 1, 0⟩
theorem s8_59_edges : next config 8 s8_59 = [] := by decide
theorem s8_59_safe : Safe 5 8 s8_59 := by
  apply safe_succ 4 8 s8_59 [] (by decide) s8_59_edges
  simp
def s8_60 : State := ⟨[1,12,67,145], 44601830679428167221535139727577117301608726, 3, 3, 1, 0⟩
theorem s8_60_edges : next config 8 s8_60 = [] := by decide
theorem s8_60_safe : Safe 5 8 s8_60 := by
  apply safe_succ 4 8 s8_60 [] (by decide) s8_60_edges
  simp
def s8_61 : State := ⟨[1,12,82,145], 44601830679428167226370695432083044324020502, 3, 3, 1, 0⟩
theorem s8_61_edges : next config 8 s8_61 = [] := by decide
theorem s8_61_safe : Safe 5 8 s8_61 := by
  apply safe_succ 4 8 s8_61 [] (by decide) s8_61_edges
  simp
def s8_62 : State := ⟨[1,12,82,145], 44601830679428167227579547464721378660520214, 3, 3, 1, 0⟩
theorem s8_62_edges : next config 8 s8_62 = [] := by decide
theorem s8_62_safe : Safe 5 8 s8_62 := by
  apply safe_succ 4 8 s8_62 [] (by decide) s8_62_edges
  simp
def s8_63 : State := ⟨[1,12,97,145], 44601830679428404906022461159661013418840342, 3, 3, 1, 0⟩
theorem s8_63_edges : next config 8 s8_63 = [] := by decide
theorem s8_63_safe : Safe 5 8 s8_63 := by
  apply safe_succ 4 8 s8_63 [] (by decide) s8_63_edges
  simp
def s8_64 : State := ⟨[1,12,104,145], 44601830679448528859301084301409773582225686, 3, 3, 1, 0⟩
theorem s8_64_edges : next config 8 s8_64 = [s9_21, s9_90] := by decide
theorem s8_64_safe : Safe 5 8 s8_64 := by
  apply safe_succ 4 8 s8_64 [s9_21, s9_90] (by decide) s8_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_21_safe
  · subst z; exact s9_90_safe
def s8_65 : State := ⟨[1,12,104,145], 133806172603038705179297810890432946676764958, 3, 1, 1, 0⟩
theorem s8_65_edges : next config 8 s8_65 = [s9_2] := by decide
theorem s8_65_safe : Safe 5 8 s8_65 := by
  apply safe_succ 4 8 s8_65 [s9_2] (by decide) s8_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_2_safe
def s8_66 : State := ⟨[1,12,104,145], 156105556672101644566979675664651581109899550, 3, 1, 1, 0⟩
theorem s8_66_edges : next config 8 s8_66 = [s9_3] := by decide
theorem s8_66_safe : Safe 5 8 s8_66 := by
  apply safe_succ 4 8 s8_66 [s9_3] (by decide) s8_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_3_safe
def s8_67 : State := ⟨[1,12,112,145], 44601830684620543308232260259516322660159766, 3, 3, 1, 0⟩
theorem s8_67_edges : next config 8 s8_67 = [] := by decide
theorem s8_67_safe : Safe 5 8 s8_67 := by
  apply safe_succ 4 8 s8_67 [] (by decide) s8_67_edges
  simp
def s8_68 : State := ⟨[1,12,113,145], 44601830689812840166767087888046818989379862, 3, 3, 1, 0⟩
theorem s8_68_edges : next config 8 s8_68 = [s9_22] := by decide
theorem s8_68_safe : Safe 5 8 s8_68 := by
  apply safe_succ 4 8 s8_68 [s9_22] (by decide) s8_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_22_safe
def s8_69 : State := ⟨[1,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179222, 3, 3, 1, 0⟩
theorem s8_69_edges : next config 8 s8_69 = [s9_23] := by decide
theorem s8_69_safe : Safe 5 8 s8_69 := by
  apply safe_succ 4 8 s8_69 [s9_23] (by decide) s8_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_23_safe
def s8_70 : State := ⟨[1,21,67,145], 44601830679428167221535102834088969882505494, 3, 3, 1, 0⟩
theorem s8_70_edges : next config 8 s8_70 = [s9_12] := by decide
theorem s8_70_safe : Safe 5 8 s8_70 := by
  apply safe_succ 4 8 s8_70 [s9_12] (by decide) s8_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_12_safe
def s8_71 : State := ⟨[1,21,67,145], 44601830679428167221535139727577117301608726, 3, 3, 1, 0⟩
theorem s8_71_edges : next config 8 s8_71 = [s9_13] := by decide
theorem s8_71_safe : Safe 5 8 s8_71 := by
  apply safe_succ 4 8 s8_71 [s9_13] (by decide) s8_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_13_safe
def s8_72 : State := ⟨[1,21,67,145], 44601830679428167303742095461371901181624598, 3, 1, 1, 0⟩
theorem s8_72_edges : next config 8 s8_72 = [] := by decide
theorem s8_72_safe : Safe 5 8 s8_72 := by
  apply safe_succ 4 8 s8_72 [] (by decide) s8_72_edges
  simp
def s8_73 : State := ⟨[1,21,67,145], 44601830679428167304950947494010235518124310, 3, 1, 1, 0⟩
theorem s8_73_edges : next config 8 s8_73 = [] := by decide
theorem s8_73_safe : Safe 5 8 s8_73 := by
  apply safe_succ 4 8 s8_73 [] (by decide) s8_73_edges
  simp
def s8_74 : State := ⟨[1,21,82,145], 44601830679428167226370695432083044324020502, 3, 3, 1, 0⟩
theorem s8_74_edges : next config 8 s8_74 = [] := by decide
theorem s8_74_safe : Safe 5 8 s8_74 := by
  apply safe_succ 4 8 s8_74 [] (by decide) s8_74_edges
  simp
def s8_75 : State := ⟨[1,21,82,145], 44601830679428167227579547464721378660520214, 3, 3, 1, 0⟩
theorem s8_75_edges : next config 8 s8_75 = [] := by decide
theorem s8_75_safe : Safe 5 8 s8_75 := by
  apply safe_succ 4 8 s8_75 [] (by decide) s8_75_edges
  simp
def s8_76 : State := ⟨[1,21,82,145], 44601830679428167303741947887419311505211670, 3, 3, 1, 0⟩
theorem s8_76_edges : next config 8 s8_76 = [] := by decide
theorem s8_76_safe : Safe 5 8 s8_76 := by
  apply safe_succ 4 8 s8_76 [] (by decide) s8_76_edges
  simp
def s8_77 : State := ⟨[1,21,82,145], 44601830679428167304950799920057645841711382, 3, 3, 1, 0⟩
theorem s8_77_edges : next config 8 s8_77 = [] := by decide
theorem s8_77_safe : Safe 5 8 s8_77 := by
  apply safe_succ 4 8 s8_77 [] (by decide) s8_77_edges
  simp
def s8_78 : State := ⟨[1,21,97,145], 44601830679428404906022461159661013418840342, 3, 3, 1, 0⟩
theorem s8_78_edges : next config 8 s8_78 = [] := by decide
theorem s8_78_safe : Safe 5 8 s8_78 := by
  apply safe_succ 4 8 s8_78 [] (by decide) s8_78_edges
  simp
def s8_79 : State := ⟨[1,21,104,145], 44601830679448528859301084301409773582225686, 3, 3, 1, 0⟩
theorem s8_79_edges : next config 8 s8_79 = [s9_24, s9_91, s9_16, s9_11] := by decide
theorem s8_79_safe : Safe 5 8 s8_79 := by
  apply safe_succ 4 8 s8_79 [s9_24, s9_91, s9_16, s9_11] (by decide) s8_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s9_24_safe
  · subst z; exact s9_91_safe
  · subst z; exact s9_16_safe
  · subst z; exact s9_11_safe
def s8_80 : State := ⟨[1,21,104,145], 44601830679448528859301379449314952935047446, 3, 3, 1, 0⟩
theorem s8_80_edges : next config 8 s8_80 = [] := by decide
theorem s8_80_safe : Safe 5 8 s8_80 := by
  apply safe_succ 4 8 s8_80 [] (by decide) s8_80_edges
  simp
def s8_81 : State := ⟨[1,21,104,145], 44601830679449796509901312530811270285426966, 3, 3, 1, 0⟩
theorem s8_81_edges : next config 8 s8_81 = [s9_25] := by decide
theorem s8_81_safe : Safe 5 8 s8_81 := by
  apply safe_succ 4 8 s8_81 [s9_25] (by decide) s8_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_25_safe
def s8_82 : State := ⟨[1,21,104,145], 44601830679773047412959511028192929602797846, 3, 3, 1, 0⟩
theorem s8_82_edges : next config 8 s8_82 = [s9_26] := by decide
theorem s8_82_safe : Safe 5 8 s8_82 := by
  apply safe_succ 4 8 s8_82 [s9_26] (by decide) s8_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_26_safe
def s8_83 : State := ⟨[1,21,112,145], 44601830684620543308232260259516322660159766, 3, 3, 1, 0⟩
theorem s8_83_edges : next config 8 s8_83 = [] := by decide
theorem s8_83_safe : Safe 5 8 s8_83 := by
  apply safe_succ 4 8 s8_83 [] (by decide) s8_83_edges
  simp
def s8_84 : State := ⟨[1,21,113,145], 44601830689812840166767087888046818989379862, 3, 3, 1, 0⟩
theorem s8_84_edges : next config 8 s8_84 = [s9_27] := by decide
theorem s8_84_safe : Safe 5 8 s8_84 := by
  apply safe_succ 4 8 s8_84 [s9_27] (by decide) s8_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_27_safe
def s8_85 : State := ⟨[1,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179222, 3, 3, 1, 0⟩
theorem s8_85_edges : next config 8 s8_85 = [s9_28] := by decide
theorem s8_85_safe : Safe 5 8 s8_85 := by
  apply safe_succ 4 8 s8_85 [s9_28] (by decide) s8_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_28_safe
def s8_86 : State := ⟨[1,68,104,145], 44601830679448528859301379449314952935047446, 3, 3, 1, 0⟩
theorem s8_86_edges : next config 8 s8_86 = [] := by decide
theorem s8_86_safe : Safe 5 8 s8_86 := by
  apply safe_succ 4 8 s8_86 [] (by decide) s8_86_edges
  simp
def s8_87 : State := ⟨[1,86,67,145], 44601830679428167303742095461371901181624598, 3, 1, 1, 0⟩
theorem s8_87_edges : next config 8 s8_87 = [] := by decide
theorem s8_87_safe : Safe 5 8 s8_87 := by
  apply safe_succ 4 8 s8_87 [] (by decide) s8_87_edges
  simp
def s8_88 : State := ⟨[1,86,67,145], 44601830679428167304950947494010235518124310, 3, 1, 1, 0⟩
theorem s8_88_edges : next config 8 s8_88 = [] := by decide
theorem s8_88_safe : Safe 5 8 s8_88 := by
  apply safe_succ 4 8 s8_88 [] (by decide) s8_88_edges
  simp
def s8_89 : State := ⟨[1,86,82,145], 44601830679428167303741947887419311505211670, 3, 3, 1, 0⟩
theorem s8_89_edges : next config 8 s8_89 = [] := by decide
theorem s8_89_safe : Safe 5 8 s8_89 := by
  apply safe_succ 4 8 s8_89 [] (by decide) s8_89_edges
  simp
def s8_90 : State := ⟨[1,86,82,145], 44601830679428167304950799920057645841711382, 3, 3, 1, 0⟩
theorem s8_90_edges : next config 8 s8_90 = [] := by decide
theorem s8_90_safe : Safe 5 8 s8_90 := by
  apply safe_succ 4 8 s8_90 [] (by decide) s8_90_edges
  simp
def s8_91 : State := ⟨[1,100,104,145], 44601830679449796509901312530811270285426966, 3, 3, 1, 0⟩
theorem s8_91_edges : next config 8 s8_91 = [s9_36] := by decide
theorem s8_91_safe : Safe 5 8 s8_91 := by
  apply safe_succ 4 8 s8_91 [s9_36] (by decide) s8_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_36_safe
def s8_92 : State := ⟨[1,108,104,145], 44601830679773047412959511028192929602797846, 3, 3, 1, 0⟩
theorem s8_92_edges : next config 8 s8_92 = [s9_37] := by decide
theorem s8_92_safe : Safe 5 8 s8_92 := by
  apply safe_succ 4 8 s8_92 [s9_37] (by decide) s8_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_37_safe
def s8_93 : State := ⟨[3,4,100,145], 44601830679429514100297660860387323034140958, 3, 3, 1, 0⟩
theorem s8_93_edges : next config 8 s8_93 = [] := by decide
theorem s8_93_safe : Safe 5 8 s8_93 := by
  apply safe_succ 4 8 s8_93 [] (by decide) s8_93_edges
  simp
def s8_94 : State := ⟨[3,4,104,145], 44601830679448528859301084301409773580128542, 3, 3, 1, 0⟩
theorem s8_94_edges : next config 8 s8_94 = [s9_175, s9_96] := by decide
theorem s8_94_safe : Safe 5 8 s8_94 := by
  apply safe_succ 4 8 s8_94 [s9_175, s9_96] (by decide) s8_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_175_safe
  · subst z; exact s9_96_safe
def s8_95 : State := ⟨[3,4,104,145], 44601830679448528859301084301409773582221598, 3, 3, 1, 0⟩
theorem s8_95_edges : next config 8 s8_95 = [s9_176, s9_97, s9_37, s9_21, s9_17, s9_20] := by decide
theorem s8_95_safe : Safe 5 8 s8_95 := by
  apply safe_succ 4 8 s8_95 [s9_176, s9_97, s9_37, s9_21, s9_17, s9_20] (by decide) s8_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s9_176_safe
  · subst z; exact s9_97_safe
  · subst z; exact s9_37_safe
  · subst z; exact s9_21_safe
  · subst z; exact s9_17_safe
  · subst z; exact s9_20_safe
def s8_96 : State := ⟨[3,4,104,145], 44601830679449796509901312530811270283329822, 3, 3, 1, 0⟩
theorem s8_96_edges : next config 8 s8_96 = [] := by decide
theorem s8_96_safe : Safe 5 8 s8_96 := by
  apply safe_succ 4 8 s8_96 [] (by decide) s8_96_edges
  simp
def s8_97 : State := ⟨[3,4,104,145], 44601830679773047412959511028192929600700702, 3, 3, 1, 0⟩
theorem s8_97_edges : next config 8 s8_97 = [] := by decide
theorem s8_97_safe : Safe 5 8 s8_97 := by
  apply safe_succ 4 8 s8_97 [] (by decide) s8_97_edges
  simp
def s8_98 : State := ⟨[3,4,104,145], 133806172603038705179297810890432946676764958, 3, 2, 1, 0⟩
theorem s8_98_edges : next config 8 s8_98 = [s9_2] := by decide
theorem s8_98_safe : Safe 5 8 s8_98 := by
  apply safe_succ 4 8 s8_98 [s9_2] (by decide) s8_98_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_2_safe
def s8_99 : State := ⟨[3,4,104,145], 156105556672101644566979675664651581109899550, 3, 2, 1, 0⟩
theorem s8_99_edges : next config 8 s8_99 = [s9_3] := by decide
theorem s8_99_safe : Safe 5 8 s8_99 := by
  apply safe_succ 4 8 s8_99 [s9_3] (by decide) s8_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_3_safe
def s8_100 : State := ⟨[3,4,113,145], 44601830689812840166767087888046818987282718, 3, 3, 1, 0⟩
theorem s8_100_edges : next config 8 s8_100 = [] := by decide
theorem s8_100_safe : Safe 5 8 s8_100 := by
  apply safe_succ 4 8 s8_100 [] (by decide) s8_100_edges
  simp
def s8_101 : State := ⟨[3,4,113,145], 44601830689812840166767087888046818989375774, 3, 3, 1, 0⟩
theorem s8_101_edges : next config 8 s8_101 = [s9_22] := by decide
theorem s8_101_safe : Safe 5 8 s8_101 := by
  apply safe_succ 4 8 s8_101 [s9_22] (by decide) s8_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_22_safe
def s8_102 : State := ⟨[3,4,117,145], 44601830845581745922811916743961708865978654, 3, 3, 1, 0⟩
theorem s8_102_edges : next config 8 s8_102 = [] := by decide
theorem s8_102_safe : Safe 5 8 s8_102 := by
  apply safe_succ 4 8 s8_102 [] (by decide) s8_102_edges
  simp
def s8_103 : State := ⟨[3,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082078, 3, 3, 1, 0⟩
theorem s8_103_edges : next config 8 s8_103 = [] := by decide
theorem s8_103_safe : Safe 5 8 s8_103 := by
  apply safe_succ 4 8 s8_103 [] (by decide) s8_103_edges
  simp
def s8_104 : State := ⟨[3,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175134, 3, 3, 1, 0⟩
theorem s8_104_edges : next config 8 s8_104 = [s9_23] := by decide
theorem s8_104_safe : Safe 5 8 s8_104 := by
  apply safe_succ 4 8 s8_104 [s9_23] (by decide) s8_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_23_safe
def s8_105 : State := ⟨[3,12,67,145], 44601830679428167221535065940600822463402270, 3, 3, 1, 0⟩
theorem s8_105_edges : next config 8 s8_105 = [s9_177, s9_100] := by decide
theorem s8_105_safe : Safe 5 8 s8_105 := by
  apply safe_succ 4 8 s8_105 [s9_177, s9_100] (by decide) s8_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_177_safe
  · subst z; exact s9_100_safe
def s8_106 : State := ⟨[3,12,96,145], 44601830679428246449697432630985826330939678, 3, 3, 1, 0⟩
theorem s8_106_edges : next config 8 s8_106 = [s9_178, s9_101, s9_23, s9_21] := by decide
theorem s8_106_safe : Safe 5 8 s8_106 := by
  apply safe_succ 4 8 s8_106 [s9_178, s9_101, s9_23, s9_21] (by decide) s8_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s9_178_safe
  · subst z; exact s9_101_safe
  · subst z; exact s9_23_safe
  · subst z; exact s9_21_safe
def s8_107 : State := ⟨[3,21,67,145], 44601830679428167221535065940600822463402270, 3, 3, 1, 0⟩
theorem s8_107_edges : next config 8 s8_107 = [s9_179, s9_103, s9_35] := by decide
theorem s8_107_safe : Safe 5 8 s8_107 := by
  apply safe_succ 4 8 s8_107 [s9_179, s9_103, s9_35] (by decide) s8_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_179_safe
  · subst z; exact s9_103_safe
  · subst z; exact s9_35_safe
def s8_108 : State := ⟨[3,21,96,145], 44601830679428246449697432630985826330939678, 3, 3, 1, 0⟩
theorem s8_108_edges : next config 8 s8_108 = [s9_104, s9_28, s9_24] := by decide
theorem s8_108_safe : Safe 5 8 s8_108 := by
  apply safe_succ 4 8 s8_108 [s9_104, s9_28, s9_24] (by decide) s8_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_104_safe
  · subst z; exact s9_28_safe
  · subst z; exact s9_24_safe
def s8_109 : State := ⟨[3,21,96,145], 44601830679429514100297660860387323034140958, 3, 3, 1, 0⟩
theorem s8_109_edges : next config 8 s8_109 = [s9_25] := by decide
theorem s8_109_safe : Safe 5 8 s8_109 := by
  apply safe_succ 4 8 s8_109 [s9_25] (by decide) s8_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_25_safe
def s8_110 : State := ⟨[3,21,108,145], 44601830679773047412959511028192929602797854, 3, 1, 1, 0⟩
theorem s8_110_edges : next config 8 s8_110 = [] := by decide
theorem s8_110_safe : Safe 5 8 s8_110 := by
  apply safe_succ 4 8 s8_110 [] (by decide) s8_110_edges
  simp
def s8_111 : State := ⟨[3,21,121,145], 44601833337904520429132830109023894142910750, 3, 1, 1, 0⟩
theorem s8_111_edges : next config 8 s8_111 = [] := by decide
theorem s8_111_safe : Safe 5 8 s8_111 := by
  apply safe_succ 4 8 s8_111 [] (by decide) s8_111_edges
  simp
def s8_112 : State := ⟨[3,21,125,145], 44601873214744393976609017223235702553248030, 3, 1, 1, 0⟩
theorem s8_112_edges : next config 8 s8_112 = [] := by decide
theorem s8_112_safe : Safe 5 8 s8_112 := by
  apply safe_succ 4 8 s8_112 [] (by decide) s8_112_edges
  simp
def s8_113 : State := ⟨[3,21,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546910, 3, 1, 1, 0⟩
theorem s8_113_edges : next config 8 s8_113 = [] := by decide
theorem s8_113_safe : Safe 5 8 s8_113 := by
  apply safe_succ 4 8 s8_113 [] (by decide) s8_113_edges
  simp
def s8_114 : State := ⟨[3,22,104,145], 44601830679448528859301084301409773586415902, 3, 1, 1, 0⟩
theorem s8_114_edges : next config 8 s8_114 = [s9_29] := by decide
theorem s8_114_safe : Safe 5 8 s8_114 := by
  apply safe_succ 4 8 s8_114 [s9_29] (by decide) s8_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_29_safe
def s8_115 : State := ⟨[3,29,104,145], 44601830679448528859301084301409774119092510, 3, 1, 1, 0⟩
theorem s8_115_edges : next config 8 s8_115 = [] := by decide
theorem s8_115_safe : Safe 5 8 s8_115 := by
  apply safe_succ 4 8 s8_115 [] (by decide) s8_115_edges
  simp
def s8_116 : State := ⟨[3,53,104,145], 44601830679448528859301084310416972836962590, 3, 1, 1, 0⟩
theorem s8_116_edges : next config 8 s8_116 = [s9_30] := by decide
theorem s8_116_safe : Safe 5 8 s8_116 := by
  apply safe_succ 4 8 s8_116 [s9_30] (by decide) s8_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_30_safe
def s8_117 : State := ⟨[3,54,67,145], 44601830679428167221535065958615220977074462, 3, 1, 1, 0⟩
theorem s8_117_edges : next config 8 s8_117 = [s9_31] := by decide
theorem s8_117_safe : Safe 5 8 s8_117 := by
  apply safe_succ 4 8 s8_117 [s9_31] (by decide) s8_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_31_safe
def s8_118 : State := ⟨[3,54,67,145], 44601830679428167221535065967622420227621150, 3, 1, 1, 0⟩
theorem s8_118_edges : next config 8 s8_118 = [s9_32] := by decide
theorem s8_118_safe : Safe 5 8 s8_118 := by
  apply safe_succ 4 8 s8_118 [s9_32] (by decide) s8_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_32_safe
def s8_119 : State := ⟨[3,54,96,145], 44601830679428246449697432649000224844611870, 3, 1, 1, 0⟩
theorem s8_119_edges : next config 8 s8_119 = [s9_33, s9_29] := by decide
theorem s8_119_safe : Safe 5 8 s8_119 := by
  apply safe_succ 4 8 s8_119 [s9_33, s9_29] (by decide) s8_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_33_safe
  · subst z; exact s9_29_safe
def s8_120 : State := ⟨[3,54,96,145], 44601830679428246449697432658007424095158558, 3, 1, 1, 0⟩
theorem s8_120_edges : next config 8 s8_120 = [s9_34, s9_30] := by decide
theorem s8_120_safe : Safe 5 8 s8_120 := by
  apply safe_succ 4 8 s8_120 [s9_34, s9_30] (by decide) s8_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_34_safe
  · subst z; exact s9_30_safe
def s8_121 : State := ⟨[3,62,64,145], 44601830679428167221534922996348649728049438, 3, 1, 1, 0⟩
theorem s8_121_edges : next config 8 s8_121 = [s9_31, s9_33] := by decide
theorem s8_121_safe : Safe 5 8 s8_121 := by
  apply safe_succ 4 8 s8_121 [s9_31, s9_33] (by decide) s8_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_31_safe
  · subst z; exact s9_33_safe
def s8_122 : State := ⟨[3,62,64,145], 44601830679428167221534923005355848978596126, 3, 1, 1, 0⟩
theorem s8_122_edges : next config 8 s8_122 = [s9_32, s9_34] := by decide
theorem s8_122_safe : Safe 5 8 s8_122 := by
  apply safe_succ 4 8 s8_122 [s9_32, s9_34] (by decide) s8_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_32_safe
  · subst z; exact s9_34_safe
def s8_123 : State := ⟨[3,100,96,145], 44601830679429514100297660860387323034140958, 3, 3, 1, 0⟩
theorem s8_123_edges : next config 8 s8_123 = [s9_36] := by decide
theorem s8_123_safe : Safe 5 8 s8_123 := by
  apply safe_succ 4 8 s8_123 [s9_36] (by decide) s8_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_36_safe
def s8_124 : State := ⟨[3,117,104,145], 44601830845602028332415568414385656117264670, 3, 1, 1, 0⟩
theorem s8_124_edges : next config 8 s8_124 = [] := by decide
theorem s8_124_safe : Safe 5 8 s8_124 := by
  apply safe_succ 4 8 s8_124 [] (by decide) s8_124_edges
  simp
def s8_125 : State := ⟨[3,125,104,145], 44601873214744393976609017223235702553248030, 3, 1, 1, 0⟩
theorem s8_125_edges : next config 8 s8_125 = [] := by decide
theorem s8_125_safe : Safe 5 8 s8_125 := by
  apply safe_succ 4 8 s8_125 [] (by decide) s8_125_edges
  simp
def s8_126 : State := ⟨[9,4,104,145], 44601830679448528859301084301409773582222102, 3, 3, 1, 0⟩
theorem s8_126_edges : next config 8 s8_126 = [] := by decide
theorem s8_126_safe : Safe 5 8 s8_126 := by
  apply safe_succ 4 8 s8_126 [] (by decide) s8_126_edges
  simp
def s8_127 : State := ⟨[17,4,67,145], 44601830679428167303742095461371901181624598, 3, 2, 1, 0⟩
theorem s8_127_edges : next config 8 s8_127 = [s9_0] := by decide
theorem s8_127_safe : Safe 5 8 s8_127 := by
  apply safe_succ 4 8 s8_127 [s9_0] (by decide) s8_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_0_safe
def s8_128 : State := ⟨[17,4,67,145], 44601830679428167304950947494010235518124310, 3, 2, 1, 0⟩
theorem s8_128_edges : next config 8 s8_128 = [s9_1] := by decide
theorem s8_128_safe : Safe 5 8 s8_128 := by
  apply safe_succ 4 8 s8_128 [s9_1] (by decide) s8_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_1_safe
def s8_129 : State := ⟨[17,4,100,145], 44601830679429514100297660860387323034140958, 3, 3, 1, 0⟩
theorem s8_129_edges : next config 8 s8_129 = [] := by decide
theorem s8_129_safe : Safe 5 8 s8_129 := by
  apply safe_succ 4 8 s8_129 [] (by decide) s8_129_edges
  simp
def s8_130 : State := ⟨[17,4,100,145], 44601830679429514100297697753875470453244182, 3, 3, 1, 0⟩
theorem s8_130_edges : next config 8 s8_130 = [] := by decide
theorem s8_130_safe : Safe 5 8 s8_130 := by
  apply safe_succ 4 8 s8_130 [] (by decide) s8_130_edges
  simp
def s8_131 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773580128542, 3, 3, 1, 0⟩
theorem s8_131_edges : next config 8 s8_131 = [s9_73, s9_128, s9_56] := by decide
theorem s8_131_safe : Safe 5 8 s8_131 := by
  apply safe_succ 4 8 s8_131 [s9_73, s9_128, s9_56] (by decide) s8_131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_73_safe
  · subst z; exact s9_128_safe
  · subst z; exact s9_56_safe
def s8_132 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773582221598, 3, 3, 1, 0⟩
theorem s8_132_edges : next config 8 s8_132 = [s9_171, s9_87, s9_129, s9_71, s9_48, s9_40, s9_38, s9_46] := by decide
theorem s8_132_safe : Safe 5 8 s8_132 := by
  apply safe_succ 4 8 s8_132 [s9_171, s9_87, s9_129, s9_71, s9_48, s9_40, s9_38, s9_46] (by decide) s8_132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s9_171_safe
  · subst z; exact s9_87_safe
  · subst z; exact s9_129_safe
  · subst z; exact s9_71_safe
  · subst z; exact s9_48_safe
  · subst z; exact s9_40_safe
  · subst z; exact s9_38_safe
  · subst z; exact s9_46_safe
def s8_133 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773582222102, 3, 3, 1, 0⟩
theorem s8_133_edges : next config 8 s8_133 = [] := by decide
theorem s8_133_safe : Safe 5 8 s8_133 := by
  apply safe_succ 4 8 s8_133 [] (by decide) s8_133_edges
  simp
def s8_134 : State := ⟨[17,4,104,145], 44601830679448528859301084301409782170063126, 3, 3, 1, 0⟩
theorem s8_134_edges : next config 8 s8_134 = [s9_74, s9_57] := by decide
theorem s8_134_safe : Safe 5 8 s8_134 := by
  apply safe_succ 4 8 s8_134 [s9_74, s9_57] (by decide) s8_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_74_safe
  · subst z; exact s9_57_safe
def s8_135 : State := ⟨[17,4,104,145], 44601830679448528859301084301409782172156182, 3, 3, 1, 0⟩
theorem s8_135_edges : next config 8 s8_135 = [s9_49] := by decide
theorem s8_135_safe : Safe 5 8 s8_135 := by
  apply safe_succ 4 8 s8_135 [s9_49] (by decide) s8_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_49_safe
def s8_136 : State := ⟨[17,4,104,145], 44601830679448528859301121194897920999231766, 3, 3, 1, 0⟩
theorem s8_136_edges : next config 8 s8_136 = [s9_75, s9_58] := by decide
theorem s8_136_safe : Safe 5 8 s8_136 := by
  apply safe_succ 4 8 s8_136 [s9_75, s9_58] (by decide) s8_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_75_safe
  · subst z; exact s9_58_safe
def s8_137 : State := ⟨[17,4,104,145], 44601830679448528859301121194897921001324822, 3, 3, 1, 0⟩
theorem s8_137_edges : next config 8 s8_137 = [s9_172, s9_88, s9_72, s9_50, s9_41, s9_39, s9_47] := by decide
theorem s8_137_safe : Safe 5 8 s8_137 := by
  apply safe_succ 4 8 s8_137 [s9_172, s9_88, s9_72, s9_50, s9_41, s9_39, s9_47] (by decide) s8_137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s9_172_safe
  · subst z; exact s9_88_safe
  · subst z; exact s9_72_safe
  · subst z; exact s9_50_safe
  · subst z; exact s9_41_safe
  · subst z; exact s9_39_safe
  · subst z; exact s9_47_safe
def s8_138 : State := ⟨[17,4,104,145], 44601830679448687315626112830084960668029206, 3, 3, 1, 0⟩
theorem s8_138_edges : next config 8 s8_138 = [s9_76, s9_59] := by decide
theorem s8_138_safe : Safe 5 8 s8_138 := by
  apply safe_succ 4 8 s8_138 [s9_76, s9_59] (by decide) s8_138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_76_safe
  · subst z; exact s9_59_safe
def s8_139 : State := ⟨[17,4,104,145], 44601830679448687315626112830084960670122262, 3, 3, 1, 0⟩
theorem s8_139_edges : next config 8 s8_139 = [s9_51] := by decide
theorem s8_139_safe : Safe 5 8 s8_139 := by
  apply safe_succ 4 8 s8_139 [s9_51] (by decide) s8_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_51_safe
def s8_140 : State := ⟨[17,4,104,145], 44601830679449796509901312530811270283329822, 3, 3, 1, 0⟩
theorem s8_140_edges : next config 8 s8_140 = [s9_77, s9_60] := by decide
theorem s8_140_safe : Safe 5 8 s8_140 := by
  apply safe_succ 4 8 s8_140 [s9_77, s9_60] (by decide) s8_140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_77_safe
  · subst z; exact s9_60_safe
def s8_141 : State := ⟨[17,4,104,145], 44601830679449796509901349424299417702433046, 3, 3, 1, 0⟩
theorem s8_141_edges : next config 8 s8_141 = [s9_78, s9_61] := by decide
theorem s8_141_safe : Safe 5 8 s8_141 := by
  apply safe_succ 4 8 s8_141 [s9_78, s9_61] (by decide) s8_141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_78_safe
  · subst z; exact s9_61_safe
def s8_142 : State := ⟨[17,4,104,145], 44601830679773047412959511028192929600700702, 3, 3, 1, 0⟩
theorem s8_142_edges : next config 8 s8_142 = [s9_79, s9_62] := by decide
theorem s8_142_safe : Safe 5 8 s8_142 := by
  apply safe_succ 4 8 s8_142 [s9_79, s9_62] (by decide) s8_142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_79_safe
  · subst z; exact s9_62_safe
def s8_143 : State := ⟨[17,4,104,145], 44601830679773047412959547921681077019803926, 3, 3, 1, 0⟩
theorem s8_143_edges : next config 8 s8_143 = [s9_80, s9_63] := by decide
theorem s8_143_safe : Safe 5 8 s8_143 := by
  apply safe_succ 4 8 s8_143 [s9_80, s9_63] (by decide) s8_143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_80_safe
  · subst z; exact s9_63_safe
def s8_144 : State := ⟨[17,4,108,128], 340282711801129888074482896206590837022, 3, 3, 0, 0⟩
theorem s8_144_edges : next config 8 s8_144 = [s9_38] := by decide
theorem s8_144_safe : Safe 5 8 s8_144 := by
  apply safe_succ 4 8 s8_144 [s9_38] (by decide) s8_144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_38_safe
def s8_145 : State := ⟨[17,4,108,128], 340282711801129888111376384354009940246, 3, 3, 0, 0⟩
theorem s8_145_edges : next config 8 s8_145 = [s9_39] := by decide
theorem s8_145_safe : Safe 5 8 s8_145 := by
  apply safe_succ 4 8 s8_145 [s9_39] (by decide) s8_145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_39_safe
def s8_146 : State := ⟨[17,4,113,145], 44601830689812840166767087888046818987282718, 3, 3, 1, 0⟩
theorem s8_146_edges : next config 8 s8_146 = [s9_81, s9_64] := by decide
theorem s8_146_safe : Safe 5 8 s8_146 := by
  apply safe_succ 4 8 s8_146 [s9_81, s9_64] (by decide) s8_146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_81_safe
  · subst z; exact s9_64_safe
def s8_147 : State := ⟨[17,4,113,145], 44601830689812840166767087888046818989375774, 3, 3, 1, 0⟩
theorem s8_147_edges : next config 8 s8_147 = [s9_52] := by decide
theorem s8_147_safe : Safe 5 8 s8_147 := by
  apply safe_succ 4 8 s8_147 [s9_52] (by decide) s8_147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_52_safe
def s8_148 : State := ⟨[17,4,113,145], 44601830689812840166767124781534966406385942, 3, 3, 1, 0⟩
theorem s8_148_edges : next config 8 s8_148 = [s9_82, s9_65] := by decide
theorem s8_148_safe : Safe 5 8 s8_148 := by
  apply safe_succ 4 8 s8_148 [s9_82, s9_65] (by decide) s8_148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_82_safe
  · subst z; exact s9_65_safe
def s8_149 : State := ⟨[17,4,113,145], 44601830689812840166767124781534966408478998, 3, 3, 1, 0⟩
theorem s8_149_edges : next config 8 s8_149 = [s9_53] := by decide
theorem s8_149_safe : Safe 5 8 s8_149 := by
  apply safe_succ 4 8 s8_149 [s9_53] (by decide) s8_149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_53_safe
def s8_150 : State := ⟨[17,4,117,145], 44601830845581745922811916743961708865978654, 3, 3, 1, 0⟩
theorem s8_150_edges : next config 8 s8_150 = [] := by decide
theorem s8_150_safe : Safe 5 8 s8_150 := by
  apply safe_succ 4 8 s8_150 [] (by decide) s8_150_edges
  simp
def s8_151 : State := ⟨[17,4,117,145], 44601830845581745922811953637449856285081878, 3, 3, 1, 0⟩
theorem s8_151_edges : next config 8 s8_151 = [] := by decide
theorem s8_151_safe : Safe 5 8 s8_151 := by
  apply safe_succ 4 8 s8_151 [] (by decide) s8_151_edges
  simp
def s8_152 : State := ⟨[17,4,121,128], 342940843274146061393563727171130949918, 3, 3, 0, 0⟩
theorem s8_152_edges : next config 8 s8_152 = [s9_40] := by decide
theorem s8_152_safe : Safe 5 8 s8_152 := by
  apply safe_succ 4 8 s8_152 [s9_40] (by decide) s8_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_40_safe
def s8_153 : State := ⟨[17,4,121,128], 342940843274146061430457215318550053142, 3, 3, 0, 0⟩
theorem s8_153_edges : next config 8 s8_153 = [s9_41] := by decide
theorem s8_153_safe : Safe 5 8 s8_153 := by
  apply safe_succ 4 8 s8_153 [s9_41] (by decide) s8_153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_41_safe
def s8_154 : State := ⟨[17,4,125,128], 382817683147693537580677938979541287198, 3, 3, 0, 0⟩
theorem s8_154_edges : next config 8 s8_154 = [s9_42] := by decide
theorem s8_154_safe : Safe 5 8 s8_154 := by
  apply safe_succ 4 8 s8_154 [s9_42] (by decide) s8_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_42_safe
def s8_155 : State := ⟨[17,4,125,128], 382817683147693537580677938988131221782, 3, 3, 0, 0⟩
theorem s8_155_edges : next config 8 s8_155 = [s9_43] := by decide
theorem s8_155_safe : Safe 5 8 s8_155 := by
  apply safe_succ 4 8 s8_155 [s9_43] (by decide) s8_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_43_safe
def s8_156 : State := ⟨[17,4,125,128], 382817683147693537617571427126960390422, 3, 3, 0, 0⟩
theorem s8_156_edges : next config 8 s8_156 = [s9_44] := by decide
theorem s8_156_safe : Safe 5 8 s8_156 := by
  apply safe_succ 4 8 s8_156 [s9_44] (by decide) s8_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_44_safe
def s8_157 : State := ⟨[17,4,125,128], 382817683306149862609206614166629187862, 3, 3, 0, 0⟩
theorem s8_157_edges : next config 8 s8_157 = [s9_45] := by decide
theorem s8_157_safe : Safe 5 8 s8_157 := by
  apply safe_succ 4 8 s8_157 [s9_45] (by decide) s8_157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_45_safe
def s8_158 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082078, 3, 3, 1, 0⟩
theorem s8_158_edges : next config 8 s8_158 = [s9_83, s9_66] := by decide
theorem s8_158_safe : Safe 5 8 s8_158 := by
  apply safe_succ 4 8 s8_158 [s9_83, s9_66] (by decide) s8_158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_83_safe
  · subst z; exact s9_66_safe
def s8_159 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175134, 3, 3, 1, 0⟩
theorem s8_159_edges : next config 8 s8_159 = [s9_54] := by decide
theorem s8_159_safe : Safe 5 8 s8_159 := by
  apply safe_succ 4 8 s8_159 [s9_54] (by decide) s8_159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_54_safe
def s8_160 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376333185302, 3, 3, 1, 0⟩
theorem s8_160_edges : next config 8 s8_160 = [s9_84, s9_67] := by decide
theorem s8_160_safe : Safe 5 8 s8_160 := by
  apply safe_succ 4 8 s8_160 [s9_84, s9_67] (by decide) s8_160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_84_safe
  · subst z; exact s9_67_safe
def s8_161 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376335278358, 3, 3, 1, 0⟩
theorem s8_161_edges : next config 8 s8_161 = [s9_55] := by decide
theorem s8_161_safe : Safe 5 8 s8_161 := by
  apply safe_succ 4 8 s8_161 [s9_55] (by decide) s8_161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_55_safe
def s8_162 : State := ⟨[17,12,67,145], 44601830679428167221535065940600822463402270, 3, 3, 1, 0⟩
theorem s8_162_edges : next config 8 s8_162 = [s9_146, s9_130] := by decide
theorem s8_162_safe : Safe 5 8 s8_162 := by
  apply safe_succ 4 8 s8_162 [s9_146, s9_130] (by decide) s8_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_146_safe
  · subst z; exact s9_130_safe
def s8_163 : State := ⟨[17,12,67,145], 44601830679428167226370843006035634000433430, 3, 2, 1, 0⟩
theorem s8_163_edges : next config 8 s8_163 = [s9_4] := by decide
theorem s8_163_safe : Safe 5 8 s8_163 := by
  apply safe_succ 4 8 s8_163 [s9_4] (by decide) s8_163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_4_safe
def s8_164 : State := ⟨[17,12,67,145], 44601830679428167227579695038673968336933142, 3, 2, 1, 0⟩
theorem s8_164_edges : next config 8 s8_164 = [s9_5] := by decide
theorem s8_164_safe : Safe 5 8 s8_164 := by
  apply safe_succ 4 8 s8_164 [s9_5] (by decide) s8_164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_5_safe
def s8_165 : State := ⟨[17,12,96,145], 44601830679428246449697432630985826330939678, 3, 3, 1, 0⟩
theorem s8_165_edges : next config 8 s8_165 = [s9_169, s9_131, s9_52, s9_54, s9_48] := by decide
theorem s8_165_safe : Safe 5 8 s8_165 := by
  apply safe_succ 4 8 s8_165 [s9_169, s9_131, s9_52, s9_54, s9_48] (by decide) s8_165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s9_169_safe
  · subst z; exact s9_131_safe
  · subst z; exact s9_52_safe
  · subst z; exact s9_54_safe
  · subst z; exact s9_48_safe
def s8_166 : State := ⟨[17,12,96,145], 44601830679428246449697432630985834920874262, 3, 3, 1, 0⟩
theorem s8_166_edges : next config 8 s8_166 = [s9_49] := by decide
theorem s8_166_safe : Safe 5 8 s8_166 := by
  apply safe_succ 4 8 s8_166 [s9_49] (by decide) s8_166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_49_safe
def s8_167 : State := ⟨[17,12,96,145], 44601830679428246449697469524473973750042902, 3, 3, 1, 0⟩
theorem s8_167_edges : next config 8 s8_167 = [s9_170, s9_53, s9_55, s9_50] := by decide
theorem s8_167_safe : Safe 5 8 s8_167 := by
  apply safe_succ 4 8 s8_167 [s9_170, s9_53, s9_55, s9_50] (by decide) s8_167_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s9_170_safe
  · subst z; exact s9_53_safe
  · subst z; exact s9_55_safe
  · subst z; exact s9_50_safe
def s8_168 : State := ⟨[17,12,96,145], 44601830679428404906022461159661013418840342, 3, 3, 1, 0⟩
theorem s8_168_edges : next config 8 s8_168 = [s9_51] := by decide
theorem s8_168_safe : Safe 5 8 s8_168 := by
  apply safe_succ 4 8 s8_168 [s9_51] (by decide) s8_168_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_51_safe
def s8_169 : State := ⟨[17,12,104,128], 340282387282576229647756113050570264862, 3, 3, 0, 0⟩
theorem s8_169_edges : next config 8 s8_169 = [s9_48] := by decide
theorem s8_169_safe : Safe 5 8 s8_169 := by
  apply safe_succ 4 8 s8_169 [s9_48] (by decide) s8_169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_48_safe
def s8_170 : State := ⟨[17,12,104,128], 340282387282576229647756113059160199446, 3, 3, 0, 0⟩
theorem s8_170_edges : next config 8 s8_170 = [s9_49] := by decide
theorem s8_170_safe : Safe 5 8 s8_170 := by
  apply safe_succ 4 8 s8_170 [s9_49] (by decide) s8_170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_49_safe
def s8_171 : State := ⟨[17,12,104,128], 340282387282576229684649601197989368086, 3, 3, 0, 0⟩
theorem s8_171_edges : next config 8 s8_171 = [s9_50] := by decide
theorem s8_171_safe : Safe 5 8 s8_171 := by
  apply safe_succ 4 8 s8_171 [s9_50] (by decide) s8_171_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_50_safe
def s8_172 : State := ⟨[17,12,104,128], 340282387441032554676284788237658165526, 3, 3, 0, 0⟩
theorem s8_172_edges : next config 8 s8_172 = [s9_51] := by decide
theorem s8_172_safe : Safe 5 8 s8_172 := by
  apply safe_succ 4 8 s8_172 [s9_51] (by decide) s8_172_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_51_safe
def s8_173 : State := ⟨[17,12,113,128], 340292751593883695651342750095977419038, 3, 3, 0, 0⟩
theorem s8_173_edges : next config 8 s8_173 = [s9_52] := by decide
theorem s8_173_safe : Safe 5 8 s8_173 := by
  apply safe_succ 4 8 s8_173 [s9_52] (by decide) s8_173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_52_safe
def s8_174 : State := ⟨[17,12,113,128], 340292751593883695688236238243396522262, 3, 3, 0, 0⟩
theorem s8_174_edges : next config 8 s8_174 = [s9_53] := by decide
theorem s8_174_safe : Safe 5 8 s8_174 := by
  apply safe_succ 4 8 s8_174 [s9_53] (by decide) s8_174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_53_safe
def s8_175 : State := ⟨[17,12,125,145], 44601873214744393976609017223235702553252118, 3, 2, 1, 0⟩
theorem s8_175_edges : next config 8 s8_175 = [s9_6] := by decide
theorem s8_175_safe : Safe 5 8 s8_175 := by
  apply safe_succ 4 8 s8_175 [s9_6] (by decide) s8_175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_6_safe
def s8_176 : State := ⟨[17,21,67,145], 44601830679428167221535065940600822463402270, 3, 3, 1, 0⟩
theorem s8_176_edges : next config 8 s8_176 = [s9_147, s9_132, s9_68] := by decide
theorem s8_176_safe : Safe 5 8 s8_176 := by
  apply safe_succ 4 8 s8_176 [s9_147, s9_132, s9_68] (by decide) s8_176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_147_safe
  · subst z; exact s9_132_safe
  · subst z; exact s9_68_safe
def s8_177 : State := ⟨[17,21,67,145], 44601830679428167226370843006035634000433430, 3, 2, 1, 0⟩
theorem s8_177_edges : next config 8 s8_177 = [s9_7] := by decide
theorem s8_177_safe : Safe 5 8 s8_177 := by
  apply safe_succ 4 8 s8_177 [s9_7] (by decide) s8_177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_7_safe
def s8_178 : State := ⟨[17,21,67,145], 44601830679428167227579695038673968336933142, 3, 2, 1, 0⟩
theorem s8_178_edges : next config 8 s8_178 = [s9_8] := by decide
theorem s8_178_safe : Safe 5 8 s8_178 := by
  apply safe_succ 4 8 s8_178 [s9_8] (by decide) s8_178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_8_safe
def s8_179 : State := ⟨[17,21,67,145], 44601830679428167303742095461371901181624598, 3, 2, 1, 0⟩
theorem s8_179_edges : next config 8 s8_179 = [s9_9] := by decide
theorem s8_179_safe : Safe 5 8 s8_179 := by
  apply safe_succ 4 8 s8_179 [s9_9] (by decide) s8_179_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_9_safe
def s8_180 : State := ⟨[17,21,67,145], 44601830679428167304950947494010235518124310, 3, 2, 1, 0⟩
theorem s8_180_edges : next config 8 s8_180 = [s9_10] := by decide
theorem s8_180_safe : Safe 5 8 s8_180 := by
  apply safe_succ 4 8 s8_180 [s9_10] (by decide) s8_180_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_10_safe
def s8_181 : State := ⟨[17,21,96,145], 44601830679428246449697432630985826330939678, 3, 3, 1, 0⟩
theorem s8_181_edges : next config 8 s8_181 = [s9_64, s9_66, s9_56] := by decide
theorem s8_181_safe : Safe 5 8 s8_181 := by
  apply safe_succ 4 8 s8_181 [s9_64, s9_66, s9_56] (by decide) s8_181_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_64_safe
  · subst z; exact s9_66_safe
  · subst z; exact s9_56_safe
def s8_182 : State := ⟨[17,21,96,145], 44601830679428246449697432630985834920874262, 3, 3, 1, 0⟩
theorem s8_182_edges : next config 8 s8_182 = [s9_57] := by decide
theorem s8_182_safe : Safe 5 8 s8_182 := by
  apply safe_succ 4 8 s8_182 [s9_57] (by decide) s8_182_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_57_safe
def s8_183 : State := ⟨[17,21,96,145], 44601830679428246449697469524473973750042902, 3, 3, 1, 0⟩
theorem s8_183_edges : next config 8 s8_183 = [s9_65, s9_67, s9_58] := by decide
theorem s8_183_safe : Safe 5 8 s8_183 := by
  apply safe_succ 4 8 s8_183 [s9_65, s9_67, s9_58] (by decide) s8_183_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_65_safe
  · subst z; exact s9_67_safe
  · subst z; exact s9_58_safe
def s8_184 : State := ⟨[17,21,96,145], 44601830679428404906022461159661013418840342, 3, 3, 1, 0⟩
theorem s8_184_edges : next config 8 s8_184 = [s9_59] := by decide
theorem s8_184_safe : Safe 5 8 s8_184 := by
  apply safe_succ 4 8 s8_184 [s9_59] (by decide) s8_184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_59_safe
def s8_185 : State := ⟨[17,21,96,145], 44601830679429514100297660860387323034140958, 3, 3, 1, 0⟩
theorem s8_185_edges : next config 8 s8_185 = [s9_60] := by decide
theorem s8_185_safe : Safe 5 8 s8_185 := by
  apply safe_succ 4 8 s8_185 [s9_60] (by decide) s8_185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_60_safe
def s8_186 : State := ⟨[17,21,96,145], 44601830679429514100297697753875470453244182, 3, 3, 1, 0⟩
theorem s8_186_edges : next config 8 s8_186 = [s9_61] := by decide
theorem s8_186_safe : Safe 5 8 s8_186 := by
  apply safe_succ 4 8 s8_186 [s9_61] (by decide) s8_186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_61_safe
def s8_187 : State := ⟨[17,21,104,128], 340282387282576229647756113050570264862, 3, 3, 0, 0⟩
theorem s8_187_edges : next config 8 s8_187 = [s9_56] := by decide
theorem s8_187_safe : Safe 5 8 s8_187 := by
  apply safe_succ 4 8 s8_187 [s9_56] (by decide) s8_187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_56_safe
def s8_188 : State := ⟨[17,21,104,128], 340282387282576229647756113059160199446, 3, 3, 0, 0⟩
theorem s8_188_edges : next config 8 s8_188 = [s9_57] := by decide
theorem s8_188_safe : Safe 5 8 s8_188 := by
  apply safe_succ 4 8 s8_188 [s9_57] (by decide) s8_188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_57_safe
def s8_189 : State := ⟨[17,21,104,128], 340282387282576229684649601197989368086, 3, 3, 0, 0⟩
theorem s8_189_edges : next config 8 s8_189 = [s9_58] := by decide
theorem s8_189_safe : Safe 5 8 s8_189 := by
  apply safe_succ 4 8 s8_189 [s9_58] (by decide) s8_189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_58_safe
def s8_190 : State := ⟨[17,21,104,128], 340282387441032554676284788237658165526, 3, 3, 0, 0⟩
theorem s8_190_edges : next config 8 s8_190 = [s9_59] := by decide
theorem s8_190_safe : Safe 5 8 s8_190 := by
  apply safe_succ 4 8 s8_190 [s9_59] (by decide) s8_190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_59_safe
def s8_191 : State := ⟨[17,21,104,128], 340282388550226829875985514547273466142, 3, 3, 0, 0⟩
theorem s8_191_edges : next config 8 s8_191 = [s9_60] := by decide
theorem s8_191_safe : Safe 5 8 s8_191 := by
  apply safe_succ 4 8 s8_191 [s9_60] (by decide) s8_191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_60_safe
def s8_192 : State := ⟨[17,21,104,128], 340282388550226829912879002694692569366, 3, 3, 0, 0⟩
theorem s8_192_edges : next config 8 s8_192 = [s9_61] := by decide
theorem s8_192_safe : Safe 5 8 s8_192 := by
  apply safe_succ 4 8 s8_192 [s9_61] (by decide) s8_192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_61_safe
def s8_193 : State := ⟨[17,21,104,128], 340282711801129888074482896206590837022, 3, 3, 0, 0⟩
theorem s8_193_edges : next config 8 s8_193 = [s9_62] := by decide
theorem s8_193_safe : Safe 5 8 s8_193 := by
  apply safe_succ 4 8 s8_193 [s9_62] (by decide) s8_193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_62_safe
def s8_194 : State := ⟨[17,21,104,128], 340282711801129888111376384354009940246, 3, 3, 0, 0⟩
theorem s8_194_edges : next config 8 s8_194 = [s9_63] := by decide
theorem s8_194_safe : Safe 5 8 s8_194 := by
  apply safe_succ 4 8 s8_194 [s9_63] (by decide) s8_194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_63_safe
def s8_195 : State := ⟨[17,21,108,145], 44601830679773047412959511028192929602797854, 3, 1, 1, 0⟩
theorem s8_195_edges : next config 8 s8_195 = [s9_38] := by decide
theorem s8_195_safe : Safe 5 8 s8_195 := by
  apply safe_succ 4 8 s8_195 [s9_38] (by decide) s8_195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_38_safe
def s8_196 : State := ⟨[17,21,108,145], 44601830679773047412959547921681077021901078, 3, 1, 1, 0⟩
theorem s8_196_edges : next config 8 s8_196 = [s9_39] := by decide
theorem s8_196_safe : Safe 5 8 s8_196 := by
  apply safe_succ 4 8 s8_196 [s9_39] (by decide) s8_196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_39_safe
def s8_197 : State := ⟨[17,21,113,128], 340292751593883695651342750095977419038, 3, 3, 0, 0⟩
theorem s8_197_edges : next config 8 s8_197 = [s9_64] := by decide
theorem s8_197_safe : Safe 5 8 s8_197 := by
  apply safe_succ 4 8 s8_197 [s9_64] (by decide) s8_197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_64_safe
def s8_198 : State := ⟨[17,21,113,128], 340292751593883695688236238243396522262, 3, 3, 0, 0⟩
theorem s8_198_edges : next config 8 s8_198 = [s9_65] := by decide
theorem s8_198_safe : Safe 5 8 s8_198 := by
  apply safe_succ 4 8 s8_198 [s9_65] (by decide) s8_198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_65_safe
def s8_199 : State := ⟨[17,21,121,145], 44601833337904520429132830109023894142910750, 3, 1, 1, 0⟩
theorem s8_199_edges : next config 8 s8_199 = [s9_40] := by decide
theorem s8_199_safe : Safe 5 8 s8_199 := by
  apply safe_succ 4 8 s8_199 [s9_40] (by decide) s8_199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_40_safe
def s8_200 : State := ⟨[17,21,121,145], 44601833337904520429132867002512041562013974, 3, 1, 1, 0⟩
theorem s8_200_edges : next config 8 s8_200 = [s9_41] := by decide
theorem s8_200_safe : Safe 5 8 s8_200 := by
  apply safe_succ 4 8 s8_200 [s9_41] (by decide) s8_200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_41_safe
def s8_201 : State := ⟨[17,21,125,145], 44601873214744393976609017223235702553248030, 3, 1, 1, 0⟩
theorem s8_201_edges : next config 8 s8_201 = [s9_42] := by decide
theorem s8_201_safe : Safe 5 8 s8_201 := by
  apply safe_succ 4 8 s8_201 [s9_42] (by decide) s8_201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_42_safe
def s8_202 : State := ⟨[17,21,125,145], 44601873214744393976609017223235702553252118, 3, 2, 1, 0⟩
theorem s8_202_edges : next config 8 s8_202 = [s9_11] := by decide
theorem s8_202_safe : Safe 5 8 s8_202 := by
  apply safe_succ 4 8 s8_202 [s9_11] (by decide) s8_202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_11_safe
def s8_203 : State := ⟨[17,21,125,145], 44601873214744393976609017223235711143182614, 3, 1, 1, 0⟩
theorem s8_203_edges : next config 8 s8_203 = [s9_43] := by decide
theorem s8_203_safe : Safe 5 8 s8_203 := by
  apply safe_succ 4 8 s8_203 [s9_43] (by decide) s8_203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_43_safe
def s8_204 : State := ⟨[17,21,125,145], 44601873214744393976609054116723849972351254, 3, 1, 1, 0⟩
theorem s8_204_edges : next config 8 s8_204 = [s9_44] := by decide
theorem s8_204_safe : Safe 5 8 s8_204 := by
  apply safe_succ 4 8 s8_204 [s9_44] (by decide) s8_204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_44_safe
def s8_205 : State := ⟨[17,21,125,145], 44601873214744552432934045751910889641148694, 3, 1, 1, 0⟩
theorem s8_205_edges : next config 8 s8_205 = [s9_45] := by decide
theorem s8_205_safe : Safe 5 8 s8_205 := by
  apply safe_succ 4 8 s8_205 [s9_45] (by decide) s8_205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_45_safe
def s8_206 : State := ⟨[17,21,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546910, 3, 1, 1, 0⟩
theorem s8_206_edges : next config 8 s8_206 = [s9_46] := by decide
theorem s8_206_safe : Safe 5 8 s8_206 := by
  apply safe_succ 4 8 s8_206 [s9_46] (by decide) s8_206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_46_safe
def s8_207 : State := ⟨[17,21,249,145], 904625697166532776746648320380418881934351203729176207679457272982822650134, 3, 1, 1, 0⟩
theorem s8_207_edges : next config 8 s8_207 = [s9_47] := by decide
theorem s8_207_safe : Safe 5 8 s8_207 := by
  apply safe_succ 4 8 s8_207 [s9_47] (by decide) s8_207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_47_safe
def s8_208 : State := ⟨[17,29,104,145], 44601830679448528859301084301409774119092510, 3, 1, 1, 0⟩
theorem s8_208_edges : next config 8 s8_208 = [] := by decide
theorem s8_208_safe : Safe 5 8 s8_208 := by
  apply safe_succ 4 8 s8_208 [] (by decide) s8_208_edges
  simp
def s8_209 : State := ⟨[17,29,104,145], 44601830679448528859301084301409782709027094, 3, 1, 1, 0⟩
theorem s8_209_edges : next config 8 s8_209 = [] := by decide
theorem s8_209_safe : Safe 5 8 s8_209 := by
  apply safe_succ 4 8 s8_209 [] (by decide) s8_209_edges
  simp
def s8_210 : State := ⟨[17,29,104,145], 44601830679448528859301121194897921538195734, 3, 1, 1, 0⟩
theorem s8_210_edges : next config 8 s8_210 = [] := by decide
theorem s8_210_safe : Safe 5 8 s8_210 := by
  apply safe_succ 4 8 s8_210 [] (by decide) s8_210_edges
  simp
def s8_211 : State := ⟨[17,53,104,145], 44601830679448528859301084310416972836962590, 3, 1, 1, 0⟩
theorem s8_211_edges : next config 8 s8_211 = [] := by decide
theorem s8_211_safe : Safe 5 8 s8_211 := by
  apply safe_succ 4 8 s8_211 [] (by decide) s8_211_edges
  simp
def s8_212 : State := ⟨[17,86,67,128], 340282366921015834881850640366632636702, 3, 3, 0, 0⟩
theorem s8_212_edges : next config 8 s8_212 = [s9_68] := by decide
theorem s8_212_safe : Safe 5 8 s8_212 := by
  apply safe_succ 4 8 s8_212 [s9_68] (by decide) s8_212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_68_safe
def s8_213 : State := ⟨[17,86,67,145], 44601830679428167298906355289425237063700758, 3, 2, 1, 0⟩
theorem s8_213_edges : next config 8 s8_213 = [s9_12] := by decide
theorem s8_213_safe : Safe 5 8 s8_213 := by
  apply safe_succ 4 8 s8_213 [s9_12] (by decide) s8_213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_12_safe
def s8_214 : State := ⟨[17,86,67,145], 44601830679428167298906392182913384482803990, 3, 2, 1, 0⟩
theorem s8_214_edges : next config 8 s8_214 = [s9_13] := by decide
theorem s8_214_safe : Safe 5 8 s8_214 := by
  apply safe_succ 4 8 s8_214 [s9_13] (by decide) s8_214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_13_safe
def s8_215 : State := ⟨[17,86,67,145], 44601830679428167303742095461371901181624598, 3, 2, 1, 0⟩
theorem s8_215_edges : next config 8 s8_215 = [s9_14] := by decide
theorem s8_215_safe : Safe 5 8 s8_215 := by
  apply safe_succ 4 8 s8_215 [s9_14] (by decide) s8_215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_14_safe
def s8_216 : State := ⟨[17,86,67,145], 44601830679428167304950947494010235518124310, 3, 2, 1, 0⟩
theorem s8_216_edges : next config 8 s8_216 = [s9_15] := by decide
theorem s8_216_safe : Safe 5 8 s8_216 := by
  apply safe_succ 4 8 s8_216 [s9_15] (by decide) s8_216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_15_safe
def s8_217 : State := ⟨[17,100,96,145], 44601830679429514100297660860387323034140958, 3, 3, 1, 0⟩
theorem s8_217_edges : next config 8 s8_217 = [s9_69] := by decide
theorem s8_217_safe : Safe 5 8 s8_217 := by
  apply safe_succ 4 8 s8_217 [s9_69] (by decide) s8_217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_69_safe
def s8_218 : State := ⟨[17,100,96,145], 44601830679429514100297697753875470453244182, 3, 3, 1, 0⟩
theorem s8_218_edges : next config 8 s8_218 = [s9_70] := by decide
theorem s8_218_safe : Safe 5 8 s8_218 := by
  apply safe_succ 4 8 s8_218 [s9_70] (by decide) s8_218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_70_safe
def s8_219 : State := ⟨[17,100,104,128], 340282388550226829875985514547273466142, 3, 3, 0, 0⟩
theorem s8_219_edges : next config 8 s8_219 = [s9_69] := by decide
theorem s8_219_safe : Safe 5 8 s8_219 := by
  apply safe_succ 4 8 s8_219 [s9_69] (by decide) s8_219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_69_safe
def s8_220 : State := ⟨[17,100,104,128], 340282388550226829912879002694692569366, 3, 3, 0, 0⟩
theorem s8_220_edges : next config 8 s8_220 = [s9_70] := by decide
theorem s8_220_safe : Safe 5 8 s8_220 := by
  apply safe_succ 4 8 s8_220 [s9_70] (by decide) s8_220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_70_safe
def s8_221 : State := ⟨[17,108,104,128], 340282711801129888074482896206590837022, 3, 3, 0, 0⟩
theorem s8_221_edges : next config 8 s8_221 = [s9_71] := by decide
theorem s8_221_safe : Safe 5 8 s8_221 := by
  apply safe_succ 4 8 s8_221 [s9_71] (by decide) s8_221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_71_safe
def s8_222 : State := ⟨[17,108,104,128], 340282711801129888111376384354009940246, 3, 3, 0, 0⟩
theorem s8_222_edges : next config 8 s8_222 = [s9_72] := by decide
theorem s8_222_safe : Safe 5 8 s8_222 := by
  apply safe_succ 4 8 s8_222 [s9_72] (by decide) s8_222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_72_safe
def s8_223 : State := ⟨[17,117,104,145], 44601830845602028332415568414385656117264670, 3, 1, 1, 0⟩
theorem s8_223_edges : next config 8 s8_223 = [] := by decide
theorem s8_223_safe : Safe 5 8 s8_223 := by
  apply safe_succ 4 8 s8_223 [] (by decide) s8_223_edges
  simp
def s8_224 : State := ⟨[17,117,104,145], 44601830845602028332415605307873803536367894, 3, 1, 1, 0⟩
theorem s8_224_edges : next config 8 s8_224 = [] := by decide
theorem s8_224_safe : Safe 5 8 s8_224 := by
  apply safe_succ 4 8 s8_224 [] (by decide) s8_224_edges
  simp
def s8_225 : State := ⟨[17,125,104,145], 44601873214744393976609017223235702553248030, 3, 1, 1, 0⟩
theorem s8_225_edges : next config 8 s8_225 = [] := by decide
theorem s8_225_safe : Safe 5 8 s8_225 := by
  apply safe_succ 4 8 s8_225 [] (by decide) s8_225_edges
  simp
def s8_226 : State := ⟨[17,125,104,145], 44601873214744393976609017223235702553252118, 3, 2, 1, 0⟩
theorem s8_226_edges : next config 8 s8_226 = [s9_16] := by decide
theorem s8_226_safe : Safe 5 8 s8_226 := by
  apply safe_succ 4 8 s8_226 [s9_16] (by decide) s8_226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_16_safe
def s8_227 : State := ⟨[17,125,104,145], 44601873214744393976609017223235711143182614, 3, 1, 1, 0⟩
theorem s8_227_edges : next config 8 s8_227 = [] := by decide
theorem s8_227_safe : Safe 5 8 s8_227 := by
  apply safe_succ 4 8 s8_227 [] (by decide) s8_227_edges
  simp
def s8_228 : State := ⟨[17,125,104,145], 44601873214744393976609054116723849972351254, 3, 1, 1, 0⟩
theorem s8_228_edges : next config 8 s8_228 = [] := by decide
theorem s8_228_safe : Safe 5 8 s8_228 := by
  apply safe_succ 4 8 s8_228 [] (by decide) s8_228_edges
  simp
def s8_229 : State := ⟨[17,125,104,145], 44601873214744552432934045751910889641148694, 3, 1, 1, 0⟩
theorem s8_229_edges : next config 8 s8_229 = [] := by decide
theorem s8_229_safe : Safe 5 8 s8_229 := by
  apply safe_succ 4 8 s8_229 [] (by decide) s8_229_edges
  simp
def s8_230 : State := ⟨[21,4,67,145], 44601830679428167221535065940600822463402270, 3, 3, 1, 0⟩
theorem s8_230_edges : next config 8 s8_230 = [s9_149] := by decide
theorem s8_230_safe : Safe 5 8 s8_230 := by
  apply safe_succ 4 8 s8_230 [s9_149] (by decide) s8_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_149_safe
def s8_231 : State := ⟨[21,4,67,145], 44601830679428167226370843006035634000433430, 3, 2, 1, 0⟩
theorem s8_231_edges : next config 8 s8_231 = [] := by decide
theorem s8_231_safe : Safe 5 8 s8_231 := by
  apply safe_succ 4 8 s8_231 [] (by decide) s8_231_edges
  simp
def s8_232 : State := ⟨[21,4,67,145], 44601830679428167227579695038673968336933142, 3, 2, 1, 0⟩
theorem s8_232_edges : next config 8 s8_232 = [] := by decide
theorem s8_232_safe : Safe 5 8 s8_232 := by
  apply safe_succ 4 8 s8_232 [] (by decide) s8_232_edges
  simp
def s8_233 : State := ⟨[21,4,67,145], 44601830679428167303742021674395606343418142, 1, 1, 1, 0⟩
theorem s8_233_edges : next config 8 s8_233 = [] := by decide
theorem s8_233_safe : Safe 5 8 s8_233 := by
  apply safe_succ 4 8 s8_233 [] (by decide) s8_233_edges
  simp
def s8_234 : State := ⟨[21,4,67,145], 44601830679428167303742095461371901181624598, 3, 2, 1, 0⟩
theorem s8_234_edges : next config 8 s8_234 = [] := by decide
theorem s8_234_safe : Safe 5 8 s8_234 := by
  apply safe_succ 4 8 s8_234 [] (by decide) s8_234_edges
  simp
def s8_235 : State := ⟨[21,4,67,145], 44601830679428167304950947494010235518124310, 3, 2, 1, 0⟩
theorem s8_235_edges : next config 8 s8_235 = [] := by decide
theorem s8_235_safe : Safe 5 8 s8_235 := by
  apply safe_succ 4 8 s8_235 [] (by decide) s8_235_edges
  simp
def s8_236 : State := ⟨[21,4,96,145], 44601830679428246449697432630985826330939678, 3, 3, 1, 0⟩
theorem s8_236_edges : next config 8 s8_236 = [s9_83, s9_73] := by decide
theorem s8_236_safe : Safe 5 8 s8_236 := by
  apply safe_succ 4 8 s8_236 [s9_83, s9_73] (by decide) s8_236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_83_safe
  · subst z; exact s9_73_safe
def s8_237 : State := ⟨[21,4,96,145], 44601830679428246449697432630985834920874262, 3, 3, 1, 0⟩
theorem s8_237_edges : next config 8 s8_237 = [s9_74] := by decide
theorem s8_237_safe : Safe 5 8 s8_237 := by
  apply safe_succ 4 8 s8_237 [s9_74] (by decide) s8_237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_74_safe
def s8_238 : State := ⟨[21,4,96,145], 44601830679428246449697469524473973750042902, 3, 3, 1, 0⟩
theorem s8_238_edges : next config 8 s8_238 = [s9_84, s9_75] := by decide
theorem s8_238_safe : Safe 5 8 s8_238 := by
  apply safe_succ 4 8 s8_238 [s9_84, s9_75] (by decide) s8_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_84_safe
  · subst z; exact s9_75_safe
def s8_239 : State := ⟨[21,4,96,145], 44601830679428404906022461159661013418840342, 3, 3, 1, 0⟩
theorem s8_239_edges : next config 8 s8_239 = [s9_76] := by decide
theorem s8_239_safe : Safe 5 8 s8_239 := by
  apply safe_succ 4 8 s8_239 [s9_76] (by decide) s8_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_76_safe
def s8_240 : State := ⟨[21,4,96,145], 44601830679429514100297660860387323034140958, 3, 3, 1, 0⟩
theorem s8_240_edges : next config 8 s8_240 = [s9_77] := by decide
theorem s8_240_safe : Safe 5 8 s8_240 := by
  apply safe_succ 4 8 s8_240 [s9_77] (by decide) s8_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_77_safe
def s8_241 : State := ⟨[21,4,96,145], 44601830679429514100297697753875470453244182, 3, 3, 1, 0⟩
theorem s8_241_edges : next config 8 s8_241 = [s9_78] := by decide
theorem s8_241_safe : Safe 5 8 s8_241 := by
  apply safe_succ 4 8 s8_241 [s9_78] (by decide) s8_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_78_safe
def s8_242 : State := ⟨[21,4,108,145], 44601830679773047412959511028192929602797854, 1, 1, 1, 0⟩
theorem s8_242_edges : next config 8 s8_242 = [] := by decide
theorem s8_242_safe : Safe 5 8 s8_242 := by
  apply safe_succ 4 8 s8_242 [] (by decide) s8_242_edges
  simp
def s8_243 : State := ⟨[21,4,108,145], 44601830679773047412959547921681077021901078, 1, 1, 1, 0⟩
theorem s8_243_edges : next config 8 s8_243 = [] := by decide
theorem s8_243_safe : Safe 5 8 s8_243 := by
  apply safe_succ 4 8 s8_243 [] (by decide) s8_243_edges
  simp
def s8_244 : State := ⟨[21,4,121,145], 44601833337904520429132830109023894142910750, 1, 1, 1, 0⟩
theorem s8_244_edges : next config 8 s8_244 = [] := by decide
theorem s8_244_safe : Safe 5 8 s8_244 := by
  apply safe_succ 4 8 s8_244 [] (by decide) s8_244_edges
  simp
def s8_245 : State := ⟨[21,4,121,145], 44601833337904520429132867002512041562013974, 1, 1, 1, 0⟩
theorem s8_245_edges : next config 8 s8_245 = [] := by decide
theorem s8_245_safe : Safe 5 8 s8_245 := by
  apply safe_succ 4 8 s8_245 [] (by decide) s8_245_edges
  simp
def s8_246 : State := ⟨[21,4,125,145], 44601873214744393976609017223235702553248030, 1, 1, 1, 0⟩
theorem s8_246_edges : next config 8 s8_246 = [s9_85] := by decide
theorem s8_246_safe : Safe 5 8 s8_246 := by
  apply safe_succ 4 8 s8_246 [s9_85] (by decide) s8_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_85_safe
def s8_247 : State := ⟨[21,4,125,145], 44601873214744393976609017223235702553252118, 3, 2, 1, 0⟩
theorem s8_247_edges : next config 8 s8_247 = [] := by decide
theorem s8_247_safe : Safe 5 8 s8_247 := by
  apply safe_succ 4 8 s8_247 [] (by decide) s8_247_edges
  simp
def s8_248 : State := ⟨[21,4,125,145], 44601873214744393976609017223235711143182614, 1, 1, 1, 0⟩
theorem s8_248_edges : next config 8 s8_248 = [] := by decide
theorem s8_248_safe : Safe 5 8 s8_248 := by
  apply safe_succ 4 8 s8_248 [] (by decide) s8_248_edges
  simp
def s8_249 : State := ⟨[21,4,125,145], 44601873214744393976609054116723849972351254, 1, 1, 1, 0⟩
theorem s8_249_edges : next config 8 s8_249 = [s9_86] := by decide
theorem s8_249_safe : Safe 5 8 s8_249 := by
  apply safe_succ 4 8 s8_249 [s9_86] (by decide) s8_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_86_safe
def s8_250 : State := ⟨[21,4,125,145], 44601873214744552432934045751910889641148694, 1, 1, 1, 0⟩
theorem s8_250_edges : next config 8 s8_250 = [] := by decide
theorem s8_250_safe : Safe 5 8 s8_250 := by
  apply safe_succ 4 8 s8_250 [] (by decide) s8_250_edges
  simp
def s8_251 : State := ⟨[21,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546910, 1, 1, 1, 0⟩
theorem s8_251_edges : next config 8 s8_251 = [] := by decide
theorem s8_251_safe : Safe 5 8 s8_251 := by
  apply safe_succ 4 8 s8_251 [] (by decide) s8_251_edges
  simp
def s8_252 : State := ⟨[21,4,249,145], 904625697166532776746648320380418881934351203729176207679457272982822650134, 1, 1, 1, 0⟩
theorem s8_252_edges : next config 8 s8_252 = [] := by decide
theorem s8_252_safe : Safe 5 8 s8_252 := by
  apply safe_succ 4 8 s8_252 [] (by decide) s8_252_edges
  simp
def s8_253 : State := ⟨[21,12,104,145], 44601830679448528859301084301409773582225694, 3, 1, 1, 0⟩
theorem s8_253_edges : next config 8 s8_253 = [s9_173, s9_73, s9_85] := by decide
theorem s8_253_safe : Safe 5 8 s8_253 := by
  apply safe_succ 4 8 s8_253 [s9_173, s9_73, s9_85] (by decide) s8_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_173_safe
  · subst z; exact s9_73_safe
  · subst z; exact s9_85_safe
def s8_254 : State := ⟨[21,12,104,145], 44601830679448528859301084301409782172160278, 3, 1, 1, 0⟩
theorem s8_254_edges : next config 8 s8_254 = [s9_74] := by decide
theorem s8_254_safe : Safe 5 8 s8_254 := by
  apply safe_succ 4 8 s8_254 [s9_74] (by decide) s8_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_74_safe
def s8_255 : State := ⟨[21,12,104,145], 44601830679448528859301121194897921001328918, 3, 1, 1, 0⟩
theorem s8_255_edges : next config 8 s8_255 = [s9_174, s9_75, s9_86] := by decide
theorem s8_255_safe : Safe 5 8 s8_255 := by
  apply safe_succ 4 8 s8_255 [s9_174, s9_75, s9_86] (by decide) s8_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_174_safe
  · subst z; exact s9_75_safe
  · subst z; exact s9_86_safe
def s8_256 : State := ⟨[21,12,104,145], 44601830679448687315626112830084960670126358, 3, 1, 1, 0⟩
theorem s8_256_edges : next config 8 s8_256 = [s9_76] := by decide
theorem s8_256_safe : Safe 5 8 s8_256 := by
  apply safe_succ 4 8 s8_256 [s9_76] (by decide) s8_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_76_safe
def s8_257 : State := ⟨[21,12,113,145], 44601830689812840166767087888046818989379870, 3, 1, 1, 0⟩
theorem s8_257_edges : next config 8 s8_257 = [s9_81] := by decide
theorem s8_257_safe : Safe 5 8 s8_257 := by
  apply safe_succ 4 8 s8_257 [s9_81] (by decide) s8_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_81_safe
def s8_258 : State := ⟨[21,12,113,145], 44601830689812840166767124781534966408483094, 3, 1, 1, 0⟩
theorem s8_258_edges : next config 8 s8_258 = [s9_82] := by decide
theorem s8_258_safe : Safe 5 8 s8_258 := by
  apply safe_succ 4 8 s8_258 [s9_82] (by decide) s8_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_82_safe
def s8_259 : State := ⟨[21,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179230, 3, 1, 1, 0⟩
theorem s8_259_edges : next config 8 s8_259 = [s9_83] := by decide
theorem s8_259_safe : Safe 5 8 s8_259 := by
  apply safe_succ 4 8 s8_259 [s9_83] (by decide) s8_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_83_safe
def s8_260 : State := ⟨[21,12,241,145], 3533694129556768659166595001530438862334396040200935385767686376335282454, 3, 1, 1, 0⟩
theorem s8_260_edges : next config 8 s8_260 = [s9_84] := by decide
theorem s8_260_safe : Safe 5 8 s8_260 := by
  apply safe_succ 4 8 s8_260 [s9_84] (by decide) s8_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_84_safe
def s8_261 : State := ⟨[21,100,104,145], 44601830679449796509901312530811270285426974, 3, 1, 1, 0⟩
theorem s8_261_edges : next config 8 s8_261 = [] := by decide
theorem s8_261_safe : Safe 5 8 s8_261 := by
  apply safe_succ 4 8 s8_261 [] (by decide) s8_261_edges
  simp
def s8_262 : State := ⟨[21,100,104,145], 44601830679449796509901349424299417704530198, 3, 1, 1, 0⟩
theorem s8_262_edges : next config 8 s8_262 = [] := by decide
theorem s8_262_safe : Safe 5 8 s8_262 := by
  apply safe_succ 4 8 s8_262 [] (by decide) s8_262_edges
  simp
def s8_263 : State := ⟨[21,108,104,145], 44601830679773047412959511028192929602797854, 3, 1, 1, 0⟩
theorem s8_263_edges : next config 8 s8_263 = [s9_79] := by decide
theorem s8_263_safe : Safe 5 8 s8_263 := by
  apply safe_succ 4 8 s8_263 [s9_79] (by decide) s8_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_79_safe
def s8_264 : State := ⟨[21,108,104,145], 44601830679773047412959547921681077021901078, 3, 1, 1, 0⟩
theorem s8_264_edges : next config 8 s8_264 = [s9_80] := by decide
theorem s8_264_safe : Safe 5 8 s8_264 := by
  apply safe_succ 4 8 s8_264 [s9_80] (by decide) s8_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_80_safe
def s8_265 : State := ⟨[22,21,104,145], 44601830679448528859301084301409773586415902, 3, 1, 1, 0⟩
theorem s8_265_edges : next config 8 s8_265 = [] := by decide
theorem s8_265_safe : Safe 5 8 s8_265 := by
  apply safe_succ 4 8 s8_265 [] (by decide) s8_265_edges
  simp
def s8_266 : State := ⟨[25,4,67,145], 44601830679428167221535065940600822496952606, 3, 3, 1, 0⟩
theorem s8_266_edges : next config 8 s8_266 = [] := by decide
theorem s8_266_safe : Safe 5 8 s8_266 := by
  apply safe_succ 4 8 s8_266 [] (by decide) s8_266_edges
  simp
def s8_267 : State := ⟨[25,4,96,145], 44601830679428246449697432630985826364490014, 3, 3, 1, 0⟩
theorem s8_267_edges : next config 8 s8_267 = [s9_87] := by decide
theorem s8_267_safe : Safe 5 8 s8_267 := by
  apply safe_succ 4 8 s8_267 [s9_87] (by decide) s8_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_87_safe
def s8_268 : State := ⟨[25,4,96,145], 44601830679428246449697469524473973783593238, 3, 3, 1, 0⟩
theorem s8_268_edges : next config 8 s8_268 = [s9_88] := by decide
theorem s8_268_safe : Safe 5 8 s8_268 := by
  apply safe_succ 4 8 s8_268 [s9_88] (by decide) s8_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_88_safe
def s8_269 : State := ⟨[25,21,104,145], 44601830679448528859301084301409773615776030, 3, 1, 1, 0⟩
theorem s8_269_edges : next config 8 s8_269 = [] := by decide
theorem s8_269_safe : Safe 5 8 s8_269 := by
  apply safe_succ 4 8 s8_269 [] (by decide) s8_269_edges
  simp
def s8_270 : State := ⟨[25,21,104,145], 44601830679448528859301121194897921034879254, 3, 1, 1, 0⟩
theorem s8_270_edges : next config 8 s8_270 = [] := by decide
theorem s8_270_safe : Safe 5 8 s8_270 := by
  apply safe_succ 4 8 s8_270 [] (by decide) s8_270_edges
  simp
def s8_271 : State := ⟨[29,4,104,145], 44601830679448528859301084301409774119092510, 1, 1, 1, 0⟩
theorem s8_271_edges : next config 8 s8_271 = [] := by decide
theorem s8_271_safe : Safe 5 8 s8_271 := by
  apply safe_succ 4 8 s8_271 [] (by decide) s8_271_edges
  simp
def s8_272 : State := ⟨[29,4,104,145], 44601830679448528859301084301409782709027094, 1, 1, 1, 0⟩
theorem s8_272_edges : next config 8 s8_272 = [] := by decide
theorem s8_272_safe : Safe 5 8 s8_272 := by
  apply safe_succ 4 8 s8_272 [] (by decide) s8_272_edges
  simp
def s8_273 : State := ⟨[29,4,104,145], 44601830679448528859301121194897921538195734, 1, 1, 1, 0⟩
theorem s8_273_edges : next config 8 s8_273 = [] := by decide
theorem s8_273_safe : Safe 5 8 s8_273 := by
  apply safe_succ 4 8 s8_273 [] (by decide) s8_273_edges
  simp
def s8_274 : State := ⟨[33,4,104,145], 44601830679448528859301084301409782170063126, 3, 3, 1, 0⟩
theorem s8_274_edges : next config 8 s8_274 = [s9_98] := by decide
theorem s8_274_safe : Safe 5 8 s8_274 := by
  apply safe_succ 4 8 s8_274 [s9_98] (by decide) s8_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_98_safe
def s8_275 : State := ⟨[33,4,104,145], 44601830679448528859301084301409782172156182, 3, 3, 1, 0⟩
theorem s8_275_edges : next config 8 s8_275 = [s9_99, s9_90] := by decide
theorem s8_275_safe : Safe 5 8 s8_275 := by
  apply safe_succ 4 8 s8_275 [s9_99, s9_90] (by decide) s8_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_99_safe
  · subst z; exact s9_90_safe
def s8_276 : State := ⟨[33,12,96,145], 44601830679428246449697432630985834920874262, 3, 3, 1, 0⟩
theorem s8_276_edges : next config 8 s8_276 = [s9_102, s9_90] := by decide
theorem s8_276_safe : Safe 5 8 s8_276 := by
  apply safe_succ 4 8 s8_276 [s9_102, s9_90] (by decide) s8_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_102_safe
  · subst z; exact s9_90_safe
def s8_277 : State := ⟨[33,21,96,145], 44601830679428246449697432630985834920874262, 3, 3, 1, 0⟩
theorem s8_277_edges : next config 8 s8_277 = [s9_105, s9_91] := by decide
theorem s8_277_safe : Safe 5 8 s8_277 := by
  apply safe_succ 4 8 s8_277 [s9_105, s9_91] (by decide) s8_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_105_safe
  · subst z; exact s9_91_safe
def s8_278 : State := ⟨[33,21,125,145], 44601873214744393976609017223235711143182614, 3, 1, 1, 0⟩
theorem s8_278_edges : next config 8 s8_278 = [] := by decide
theorem s8_278_safe : Safe 5 8 s8_278 := by
  apply safe_succ 4 8 s8_278 [] (by decide) s8_278_edges
  simp
def s8_279 : State := ⟨[33,29,104,145], 44601830679448528859301084301409782709027094, 3, 1, 1, 0⟩
theorem s8_279_edges : next config 8 s8_279 = [] := by decide
theorem s8_279_safe : Safe 5 8 s8_279 := by
  apply safe_succ 4 8 s8_279 [] (by decide) s8_279_edges
  simp
def s8_280 : State := ⟨[33,125,104,145], 44601873214744393976609017223235711143182614, 3, 1, 1, 0⟩
theorem s8_280_edges : next config 8 s8_280 = [] := by decide
theorem s8_280_safe : Safe 5 8 s8_280 := by
  apply safe_succ 4 8 s8_280 [] (by decide) s8_280_edges
  simp
def s8_281 : State := ⟨[35,4,67,145], 44601830679428167221535065940600856821043486, 3, 3, 1, 0⟩
theorem s8_281_edges : next config 8 s8_281 = [s9_151] := by decide
theorem s8_281_safe : Safe 5 8 s8_281 := by
  apply safe_succ 4 8 s8_281 [s9_151] (by decide) s8_281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_151_safe
def s8_282 : State := ⟨[35,4,67,145], 44601830679428167221535065940600856823136542, 3, 3, 1, 0⟩
theorem s8_282_edges : next config 8 s8_282 = [s9_152, s9_118, s9_100] := by decide
theorem s8_282_safe : Safe 5 8 s8_282 := by
  apply safe_succ 4 8 s8_282 [s9_152, s9_118, s9_100] (by decide) s8_282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_152_safe
  · subst z; exact s9_118_safe
  · subst z; exact s9_100_safe
def s8_283 : State := ⟨[35,4,67,145], 44602511244162088326624506954153313901285662, 3, 2, 1, 0⟩
theorem s8_283_edges : next config 8 s8_283 = [] := by decide
theorem s8_283_safe : Safe 5 8 s8_283 := by
  apply safe_succ 4 8 s8_283 [] (by decide) s8_283_edges
  simp
def s8_284 : State := ⟨[35,4,67,145], 44602511244162088326624506954153322491220246, 3, 2, 1, 0⟩
theorem s8_284_edges : next config 8 s8_284 = [] := by decide
theorem s8_284_safe : Safe 5 8 s8_284 := by
  apply safe_succ 4 8 s8_284 [] (by decide) s8_284_edges
  simp
def s8_285 : State := ⟨[35,4,67,145], 66902575877958869591233298477586811870843166, 3, 2, 1, 0⟩
theorem s8_285_edges : next config 8 s8_285 = [] := by decide
theorem s8_285_safe : Safe 5 8 s8_285 := by
  apply safe_succ 4 8 s8_285 [] (by decide) s8_285_edges
  simp
def s8_286 : State := ⟨[35,4,67,145], 66902575877958869591233298477586820460777750, 3, 2, 1, 0⟩
theorem s8_286_edges : next config 8 s8_286 = [] := by decide
theorem s8_286_safe : Safe 5 8 s8_286 := by
  apply safe_succ 4 8 s8_286 [] (by decide) s8_286_edges
  simp
def s8_287 : State := ⟨[35,4,96,145], 44601830679428246449697432630985860688580894, 3, 3, 1, 0⟩
theorem s8_287_edges : next config 8 s8_287 = [s9_92, s9_96] := by decide
theorem s8_287_safe : Safe 5 8 s8_287 := by
  apply safe_succ 4 8 s8_287 [s9_92, s9_96] (by decide) s8_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_92_safe
  · subst z; exact s9_96_safe
def s8_288 : State := ⟨[35,4,96,145], 44601830679428246449697432630985860690673950, 3, 3, 1, 0⟩
theorem s8_288_edges : next config 8 s8_288 = [s9_121, s9_101, s9_93, s9_97] := by decide
theorem s8_288_safe : Safe 5 8 s8_288 := by
  apply safe_succ 4 8 s8_288 [s9_121, s9_101, s9_93, s9_97] (by decide) s8_288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s9_121_safe
  · subst z; exact s9_101_safe
  · subst z; exact s9_93_safe
  · subst z; exact s9_97_safe
def s8_289 : State := ⟨[35,4,96,145], 44601830679428246449697432630985869278515478, 3, 3, 1, 0⟩
theorem s8_289_edges : next config 8 s8_289 = [s9_94, s9_98] := by decide
theorem s8_289_safe : Safe 5 8 s8_289 := by
  apply safe_succ 4 8 s8_289 [s9_94, s9_98] (by decide) s8_289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_94_safe
  · subst z; exact s9_98_safe
def s8_290 : State := ⟨[35,4,96,145], 44601830679428246449697432630985869280608534, 3, 3, 1, 0⟩
theorem s8_290_edges : next config 8 s8_290 = [s9_122, s9_102, s9_95, s9_99] := by decide
theorem s8_290_safe : Safe 5 8 s8_290 := by
  apply safe_succ 4 8 s8_290 [s9_122, s9_102, s9_95, s9_99] (by decide) s8_290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s9_122_safe
  · subst z; exact s9_102_safe
  · subst z; exact s9_95_safe
  · subst z; exact s9_99_safe
def s8_291 : State := ⟨[35,4,104,145], 44602511244182370736228011050624671476158750, 3, 2, 1, 0⟩
theorem s8_291_edges : next config 8 s8_291 = [] := by decide
theorem s8_291_safe : Safe 5 8 s8_291 := by
  apply safe_succ 4 8 s8_291 [] (by decide) s8_291_edges
  simp
def s8_292 : State := ⟨[35,4,104,145], 44602511244182370736228011050624680066093334, 3, 2, 1, 0⟩
theorem s8_292_edges : next config 8 s8_292 = [] := by decide
theorem s8_292_safe : Safe 5 8 s8_292 := by
  apply safe_succ 4 8 s8_292 [] (by decide) s8_292_edges
  simp
def s8_293 : State := ⟨[35,4,104,145], 66902575877979152000836802574058169445716254, 3, 2, 1, 0⟩
theorem s8_293_edges : next config 8 s8_293 = [] := by decide
theorem s8_293_safe : Safe 5 8 s8_293 := by
  apply safe_succ 4 8 s8_293 [] (by decide) s8_293_edges
  simp
def s8_294 : State := ⟨[35,4,104,145], 66902575877979152000836802574058178035650838, 3, 2, 1, 0⟩
theorem s8_294_edges : next config 8 s8_294 = [] := by decide
theorem s8_294_safe : Safe 5 8 s8_294 := by
  apply safe_succ 4 8 s8_294 [] (by decide) s8_294_edges
  simp
def s8_295 : State := ⟨[35,12,64,145], 44601830679428167221534918366648267146727710, 3, 3, 1, 0⟩
theorem s8_295_edges : next config 8 s8_295 = [s9_101] := by decide
theorem s8_295_safe : Safe 5 8 s8_295 := by
  apply safe_succ 4 8 s8_295 [s9_101] (by decide) s8_295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_101_safe
def s8_296 : State := ⟨[35,12,64,145], 44601830679428167221534918366648275736662294, 3, 3, 1, 0⟩
theorem s8_296_edges : next config 8 s8_296 = [s9_102] := by decide
theorem s8_296_safe : Safe 5 8 s8_296 := by
  apply safe_succ 4 8 s8_296 [s9_102] (by decide) s8_296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_102_safe
def s8_297 : State := ⟨[35,12,67,145], 44601830679428246449697580204938450364993822, 3, 1, 1, 0⟩
theorem s8_297_edges : next config 8 s8_297 = [s9_92] := by decide
theorem s8_297_safe : Safe 5 8 s8_297 := by
  apply safe_succ 4 8 s8_297 [s9_92] (by decide) s8_297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_92_safe
def s8_298 : State := ⟨[35,12,67,145], 44601830679428246449697580204938458954928406, 3, 1, 1, 0⟩
theorem s8_298_edges : next config 8 s8_298 = [s9_94] := by decide
theorem s8_298_safe : Safe 5 8 s8_298 := by
  apply safe_succ 4 8 s8_298 [s9_94] (by decide) s8_298_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_94_safe
def s8_299 : State := ⟨[35,12,104,145], 44601830679448528859301084301409807939866910, 3, 1, 1, 0⟩
theorem s8_299_edges : next config 8 s8_299 = [s9_96] := by decide
theorem s8_299_safe : Safe 5 8 s8_299 := by
  apply safe_succ 4 8 s8_299 [s9_96] (by decide) s8_299_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_96_safe
def s8_300 : State := ⟨[35,12,104,145], 44601830679448528859301084301409816529801494, 3, 1, 1, 0⟩
theorem s8_300_edges : next config 8 s8_300 = [s9_98] := by decide
theorem s8_300_safe : Safe 5 8 s8_300 := by
  apply safe_succ 4 8 s8_300 [s9_98] (by decide) s8_300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_98_safe
def s8_301 : State := ⟨[35,21,64,145], 44601830679428167221534918366648267146727710, 3, 3, 1, 0⟩
theorem s8_301_edges : next config 8 s8_301 = [s9_104] := by decide
theorem s8_301_safe : Safe 5 8 s8_301 := by
  apply safe_succ 4 8 s8_301 [s9_104] (by decide) s8_301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_104_safe
def s8_302 : State := ⟨[35,21,64,145], 44601830679428167221534918366648275736662294, 3, 3, 1, 0⟩
theorem s8_302_edges : next config 8 s8_302 = [s9_105] := by decide
theorem s8_302_safe : Safe 5 8 s8_302 := by
  apply safe_succ 4 8 s8_302 [s9_105] (by decide) s8_302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_105_safe
def s8_303 : State := ⟨[35,21,67,145], 44601830679428246449697580204938450367086878, 3, 1, 1, 0⟩
theorem s8_303_edges : next config 8 s8_303 = [s9_133, s9_123, s9_108, s9_116, s9_106] := by decide
theorem s8_303_safe : Safe 5 8 s8_303 := by
  apply safe_succ 4 8 s8_303 [s9_133, s9_123, s9_108, s9_116, s9_106] (by decide) s8_303_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s9_133_safe
  · subst z; exact s9_123_safe
  · subst z; exact s9_108_safe
  · subst z; exact s9_116_safe
  · subst z; exact s9_106_safe
def s8_304 : State := ⟨[35,21,67,145], 44601830679428246449697580204938458957021462, 3, 1, 1, 0⟩
theorem s8_304_edges : next config 8 s8_304 = [s9_134, s9_124, s9_109, s9_117, s9_107] := by decide
theorem s8_304_safe : Safe 5 8 s8_304 := by
  apply safe_succ 4 8 s8_304 [s9_134, s9_124, s9_109, s9_117, s9_107] (by decide) s8_304_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s9_134_safe
  · subst z; exact s9_124_safe
  · subst z; exact s9_109_safe
  · subst z; exact s9_117_safe
  · subst z; exact s9_107_safe
def s8_305 : State := ⟨[35,21,104,145], 44601830679448528859301084301409807941959966, 3, 1, 1, 0⟩
theorem s8_305_edges : next config 8 s8_305 = [s9_125] := by decide
theorem s8_305_safe : Safe 5 8 s8_305 := by
  apply safe_succ 4 8 s8_305 [s9_125] (by decide) s8_305_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_125_safe
def s8_306 : State := ⟨[35,21,104,145], 44601830679448528859301084301409816531894550, 3, 1, 1, 0⟩
theorem s8_306_edges : next config 8 s8_306 = [s9_126] := by decide
theorem s8_306_safe : Safe 5 8 s8_306 := by
  apply safe_succ 4 8 s8_306 [s9_126] (by decide) s8_306_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_126_safe
def s8_307 : State := ⟨[35,29,67,145], 44601830679428167221535065940600857360007454, 3, 1, 1, 0⟩
theorem s8_307_edges : next config 8 s8_307 = [s9_138, s9_154, s9_110] := by decide
theorem s8_307_safe : Safe 5 8 s8_307 := by
  apply safe_succ 4 8 s8_307 [s9_138, s9_154, s9_110] (by decide) s8_307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_138_safe
  · subst z; exact s9_154_safe
  · subst z; exact s9_110_safe
def s8_308 : State := ⟨[35,29,96,145], 44601830679428246449697432630985861227544862, 3, 1, 1, 0⟩
theorem s8_308_edges : next config 8 s8_308 = [s9_112, s9_106] := by decide
theorem s8_308_safe : Safe 5 8 s8_308 := by
  apply safe_succ 4 8 s8_308 [s9_112, s9_106] (by decide) s8_308_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_112_safe
  · subst z; exact s9_106_safe
def s8_309 : State := ⟨[35,29,96,145], 44601830679428246449697432630985869817479446, 3, 1, 1, 0⟩
theorem s8_309_edges : next config 8 s8_309 = [s9_113, s9_107] := by decide
theorem s8_309_safe : Safe 5 8 s8_309 := by
  apply safe_succ 4 8 s8_309 [s9_113, s9_107] (by decide) s8_309_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_113_safe
  · subst z; exact s9_107_safe
def s8_310 : State := ⟨[35,54,67,145], 44601830679428167221535065958615255332618526, 3, 1, 1, 0⟩
theorem s8_310_edges : next config 8 s8_310 = [s9_155, s9_111] := by decide
theorem s8_310_safe : Safe 5 8 s8_310 := by
  apply safe_succ 4 8 s8_310 [s9_155, s9_111] (by decide) s8_310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_155_safe
  · subst z; exact s9_111_safe
def s8_311 : State := ⟨[35,54,96,145], 44601830679428246449697432649000259200155934, 3, 1, 1, 0⟩
theorem s8_311_edges : next config 8 s8_311 = [s9_114, s9_108] := by decide
theorem s8_311_safe : Safe 5 8 s8_311 := by
  apply safe_succ 4 8 s8_311 [s9_114, s9_108] (by decide) s8_311_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_114_safe
  · subst z; exact s9_108_safe
def s8_312 : State := ⟨[35,54,96,145], 44601830679428246449697432649000267790090518, 3, 1, 1, 0⟩
theorem s8_312_edges : next config 8 s8_312 = [s9_115, s9_109] := by decide
theorem s8_312_safe : Safe 5 8 s8_312 := by
  apply safe_succ 4 8 s8_312 [s9_115, s9_109] (by decide) s8_312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_115_safe
  · subst z; exact s9_109_safe
def s8_313 : State := ⟨[35,62,64,145], 44601830679428167221534922978334286110982430, 3, 1, 1, 0⟩
theorem s8_313_edges : next config 8 s8_313 = [s9_112] := by decide
theorem s8_313_safe : Safe 5 8 s8_313 := by
  apply safe_succ 4 8 s8_313 [s9_112] (by decide) s8_313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_112_safe
def s8_314 : State := ⟨[35,62,64,145], 44601830679428167221534922978334294700917014, 3, 1, 1, 0⟩
theorem s8_314_edges : next config 8 s8_314 = [s9_113] := by decide
theorem s8_314_safe : Safe 5 8 s8_314 := by
  apply safe_succ 4 8 s8_314 [s9_113] (by decide) s8_314_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_113_safe
def s8_315 : State := ⟨[35,62,64,145], 44601830679428167221534922996348684083593502, 3, 1, 1, 0⟩
theorem s8_315_edges : next config 8 s8_315 = [s9_114] := by decide
theorem s8_315_safe : Safe 5 8 s8_315 := by
  apply safe_succ 4 8 s8_315 [s9_114] (by decide) s8_315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_114_safe
def s8_316 : State := ⟨[35,62,64,145], 44601830679428167221534922996348692673528086, 3, 1, 1, 0⟩
theorem s8_316_edges : next config 8 s8_316 = [s9_115] := by decide
theorem s8_316_safe : Safe 5 8 s8_316 := by
  apply safe_succ 4 8 s8_316 [s9_115] (by decide) s8_316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_115_safe
def s8_317 : State := ⟨[35,86,67,145], 44601830679428167298906318395937124004331806, 3, 1, 1, 0⟩
theorem s8_317_edges : next config 8 s8_317 = [s9_156] := by decide
theorem s8_317_safe : Safe 5 8 s8_317 := by
  apply safe_succ 4 8 s8_317 [s9_156] (by decide) s8_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_156_safe
def s8_318 : State := ⟨[43,4,64,145], 44601830679428167221534918366657063239745822, 3, 3, 1, 0⟩
theorem s8_318_edges : next config 8 s8_318 = [s9_121] := by decide
theorem s8_318_safe : Safe 5 8 s8_318 := by
  apply safe_succ 4 8 s8_318 [s9_121] (by decide) s8_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_121_safe
def s8_319 : State := ⟨[43,4,64,145], 44601830679428167221534918366657071829680406, 3, 3, 1, 0⟩
theorem s8_319_edges : next config 8 s8_319 = [s9_122] := by decide
theorem s8_319_safe : Safe 5 8 s8_319 := by
  apply safe_succ 4 8 s8_319 [s9_122] (by decide) s8_319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_122_safe
def s8_320 : State := ⟨[43,4,67,145], 44601830679428246449697580204947246458011934, 1, 1, 1, 0⟩
theorem s8_320_edges : next config 8 s8_320 = [s9_158] := by decide
theorem s8_320_safe : Safe 5 8 s8_320 := by
  apply safe_succ 4 8 s8_320 [s9_158] (by decide) s8_320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_158_safe
def s8_321 : State := ⟨[43,4,67,145], 44601830679428246449697580204947255047946518, 1, 1, 1, 0⟩
theorem s8_321_edges : next config 8 s8_321 = [s9_159] := by decide
theorem s8_321_safe : Safe 5 8 s8_321 := by
  apply safe_succ 4 8 s8_321 [s9_159] (by decide) s8_321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_159_safe
def s8_322 : State := ⟨[43,4,67,145], 44602511244182370736228158624586057245589790, 1, 0, 1, 0⟩
theorem s8_322_edges : next config 8 s8_322 = [] := by decide
theorem s8_322_safe : Safe 5 8 s8_322 := by
  apply safe_succ 4 8 s8_322 [] (by decide) s8_322_edges
  simp
def s8_323 : State := ⟨[43,4,67,145], 44602511244182370736228158624586065835524374, 1, 0, 1, 0⟩
theorem s8_323_edges : next config 8 s8_323 = [] := by decide
theorem s8_323_safe : Safe 5 8 s8_323 := by
  apply safe_succ 4 8 s8_323 [] (by decide) s8_323_edges
  simp
def s8_324 : State := ⟨[43,4,67,145], 66902575877979152000836950148019555215147294, 1, 0, 1, 0⟩
theorem s8_324_edges : next config 8 s8_324 = [] := by decide
theorem s8_324_safe : Safe 5 8 s8_324 := by
  apply safe_succ 4 8 s8_324 [] (by decide) s8_324_edges
  simp
def s8_325 : State := ⟨[43,4,67,145], 66902575877979152000836950148019563805081878, 1, 0, 1, 0⟩
theorem s8_325_edges : next config 8 s8_325 = [] := by decide
theorem s8_325_safe : Safe 5 8 s8_325 := by
  apply safe_succ 4 8 s8_325 [] (by decide) s8_325_edges
  simp
def s8_326 : State := ⟨[43,4,104,145], 44601830679448528859301084301418604032885022, 1, 1, 1, 0⟩
theorem s8_326_edges : next config 8 s8_326 = [s9_119] := by decide
theorem s8_326_safe : Safe 5 8 s8_326 := by
  apply safe_succ 4 8 s8_326 [s9_119] (by decide) s8_326_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_119_safe
def s8_327 : State := ⟨[43,4,104,145], 44601830679448528859301084301418612622819606, 1, 1, 1, 0⟩
theorem s8_327_edges : next config 8 s8_327 = [s9_120] := by decide
theorem s8_327_safe : Safe 5 8 s8_327 := by
  apply safe_succ 4 8 s8_327 [s9_120] (by decide) s8_327_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_120_safe
def s8_328 : State := ⟨[43,21,67,145], 44601830679428167221535065940609652916158750, 3, 1, 1, 0⟩
theorem s8_328_edges : next config 8 s8_328 = [s9_135, s9_163, s9_127] := by decide
theorem s8_328_safe : Safe 5 8 s8_328 := by
  apply safe_succ 4 8 s8_328 [s9_135, s9_163, s9_127] (by decide) s8_328_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_135_safe
  · subst z; exact s9_163_safe
  · subst z; exact s9_127_safe
def s8_329 : State := ⟨[43,21,96,145], 44601830679428246449697432630994656783696158, 3, 1, 1, 0⟩
theorem s8_329_edges : next config 8 s8_329 = [s9_125] := by decide
theorem s8_329_safe : Safe 5 8 s8_329 := by
  apply safe_succ 4 8 s8_329 [s9_125] (by decide) s8_329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_125_safe
def s8_330 : State := ⟨[43,21,96,145], 44601830679428246449697432630994665373630742, 3, 1, 1, 0⟩
theorem s8_330_edges : next config 8 s8_330 = [s9_126] := by decide
theorem s8_330_safe : Safe 5 8 s8_330 := by
  apply safe_succ 4 8 s8_330 [s9_126] (by decide) s8_330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_126_safe
def s8_331 : State := ⟨[43,62,64,145], 44601830679428167221534922978343081667133726, 3, 1, 1, 0⟩
theorem s8_331_edges : next config 8 s8_331 = [] := by decide
theorem s8_331_safe : Safe 5 8 s8_331 := by
  apply safe_succ 4 8 s8_331 [] (by decide) s8_331_edges
  simp
def s8_332 : State := ⟨[43,62,64,145], 44601830679428167221534922978343090257068310, 3, 1, 1, 0⟩
theorem s8_332_edges : next config 8 s8_332 = [] := by decide
theorem s8_332_safe : Safe 5 8 s8_332 := by
  apply safe_succ 4 8 s8_332 [] (by decide) s8_332_edges
  simp
def s8_333 : State := ⟨[49,4,67,145], 44601830679428167221535065941163772414726430, 3, 3, 1, 0⟩
theorem s8_333_edges : next config 8 s8_333 = [] := by decide
theorem s8_333_safe : Safe 5 8 s8_333 := by
  apply safe_succ 4 8 s8_333 [] (by decide) s8_333_edges
  simp
def s8_334 : State := ⟨[49,4,67,145], 44601830679428167221535065941163772416819486, 3, 3, 1, 0⟩
theorem s8_334_edges : next config 8 s8_334 = [s9_130] := by decide
theorem s8_334_safe : Safe 5 8 s8_334 := by
  apply safe_succ 4 8 s8_334 [s9_130] (by decide) s8_334_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_130_safe
def s8_335 : State := ⟨[49,4,96,145], 44601830679428246449697432631548776282263838, 3, 3, 1, 0⟩
theorem s8_335_edges : next config 8 s8_335 = [s9_128] := by decide
theorem s8_335_safe : Safe 5 8 s8_335 := by
  apply safe_succ 4 8 s8_335 [s9_128] (by decide) s8_335_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_128_safe
def s8_336 : State := ⟨[49,4,96,145], 44601830679428246449697432631548776284356894, 3, 3, 1, 0⟩
theorem s8_336_edges : next config 8 s8_336 = [s9_131, s9_129] := by decide
theorem s8_336_safe : Safe 5 8 s8_336 := by
  apply safe_succ 4 8 s8_336 [s9_131, s9_129] (by decide) s8_336_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_131_safe
  · subst z; exact s9_129_safe
def s8_337 : State := ⟨[49,4,125,145], 44601873214744393976609017223798652506669334, 3, 2, 1, 0⟩
theorem s8_337_edges : next config 8 s8_337 = [] := by decide
theorem s8_337_safe : Safe 5 8 s8_337 := by
  apply safe_succ 4 8 s8_337 [] (by decide) s8_337_edges
  simp
def s8_338 : State := ⟨[49,12,64,145], 44601830679428167221534918367211182740410654, 3, 3, 1, 0⟩
theorem s8_338_edges : next config 8 s8_338 = [s9_131] := by decide
theorem s8_338_safe : Safe 5 8 s8_338 := by
  apply safe_succ 4 8 s8_338 [s9_131] (by decide) s8_338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_131_safe
def s8_339 : State := ⟨[49,12,104,145], 44601830679448528859301084301972723533549854, 3, 1, 1, 0⟩
theorem s8_339_edges : next config 8 s8_339 = [s9_128] := by decide
theorem s8_339_safe : Safe 5 8 s8_339 := by
  apply safe_succ 4 8 s8_339 [s9_128] (by decide) s8_339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_128_safe
def s8_340 : State := ⟨[49,12,104,145], 44601830679448528859301084301972723535646998, 3, 2, 1, 0⟩
theorem s8_340_edges : next config 8 s8_340 = [] := by decide
theorem s8_340_safe : Safe 5 8 s8_340 := by
  apply safe_succ 4 8 s8_340 [] (by decide) s8_340_edges
  simp
def s8_341 : State := ⟨[49,21,64,145], 44601830679428167221534918367211182740410654, 3, 3, 1, 0⟩
theorem s8_341_edges : next config 8 s8_341 = [] := by decide
theorem s8_341_safe : Safe 5 8 s8_341 := by
  apply safe_succ 4 8 s8_341 [] (by decide) s8_341_edges
  simp
def s8_342 : State := ⟨[49,21,104,145], 44601830679448528859301084301972723535642910, 3, 1, 1, 0⟩
theorem s8_342_edges : next config 8 s8_342 = [] := by decide
theorem s8_342_safe : Safe 5 8 s8_342 := by
  apply safe_succ 4 8 s8_342 [] (by decide) s8_342_edges
  simp
def s8_343 : State := ⟨[49,21,104,145], 44601830679448528859301084301972723535646998, 3, 2, 1, 0⟩
theorem s8_343_edges : next config 8 s8_343 = [] := by decide
theorem s8_343_safe : Safe 5 8 s8_343 := by
  apply safe_succ 4 8 s8_343 [] (by decide) s8_343_edges
  simp
def s8_344 : State := ⟨[49,86,67,145], 44601830679428167298906318396500039598014750, 3, 1, 1, 0⟩
theorem s8_344_edges : next config 8 s8_344 = [] := by decide
theorem s8_344_safe : Safe 5 8 s8_344 := by
  apply safe_succ 4 8 s8_344 [] (by decide) s8_344_edges
  simp
def s8_345 : State := ⟨[53,4,104,145], 44601830679448528859301084310416972836962590, 1, 1, 1, 0⟩
theorem s8_345_edges : next config 8 s8_345 = [] := by decide
theorem s8_345_safe : Safe 5 8 s8_345 := by
  apply safe_succ 4 8 s8_345 [] (by decide) s8_345_edges
  simp
def s8_346 : State := ⟨[54,21,67,145], 44601830679428167221535065958615220977074462, 3, 1, 1, 0⟩
theorem s8_346_edges : next config 8 s8_346 = [s9_136] := by decide
theorem s8_346_safe : Safe 5 8 s8_346 := by
  apply safe_succ 4 8 s8_346 [s9_136] (by decide) s8_346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_136_safe
def s8_347 : State := ⟨[54,21,67,145], 44601830679428167221535065958615255332618526, 3, 1, 1, 0⟩
theorem s8_347_edges : next config 8 s8_347 = [s9_137] := by decide
theorem s8_347_safe : Safe 5 8 s8_347 := by
  apply safe_succ 4 8 s8_347 [s9_137] (by decide) s8_347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_137_safe
def s8_348 : State := ⟨[54,21,96,145], 44601830679428246449697432649000224844611870, 3, 1, 1, 0⟩
theorem s8_348_edges : next config 8 s8_348 = [] := by decide
theorem s8_348_safe : Safe 5 8 s8_348 := by
  apply safe_succ 4 8 s8_348 [] (by decide) s8_348_edges
  simp
def s8_349 : State := ⟨[54,21,96,145], 44601830679428246449697432649000259200155934, 3, 1, 1, 0⟩
theorem s8_349_edges : next config 8 s8_349 = [] := by decide
theorem s8_349_safe : Safe 5 8 s8_349 := by
  apply safe_succ 4 8 s8_349 [] (by decide) s8_349_edges
  simp
def s8_350 : State := ⟨[54,21,96,145], 44601830679428246449697432649000267790090518, 3, 1, 1, 0⟩
theorem s8_350_edges : next config 8 s8_350 = [] := by decide
theorem s8_350_safe : Safe 5 8 s8_350 := by
  apply safe_succ 4 8 s8_350 [] (by decide) s8_350_edges
  simp
def s8_351 : State := ⟨[54,53,67,145], 44601830679428167221535065967622420227621150, 3, 1, 1, 0⟩
theorem s8_351_edges : next config 8 s8_351 = [s9_139] := by decide
theorem s8_351_safe : Safe 5 8 s8_351 := by
  apply safe_succ 4 8 s8_351 [s9_139] (by decide) s8_351_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_139_safe
def s8_352 : State := ⟨[54,53,96,145], 44601830679428246449697432658007424095158558, 3, 1, 1, 0⟩
theorem s8_352_edges : next config 8 s8_352 = [] := by decide
theorem s8_352_safe : Safe 5 8 s8_352 := by
  apply safe_succ 4 8 s8_352 [] (by decide) s8_352_edges
  simp
def s8_353 : State := ⟨[62,21,64,145], 44601830679428167221534922978343081667133726, 3, 1, 1, 0⟩
theorem s8_353_edges : next config 8 s8_353 = [] := by decide
theorem s8_353_safe : Safe 5 8 s8_353 := by
  apply safe_succ 4 8 s8_353 [] (by decide) s8_353_edges
  simp
def s8_354 : State := ⟨[62,21,64,145], 44601830679428167221534922978343090257068310, 3, 1, 1, 0⟩
theorem s8_354_edges : next config 8 s8_354 = [] := by decide
theorem s8_354_safe : Safe 5 8 s8_354 := by
  apply safe_succ 4 8 s8_354 [] (by decide) s8_354_edges
  simp
def s8_355 : State := ⟨[62,21,64,145], 44601830679428167221534922996348649728049438, 3, 1, 1, 0⟩
theorem s8_355_edges : next config 8 s8_355 = [] := by decide
theorem s8_355_safe : Safe 5 8 s8_355 := by
  apply safe_succ 4 8 s8_355 [] (by decide) s8_355_edges
  simp
def s8_356 : State := ⟨[62,21,64,145], 44601830679428167221534922996348684083593502, 3, 1, 1, 0⟩
theorem s8_356_edges : next config 8 s8_356 = [] := by decide
theorem s8_356_safe : Safe 5 8 s8_356 := by
  apply safe_succ 4 8 s8_356 [] (by decide) s8_356_edges
  simp
def s8_357 : State := ⟨[62,21,64,145], 44601830679428167221534922996348692673528086, 3, 1, 1, 0⟩
theorem s8_357_edges : next config 8 s8_357 = [] := by decide
theorem s8_357_safe : Safe 5 8 s8_357 := by
  apply safe_succ 4 8 s8_357 [] (by decide) s8_357_edges
  simp
def s8_358 : State := ⟨[62,29,64,145], 44601830679428167221534922978334286110982430, 3, 1, 1, 0⟩
theorem s8_358_edges : next config 8 s8_358 = [] := by decide
theorem s8_358_safe : Safe 5 8 s8_358 := by
  apply safe_succ 4 8 s8_358 [] (by decide) s8_358_edges
  simp
def s8_359 : State := ⟨[62,29,64,145], 44601830679428167221534922978334294700917014, 3, 1, 1, 0⟩
theorem s8_359_edges : next config 8 s8_359 = [] := by decide
theorem s8_359_safe : Safe 5 8 s8_359 := by
  apply safe_succ 4 8 s8_359 [] (by decide) s8_359_edges
  simp
def s8_360 : State := ⟨[62,53,64,145], 44601830679428167221534923005355848978596126, 3, 1, 1, 0⟩
theorem s8_360_edges : next config 8 s8_360 = [] := by decide
theorem s8_360_safe : Safe 5 8 s8_360 := by
  apply safe_succ 4 8 s8_360 [] (by decide) s8_360_edges
  simp
def s8_361 : State := ⟨[65,4,100,145], 44601830679429514100297697753875470453244182, 3, 3, 1, 0⟩
theorem s8_361_edges : next config 8 s8_361 = [] := by decide
theorem s8_361_safe : Safe 5 8 s8_361 := by
  apply safe_succ 4 8 s8_361 [] (by decide) s8_361_edges
  simp
def s8_362 : State := ⟨[65,4,104,145], 44601830679448528859301121194897920999231766, 3, 3, 1, 0⟩
theorem s8_362_edges : next config 8 s8_362 = [] := by decide
theorem s8_362_safe : Safe 5 8 s8_362 := by
  apply safe_succ 4 8 s8_362 [] (by decide) s8_362_edges
  simp
def s8_363 : State := ⟨[65,4,104,145], 44601830679448528859301121194897921001324822, 3, 3, 1, 0⟩
theorem s8_363_edges : next config 8 s8_363 = [s9_144, s9_142, s9_140, s9_141] := by decide
theorem s8_363_safe : Safe 5 8 s8_363 := by
  apply safe_succ 4 8 s8_363 [s9_144, s9_142, s9_140, s9_141] (by decide) s8_363_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s9_144_safe
  · subst z; exact s9_142_safe
  · subst z; exact s9_140_safe
  · subst z; exact s9_141_safe
def s8_364 : State := ⟨[65,4,104,145], 44601830679449796509901349424299417702433046, 3, 3, 1, 0⟩
theorem s8_364_edges : next config 8 s8_364 = [] := by decide
theorem s8_364_safe : Safe 5 8 s8_364 := by
  apply safe_succ 4 8 s8_364 [] (by decide) s8_364_edges
  simp
def s8_365 : State := ⟨[65,4,104,145], 44601830679773047412959547921681077019803926, 3, 3, 1, 0⟩
theorem s8_365_edges : next config 8 s8_365 = [] := by decide
theorem s8_365_safe : Safe 5 8 s8_365 := by
  apply safe_succ 4 8 s8_365 [] (by decide) s8_365_edges
  simp
def s8_366 : State := ⟨[65,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376333185302, 3, 3, 1, 0⟩
theorem s8_366_edges : next config 8 s8_366 = [] := by decide
theorem s8_366_safe : Safe 5 8 s8_366 := by
  apply safe_succ 4 8 s8_366 [] (by decide) s8_366_edges
  simp
def s8_367 : State := ⟨[65,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376335278358, 3, 3, 1, 0⟩
theorem s8_367_edges : next config 8 s8_367 = [s9_143] := by decide
theorem s8_367_safe : Safe 5 8 s8_367 := by
  apply safe_succ 4 8 s8_367 [s9_143] (by decide) s8_367_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_143_safe
def s8_368 : State := ⟨[65,12,96,145], 44601830679428246449697469524473973750042902, 3, 3, 1, 0⟩
theorem s8_368_edges : next config 8 s8_368 = [s9_143, s9_142] := by decide
theorem s8_368_safe : Safe 5 8 s8_368 := by
  apply safe_succ 4 8 s8_368 [s9_143, s9_142] (by decide) s8_368_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_143_safe
  · subst z; exact s9_142_safe
def s8_369 : State := ⟨[65,21,96,145], 44601830679428246449697469524473973750042902, 3, 3, 1, 0⟩
theorem s8_369_edges : next config 8 s8_369 = [] := by decide
theorem s8_369_safe : Safe 5 8 s8_369 := by
  apply safe_succ 4 8 s8_369 [] (by decide) s8_369_edges
  simp
def s8_370 : State := ⟨[65,21,125,145], 44601873214744393976609054116723849972351254, 3, 1, 1, 0⟩
theorem s8_370_edges : next config 8 s8_370 = [] := by decide
theorem s8_370_safe : Safe 5 8 s8_370 := by
  apply safe_succ 4 8 s8_370 [] (by decide) s8_370_edges
  simp
def s8_371 : State := ⟨[65,21,249,145], 904625697166532776746648320380418881934351203729176207679457272982822650134, 3, 1, 1, 0⟩
theorem s8_371_edges : next config 8 s8_371 = [] := by decide
theorem s8_371_safe : Safe 5 8 s8_371 := by
  apply safe_succ 4 8 s8_371 [] (by decide) s8_371_edges
  simp
def s8_372 : State := ⟨[65,29,104,145], 44601830679448528859301121194897921538195734, 3, 1, 1, 0⟩
theorem s8_372_edges : next config 8 s8_372 = [] := by decide
theorem s8_372_safe : Safe 5 8 s8_372 := by
  apply safe_succ 4 8 s8_372 [] (by decide) s8_372_edges
  simp
def s8_373 : State := ⟨[65,100,96,145], 44601830679429514100297697753875470453244182, 3, 3, 1, 0⟩
theorem s8_373_edges : next config 8 s8_373 = [] := by decide
theorem s8_373_safe : Safe 5 8 s8_373 := by
  apply safe_succ 4 8 s8_373 [] (by decide) s8_373_edges
  simp
def s8_374 : State := ⟨[65,117,104,145], 44601830845602028332415605307873803536367894, 3, 1, 1, 0⟩
theorem s8_374_edges : next config 8 s8_374 = [] := by decide
theorem s8_374_safe : Safe 5 8 s8_374 := by
  apply safe_succ 4 8 s8_374 [] (by decide) s8_374_edges
  simp
def s8_375 : State := ⟨[65,125,104,145], 44601873214744393976609054116723849972351254, 3, 1, 1, 0⟩
theorem s8_375_edges : next config 8 s8_375 = [] := by decide
theorem s8_375_safe : Safe 5 8 s8_375 := by
  apply safe_succ 4 8 s8_375 [] (by decide) s8_375_edges
  simp
def s8_376 : State := ⟨[81,12,104,145], 44601830679448528861718935940639031931638038, 3, 2, 1, 0⟩
theorem s8_376_edges : next config 8 s8_376 = [] := by decide
theorem s8_376_safe : Safe 5 8 s8_376 := by
  apply safe_succ 4 8 s8_376 [] (by decide) s8_376_edges
  simp
def s8_377 : State := ⟨[81,21,104,145], 44601830679448528861718935940639031931638038, 3, 2, 1, 0⟩
theorem s8_377_edges : next config 8 s8_377 = [] := by decide
theorem s8_377_safe : Safe 5 8 s8_377 := by
  apply safe_succ 4 8 s8_377 [] (by decide) s8_377_edges
  simp
def s8_378 : State := ⟨[82,4,67,145], 44601830679428167226370769219059339160129822, 3, 3, 1, 0⟩
theorem s8_378_edges : next config 8 s8_378 = [] := by decide
theorem s8_378_safe : Safe 5 8 s8_378 := by
  apply safe_succ 4 8 s8_378 [] (by decide) s8_378_edges
  simp
def s8_379 : State := ⟨[82,4,67,145], 44601830679428167226370769219059339162222878, 3, 3, 1, 0⟩
theorem s8_379_edges : next config 8 s8_379 = [s9_150, s9_148, s9_146] := by decide
theorem s8_379_safe : Safe 5 8 s8_379 := by
  apply safe_succ 4 8 s8_379 [s9_150, s9_148, s9_146] (by decide) s8_379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_150_safe
  · subst z; exact s9_148_safe
  · subst z; exact s9_146_safe
def s8_380 : State := ⟨[82,4,67,145], 44601830679428167303742021674395606341320990, 3, 3, 1, 0⟩
theorem s8_380_edges : next config 8 s8_380 = [] := by decide
theorem s8_380_safe : Safe 5 8 s8_380 := by
  apply safe_succ 4 8 s8_380 [] (by decide) s8_380_edges
  simp
def s8_381 : State := ⟨[82,4,67,145], 44601830679428167303742021674395606343418142, 1, 1, 1, 0⟩
theorem s8_381_edges : next config 8 s8_381 = [] := by decide
theorem s8_381_safe : Safe 5 8 s8_381 := by
  apply safe_succ 4 8 s8_381 [] (by decide) s8_381_edges
  simp
def s8_382 : State := ⟨[82,4,67,145], 44601830679428167303742058567883753762521366, 3, 2, 1, 0⟩
theorem s8_382_edges : next config 8 s8_382 = [] := by decide
theorem s8_382_safe : Safe 5 8 s8_382 := by
  apply safe_succ 4 8 s8_382 [] (by decide) s8_382_edges
  simp
def s8_383 : State := ⟨[82,4,67,145], 44601830679428167303742095461371901181624598, 3, 2, 1, 0⟩
theorem s8_383_edges : next config 8 s8_383 = [] := by decide
theorem s8_383_safe : Safe 5 8 s8_383 := by
  apply safe_succ 4 8 s8_383 [] (by decide) s8_383_edges
  simp
def s8_384 : State := ⟨[82,12,67,145], 44601830679428167226370806112547486581330198, 3, 2, 1, 0⟩
theorem s8_384_edges : next config 8 s8_384 = [] := by decide
theorem s8_384_safe : Safe 5 8 s8_384 := by
  apply safe_succ 4 8 s8_384 [] (by decide) s8_384_edges
  simp
def s8_385 : State := ⟨[82,12,67,145], 44601830679428167226370843006035634000433430, 3, 2, 1, 0⟩
theorem s8_385_edges : next config 8 s8_385 = [] := by decide
theorem s8_385_safe : Safe 5 8 s8_385 := by
  apply safe_succ 4 8 s8_385 [] (by decide) s8_385_edges
  simp
def s8_386 : State := ⟨[82,21,67,145], 44601830679428167226370806112547486581330198, 3, 2, 1, 0⟩
theorem s8_386_edges : next config 8 s8_386 = [] := by decide
theorem s8_386_safe : Safe 5 8 s8_386 := by
  apply safe_succ 4 8 s8_386 [] (by decide) s8_386_edges
  simp
def s8_387 : State := ⟨[82,21,67,145], 44601830679428167226370843006035634000433430, 3, 2, 1, 0⟩
theorem s8_387_edges : next config 8 s8_387 = [] := by decide
theorem s8_387_safe : Safe 5 8 s8_387 := by
  apply safe_succ 4 8 s8_387 [] (by decide) s8_387_edges
  simp
def s8_388 : State := ⟨[82,21,67,145], 44601830679428167303742021674395606343418142, 3, 1, 1, 0⟩
theorem s8_388_edges : next config 8 s8_388 = [] := by decide
theorem s8_388_safe : Safe 5 8 s8_388 := by
  apply safe_succ 4 8 s8_388 [] (by decide) s8_388_edges
  simp
def s8_389 : State := ⟨[82,86,67,145], 44601830679428167303742021674395606343418142, 3, 1, 1, 0⟩
theorem s8_389_edges : next config 8 s8_389 = [s9_145] := by decide
theorem s8_389_safe : Safe 5 8 s8_389 := by
  apply safe_succ 4 8 s8_389 [s9_145] (by decide) s8_389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_145_safe
def s8_390 : State := ⟨[82,86,67,145], 44601830679428167303742058567883753762521366, 3, 2, 1, 0⟩
theorem s8_390_edges : next config 8 s8_390 = [] := by decide
theorem s8_390_safe : Safe 5 8 s8_390 := by
  apply safe_succ 4 8 s8_390 [] (by decide) s8_390_edges
  simp
def s8_391 : State := ⟨[82,86,67,145], 44601830679428167303742095461371901181624598, 3, 2, 1, 0⟩
theorem s8_391_edges : next config 8 s8_391 = [] := by decide
theorem s8_391_safe : Safe 5 8 s8_391 := by
  apply safe_succ 4 8 s8_391 [] (by decide) s8_391_edges
  simp
def s8_392 : State := ⟨[86,4,67,145], 44601830679428167298906355289425237063700758, 3, 2, 1, 0⟩
theorem s8_392_edges : next config 8 s8_392 = [] := by decide
theorem s8_392_safe : Safe 5 8 s8_392 := by
  apply safe_succ 4 8 s8_392 [] (by decide) s8_392_edges
  simp
def s8_393 : State := ⟨[86,4,67,145], 44601830679428167298906392182913384482803990, 3, 2, 1, 0⟩
theorem s8_393_edges : next config 8 s8_393 = [] := by decide
theorem s8_393_safe : Safe 5 8 s8_393 := by
  apply safe_succ 4 8 s8_393 [] (by decide) s8_393_edges
  simp
def s8_394 : State := ⟨[86,4,67,145], 44601830679428167303742058567883753762521366, 3, 2, 1, 0⟩
theorem s8_394_edges : next config 8 s8_394 = [] := by decide
theorem s8_394_safe : Safe 5 8 s8_394 := by
  apply safe_succ 4 8 s8_394 [] (by decide) s8_394_edges
  simp
def s8_395 : State := ⟨[86,4,67,145], 44601830679428167303742095461371901181624598, 3, 2, 1, 0⟩
theorem s8_395_edges : next config 8 s8_395 = [] := by decide
theorem s8_395_safe : Safe 5 8 s8_395 := by
  apply safe_succ 4 8 s8_395 [] (by decide) s8_395_edges
  simp
def s8_396 : State := ⟨[86,12,67,145], 44601830679428167298906318395937089644597534, 3, 1, 1, 0⟩
theorem s8_396_edges : next config 8 s8_396 = [s9_149] := by decide
theorem s8_396_safe : Safe 5 8 s8_396 := by
  apply safe_succ 4 8 s8_396 [s9_149] (by decide) s8_396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_149_safe
def s8_397 : State := ⟨[86,82,67,145], 44601830679428167303742021674395606343418142, 3, 1, 1, 0⟩
theorem s8_397_edges : next config 8 s8_397 = [s9_150] := by decide
theorem s8_397_safe : Safe 5 8 s8_397 := by
  apply safe_succ 4 8 s8_397 [s9_150] (by decide) s8_397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_150_safe
def s8_398 : State := ⟨[96,4,67,145], 44602511244162088326624506954153313901285662, 3, 2, 1, 0⟩
theorem s8_398_edges : next config 8 s8_398 = [s9_160] := by decide
theorem s8_398_safe : Safe 5 8 s8_398 := by
  apply safe_succ 4 8 s8_398 [s9_160] (by decide) s8_398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_160_safe
def s8_399 : State := ⟨[96,4,67,145], 44602511244182370736228158624586057245589790, 1, 0, 1, 0⟩
theorem s8_399_edges : next config 8 s8_399 = [] := by decide
theorem s8_399_safe : Safe 5 8 s8_399 := by
  apply safe_succ 4 8 s8_399 [] (by decide) s8_399_edges
  simp
def s8_400 : State := ⟨[96,4,67,145], 66902575877958869591233298477586811870843166, 3, 2, 1, 0⟩
theorem s8_400_edges : next config 8 s8_400 = [s9_161] := by decide
theorem s8_400_safe : Safe 5 8 s8_400 := by
  apply safe_succ 4 8 s8_400 [s9_161] (by decide) s8_400_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_161_safe
def s8_401 : State := ⟨[96,4,67,145], 66902575877979152000836950148019555215147294, 1, 0, 1, 0⟩
theorem s8_401_edges : next config 8 s8_401 = [] := by decide
theorem s8_401_safe : Safe 5 8 s8_401 := by
  apply safe_succ 4 8 s8_401 [] (by decide) s8_401_edges
  simp
def s8_402 : State := ⟨[96,12,67,145], 44601830679428246449697580204938450364993822, 3, 1, 1, 0⟩
theorem s8_402_edges : next config 8 s8_402 = [s9_162, s9_151] := by decide
theorem s8_402_safe : Safe 5 8 s8_402 := by
  apply safe_succ 4 8 s8_402 [s9_162, s9_151] (by decide) s8_402_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_162_safe
  · subst z; exact s9_151_safe
def s8_403 : State := ⟨[96,21,67,145], 44601830679428246449697580204938450367086878, 3, 1, 1, 0⟩
theorem s8_403_edges : next config 8 s8_403 = [s9_164, s9_156, s9_154] := by decide
theorem s8_403_safe : Safe 5 8 s8_403 := by
  apply safe_succ 4 8 s8_403 [s9_164, s9_156, s9_154] (by decide) s8_403_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s9_164_safe
  · subst z; exact s9_156_safe
  · subst z; exact s9_154_safe
def s8_404 : State := ⟨[97,4,104,145], 44601830679448687315626112830084960668029206, 3, 3, 1, 0⟩
theorem s8_404_edges : next config 8 s8_404 = [] := by decide
theorem s8_404_safe : Safe 5 8 s8_404 := by
  apply safe_succ 4 8 s8_404 [] (by decide) s8_404_edges
  simp
def s8_405 : State := ⟨[97,4,104,145], 44601830679448687315626112830084960670122262, 3, 3, 1, 0⟩
theorem s8_405_edges : next config 8 s8_405 = [s9_157] := by decide
theorem s8_405_safe : Safe 5 8 s8_405 := by
  apply safe_succ 4 8 s8_405 [s9_157] (by decide) s8_405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_157_safe
def s8_406 : State := ⟨[97,12,96,145], 44601830679428404906022461159661013418840342, 3, 3, 1, 0⟩
theorem s8_406_edges : next config 8 s8_406 = [s9_157] := by decide
theorem s8_406_safe : Safe 5 8 s8_406 := by
  apply safe_succ 4 8 s8_406 [s9_157] (by decide) s8_406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_157_safe
def s8_407 : State := ⟨[97,21,96,145], 44601830679428404906022461159661013418840342, 3, 3, 1, 0⟩
theorem s8_407_edges : next config 8 s8_407 = [] := by decide
theorem s8_407_safe : Safe 5 8 s8_407 := by
  apply safe_succ 4 8 s8_407 [] (by decide) s8_407_edges
  simp
def s8_408 : State := ⟨[97,21,125,145], 44601873214744552432934045751910889641148694, 3, 1, 1, 0⟩
theorem s8_408_edges : next config 8 s8_408 = [] := by decide
theorem s8_408_safe : Safe 5 8 s8_408 := by
  apply safe_succ 4 8 s8_408 [] (by decide) s8_408_edges
  simp
def s8_409 : State := ⟨[97,125,104,145], 44601873214744552432934045751910889641148694, 3, 1, 1, 0⟩
theorem s8_409_edges : next config 8 s8_409 = [] := by decide
theorem s8_409_safe : Safe 5 8 s8_409 := by
  apply safe_succ 4 8 s8_409 [] (by decide) s8_409_edges
  simp
def s8_410 : State := ⟨[104,4,67,129], 1020847121124453156722079280538140610846, 3, 2, 1, 0⟩
theorem s8_410_edges : next config 8 s8_410 = [s9_160] := by decide
theorem s8_410_safe : Safe 5 8 s8_410 := by
  apply safe_succ 4 8 s8_410 [s9_160] (by decide) s8_410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_160_safe
def s8_411 : State := ⟨[104,4,67,130], 1701411854966330083648828495401677033758, 3, 2, 1, 0⟩
theorem s8_411_edges : next config 8 s8_411 = [] := by decide
theorem s8_411_safe : Safe 5 8 s8_411 := by
  apply safe_succ 4 8 s8_411 [] (by decide) s8_411_edges
  simp
def s8_412 : State := ⟨[104,4,67,131], 3062541322650083937502326925128749879582, 3, 2, 1, 0⟩
theorem s8_412_edges : next config 8 s8_412 = [] := by decide
theorem s8_412_safe : Safe 5 8 s8_412 := by
  apply safe_succ 4 8 s8_412 [] (by decide) s8_412_edges
  simp
def s8_413 : State := ⟨[104,4,67,132], 5784800258017591645209323784582895571230, 3, 2, 1, 0⟩
theorem s8_413_edges : next config 8 s8_413 = [] := by decide
theorem s8_413_safe : Safe 5 8 s8_413 := by
  apply safe_succ 4 8 s8_413 [] (by decide) s8_413_edges
  simp
def s8_414 : State := ⟨[104,4,67,136], 87452568319042822876419229568207266320670, 3, 2, 1, 0⟩
theorem s8_414_edges : next config 8 s8_414 = [] := by decide
theorem s8_414_safe : Safe 5 8 s8_414 := by
  apply safe_succ 4 8 s8_414 [] (by decide) s8_414_edges
  simp
def s8_415 : State := ⟨[104,4,67,136], 1481249143227206769222401621608729860440350, 3, 2, 1, 0⟩
theorem s8_415_edges : next config 8 s8_415 = [] := by decide
theorem s8_415_safe : Safe 5 8 s8_415 := by
  apply safe_succ 4 8 s8_415 [] (by decide) s8_415_edges
  simp
def s8_416 : State := ⟨[104,4,67,140], 1394136857295446522575777722106197198311710, 3, 2, 1, 0⟩
theorem s8_416_edges : next config 8 s8_416 = [] := by decide
theorem s8_416_safe : Safe 5 8 s8_416 := by
  apply safe_succ 4 8 s8_416 [] (by decide) s8_416_edges
  simp
def s8_417 : State := ⟨[104,4,67,144], 22301085480917905717765513602714036110168350, 3, 2, 1, 0⟩
theorem s8_417_edges : next config 8 s8_417 = [] := by decide
theorem s8_417_safe : Safe 5 8 s8_417 := by
  apply safe_succ 4 8 s8_417 [] (by decide) s8_417_edges
  simp
def s8_418 : State := ⟨[104,4,67,145], 44601830679448449631138717611033600165347614, 1, 1, 1, 0⟩
theorem s8_418_edges : next config 8 s8_418 = [s9_153] := by decide
theorem s8_418_safe : Safe 5 8 s8_418 := by
  apply safe_succ 4 8 s8_418 [s9_153] (by decide) s8_418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_153_safe
def s8_419 : State := ⟨[104,4,67,145], 44601830679448528859301231875362397616275742, 1, 1, 1, 0⟩
theorem s8_419_edges : next config 8 s8_419 = [s9_119, s9_162] := by decide
theorem s8_419_safe : Safe 5 8 s8_419 := by
  apply safe_succ 4 8 s8_419 [s9_119, s9_162] (by decide) s8_419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_119_safe
  · subst z; exact s9_162_safe
def s8_420 : State := ⟨[104,4,67,145], 44602511244182370736228158624586057245589790, 1, 0, 1, 0⟩
theorem s8_420_edges : next config 8 s8_420 = [] := by decide
theorem s8_420_safe : Safe 5 8 s8_420 := by
  apply safe_succ 4 8 s8_420 [] (by decide) s8_420_edges
  simp
def s8_421 : State := ⟨[104,4,67,145], 44602511244182370736228158624586065835524374, 1, 0, 1, 0⟩
theorem s8_421_edges : next config 8 s8_421 = [] := by decide
theorem s8_421_safe : Safe 5 8 s8_421 := by
  apply safe_succ 4 8 s8_421 [] (by decide) s8_421_edges
  simp
def s8_422 : State := ⟨[104,4,67,145], 66902575877979152000836950148019555215147294, 1, 0, 1, 0⟩
theorem s8_422_edges : next config 8 s8_422 = [] := by decide
theorem s8_422_safe : Safe 5 8 s8_422 := by
  apply safe_succ 4 8 s8_422 [] (by decide) s8_422_edges
  simp
def s8_423 : State := ⟨[104,4,67,145], 66902575877979152000836950148019563805081878, 1, 0, 1, 0⟩
theorem s8_423_edges : next config 8 s8_423 = [] := by decide
theorem s8_423_safe : Safe 5 8 s8_423 := by
  apply safe_succ 4 8 s8_423 [] (by decide) s8_423_edges
  simp
def s8_424 : State := ⟨[104,4,67,160], 1461501637671185305486261062511613085330536730910, 3, 2, 1, 0⟩
theorem s8_424_edges : next config 8 s8_424 = [] := by decide
theorem s8_424_safe : Safe 5 8 s8_424 := by
  apply safe_succ 4 8 s8_424 [] (by decide) s8_424_edges
  simp
def s8_425 : State := ⟨[104,4,67,163], 11692013098987505732912054891525594222922064531742, 3, 2, 1, 0⟩
theorem s8_425_edges : next config 8 s8_425 = [] := by decide
theorem s8_425_safe : Safe 5 8 s8_425 := by
  apply safe_succ 4 8 s8_425 [] (by decide) s8_425_edges
  simp
def s8_426 : State := ⟨[104,4,67,192], 6277101735386680764176071810490242645897685510138638700830, 3, 2, 1, 0⟩
theorem s8_426_edges : next config 8 s8_426 = [] := by decide
theorem s8_426_safe : Safe 5 8 s8_426 := by
  apply safe_succ 4 8 s8_426 [] (by decide) s8_426_edges
  simp
def s8_427 : State := ⟨[104,4,67,195], 50216813883093446111026597772943907558614173621386880291102, 3, 2, 1, 0⟩
theorem s8_427_edges : next config 8 s8_427 = [] := by decide
theorem s8_427_safe : Safe 5 8 s8_427 := by
  apply safe_succ 4 8 s8_427 [] (by decide) s8_427_edges
  simp
def s8_428 : State := ⟨[104,4,67,224], 26959946667150639794667015087359913060919720652335902546778214437150, 3, 2, 1, 0⟩
theorem s8_428_edges : next config 8 s8_428 = [] := by decide
theorem s8_428_safe : Safe 5 8 s8_428 := by
  apply safe_succ 4 8 s8_428 [] (by decide) s8_428_edges
  simp
def s8_429 : State := ⟨[104,4,67,232], 6901746346790563787434755862277365734838391548400181885228198827987230, 3, 2, 1, 0⟩
theorem s8_429_edges : next config 8 s8_429 = [] := by decide
theorem s8_429_safe : Safe 5 8 s8_429 := by
  apply safe_succ 4 8 s8_429 [] (by decide) s8_429_edges
  simp
def s8_430 : State := ⟨[104,12,67,145], 44602511244182370736228158624577261152571678, 3, 0, 1, 0⟩
theorem s8_430_edges : next config 8 s8_430 = [s9_160] := by decide
theorem s8_430_safe : Safe 5 8 s8_430 := by
  apply safe_succ 4 8 s8_430 [s9_160] (by decide) s8_430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_160_safe
def s8_431 : State := ⟨[104,12,67,145], 66902575877979152000836950148010759122129182, 3, 0, 1, 0⟩
theorem s8_431_edges : next config 8 s8_431 = [s9_161] := by decide
theorem s8_431_safe : Safe 5 8 s8_431 := by
  apply safe_succ 4 8 s8_431 [s9_161] (by decide) s8_431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_161_safe
def s8_432 : State := ⟨[113,4,96,145], 44601830689812840166767087888046818987282718, 3, 3, 1, 0⟩
theorem s8_432_edges : next config 8 s8_432 = [s9_165] := by decide
theorem s8_432_safe : Safe 5 8 s8_432 := by
  apply safe_succ 4 8 s8_432 [s9_165] (by decide) s8_432_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_165_safe
def s8_433 : State := ⟨[113,4,96,145], 44601830689812840166767087888046818989375774, 3, 3, 1, 0⟩
theorem s8_433_edges : next config 8 s8_433 = [s9_169, s9_166] := by decide
theorem s8_433_safe : Safe 5 8 s8_433 := by
  apply safe_succ 4 8 s8_433 [s9_169, s9_166] (by decide) s8_433_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_169_safe
  · subst z; exact s9_166_safe
def s8_434 : State := ⟨[113,4,96,145], 44601830689812840166767124781534966406385942, 3, 3, 1, 0⟩
theorem s8_434_edges : next config 8 s8_434 = [s9_167] := by decide
theorem s8_434_safe : Safe 5 8 s8_434 := by
  apply safe_succ 4 8 s8_434 [s9_167] (by decide) s8_434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_167_safe
def s8_435 : State := ⟨[113,4,96,145], 44601830689812840166767124781534966408478998, 3, 3, 1, 0⟩
theorem s8_435_edges : next config 8 s8_435 = [s9_170, s9_168] := by decide
theorem s8_435_safe : Safe 5 8 s8_435 := by
  apply safe_succ 4 8 s8_435 [s9_170, s9_168] (by decide) s8_435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_170_safe
  · subst z; exact s9_168_safe
def s8_436 : State := ⟨[113,12,104,145], 44601830689833122576370739558470766238568734, 3, 1, 1, 0⟩
theorem s8_436_edges : next config 8 s8_436 = [s9_165] := by decide
theorem s8_436_safe : Safe 5 8 s8_436 := by
  apply safe_succ 4 8 s8_436 [s9_165] (by decide) s8_436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_165_safe
def s8_437 : State := ⟨[113,12,104,145], 44601830689833122576370739558470766240665878, 3, 2, 1, 0⟩
theorem s8_437_edges : next config 8 s8_437 = [] := by decide
theorem s8_437_safe : Safe 5 8 s8_437 := by
  apply safe_succ 4 8 s8_437 [] (by decide) s8_437_edges
  simp
def s8_438 : State := ⟨[113,12,104,145], 44601830689833122576370776451958913657671958, 3, 1, 1, 0⟩
theorem s8_438_edges : next config 8 s8_438 = [s9_167] := by decide
theorem s8_438_safe : Safe 5 8 s8_438 := by
  apply safe_succ 4 8 s8_438 [s9_167] (by decide) s8_438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_167_safe
def s8_439 : State := ⟨[113,21,104,145], 44601830689833122576370739558470766240661790, 3, 1, 1, 0⟩
theorem s8_439_edges : next config 8 s8_439 = [] := by decide
theorem s8_439_safe : Safe 5 8 s8_439 := by
  apply safe_succ 4 8 s8_439 [] (by decide) s8_439_edges
  simp
def s8_440 : State := ⟨[113,21,104,145], 44601830689833122576370739558470766240665878, 3, 2, 1, 0⟩
theorem s8_440_edges : next config 8 s8_440 = [] := by decide
theorem s8_440_safe : Safe 5 8 s8_440 := by
  apply safe_succ 4 8 s8_440 [] (by decide) s8_440_edges
  simp
def s8_441 : State := ⟨[113,21,104,145], 44601830689833122576370776451958913659765014, 3, 1, 1, 0⟩
theorem s8_441_edges : next config 8 s8_441 = [] := by decide
theorem s8_441_safe : Safe 5 8 s8_441 := by
  apply safe_succ 4 8 s8_441 [] (by decide) s8_441_edges
  simp
def s8_442 : State := ⟨[117,4,104,145], 44601830845602028332415568414385656117264670, 1, 1, 1, 0⟩
theorem s8_442_edges : next config 8 s8_442 = [] := by decide
theorem s8_442_safe : Safe 5 8 s8_442 := by
  apply safe_succ 4 8 s8_442 [] (by decide) s8_442_edges
  simp
def s8_443 : State := ⟨[117,4,104,145], 44601830845602028332415605307873803536367894, 1, 1, 1, 0⟩
theorem s8_443_edges : next config 8 s8_443 = [] := by decide
theorem s8_443_safe : Safe 5 8 s8_443 := by
  apply safe_succ 4 8 s8_443 [] (by decide) s8_443_edges
  simp
def s8_444 : State := ⟨[121,21,104,145], 44601833337904520429132830109023894142910750, 3, 1, 1, 0⟩
theorem s8_444_edges : next config 8 s8_444 = [] := by decide
theorem s8_444_safe : Safe 5 8 s8_444 := by
  apply safe_succ 4 8 s8_444 [] (by decide) s8_444_edges
  simp
def s8_445 : State := ⟨[121,21,104,145], 44601833337904520429132867002512041562013974, 3, 1, 1, 0⟩
theorem s8_445_edges : next config 8 s8_445 = [] := by decide
theorem s8_445_safe : Safe 5 8 s8_445 := by
  apply safe_succ 4 8 s8_445 [] (by decide) s8_445_edges
  simp
def s8_446 : State := ⟨[125,4,104,145], 44601873214744393976609017223235702553248030, 1, 1, 1, 0⟩
theorem s8_446_edges : next config 8 s8_446 = [s9_173] := by decide
theorem s8_446_safe : Safe 5 8 s8_446 := by
  apply safe_succ 4 8 s8_446 [s9_173] (by decide) s8_446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_173_safe
def s8_447 : State := ⟨[125,4,104,145], 44601873214744393976609017223235702553252118, 3, 2, 1, 0⟩
theorem s8_447_edges : next config 8 s8_447 = [] := by decide
theorem s8_447_safe : Safe 5 8 s8_447 := by
  apply safe_succ 4 8 s8_447 [] (by decide) s8_447_edges
  simp
def s8_448 : State := ⟨[125,4,104,145], 44601873214744393976609017223235711143182614, 1, 1, 1, 0⟩
theorem s8_448_edges : next config 8 s8_448 = [] := by decide
theorem s8_448_safe : Safe 5 8 s8_448 := by
  apply safe_succ 4 8 s8_448 [] (by decide) s8_448_edges
  simp
def s8_449 : State := ⟨[125,4,104,145], 44601873214744393976609054116723849972351254, 1, 1, 1, 0⟩
theorem s8_449_edges : next config 8 s8_449 = [s9_174] := by decide
theorem s8_449_safe : Safe 5 8 s8_449 := by
  apply safe_succ 4 8 s8_449 [s9_174] (by decide) s8_449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_174_safe
def s8_450 : State := ⟨[125,4,104,145], 44601873214744552432934045751910889641148694, 1, 1, 1, 0⟩
theorem s8_450_edges : next config 8 s8_450 = [] := by decide
theorem s8_450_safe : Safe 5 8 s8_450 := by
  apply safe_succ 4 8 s8_450 [] (by decide) s8_450_edges
  simp
def s8_451 : State := ⟨[146,4,67,145], 133804811473550659787677939031194268485226782, 3, 3, 1, 0⟩
theorem s8_451_edges : next config 8 s8_451 = [] := by decide
theorem s8_451_safe : Safe 5 8 s8_451 := by
  apply safe_succ 4 8 s8_451 [] (by decide) s8_451_edges
  simp
def s8_452 : State := ⟨[146,4,67,145], 133804811473550659787677939031194268487319838, 3, 3, 1, 0⟩
theorem s8_452_edges : next config 8 s8_452 = [s9_177] := by decide
theorem s8_452_safe : Safe 5 8 s8_452 := by
  apply safe_succ 4 8 s8_452 [s9_177] (by decide) s8_452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_177_safe
def s8_453 : State := ⟨[146,4,96,145], 133804811473550739015840305721579272352764190, 3, 3, 1, 0⟩
theorem s8_453_edges : next config 8 s8_453 = [s9_175] := by decide
theorem s8_453_safe : Safe 5 8 s8_453 := by
  apply safe_succ 4 8 s8_453 [s9_175] (by decide) s8_453_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_175_safe
def s8_454 : State := ⟨[146,4,96,145], 133804811473550739015840305721579272354857246, 3, 3, 1, 0⟩
theorem s8_454_edges : next config 8 s8_454 = [s9_178, s9_176] := by decide
theorem s8_454_safe : Safe 5 8 s8_454 := by
  apply safe_succ 4 8 s8_454 [s9_178, s9_176] (by decide) s8_454_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s9_178_safe
  · subst z; exact s9_176_safe
def s8_455 : State := ⟨[146,4,104,145], 133805492038304863302370884141218083140342046, 3, 2, 1, 0⟩
theorem s8_455_edges : next config 8 s8_455 = [] := by decide
theorem s8_455_safe : Safe 5 8 s8_455 := by
  apply safe_succ 4 8 s8_455 [] (by decide) s8_455_edges
  simp
def s8_456 : State := ⟨[146,4,104,145], 156105556672101644566979675664651581109899550, 3, 2, 1, 0⟩
theorem s8_456_edges : next config 8 s8_456 = [] := by decide
theorem s8_456_safe : Safe 5 8 s8_456 := by
  apply safe_succ 4 8 s8_456 [] (by decide) s8_456_edges
  simp
def s8_457 : State := ⟨[146,12,64,145], 133804811473550659787677791457241678810911006, 3, 3, 1, 0⟩
theorem s8_457_edges : next config 8 s8_457 = [s9_178] := by decide
theorem s8_457_safe : Safe 5 8 s8_457 := by
  apply safe_succ 4 8 s8_457 [s9_178] (by decide) s8_457_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_178_safe
def s8_458 : State := ⟨[146,12,104,145], 133804811473571021425443957392003219604050206, 3, 1, 1, 0⟩
theorem s8_458_edges : next config 8 s8_458 = [s9_175] := by decide
theorem s8_458_safe : Safe 5 8 s8_458 := by
  apply safe_succ 4 8 s8_458 [s9_175] (by decide) s8_458_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s9_175_safe
def s8_459 : State := ⟨[146,21,64,145], 133804811473550659787677791457241678810911006, 3, 3, 1, 0⟩
theorem s8_459_edges : next config 8 s8_459 = [] := by decide
theorem s8_459_safe : Safe 5 8 s8_459 := by
  apply safe_succ 4 8 s8_459 [] (by decide) s8_459_edges
  simp
def s8_460 : State := ⟨[146,21,104,145], 133804811473571021425443957392003219606143262, 3, 1, 1, 0⟩
theorem s8_460_edges : next config 8 s8_460 = [] := by decide
theorem s8_460_safe : Safe 5 8 s8_460 := by
  apply safe_succ 4 8 s8_460 [] (by decide) s8_460_edges
  simp
def s8_461 : State := ⟨[146,86,67,145], 133804811473550659865049191486530535668515102, 3, 1, 1, 0⟩
theorem s8_461_edges : next config 8 s8_461 = [] := by decide
theorem s8_461_safe : Safe 5 8 s8_461 := by
  apply safe_succ 4 8 s8_461 [] (by decide) s8_461_edges
  simp
end HGP13.SectorGraph234
