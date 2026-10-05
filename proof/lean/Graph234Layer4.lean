import Graph234Layer5
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s4_0 : State := ⟨[1,4,64,128], 340282366920938463481821351509772800286, 3, 3, 0, 0⟩
theorem s4_0_edges : next config 4 s4_0 = [s5_946, s5_184, s5_0, s5_8, s5_47, s5_3, s5_11, s5_20, s5_28] := by decide
theorem s4_0_safe : Safe 9 4 s4_0 := by
  apply safe_succ 8 4 s4_0 [s5_946, s5_184, s5_0, s5_8, s5_47, s5_3, s5_11, s5_20, s5_28] (by decide) s4_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_946_safe
  · subst z; exact s5_184_safe
  · subst z; exact s5_0_safe
  · subst z; exact s5_8_safe
  · subst z; exact s5_47_safe
  · subst z; exact s5_3_safe
  · subst z; exact s5_11_safe
  · subst z; exact s5_20_safe
  · subst z; exact s5_28_safe
def s4_1 : State := ⟨[1,4,64,128], 340282366920938463481821351518362734870, 3, 3, 0, 0⟩
theorem s4_1_edges : next config 4 s4_1 = [s5_949, s5_185, s5_1, s5_9, s5_48, s5_4, s5_12, s5_21, s5_29] := by decide
theorem s4_1_safe : Safe 9 4 s4_1 := by
  apply safe_succ 8 4 s4_1 [s5_949, s5_185, s5_1, s5_9, s5_48, s5_4, s5_12, s5_21, s5_29] (by decide) s4_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_949_safe
  · subst z; exact s5_185_safe
  · subst z; exact s5_1_safe
  · subst z; exact s5_9_safe
  · subst z; exact s5_48_safe
  · subst z; exact s5_4_safe
  · subst z; exact s5_12_safe
  · subst z; exact s5_21_safe
  · subst z; exact s5_29_safe
def s4_2 : State := ⟨[1,4,64,128], 340282366920938463518714839657191903510, 3, 3, 0, 0⟩
theorem s4_2_edges : next config 4 s4_2 = [s5_951, s5_186, s5_2, s5_10, s5_49, s5_5, s5_13, s5_22, s5_30] := by decide
theorem s4_2_safe : Safe 9 4 s4_2 := by
  apply safe_succ 8 4 s4_2 [s5_951, s5_186, s5_2, s5_10, s5_49, s5_5, s5_13, s5_22, s5_30] (by decide) s4_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_951_safe
  · subst z; exact s5_186_safe
  · subst z; exact s5_2_safe
  · subst z; exact s5_10_safe
  · subst z; exact s5_49_safe
  · subst z; exact s5_5_safe
  · subst z; exact s5_13_safe
  · subst z; exact s5_22_safe
  · subst z; exact s5_30_safe
def s4_3 : State := ⟨[1,4,64,131], 3743106036130323098115567425827454914838, 2, 2, 1, 0⟩
theorem s4_3_edges : next config 4 s4_3 = [s5_190, s5_33] := by decide
theorem s4_3_safe : Safe 9 4 s4_3 := by
  apply safe_succ 8 4 s4_3 [s5_190, s5_33] (by decide) s4_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_190_safe
  · subst z; exact s5_33_safe
def s4_4 : State := ⟨[1,4,64,131], 4423670769972200025042316640690991337750, 2, 2, 1, 0⟩
theorem s4_4_edges : next config 4 s4_4 = [s5_192, s5_34] := by decide
theorem s4_4_safe : Safe 9 4 s4_4 := by
  apply safe_succ 8 4 s4_4 [s5_192, s5_34] (by decide) s4_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_192_safe
  · subst z; exact s5_34_safe
def s4_5 : State := ⟨[1,4,64,140], 1399581375145819900224878207110940658303262, 1, 1, 1, 0⟩
theorem s4_5_edges : next config 4 s4_5 = [s5_194] := by decide
theorem s4_5_safe : Safe 9 4 s4_5 := by
  apply safe_succ 8 4 s4_5 [s5_194] (by decide) s4_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_194_safe
def s4_6 : State := ⟨[1,4,64,140], 1399581375145819900224878207110949248237846, 1, 1, 1, 0⟩
theorem s4_6_edges : next config 4 s4_6 = [s5_195] := by decide
theorem s4_6_safe : Safe 9 4 s4_6 := by
  apply safe_succ 8 4 s4_6 [s5_195] (by decide) s4_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_195_safe
def s4_7 : State := ⟨[1,4,64,140], 1399581375145819900224915100599088077406486, 1, 1, 1, 0⟩
theorem s4_7_edges : next config 4 s4_7 = [s5_196] := by decide
theorem s4_7_safe : Safe 9 4 s4_7 := by
  apply safe_succ 8 4 s4_7 [s5_196] (by decide) s4_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_196_safe
def s4_8 : State := ⟨[1,4,64,140], 1481249143206845131456088112894565029052702, 1, 1, 1, 0⟩
theorem s4_8_edges : next config 4 s4_8 = [s5_198] := by decide
theorem s4_8_safe : Safe 9 4 s4_8 := by
  apply safe_succ 8 4 s4_8 [s5_198] (by decide) s4_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_198_safe
def s4_9 : State := ⟨[1,4,64,140], 1481249143206845131456088112894573618987286, 1, 1, 1, 0⟩
theorem s4_9_edges : next config 4 s4_9 = [s5_199] := by decide
theorem s4_9_safe : Safe 9 4 s4_9 := by
  apply safe_succ 8 4 s4_9 [s5_199] (by decide) s4_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_199_safe
def s4_10 : State := ⟨[1,4,64,140], 1481249143206845131456125006382712448155926, 1, 1, 1, 0⟩
theorem s4_10_edges : next config 4 s4_10 = [s5_200] := by decide
theorem s4_10_safe : Safe 9 4 s4_10 := by
  apply safe_succ 8 4 s4_10 [s5_200] (by decide) s4_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_200_safe
def s4_11 : State := ⟨[1,4,64,145], 44602511244162009098461845115863096321179934, 1, 1, 1, 0⟩
theorem s4_11_edges : next config 4 s4_11 = [s5_519, s5_202] := by decide
theorem s4_11_safe : Safe 9 4 s4_11 := by
  apply safe_succ 8 4 s4_11 [s5_519, s5_202] (by decide) s4_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_519_safe
  · subst z; exact s5_202_safe
def s4_12 : State := ⟨[1,4,64,145], 44602511244162009098461845115863096321180438, 1, 1, 1, 0⟩
theorem s4_12_edges : next config 4 s4_12 = [s5_203] := by decide
theorem s4_12_safe : Safe 9 4 s4_12 := by
  apply safe_succ 8 4 s4_12 [s5_203] (by decide) s4_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_203_safe
def s4_13 : State := ⟨[1,4,64,145], 44602511244162009098461845115863096321184022, 2, 2, 1, 0⟩
theorem s4_13_edges : next config 4 s4_13 = [s5_1367, s5_788, s5_1143, s5_66, s5_493, s5_74, s5_128, s5_204] := by decide
theorem s4_13_safe : Safe 9 4 s4_13 := by
  apply safe_succ 8 4 s4_13 [s5_1367, s5_788, s5_1143, s5_66, s5_493, s5_74, s5_128, s5_204] (by decide) s4_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1367_safe
  · subst z; exact s5_788_safe
  · subst z; exact s5_1143_safe
  · subst z; exact s5_66_safe
  · subst z; exact s5_493_safe
  · subst z; exact s5_74_safe
  · subst z; exact s5_128_safe
  · subst z; exact s5_204_safe
def s4_14 : State := ⟨[1,4,64,145], 44602511244162009098461845115863104911114518, 1, 1, 1, 0⟩
theorem s4_14_edges : next config 4 s4_14 = [s5_520, s5_205] := by decide
theorem s4_14_safe : Safe 9 4 s4_14 := by
  apply safe_succ 8 4 s4_14 [s5_520, s5_205] (by decide) s4_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_520_safe
  · subst z; exact s5_205_safe
def s4_15 : State := ⟨[1,4,64,145], 44602511244162009098461882009351243740283158, 1, 1, 1, 0⟩
theorem s4_15_edges : next config 4 s4_15 = [s5_521, s5_206] := by decide
theorem s4_15_safe : Safe 9 4 s4_15 := by
  apply safe_succ 8 4 s4_15 [s5_521, s5_206] (by decide) s4_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_521_safe
  · subst z; exact s5_206_safe
def s4_16 : State := ⟨[1,4,64,145], 44602511244162009098462140263768275674005782, 2, 2, 1, 0⟩
theorem s4_16_edges : next config 4 s4_16 = [s5_207] := by decide
theorem s4_16_safe : Safe 9 4 s4_16 := by
  apply safe_succ 8 4 s4_16 [s5_207] (by decide) s4_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_207_safe
def s4_17 : State := ⟨[1,4,64,145], 66902575877958790363070636639296594290737438, 1, 1, 1, 0⟩
theorem s4_17_edges : next config 4 s4_17 = [s5_522, s5_210] := by decide
theorem s4_17_safe : Safe 9 4 s4_17 := by
  apply safe_succ 8 4 s4_17 [s5_522, s5_210] (by decide) s4_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_522_safe
  · subst z; exact s5_210_safe
def s4_18 : State := ⟨[1,4,64,145], 66902575877958790363070636639296594290737942, 1, 1, 1, 0⟩
theorem s4_18_edges : next config 4 s4_18 = [s5_211] := by decide
theorem s4_18_safe : Safe 9 4 s4_18 := by
  apply safe_succ 8 4 s4_18 [s5_211] (by decide) s4_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_211_safe
def s4_19 : State := ⟨[1,4,64,145], 66902575877958790363070636639296594290741526, 2, 2, 1, 0⟩
theorem s4_19_edges : next config 4 s4_19 = [s5_1368, s5_789, s5_1144, s5_67, s5_494, s5_75, s5_129, s5_212] := by decide
theorem s4_19_safe : Safe 9 4 s4_19 := by
  apply safe_succ 8 4 s4_19 [s5_1368, s5_789, s5_1144, s5_67, s5_494, s5_75, s5_129, s5_212] (by decide) s4_19_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1368_safe
  · subst z; exact s5_789_safe
  · subst z; exact s5_1144_safe
  · subst z; exact s5_67_safe
  · subst z; exact s5_494_safe
  · subst z; exact s5_75_safe
  · subst z; exact s5_129_safe
  · subst z; exact s5_212_safe
def s4_20 : State := ⟨[1,4,64,145], 66902575877958790363070636639296602880672022, 1, 1, 1, 0⟩
theorem s4_20_edges : next config 4 s4_20 = [s5_523, s5_213] := by decide
theorem s4_20_safe : Safe 9 4 s4_20 := by
  apply safe_succ 8 4 s4_20 [s5_523, s5_213] (by decide) s4_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_523_safe
  · subst z; exact s5_213_safe
def s4_21 : State := ⟨[1,4,64,145], 66902575877958790363070673532784741709840662, 1, 1, 1, 0⟩
theorem s4_21_edges : next config 4 s4_21 = [s5_524, s5_214] := by decide
theorem s4_21_safe : Safe 9 4 s4_21 := by
  apply safe_succ 8 4 s4_21 [s5_524, s5_214] (by decide) s4_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_524_safe
  · subst z; exact s5_214_safe
def s4_22 : State := ⟨[1,4,64,145], 66902575877958790363070931787201773643563286, 2, 2, 1, 0⟩
theorem s4_22_edges : next config 4 s4_22 = [s5_215] := by decide
theorem s4_22_safe : Safe 9 4 s4_22 := by
  apply safe_succ 8 4 s4_22 [s5_215] (by decide) s4_22_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_215_safe
def s4_23 : State := ⟨[1,4,64,146], 89204682205957097258460208410374682869563678, 1, 1, 1, 0⟩
theorem s4_23_edges : next config 4 s4_23 = [s5_525, s5_218] := by decide
theorem s4_23_safe : Safe 9 4 s4_23 := by
  apply safe_succ 8 4 s4_23 [s5_525, s5_218] (by decide) s4_23_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_525_safe
  · subst z; exact s5_218_safe
def s4_24 : State := ⟨[1,4,64,146], 89204682205957097258460208410374682869567766, 2, 2, 1, 0⟩
theorem s4_24_edges : next config 4 s4_24 = [s5_1369, s5_790, s5_68, s5_503, s5_76, s5_219, s5_52] := by decide
theorem s4_24_safe : Safe 9 4 s4_24 := by
  apply safe_succ 8 4 s4_24 [s5_1369, s5_790, s5_68, s5_503, s5_76, s5_219, s5_52] (by decide) s4_24_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1369_safe
  · subst z; exact s5_790_safe
  · subst z; exact s5_68_safe
  · subst z; exact s5_503_safe
  · subst z; exact s5_76_safe
  · subst z; exact s5_219_safe
  · subst z; exact s5_52_safe
def s4_25 : State := ⟨[1,4,64,146], 89204682205957097258460245303862830288666902, 1, 1, 1, 0⟩
theorem s4_25_edges : next config 4 s4_25 = [s5_526, s5_220] := by decide
theorem s4_25_safe : Safe 9 4 s4_25 := by
  apply safe_succ 8 4 s4_25 [s5_526, s5_220] (by decide) s4_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_526_safe
  · subst z; exact s5_220_safe
def s4_26 : State := ⟨[1,4,64,146], 89204682205957097258460503558279862222389526, 2, 2, 1, 0⟩
theorem s4_26_edges : next config 4 s4_26 = [s5_221] := by decide
theorem s4_26_safe : Safe 9 4 s4_26 := by
  apply safe_succ 8 4 s4_26 [s5_221] (by decide) s4_26_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_221_safe
def s4_27 : State := ⟨[1,4,64,146], 89207404464892464766167915407234137015255318, 1, 1, 1, 0⟩
theorem s4_27_edges : next config 4 s4_27 = [s5_527, s5_223] := by decide
theorem s4_27_safe : Safe 9 4 s4_27 := by
  apply safe_succ 8 4 s4_27 [s5_527, s5_223] (by decide) s4_27_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_527_safe
  · subst z; exact s5_223_safe
def s4_28 : State := ⟨[1,4,64,146], 111504066275020036646142073184593317302698270, 1, 1, 1, 0⟩
theorem s4_28_edges : next config 4 s4_28 = [s5_528, s5_224] := by decide
theorem s4_28_safe : Safe 9 4 s4_28 := by
  apply safe_succ 8 4 s4_28 [s5_528, s5_224] (by decide) s4_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_528_safe
  · subst z; exact s5_224_safe
def s4_29 : State := ⟨[1,4,64,146], 111504066275020036646142073184593317302702358, 2, 2, 1, 0⟩
theorem s4_29_edges : next config 4 s4_29 = [s5_1370, s5_791, s5_69, s5_504, s5_77, s5_225, s5_53] := by decide
theorem s4_29_safe : Safe 9 4 s4_29 := by
  apply safe_succ 8 4 s4_29 [s5_1370, s5_791, s5_69, s5_504, s5_77, s5_225, s5_53] (by decide) s4_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1370_safe
  · subst z; exact s5_791_safe
  · subst z; exact s5_69_safe
  · subst z; exact s5_504_safe
  · subst z; exact s5_77_safe
  · subst z; exact s5_225_safe
  · subst z; exact s5_53_safe
def s4_30 : State := ⟨[1,4,64,146], 111504066275020036646142110078081464721801494, 1, 1, 1, 0⟩
theorem s4_30_edges : next config 4 s4_30 = [s5_529, s5_226] := by decide
theorem s4_30_safe : Safe 9 4 s4_30 := by
  apply safe_succ 8 4 s4_30 [s5_529, s5_226] (by decide) s4_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_529_safe
  · subst z; exact s5_226_safe
def s4_31 : State := ⟨[1,4,64,146], 111504066275020036646142368332498496655524118, 2, 2, 1, 0⟩
theorem s4_31_edges : next config 4 s4_31 = [s5_227] := by decide
theorem s4_31_safe : Safe 9 4 s4_31 := by
  apply safe_succ 8 4 s4_31 [s5_227] (by decide) s4_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_227_safe
def s4_32 : State := ⟨[1,4,64,146], 1516452374911916978316746177859869819252310294, 2, 2, 1, 0⟩
theorem s4_32_edges : next config 4 s4_32 = [s5_229] := by decide
theorem s4_32_safe : Safe 9 4 s4_32 := by
  apply safe_succ 8 4 s4_32 [s5_229] (by decide) s4_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_229_safe
def s4_33 : State := ⟨[1,4,64,146], 1538751758980979917704428042634088453685444886, 2, 2, 1, 0⟩
theorem s4_33_edges : next config 4 s4_33 = [s5_230] := by decide
theorem s4_33_safe : Safe 9 4 s4_33 := by
  apply safe_succ 8 4 s4_33 [s5_230] (by decide) s4_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_230_safe
def s4_34 : State := ⟨[1,4,64,161], 2923003275682652937170185055841136605685174309142, 2, 2, 1, 0⟩
theorem s4_34_edges : next config 4 s4_34 = [s5_231, s5_35] := by decide
theorem s4_34_safe : Safe 9 4 s4_34 := by
  apply safe_succ 8 4 s4_34 [s5_231, s5_35] (by decide) s4_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_231_safe
  · subst z; exact s5_35_safe
def s4_35 : State := ⟨[1,4,64,161], 4384504912332991121531992961630670410477570429206, 2, 2, 1, 0⟩
theorem s4_35_edges : next config 4 s4_35 = [s5_232, s5_36] := by decide
theorem s4_35_safe : Safe 9 4 s4_35 := by
  apply safe_succ 8 4 s4_35 [s5_232, s5_36] (by decide) s4_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_232_safe
  · subst z; exact s5_36_safe
def s4_36 : State := ⟨[1,4,64,162], 5846006551025023507419431648200451859860575813918, 1, 1, 1, 0⟩
theorem s4_36_edges : next config 4 s4_36 = [s5_530, s5_233] := by decide
theorem s4_36_safe : Safe 9 4 s4_36 := by
  apply safe_succ 8 4 s4_36 [s5_530, s5_233] (by decide) s4_36_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_530_safe
  · subst z; exact s5_233_safe
def s4_37 : State := ⟨[1,4,64,162], 5846006551025023507419431648200451859860575814422, 1, 1, 1, 0⟩
theorem s4_37_edges : next config 4 s4_37 = [s5_234] := by decide
theorem s4_37_safe : Safe 9 4 s4_37 := by
  apply safe_succ 8 4 s4_37 [s5_234] (by decide) s4_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_234_safe
def s4_38 : State := ⟨[1,4,64,162], 5846006551025023507419431648200451859860575818006, 2, 2, 1, 0⟩
theorem s4_38_edges : next config 4 s4_38 = [s5_1371, s5_1565, s5_792, s5_70, s5_78, s5_235, s5_37] := by decide
theorem s4_38_safe : Safe 9 4 s4_38 := by
  apply safe_succ 8 4 s4_38 [s5_1371, s5_1565, s5_792, s5_70, s5_78, s5_235, s5_37] (by decide) s4_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1371_safe
  · subst z; exact s5_1565_safe
  · subst z; exact s5_792_safe
  · subst z; exact s5_70_safe
  · subst z; exact s5_78_safe
  · subst z; exact s5_235_safe
  · subst z; exact s5_37_safe
def s4_39 : State := ⟨[1,4,64,162], 5846006551025023507419431648237345348007994917142, 1, 1, 1, 0⟩
theorem s4_39_edges : next config 4 s4_39 = [s5_531, s5_236] := by decide
theorem s4_39_safe : Safe 9 4 s4_39 := by
  apply safe_succ 8 4 s4_39 [s5_531, s5_236] (by decide) s4_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_531_safe
  · subst z; exact s5_236_safe
def s4_40 : State := ⟨[1,4,64,162], 5846006553747282442786939355907448719314721505558, 1, 1, 1, 0⟩
theorem s4_40_edges : next config 4 s4_40 = [s5_532, s5_239] := by decide
theorem s4_40_safe : Safe 9 4 s4_40 := by
  apply safe_succ 8 4 s4_40 [s5_532, s5_239] (by decide) s4_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_532_safe
  · subst z; exact s5_239_safe
def s4_41 : State := ⟨[1,4,64,162], 7307508186994796957939362627063236449789435511070, 1, 1, 1, 0⟩
theorem s4_41_edges : next config 4 s4_41 = [s5_533, s5_240] := by decide
theorem s4_41_safe : Safe 9 4 s4_41 := by
  apply safe_succ 8 4 s4_41 [s5_533, s5_240] (by decide) s4_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_533_safe
  · subst z; exact s5_240_safe
def s4_42 : State := ⟨[1,4,64,162], 7307508186994796957939362627063236449789435511574, 1, 1, 1, 0⟩
theorem s4_42_edges : next config 4 s4_42 = [s5_241] := by decide
theorem s4_42_safe : Safe 9 4 s4_42 := by
  apply safe_succ 8 4 s4_42 [s5_241] (by decide) s4_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_241_safe
def s4_43 : State := ⟨[1,4,64,162], 7307508186994796957939362627063236449789435515158, 2, 2, 1, 0⟩
theorem s4_43_edges : next config 4 s4_43 = [s5_1372, s5_1566, s5_793, s5_71, s5_79, s5_242, s5_38] := by decide
theorem s4_43_safe : Safe 9 4 s4_43 := by
  apply safe_succ 8 4 s4_43 [s5_1372, s5_1566, s5_793, s5_71, s5_79, s5_242, s5_38] (by decide) s4_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1372_safe
  · subst z; exact s5_1566_safe
  · subst z; exact s5_793_safe
  · subst z; exact s5_71_safe
  · subst z; exact s5_79_safe
  · subst z; exact s5_242_safe
  · subst z; exact s5_38_safe
def s4_44 : State := ⟨[1,4,64,162], 7307508186994796957939362627100129937936854614294, 1, 1, 1, 0⟩
theorem s4_44_edges : next config 4 s4_44 = [s5_534, s5_243] := by decide
theorem s4_44_safe : Safe 9 4 s4_44 := by
  apply safe_succ 8 4 s4_44 [s5_534, s5_243] (by decide) s4_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_534_safe
  · subst z; exact s5_243_safe
def s4_45 : State := ⟨[1,4,64,162], 17538019649672246853048910309930716017108036157718, 1, 1, 1, 0⟩
theorem s4_45_edges : next config 4 s4_45 = [s5_535, s5_246] := by decide
theorem s4_45_safe : Safe 9 4 s4_45 := by
  apply safe_succ 8 4 s4_45 [s5_535, s5_246] (by decide) s4_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_535_safe
  · subst z; exact s5_246_safe
def s4_46 : State := ⟨[1,4,64,162], 18999521285642020303568841288793500607036895854870, 1, 1, 1, 0⟩
theorem s4_46_edges : next config 4 s4_46 = [s5_536, s5_247] := by decide
theorem s4_46_safe : Safe 9 4 s4_46 := by
  apply safe_succ 8 4 s4_46 [s5_536, s5_247] (by decide) s4_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_536_safe
  · subst z; exact s5_247_safe
def s4_47 : State := ⟨[1,4,64,163], 11692013100348635180234170979065583938492895920406, 1, 1, 1, 0⟩
theorem s4_47_edges : next config 4 s4_47 = [s5_537, s5_248, s5_43] := by decide
theorem s4_47_safe : Safe 9 4 s4_47 := by
  apply safe_succ 8 4 s4_47 [s5_537, s5_248, s5_43] (by decide) s4_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_537_safe
  · subst z; exact s5_248_safe
  · subst z; exact s5_43_safe
def s4_48 : State := ⟨[1,4,64,163], 11692013101709764647917924832919082368211378831646, 1, 1, 1, 0⟩
theorem s4_48_edges : next config 4 s4_48 = [s5_538, s5_249, s5_44] := by decide
theorem s4_48_safe : Safe 9 4 s4_48 := by
  apply safe_succ 8 4 s4_48 [s5_538, s5_249, s5_44] (by decide) s4_48_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_538_safe
  · subst z; exact s5_249_safe
  · subst z; exact s5_44_safe
def s4_49 : State := ⟨[1,4,64,163], 13153514736318408630754101957928368528413165682974, 1, 1, 1, 0⟩
theorem s4_49_edges : next config 4 s4_49 = [s5_539, s5_250, s5_45] := by decide
theorem s4_49_safe : Safe 9 4 s4_49 := by
  apply safe_succ 8 4 s4_49 [s5_539, s5_250, s5_45] (by decide) s4_49_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_539_safe
  · subst z; exact s5_250_safe
  · subst z; exact s5_45_safe
def s4_50 : State := ⟨[1,4,64,163], 14615016373649311548957786790644651548077688160534, 1, 1, 1, 0⟩
theorem s4_50_edges : next config 4 s4_50 = [s5_540, s5_251, s5_46] := by decide
theorem s4_50_safe : Safe 9 4 s4_50 := by
  apply safe_succ 8 4 s4_50 [s5_540, s5_251, s5_46] (by decide) s4_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_540_safe
  · subst z; exact s5_251_safe
  · subst z; exact s5_46_safe
def s4_51 : State := ⟨[1,4,64,171], 3004847366356079505862906339162793455838424763269398, 0, 0, 1, 0⟩
theorem s4_51_edges : next config 4 s4_51 = [s5_252] := by decide
theorem s4_51_safe : Safe 9 4 s4_51 := by
  apply safe_succ 8 4 s4_51 [s5_252] (by decide) s4_51_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_252_safe
def s4_52 : State := ⟨[1,4,64,171], 3004847366356760070596748216089720205053288299692310, 0, 0, 1, 0⟩
theorem s4_52_edges : next config 4 s4_52 = [s5_253] := by decide
theorem s4_52_safe : Safe 9 4 s4_52 := by
  apply safe_succ 8 4 s4_52 [s5_253] (by decide) s4_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_253_safe
def s4_53 : State := ⟨[1,4,64,171], 3007770369628019052763946201120519025018282482663702, 0, 0, 1, 0⟩
theorem s4_53_edges : next config 4 s4_53 = [s5_254] := by decide
theorem s4_53_safe : Safe 9 4 s4_53 := by
  apply safe_succ 8 4 s4_53 [s5_254] (by decide) s4_53_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_254_safe
def s4_54 : State := ⟨[1,4,64,171], 3009231871264669390948308009026308558823074878783766, 0, 0, 1, 0⟩
theorem s4_54_edges : next config 4 s4_54 = [s5_255] := by decide
theorem s4_54_safe : Safe 9 4 s4_54 := by
  apply safe_succ 8 4 s4_54 [s5_255] (by decide) s4_54_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_255_safe
def s4_55 : State := ⟨[1,4,64,171], 3010693372903361423334195447712878340272457884172566, 0, 0, 1, 0⟩
theorem s4_55_edges : next config 4 s4_55 = [s5_256] := by decide
theorem s4_55_safe : Safe 9 4 s4_55 := by
  apply safe_succ 8 4 s4_55 [s5_256] (by decide) s4_55_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_256_safe
def s4_56 : State := ⟨[1,4,64,171], 3012154874539331196784715378691741124862386743869718, 0, 0, 1, 0⟩
theorem s4_56_edges : next config 4 s4_56 = [s5_257] := by decide
theorem s4_56_safe : Safe 9 4 s4_56 := by
  apply safe_succ 8 4 s4_56 [s5_257] (by decide) s4_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_257_safe
def s4_57 : State := ⟨[1,4,64,171], 4495579036431558788229139237752621888242885347836182, 0, 0, 1, 0⟩
theorem s4_57_edges : next config 4 s4_57 = [s5_258] := by decide
theorem s4_57_safe : Safe 9 4 s4_57 := by
  apply safe_succ 8 4 s4_57 [s5_258] (by decide) s4_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_258_safe
def s4_58 : State := ⟨[1,4,64,171], 4497040538067528561679659168731484672832814207533334, 0, 0, 1, 0⟩
theorem s4_58_edges : next config 4 s4_58 = [s5_259] := by decide
theorem s4_58_safe : Safe 9 4 s4_58 := by
  apply safe_succ 8 4 s4_58 [s5_259] (by decide) s4_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_259_safe
def s4_59 : State := ⟨[1,4,64,176], 95780971326419139128294233276893524070171066415251742, 1, 1, 1, 0⟩
theorem s4_59_edges : next config 4 s4_59 = [s5_541, s5_260] := by decide
theorem s4_59_safe : Safe 9 4 s4_59 := by
  apply safe_succ 8 4 s4_59 [s5_541, s5_260] (by decide) s4_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_541_safe
  · subst z; exact s5_260_safe
def s4_60 : State := ⟨[1,4,64,176], 95780971326419139128294233276893524070171066415255830, 2, 2, 1, 0⟩
theorem s4_60_edges : next config 4 s4_60 = [s5_1373, s5_796, s5_72, s5_80, s5_261] := by decide
theorem s4_60_safe : Safe 9 4 s4_60 := by
  apply safe_succ 8 4 s4_60 [s5_1373, s5_796, s5_72, s5_80, s5_261] (by decide) s4_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1373_safe
  · subst z; exact s5_796_safe
  · subst z; exact s5_72_safe
  · subst z; exact s5_80_safe
  · subst z; exact s5_261_safe
def s4_61 : State := ⟨[1,4,64,176], 95780971326419139128294233276893560963659213834354966, 1, 1, 1, 0⟩
theorem s4_61_edges : next config 4 s4_61 = [s5_542, s5_262] := by decide
theorem s4_61_safe : Safe 9 4 s4_61 := by
  apply safe_succ 8 4 s4_61 [s5_542, s5_262] (by decide) s4_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_542_safe
  · subst z; exact s5_262_safe
def s4_62 : State := ⟨[1,4,64,176], 95782432805755724832681813820190522080542360841814302, 1, 1, 1, 0⟩
theorem s4_62_edges : next config 4 s4_62 = [s5_543, s5_264] := by decide
theorem s4_62_safe : Safe 9 4 s4_62 := by
  apply safe_succ 8 4 s4_62 [s5_543, s5_264] (by decide) s4_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_543_safe
  · subst z; exact s5_264_safe
def s4_63 : State := ⟨[1,4,64,176], 95782432805755724832681813820190522080542360841818390, 2, 2, 1, 0⟩
theorem s4_63_edges : next config 4 s4_63 = [s5_1374, s5_797, s5_73, s5_81, s5_265] := by decide
theorem s4_63_safe : Safe 9 4 s4_63 := by
  apply safe_succ 8 4 s4_63 [s5_1374, s5_797, s5_73, s5_81, s5_265] (by decide) s4_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1374_safe
  · subst z; exact s5_797_safe
  · subst z; exact s5_73_safe
  · subst z; exact s5_81_safe
  · subst z; exact s5_265_safe
def s4_64 : State := ⟨[1,4,64,176], 95782432805755724832681813820190558974030508260917526, 1, 1, 1, 0⟩
theorem s4_64_edges : next config 4 s4_64 = [s5_544, s5_266] := by decide
theorem s4_64_safe : Safe 9 4 s4_64 := by
  apply safe_succ 8 4 s4_64 [s5_544, s5_266] (by decide) s4_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_544_safe
  · subst z; exact s5_266_safe
def s4_65 : State := ⟨[1,4,64,193], 12554203470773361528692425947178148222613281455301378248982, 2, 2, 1, 0⟩
theorem s4_65_edges : next config 4 s4_65 = [s5_268] := by decide
theorem s4_65_safe : Safe 9 4 s4_65 := by
  apply safe_succ 8 4 s4_65 [s5_268] (by decide) s4_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_268_safe
def s4_66 : State := ⟨[1,4,64,193], 18831305206160042291847650636543937711788887684901876338966, 2, 2, 1, 0⟩
theorem s4_66_edges : next config 4 s4_66 = [s5_270] := by decide
theorem s4_66_safe : Safe 9 4 s4_66 := by
  apply safe_succ 8 4 s4_66 [s5_270] (by decide) s4_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_270_safe
def s4_67 : State := ⟨[1,4,64,194], 25108406941546723057044569527435357981744741559092983697686, 2, 2, 1, 0⟩
theorem s4_67_edges : next config 4 s4_67 = [s5_272, s5_54] := by decide
theorem s4_67_safe : Safe 9 4 s4_67 := by
  apply safe_succ 8 4 s4_67 [s5_272, s5_54] (by decide) s4_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_272_safe
  · subst z; exact s5_54_safe
def s4_68 : State := ⟨[1,4,64,194], 31385508676933403819519229482959270543993598573829945364758, 2, 2, 1, 0⟩
theorem s4_68_edges : next config 4 s4_68 = [s5_274, s5_55] := by decide
theorem s4_68_safe : Safe 9 4 s4_68 := by
  apply safe_succ 8 4 s4_68 [s5_274, s5_55] (by decide) s4_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_274_safe
  · subst z; exact s5_55_safe
def s4_69 : State := ⟨[1,4,64,208], 411376139330301510561043381120235170325683166502394837115932950, 2, 2, 1, 0⟩
theorem s4_69_edges : next config 4 s4_69 = [s5_276, s5_56] := by decide
theorem s4_69_safe : Safe 9 4 s4_69 := by
  apply safe_succ 8 4 s4_69 [s5_276, s5_56] (by decide) s4_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_276_safe
  · subst z; exact s5_56_safe
def s4_70 : State := ⟨[1,4,64,208], 411382416432036897219506471711127754850563550585190939644465430, 2, 2, 1, 0⟩
theorem s4_70_edges : next config 4 s4_70 = [s5_277, s5_57] := by decide
theorem s4_70_safe : Safe 9 4 s4_70 := by
  apply safe_succ 8 4 s4_70 [s5_277, s5_57] (by decide) s4_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_277_safe
  · subst z; exact s5_57_safe
def s4_71 : State := ⟨[1,4,64,214], 26328072917139296675995959295829525058040520027997147632830054678, 0, 0, 1, 0⟩
theorem s4_71_edges : next config 4 s4_71 = [s5_278] := by decide
theorem s4_71_safe : Safe 9 4 s4_71 := by
  apply safe_succ 8 4 s4_71 [s5_278] (by decide) s4_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_278_safe
def s4_72 : State := ⟨[1,4,64,214], 26328072917139296676018258679898587997428201892771366267263189270, 0, 0, 1, 0⟩
theorem s4_72_edges : next config 4 s4_72 = [s5_279] := by decide
theorem s4_72_safe : Safe 9 4 s4_72 := by
  apply safe_succ 8 4 s4_72 [s5_279] (by decide) s4_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_279_safe
def s4_73 : State := ⟨[1,4,64,214], 27973577474460502716723680785680915681964969924181232359795917078, 0, 0, 1, 0⟩
theorem s4_73_edges : next config 4 s4_73 = [s5_280] := by decide
theorem s4_73_safe : Safe 9 4 s4_73 := by
  apply safe_succ 8 4 s4_73 [s5_280] (by decide) s4_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_280_safe
def s4_74 : State := ⟨[1,4,64,214], 27973577474460502716745980169749978621352651788955450994229051670, 0, 0, 1, 0⟩
theorem s4_74_edges : next config 4 s4_74 = [s5_281] := by decide
theorem s4_74_safe : Safe 9 4 s4_74 := by
  apply safe_succ 8 4 s4_74 [s5_281] (by decide) s4_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_281_safe
def s4_75 : State := ⟨[1,4,64,214], 27973602582867444263357533148044486020064491460512416769910046998, 0, 0, 1, 0⟩
theorem s4_75_edges : next config 4 s4_75 = [s5_282] := by decide
theorem s4_75_safe : Safe 9 4 s4_75 := by
  apply safe_succ 8 4 s4_75 [s5_282] (by decide) s4_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_282_safe
def s4_76 : State := ⟨[1,4,64,214], 27973608859969179650038295622704441543977053709369431506871714070, 0, 0, 1, 0⟩
theorem s4_76_edges : next config 4 s4_76 = [s5_283] := by decide
theorem s4_76_safe : Safe 9 4 s4_76 := by
  apply safe_succ 8 4 s4_76 [s5_283] (by decide) s4_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_283_safe
def s4_77 : State := ⟨[1,4,64,214], 28384953613790804227195519484595193755032192882273252514042282262, 0, 0, 1, 0⟩
theorem s4_77_edges : next config 4 s4_77 = [s5_284] := by decide
theorem s4_77_safe : Safe 9 4 s4_77 := by
  apply safe_succ 8 4 s4_77 [s5_284] (by decide) s4_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_284_safe
def s4_78 : State := ⟨[1,4,64,214], 28384959890892539613853982575186086339557073266356048616570814742, 0, 0, 1, 0⟩
theorem s4_78_edges : next config 4 s4_78 = [s5_285] := by decide
theorem s4_78_safe : Safe 9 4 s4_78 := by
  apply safe_succ 8 4 s4_78 [s5_285] (by decide) s4_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_285_safe
def s4_79 : State := ⟨[1,4,65,129], 1020847100762815390445464054520728326422, 2, 2, 1, 0⟩
theorem s4_79_edges : next config 4 s4_79 = [s5_87, s5_66] := by decide
theorem s4_79_safe : Safe 9 4 s4_79 := by
  apply safe_succ 8 4 s4_79 [s5_87, s5_66] (by decide) s4_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_87_safe
  · subst z; exact s5_66_safe
def s4_80 : State := ⟨[1,4,65,130], 1701411834604692317372213269384264749334, 2, 2, 1, 0⟩
theorem s4_80_edges : next config 4 s4_80 = [s5_89, s5_68, s5_70] := by decide
theorem s4_80_safe : Safe 9 4 s4_80 := by
  apply safe_succ 8 4 s4_80 [s5_89, s5_68, s5_70] (by decide) s4_80_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_89_safe
  · subst z; exact s5_68_safe
  · subst z; exact s5_70_safe
def s4_81 : State := ⟨[1,4,65,132], 5784800237655953878932708558565483286806, 2, 2, 1, 0⟩
theorem s4_81_edges : next config 4 s4_81 = [s5_91] := by decide
theorem s4_81_safe : Safe 9 4 s4_81 := by
  apply safe_succ 8 4 s4_81 [s5_91] (by decide) s4_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_91_safe
def s4_82 : State := ⟨[1,4,65,136], 87452568298681185110142614342189854036246, 2, 2, 1, 0⟩
theorem s4_82_edges : next config 4 s4_82 = [s5_93] := by decide
theorem s4_82_safe : Safe 9 4 s4_82 := by
  apply safe_succ 8 4 s4_82 [s5_93] (by decide) s4_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_93_safe
def s4_83 : State := ⟨[1,4,65,136], 1481249143206845131456125006382712448155926, 2, 2, 1, 0⟩
theorem s4_83_edges : next config 4 s4_83 = [s5_95] := by decide
theorem s4_83_safe : Safe 9 4 s4_83 := by
  apply safe_succ 8 4 s4_83 [s5_95] (by decide) s4_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_95_safe
def s4_84 : State := ⟨[1,4,65,140], 1394136857275084884809501106880179786027286, 2, 2, 1, 0⟩
theorem s4_84_edges : next config 4 s4_84 = [s5_97] := by decide
theorem s4_84_safe : Safe 9 4 s4_84 := by
  apply safe_succ 8 4 s4_84 [s5_97] (by decide) s4_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_97_safe
def s4_85 : State := ⟨[1,4,65,144], 22301085480897544079999236987488018697883926, 2, 2, 1, 0⟩
theorem s4_85_edges : next config 4 s4_85 = [s5_101, s5_67, s5_69, s5_72] := by decide
theorem s4_85_safe : Safe 9 4 s4_85 := by
  apply safe_succ 8 4 s4_85 [s5_101, s5_67, s5_69, s5_72] (by decide) s4_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_101_safe
  · subst z; exact s5_67_safe
  · subst z; exact s5_69_safe
  · subst z; exact s5_72_safe
def s4_86 : State := ⟨[1,4,65,145], 44601830679428167221534955260136380203991318, 1, 1, 1, 0⟩
theorem s4_86_edges : next config 4 s4_86 = [s5_545, s5_103] := by decide
theorem s4_86_safe : Safe 9 4 s4_86 := by
  apply safe_succ 8 4 s4_86 [s5_545, s5_103] (by decide) s4_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_545_safe
  · subst z; exact s5_103_safe
def s4_87 : State := ⟨[1,4,65,160], 1461501637671185285124623296234997859313124446486, 2, 2, 1, 0⟩
theorem s4_87_edges : next config 4 s4_87 = [s5_112, s5_71, s5_73] := by decide
theorem s4_87_safe : Safe 9 4 s4_87 := by
  apply safe_succ 8 4 s4_87 [s5_112, s5_71, s5_73] (by decide) s4_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_112_safe
  · subst z; exact s5_71_safe
  · subst z; exact s5_73_safe
def s4_88 : State := ⟨[1,4,65,192], 6277101735386680764176071790128604879621070284121226416406, 2, 2, 1, 0⟩
theorem s4_88_edges : next config 4 s4_88 = [s5_120] := by decide
theorem s4_88_safe : Safe 9 4 s4_88 := by
  apply safe_succ 8 4 s4_88 [s5_120] (by decide) s4_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_120_safe
def s4_89 : State := ⟨[1,4,65,193], 12554203470773361528011861213336271295723425728585260929302, 2, 2, 1, 0⟩
theorem s4_89_edges : next config 4 s4_89 = [s5_122] := by decide
theorem s4_89_safe : Safe 9 4 s4_89 := by
  apply safe_succ 8 4 s4_89 [s5_122] (by decide) s4_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_122_safe
def s4_90 : State := ⟨[1,4,66,129], 1020847100762815390482357542668147429654, 2, 2, 1, 0⟩
theorem s4_90_edges : next config 4 s4_90 = [s5_88, s5_134, s5_74] := by decide
theorem s4_90_safe : Safe 9 4 s4_90 := by
  apply safe_succ 8 4 s4_90 [s5_88, s5_134, s5_74] (by decide) s4_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_88_safe
  · subst z; exact s5_134_safe
  · subst z; exact s5_74_safe
def s4_91 : State := ⟨[1,4,66,130], 1701411834604692317409106757531683852566, 2, 2, 1, 0⟩
theorem s4_91_edges : next config 4 s4_91 = [s5_90, s5_138, s5_76, s5_78] := by decide
theorem s4_91_safe : Safe 9 4 s4_91 := by
  apply safe_succ 8 4 s4_91 [s5_90, s5_138, s5_76, s5_78] (by decide) s4_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_90_safe
  · subst z; exact s5_138_safe
  · subst z; exact s5_76_safe
  · subst z; exact s5_78_safe
def s4_92 : State := ⟨[1,4,66,132], 5784800237655953878969602046712902390038, 2, 2, 1, 0⟩
theorem s4_92_edges : next config 4 s4_92 = [s5_92, s5_142] := by decide
theorem s4_92_safe : Safe 9 4 s4_92 := by
  apply safe_succ 8 4 s4_92 [s5_92, s5_142] (by decide) s4_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_92_safe
  · subst z; exact s5_142_safe
def s4_93 : State := ⟨[1,4,66,136], 87452568298681185110179507830337273139478, 2, 2, 1, 0⟩
theorem s4_93_edges : next config 4 s4_93 = [s5_94, s5_146] := by decide
theorem s4_93_safe : Safe 9 4 s4_93 := by
  apply safe_succ 8 4 s4_93 [s5_94, s5_146] (by decide) s4_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_94_safe
  · subst z; exact s5_146_safe
def s4_94 : State := ⟨[1,4,66,136], 1481249143206845131456161899870859867259158, 2, 2, 1, 0⟩
theorem s4_94_edges : next config 4 s4_94 = [s5_96, s5_150] := by decide
theorem s4_94_safe : Safe 9 4 s4_94 := by
  apply safe_succ 8 4 s4_94 [s5_96, s5_150] (by decide) s4_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_96_safe
  · subst z; exact s5_150_safe
def s4_95 : State := ⟨[1,4,66,140], 1394136857275084884809538000368327205130518, 2, 2, 1, 0⟩
theorem s4_95_edges : next config 4 s4_95 = [s5_98, s5_152] := by decide
theorem s4_95_safe : Safe 9 4 s4_95 := by
  apply safe_succ 8 4 s4_95 [s5_98, s5_152] (by decide) s4_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_98_safe
  · subst z; exact s5_152_safe
def s4_96 : State := ⟨[1,4,66,144], 22301085480897544079999273880976166116987158, 2, 2, 1, 0⟩
theorem s4_96_edges : next config 4 s4_96 = [s5_102, s5_499, s5_154, s5_75, s5_82, s5_77, s5_80] := by decide
theorem s4_96_safe : Safe 9 4 s4_96 := by
  apply safe_succ 8 4 s4_96 [s5_102, s5_499, s5_154, s5_75, s5_82, s5_77, s5_80] (by decide) s4_96_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_102_safe
  · subst z; exact s5_499_safe
  · subst z; exact s5_154_safe
  · subst z; exact s5_75_safe
  · subst z; exact s5_82_safe
  · subst z; exact s5_77_safe
  · subst z; exact s5_80_safe
def s4_97 : State := ⟨[1,4,66,145], 44601830679428167221534992153624527623094550, 1, 1, 1, 0⟩
theorem s4_97_edges : next config 4 s4_97 = [s5_546, s5_104, s5_158] := by decide
theorem s4_97_safe : Safe 9 4 s4_97 := by
  apply safe_succ 8 4 s4_97 [s5_546, s5_104, s5_158] (by decide) s4_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_546_safe
  · subst z; exact s5_104_safe
  · subst z; exact s5_158_safe
def s4_98 : State := ⟨[1,4,66,160], 1461501637671185285124623296271891347460543549718, 2, 2, 1, 0⟩
theorem s4_98_edges : next config 4 s4_98 = [s5_113, s5_160, s5_79, s5_81] := by decide
theorem s4_98_safe : Safe 9 4 s4_98 := by
  apply safe_succ 8 4 s4_98 [s5_113, s5_160, s5_79, s5_81] (by decide) s4_98_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_113_safe
  · subst z; exact s5_160_safe
  · subst z; exact s5_79_safe
  · subst z; exact s5_81_safe
def s4_99 : State := ⟨[1,4,66,192], 6277101735386680764176071790128604879657963772268645519638, 2, 2, 1, 0⟩
theorem s4_99_edges : next config 4 s4_99 = [s5_121, s5_164] := by decide
theorem s4_99_safe : Safe 9 4 s4_99 := by
  apply safe_succ 8 4 s4_99 [s5_121, s5_164] (by decide) s4_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_121_safe
  · subst z; exact s5_164_safe
def s4_100 : State := ⟨[1,4,66,194], 25108406941546723055683440059751604127965030105660749058326, 2, 2, 1, 0⟩
theorem s4_100_edges : next config 4 s4_100 = [s5_123, s5_168, s5_83] := by decide
theorem s4_100_safe : Safe 9 4 s4_100 := by
  apply safe_succ 8 4 s4_100 [s5_123, s5_168, s5_83] (by decide) s4_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_123_safe
  · subst z; exact s5_168_safe
  · subst z; exact s5_83_safe
def s4_101 : State := ⟨[1,4,66,214], 27973577474460502716656777188955856128786508989651833843043336470, 0, 0, 1, 0⟩
theorem s4_101_edges : next config 4 s4_101 = [s5_126] := by decide
theorem s4_101_safe : Safe 9 4 s4_101 := by
  apply safe_succ 8 4 s4_101 [s5_126] (by decide) s4_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_126_safe
def s4_102 : State := ⟨[1,4,66,214], 27973602582867444263357531786915018336310637680800963337675407638, 0, 0, 1, 0⟩
theorem s4_102_edges : next config 4 s4_102 = [s5_127] := by decide
theorem s4_102_safe : Safe 9 4 s4_102 := by
  apply safe_succ 8 4 s4_102 [s5_127] (by decide) s4_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_127_safe
def s4_103 : State := ⟨[1,4,67,128], 340282366920938463666288792246868316438, 2, 2, 0, 0⟩
theorem s4_103_edges : next config 4 s4_103 = [s5_957, s5_87, s5_91, s5_124, s5_89, s5_93, s5_101, s5_112] := by decide
theorem s4_103_safe : Safe 9 4 s4_103 := by
  apply safe_succ 8 4 s4_103 [s5_957, s5_87, s5_91, s5_124, s5_89, s5_93, s5_101, s5_112] (by decide) s4_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_957_safe
  · subst z; exact s5_87_safe
  · subst z; exact s5_91_safe
  · subst z; exact s5_124_safe
  · subst z; exact s5_89_safe
  · subst z; exact s5_93_safe
  · subst z; exact s5_101_safe
  · subst z; exact s5_112_safe
def s4_104 : State := ⟨[1,4,67,128], 340282366920938463703182280394287419670, 2, 2, 0, 0⟩
theorem s4_104_edges : next config 4 s4_104 = [s5_959, s5_88, s5_92, s5_125, s5_90, s5_94, s5_102, s5_113] := by decide
theorem s4_104_safe : Safe 9 4 s4_104 := by
  apply safe_succ 8 4 s4_104 [s5_959, s5_88, s5_92, s5_125, s5_90, s5_94, s5_102, s5_113] (by decide) s4_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_959_safe
  · subst z; exact s5_88_safe
  · subst z; exact s5_92_safe
  · subst z; exact s5_125_safe
  · subst z; exact s5_90_safe
  · subst z; exact s5_94_safe
  · subst z; exact s5_102_safe
  · subst z; exact s5_113_safe
def s4_105 : State := ⟨[1,4,67,129], 1020847100762815390556144518962985632030, 1, 1, 1, 0⟩
theorem s4_105_edges : next config 4 s4_105 = [s5_547, s5_105] := by decide
theorem s4_105_safe : Safe 9 4 s4_105 := by
  apply safe_succ 8 4 s4_105 [s5_547, s5_105] (by decide) s4_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_547_safe
  · subst z; exact s5_105_safe
def s4_106 : State := ⟨[1,4,67,130], 1701411834604692317482893733826522054942, 1, 1, 1, 0⟩
theorem s4_106_edges : next config 4 s4_106 = [s5_548, s5_110, s5_114] := by decide
theorem s4_106_safe : Safe 9 4 s4_106 := by
  apply safe_succ 8 4 s4_106 [s5_548, s5_110, s5_114] (by decide) s4_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_548_safe
  · subst z; exact s5_110_safe
  · subst z; exact s5_114_safe
def s4_107 : State := ⟨[1,4,67,131], 3062541302288446171336392163553594900766, 1, 1, 1, 0⟩
theorem s4_107_edges : next config 4 s4_107 = [s5_549, s5_116] := by decide
theorem s4_107_safe : Safe 9 4 s4_107 := by
  apply safe_succ 8 4 s4_107 [s5_549, s5_116] (by decide) s4_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_549_safe
  · subst z; exact s5_116_safe
def s4_108 : State := ⟨[1,4,67,132], 5784800237655953879043389023007740592414, 1, 1, 1, 0⟩
theorem s4_108_edges : next config 4 s4_108 = [s5_550, s5_99] := by decide
theorem s4_108_safe : Safe 9 4 s4_108 := by
  apply safe_succ 8 4 s4_108 [s5_550, s5_99] (by decide) s4_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_550_safe
  · subst z; exact s5_99_safe
def s4_109 : State := ⟨[1,4,67,136], 87452568298681185110253294806632111341854, 1, 1, 1, 0⟩
theorem s4_109_edges : next config 4 s4_109 = [s5_765, s5_551, s5_100] := by decide
theorem s4_109_safe : Safe 9 4 s4_109 := by
  apply safe_succ 8 4 s4_109 [s5_765, s5_551, s5_100] (by decide) s4_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_765_safe
  · subst z; exact s5_551_safe
  · subst z; exact s5_100_safe
def s4_110 : State := ⟨[1,4,67,140], 1399581375145819900225062674551677753819414, 0, 0, 1, 0⟩
theorem s4_110_edges : next config 4 s4_110 = [] := by decide
theorem s4_110_safe : Safe 9 4 s4_110 := by
  apply safe_succ 8 4 s4_110 [] (by decide) s4_110_edges
  simp
def s4_111 : State := ⟨[1,4,67,140], 1399581375145819900225099568039825172922646, 0, 0, 1, 0⟩
theorem s4_111_edges : next config 4 s4_111 = [] := by decide
theorem s4_111_safe : Safe 9 4 s4_111 := by
  apply safe_succ 8 4 s4_111 [] (by decide) s4_111_edges
  simp
def s4_112 : State := ⟨[1,4,67,140], 1481249143206845131456272580335302124568854, 0, 0, 1, 0⟩
theorem s4_112_edges : next config 4 s4_112 = [] := by decide
theorem s4_112_safe : Safe 9 4 s4_112 := by
  apply safe_succ 8 4 s4_112 [] (by decide) s4_112_edges
  simp
def s4_113 : State := ⟨[1,4,67,140], 1481249143206845131456309473823449543672086, 0, 0, 1, 0⟩
theorem s4_113_edges : next config 4 s4_113 = [] := by decide
theorem s4_113_safe : Safe 9 4 s4_113 := by
  apply safe_succ 8 4 s4_113 [] (by decide) s4_113_edges
  simp
def s4_114 : State := ⟨[1,4,67,144], 22301085480897544079999347667952460955189534, 1, 1, 1, 0⟩
theorem s4_114_edges : next config 4 s4_114 = [s5_553, s5_106, s5_111, s5_118] := by decide
theorem s4_114_safe : Safe 9 4 s4_114 := by
  apply safe_succ 8 4 s4_114 [s5_553, s5_106, s5_111, s5_118] (by decide) s4_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_553_safe
  · subst z; exact s5_106_safe
  · subst z; exact s5_111_safe
  · subst z; exact s5_118_safe
def s4_115 : State := ⟨[1,4,67,145], 44602511244162009098462029583303833416696086, 0, 0, 1, 0⟩
theorem s4_115_edges : next config 4 s4_115 = [s5_554] := by decide
theorem s4_115_safe : Safe 9 4 s4_115 := by
  apply safe_succ 8 4 s4_115 [s5_554] (by decide) s4_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_554_safe
def s4_116 : State := ⟨[1,4,67,145], 44602511244162009098462066476791980835799318, 0, 0, 1, 0⟩
theorem s4_116_edges : next config 4 s4_116 = [s5_555] := by decide
theorem s4_116_safe : Safe 9 4 s4_116 := by
  apply safe_succ 8 4 s4_116 [s5_555] (by decide) s4_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_555_safe
def s4_117 : State := ⟨[1,4,67,145], 66902575877958790363070821106737331386253590, 0, 0, 1, 0⟩
theorem s4_117_edges : next config 4 s4_117 = [s5_556] := by decide
theorem s4_117_safe : Safe 9 4 s4_117 := by
  apply safe_succ 8 4 s4_117 [s5_556] (by decide) s4_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_556_safe
def s4_118 : State := ⟨[1,4,67,145], 66902575877958790363070858000225478805356822, 0, 0, 1, 0⟩
theorem s4_118_edges : next config 4 s4_118 = [s5_557] := by decide
theorem s4_118_safe : Safe 9 4 s4_118 := by
  apply safe_succ 8 4 s4_118 [s5_557] (by decide) s4_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_557_safe
def s4_119 : State := ⟨[1,4,67,146], 89204682205957097258460392877815419965079830, 0, 0, 1, 0⟩
theorem s4_119_edges : next config 4 s4_119 = [s5_558] := by decide
theorem s4_119_safe : Safe 9 4 s4_119 := by
  apply safe_succ 8 4 s4_119 [s5_558] (by decide) s4_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_558_safe
def s4_120 : State := ⟨[1,4,67,146], 89204682205957097258460429771303567384183062, 0, 0, 1, 0⟩
theorem s4_120_edges : next config 4 s4_120 = [s5_559] := by decide
theorem s4_120_safe : Safe 9 4 s4_120 := by
  apply safe_succ 8 4 s4_120 [s5_559] (by decide) s4_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_559_safe
def s4_121 : State := ⟨[1,4,67,146], 111504066275020036646142257652034054398214422, 0, 0, 1, 0⟩
theorem s4_121_edges : next config 4 s4_121 = [s5_560] := by decide
theorem s4_121_safe : Safe 9 4 s4_121 := by
  apply safe_succ 8 4 s4_121 [s5_560] (by decide) s4_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_560_safe
def s4_122 : State := ⟨[1,4,67,146], 111504066275020036646142294545522201817317654, 0, 0, 1, 0⟩
theorem s4_122_edges : next config 4 s4_122 = [s5_561] := by decide
theorem s4_122_safe : Safe 9 4 s4_122 := by
  apply safe_succ 8 4 s4_122 [s5_561] (by decide) s4_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_561_safe
def s4_123 : State := ⟨[1,4,67,160], 1461501637671185285124623296345678323755381752094, 1, 1, 1, 0⟩
theorem s4_123_edges : next config 4 s4_123 = [s5_562, s5_115, s5_119] := by decide
theorem s4_123_safe : Safe 9 4 s4_123 := by
  apply safe_succ 8 4 s4_123 [s5_562, s5_115, s5_119] (by decide) s4_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_562_safe
  · subst z; exact s5_115_safe
  · subst z; exact s5_119_safe
def s4_124 : State := ⟨[1,4,67,162], 5846006551025023507419431648384919300597671330070, 0, 0, 1, 0⟩
theorem s4_124_edges : next config 4 s4_124 = [s5_563] := by decide
theorem s4_124_safe : Safe 9 4 s4_124 := by
  apply safe_succ 8 4 s4_124 [s5_563] (by decide) s4_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_563_safe
def s4_125 : State := ⟨[1,4,67,162], 5846006551025023507419431648421812788745090433302, 0, 0, 1, 0⟩
theorem s4_125_edges : next config 4 s4_125 = [s5_564] := by decide
theorem s4_125_safe : Safe 9 4 s4_125 := by
  apply safe_succ 8 4 s4_125 [s5_564] (by decide) s4_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_564_safe
def s4_126 : State := ⟨[1,4,67,162], 7307508186994796957939362627247703890526531027222, 0, 0, 1, 0⟩
theorem s4_126_edges : next config 4 s4_126 = [s5_565] := by decide
theorem s4_126_safe : Safe 9 4 s4_126 := by
  apply safe_succ 8 4 s4_126 [s5_565] (by decide) s4_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_565_safe
def s4_127 : State := ⟨[1,4,67,162], 7307508186994796957939362627284597378673950130454, 0, 0, 1, 0⟩
theorem s4_127_edges : next config 4 s4_127 = [s5_566] := by decide
theorem s4_127_safe : Safe 9 4 s4_127 := by
  apply safe_succ 8 4 s4_127 [s5_566] (by decide) s4_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_566_safe
def s4_128 : State := ⟨[1,4,67,176], 95780971326419139128294233276893708537611803510767894, 0, 0, 1, 0⟩
theorem s4_128_edges : next config 4 s4_128 = [s5_567] := by decide
theorem s4_128_safe : Safe 9 4 s4_128 := by
  apply safe_succ 8 4 s4_128 [s5_567] (by decide) s4_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_567_safe
def s4_129 : State := ⟨[1,4,67,176], 95780971326419139128294233276893745431099950929871126, 0, 0, 1, 0⟩
theorem s4_129_edges : next config 4 s4_129 = [s5_568] := by decide
theorem s4_129_safe : Safe 9 4 s4_129 := by
  apply safe_succ 8 4 s4_129 [s5_568] (by decide) s4_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_568_safe
def s4_130 : State := ⟨[1,4,67,176], 95782432805755724832681813820190706547983097937330454, 0, 0, 1, 0⟩
theorem s4_130_edges : next config 4 s4_130 = [s5_569] := by decide
theorem s4_130_safe : Safe 9 4 s4_130 := by
  apply safe_succ 8 4 s4_130 [s5_569] (by decide) s4_130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_569_safe
def s4_131 : State := ⟨[1,4,67,176], 95782432805755724832681813820190743441471245356433686, 0, 0, 1, 0⟩
theorem s4_131_edges : next config 4 s4_131 = [s5_570] := by decide
theorem s4_131_safe : Safe 9 4 s4_131 := by
  apply safe_succ 8 4 s4_131 [s5_570] (by decide) s4_131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_570_safe
def s4_132 : State := ⟨[1,4,67,192], 6277101735386680764176071790128604879731750748563483722014, 1, 1, 1, 0⟩
theorem s4_132_edges : next config 4 s4_132 = [s5_571] := by decide
theorem s4_132_safe : Safe 9 4 s4_132 := by
  apply safe_succ 8 4 s4_132 [s5_571] (by decide) s4_132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_571_safe
def s4_133 : State := ⟨[1,4,67,195], 50216813883093446111026597752582269792448238859811725312286, 1, 1, 1, 0⟩
theorem s4_133_edges : next config 4 s4_133 = [s5_572] := by decide
theorem s4_133_safe : Safe 9 4 s4_133 := by
  apply safe_succ 8 4 s4_133 [s5_572] (by decide) s4_133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_572_safe
def s4_134 : State := ⟨[1,4,67,210], 1645504557321206042177270268038248049062735287088508619142005014, 0, 0, 1, 0⟩
theorem s4_134_edges : next config 4 s4_134 = [s5_772, s5_573, s5_126, s5_107] := by decide
theorem s4_134_safe : Safe 9 4 s4_134 := by
  apply safe_succ 8 4 s4_134 [s5_772, s5_573, s5_126, s5_107] (by decide) s4_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_772_safe
  · subst z; exact s5_573_safe
  · subst z; exact s5_126_safe
  · subst z; exact s5_107_safe
def s4_135 : State := ⟨[1,4,67,210], 1645529665728147588878024865997410256586863978237638113774076182, 0, 0, 1, 0⟩
theorem s4_135_edges : next config 4 s4_135 = [s5_773, s5_574, s5_127, s5_108] := by decide
theorem s4_135_safe : Safe 9 4 s4_135 := by
  apply safe_succ 8 4 s4_135 [s5_773, s5_574, s5_127, s5_108] (by decide) s4_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_773_safe
  · subst z; exact s5_574_safe
  · subst z; exact s5_127_safe
  · subst z; exact s5_108_safe
def s4_136 : State := ⟨[1,4,68,145], 44601830679428167221535213514553412137713942, 1, 1, 1, 0⟩
theorem s4_136_edges : next config 4 s4_136 = [] := by decide
theorem s4_136_safe : Safe 9 4 s4_136 := by
  apply safe_succ 8 4 s4_136 [] (by decide) s4_136_edges
  simp
def s4_137 : State := ⟨[1,4,68,214], 26328072917139296674568711603123565176982234353695557675800133910, 0, 0, 1, 0⟩
theorem s4_137_edges : next config 4 s4_137 = [] := by decide
theorem s4_137_safe : Safe 9 4 s4_137 := by
  apply safe_succ 8 4 s4_137 [] (by decide) s4_137_edges
  simp
def s4_138 : State := ⟨[1,4,68,214], 26328072917139296674591010987192628116369916218469776310233268502, 0, 0, 1, 0⟩
theorem s4_138_edges : next config 4 s4_138 = [] := by decide
theorem s4_138_safe : Safe 9 4 s4_138 := by
  apply safe_succ 8 4 s4_138 [] (by decide) s4_138_edges
  simp
def s4_139 : State := ⟨[1,4,80,129], 1020847100762816599334390181002483929366, 2, 2, 1, 0⟩
theorem s4_139_edges : next config 4 s4_139 = [s5_135, s5_128] := by decide
theorem s4_139_safe : Safe 9 4 s4_139 := by
  apply safe_succ 8 4 s4_139 [s5_135, s5_128] (by decide) s4_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_135_safe
  · subst z; exact s5_128_safe
def s4_140 : State := ⟨[1,4,80,130], 1701411834604693526261139395866020352278, 2, 2, 1, 0⟩
theorem s4_140_edges : next config 4 s4_140 = [s5_495, s5_139, s5_130] := by decide
theorem s4_140_safe : Safe 9 4 s4_140 := by
  apply safe_succ 8 4 s4_140 [s5_495, s5_139, s5_130] (by decide) s4_140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_495_safe
  · subst z; exact s5_139_safe
  · subst z; exact s5_130_safe
def s4_141 : State := ⟨[1,4,80,132], 5784800237655955087821634685047238889750, 2, 2, 1, 0⟩
theorem s4_141_edges : next config 4 s4_141 = [s5_143] := by decide
theorem s4_141_safe : Safe 9 4 s4_141 := by
  apply safe_succ 8 4 s4_141 [s5_143] (by decide) s4_141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_143_safe
def s4_142 : State := ⟨[1,4,80,136], 87452568298681186319031540468671609639190, 2, 2, 1, 0⟩
theorem s4_142_edges : next config 4 s4_142 = [s5_147] := by decide
theorem s4_142_safe : Safe 9 4 s4_142 := by
  apply safe_succ 8 4 s4_142 [s5_147] (by decide) s4_142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_147_safe
def s4_143 : State := ⟨[1,4,80,136], 1481249143206845132665013932509194203758870, 2, 2, 1, 0⟩
theorem s4_143_edges : next config 4 s4_143 = [s5_151] := by decide
theorem s4_143_safe : Safe 9 4 s4_143 := by
  apply safe_succ 8 4 s4_143 [s5_151] (by decide) s4_143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_151_safe
def s4_144 : State := ⟨[1,4,80,140], 1394136857275084886018390033006661541630230, 2, 2, 1, 0⟩
theorem s4_144_edges : next config 4 s4_144 = [s5_153] := by decide
theorem s4_144_safe : Safe 9 4 s4_144 := by
  apply safe_succ 8 4 s4_144 [s5_153] (by decide) s4_144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_153_safe
def s4_145 : State := ⟨[1,4,80,144], 22301085480897544081208125913614500453486870, 2, 2, 1, 0⟩
theorem s4_145_edges : next config 4 s4_145 = [s5_155, s5_129] := by decide
theorem s4_145_safe : Safe 9 4 s4_145 := by
  apply safe_succ 8 4 s4_145 [s5_155, s5_129] (by decide) s4_145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_155_safe
  · subst z; exact s5_129_safe
def s4_146 : State := ⟨[1,4,80,145], 44601830679428167222743844186262861959594262, 1, 1, 1, 0⟩
theorem s4_146_edges : next config 4 s4_146 = [s5_575, s5_159] := by decide
theorem s4_146_safe : Safe 9 4 s4_146 := by
  apply safe_succ 8 4 s4_146 [s5_575, s5_159] (by decide) s4_146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_575_safe
  · subst z; exact s5_159_safe
def s4_147 : State := ⟨[1,4,80,160], 1461501637671185285124624505123923985794880049430, 2, 2, 1, 0⟩
theorem s4_147_edges : next config 4 s4_147 = [s5_161] := by decide
theorem s4_147_safe : Safe 9 4 s4_147 := by
  apply safe_succ 8 4 s4_147 [s5_161] (by decide) s4_147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_161_safe
def s4_148 : State := ⟨[1,4,80,192], 6277101735386680764176071790128606088509996410602982019350, 2, 2, 1, 0⟩
theorem s4_148_edges : next config 4 s4_148 = [s5_165] := by decide
theorem s4_148_safe : Safe 9 4 s4_148 := by
  apply safe_succ 8 4 s4_148 [s5_165] (by decide) s4_148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_165_safe
def s4_149 : State := ⟨[1,4,80,208], 411376139330301510538742635921704547185356374049361104784658710, 2, 2, 1, 0⟩
theorem s4_149_edges : next config 4 s4_149 = [s5_170, s5_131] := by decide
theorem s4_149_safe : Safe 9 4 s4_149 := by
  apply safe_succ 8 4 s4_149 [s5_170, s5_131] (by decide) s4_149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_170_safe
  · subst z; exact s5_131_safe
def s4_150 : State := ⟨[1,4,80,214], 27973577474460502716634477804886793189400035976910253542946701590, 0, 0, 1, 0⟩
theorem s4_150_edges : next config 4 s4_150 = [] := by decide
theorem s4_150_safe : Safe 9 4 s4_150 := by
  apply safe_succ 8 4 s4_150 [] (by decide) s4_150_edges
  simp
def s4_151 : State := ⟨[1,4,80,214], 28384953613790804227173218739396663131891866089820218781711008022, 0, 0, 1, 0⟩
theorem s4_151_edges : next config 4 s4_151 = [] := by decide
theorem s4_151_safe : Safe 9 4 s4_151 := by
  apply safe_succ 8 4 s4_151 [] (by decide) s4_151_edges
  simp
def s4_152 : State := ⟨[1,4,81,145], 44601830679428167223952770005877491134300438, 1, 1, 1, 0⟩
theorem s4_152_edges : next config 4 s4_152 = [s5_576] := by decide
theorem s4_152_safe : Safe 9 4 s4_152 := by
  apply safe_succ 8 4 s4_152 [s5_576] (by decide) s4_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_576_safe
def s4_153 : State := ⟨[1,4,82,128], 340282366920943299258886786321309831446, 2, 2, 0, 0⟩
theorem s4_153_edges : next config 4 s4_153 = [s5_969, s5_134, s5_142, s5_172, s5_138, s5_146, s5_154, s5_160] := by decide
theorem s4_153_safe : Safe 9 4 s4_153 := by
  apply safe_succ 8 4 s4_153 [s5_969, s5_134, s5_142, s5_172, s5_138, s5_146, s5_154, s5_160] (by decide) s4_153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_969_safe
  · subst z; exact s5_134_safe
  · subst z; exact s5_142_safe
  · subst z; exact s5_172_safe
  · subst z; exact s5_138_safe
  · subst z; exact s5_146_safe
  · subst z; exact s5_154_safe
  · subst z; exact s5_160_safe
def s4_154 : State := ⟨[1,4,82,128], 340282366920944508110919424655646331158, 2, 2, 0, 0⟩
theorem s4_154_edges : next config 4 s4_154 = [s5_971, s5_135, s5_143, s5_173, s5_139, s5_147, s5_155, s5_161] := by decide
theorem s4_154_safe : Safe 9 4 s4_154 := by
  apply safe_succ 8 4 s4_154 [s5_971, s5_135, s5_143, s5_173, s5_139, s5_147, s5_155, s5_161] (by decide) s4_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_971_safe
  · subst z; exact s5_135_safe
  · subst z; exact s5_143_safe
  · subst z; exact s5_173_safe
  · subst z; exact s5_139_safe
  · subst z; exact s5_147_safe
  · subst z; exact s5_155_safe
  · subst z; exact s5_161_safe
def s4_155 : State := ⟨[1,4,82,128], 340282366921020670511342122588491022614, 2, 2, 0, 0⟩
theorem s4_155_edges : next config 4 s4_155 = [s5_973, s5_136, s5_144, s5_174, s5_140, s5_148, s5_156, s5_162] := by decide
theorem s4_155_safe : Safe 9 4 s4_155 := by
  apply safe_succ 8 4 s4_155 [s5_973, s5_136, s5_144, s5_174, s5_140, s5_148, s5_156, s5_162] (by decide) s4_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_973_safe
  · subst z; exact s5_136_safe
  · subst z; exact s5_144_safe
  · subst z; exact s5_174_safe
  · subst z; exact s5_140_safe
  · subst z; exact s5_148_safe
  · subst z; exact s5_156_safe
  · subst z; exact s5_162_safe
def s4_156 : State := ⟨[1,4,82,128], 340282366921021879363374760922827522326, 2, 2, 0, 0⟩
theorem s4_156_edges : next config 4 s4_156 = [s5_974, s5_137, s5_145, s5_175, s5_141, s5_149, s5_157, s5_163] := by decide
theorem s4_156_safe : Safe 9 4 s4_156 := by
  apply safe_succ 8 4 s4_156 [s5_974, s5_137, s5_145, s5_175, s5_141, s5_149, s5_157, s5_163] (by decide) s4_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_974_safe
  · subst z; exact s5_137_safe
  · subst z; exact s5_145_safe
  · subst z; exact s5_175_safe
  · subst z; exact s5_141_safe
  · subst z; exact s5_149_safe
  · subst z; exact s5_157_safe
  · subst z; exact s5_163_safe
def s4_157 : State := ⟨[1,4,82,140], 1399581375145819905060655272545752195334422, 0, 0, 1, 0⟩
theorem s4_157_edges : next config 4 s4_157 = [] := by decide
theorem s4_157_safe : Safe 9 4 s4_157 := by
  apply safe_succ 8 4 s4_157 [] (by decide) s4_157_edges
  simp
def s4_158 : State := ⟨[1,4,82,140], 1399581375145819906269507305184086531834134, 0, 0, 1, 0⟩
theorem s4_158_edges : next config 4 s4_158 = [] := by decide
theorem s4_158_safe : Safe 9 4 s4_158 := by
  apply safe_succ 8 4 s4_158 [] (by decide) s4_158_edges
  simp
def s4_159 : State := ⟨[1,4,82,140], 1481249143206845136291865178329376566083862, 0, 0, 1, 0⟩
theorem s4_159_edges : next config 4 s4_159 = [] := by decide
theorem s4_159_safe : Safe 9 4 s4_159 := by
  apply safe_succ 8 4 s4_159 [] (by decide) s4_159_edges
  simp
def s4_160 : State := ⟨[1,4,82,140], 1481249143206845137500717210967710902583574, 0, 0, 1, 0⟩
theorem s4_160_edges : next config 4 s4_160 = [] := by decide
theorem s4_160_safe : Safe 9 4 s4_160 := by
  apply safe_succ 8 4 s4_160 [] (by decide) s4_160_edges
  simp
def s4_161 : State := ⟨[1,4,82,145], 44602511244162009103297622181297907858211094, 0, 0, 1, 0⟩
theorem s4_161_edges : next config 4 s4_161 = [s5_704, s5_577, s5_180] := by decide
theorem s4_161_safe : Safe 9 4 s4_161 := by
  apply safe_succ 8 4 s4_161 [s5_704, s5_577, s5_180] (by decide) s4_161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_704_safe
  · subst z; exact s5_577_safe
  · subst z; exact s5_180_safe
def s4_162 : State := ⟨[1,4,82,145], 44602511244162009104506474213936242194710806, 0, 0, 1, 0⟩
theorem s4_162_edges : next config 4 s4_162 = [s5_705, s5_578, s5_181] := by decide
theorem s4_162_safe : Safe 9 4 s4_162 := by
  apply safe_succ 8 4 s4_162 [s5_705, s5_578, s5_181] (by decide) s4_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_705_safe
  · subst z; exact s5_578_safe
  · subst z; exact s5_181_safe
def s4_163 : State := ⟨[1,4,82,145], 66902575877958790367906413704731405827768598, 0, 0, 1, 0⟩
theorem s4_163_edges : next config 4 s4_163 = [s5_706, s5_579, s5_182] := by decide
theorem s4_163_safe : Safe 9 4 s4_163 := by
  apply safe_succ 8 4 s4_163 [s5_706, s5_579, s5_182] (by decide) s4_163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_706_safe
  · subst z; exact s5_579_safe
  · subst z; exact s5_182_safe
def s4_164 : State := ⟨[1,4,82,145], 66902575877958790369115265737369740164268310, 0, 0, 1, 0⟩
theorem s4_164_edges : next config 4 s4_164 = [s5_707, s5_580, s5_183] := by decide
theorem s4_164_safe : Safe 9 4 s4_164 := by
  apply safe_succ 8 4 s4_164 [s5_707, s5_580, s5_183] (by decide) s4_164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_707_safe
  · subst z; exact s5_580_safe
  · subst z; exact s5_183_safe
def s4_165 : State := ⟨[1,4,82,214], 26328072917139296674479512705717845735682488523017783043178955030, 0, 0, 1, 0⟩
theorem s4_165_edges : next config 4 s4_165 = [] := by decide
theorem s4_165_safe : Safe 9 4 s4_165 := by
  apply safe_succ 8 4 s4_165 [] (by decide) s4_165_edges
  simp
def s4_166 : State := ⟨[1,4,82,214], 26328072917139296674479512705717845735683697375050421377515454742, 0, 0, 1, 0⟩
theorem s4_166_edges : next config 4 s4_166 = [] := by decide
theorem s4_166_safe : Safe 9 4 s4_166 := by
  apply safe_succ 8 4 s4_166 [] (by decide) s4_166_edges
  simp
def s4_167 : State := ⟨[1,4,82,214], 27973577474460502716634476443757325505649808974657643998236180758, 0, 0, 1, 0⟩
theorem s4_167_edges : next config 4 s4_167 = [] := by decide
theorem s4_167_safe : Safe 9 4 s4_167 := by
  apply safe_succ 8 4 s4_167 [] (by decide) s4_167_edges
  simp
def s4_168 : State := ⟨[1,4,82,214], 27973577474460502716634476443757325505651017826690282332572680470, 0, 0, 1, 0⟩
theorem s4_168_edges : next config 4 s4_168 = [] := by decide
theorem s4_168_safe : Safe 9 4 s4_168 := by
  apply safe_succ 8 4 s4_168 [] (by decide) s4_168_edges
  simp
def s4_169 : State := ⟨[1,4,86,129], 1020847100762897597438091337452027445526, 0, 0, 1, 0⟩
theorem s4_169_edges : next config 4 s4_169 = [s5_180] := by decide
theorem s4_169_safe : Safe 9 4 s4_169 := by
  apply safe_succ 8 4 s4_169 [s5_180] (by decide) s4_169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_180_safe
def s4_170 : State := ⟨[1,4,86,129], 1020847100762898806290123975786363945238, 0, 0, 1, 0⟩
theorem s4_170_edges : next config 4 s4_170 = [s5_181] := by decide
theorem s4_170_safe : Safe 9 4 s4_170 := by
  apply safe_succ 8 4 s4_170 [s5_181] (by decide) s4_170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_181_safe
def s4_171 : State := ⟨[1,4,86,130], 1701411834604774524364840552315563868438, 0, 0, 1, 0⟩
theorem s4_171_edges : next config 4 s4_171 = [] := by decide
theorem s4_171_safe : Safe 9 4 s4_171 := by
  apply safe_succ 8 4 s4_171 [] (by decide) s4_171_edges
  simp
def s4_172 : State := ⟨[1,4,86,130], 1701411834604775733216873190649900368150, 0, 0, 1, 0⟩
theorem s4_172_edges : next config 4 s4_172 = [] := by decide
theorem s4_172_safe : Safe 9 4 s4_172 := by
  apply safe_succ 8 4 s4_172 [] (by decide) s4_172_edges
  simp
def s4_173 : State := ⟨[1,4,86,132], 5784800237656036085925335841496782405910, 0, 0, 1, 0⟩
theorem s4_173_edges : next config 4 s4_173 = [] := by decide
theorem s4_173_safe : Safe 9 4 s4_173 := by
  apply safe_succ 8 4 s4_173 [] (by decide) s4_173_edges
  simp
def s4_174 : State := ⟨[1,4,86,132], 5784800237656037294777368479831118905622, 0, 0, 1, 0⟩
theorem s4_174_edges : next config 4 s4_174 = [] := by decide
theorem s4_174_safe : Safe 9 4 s4_174 := by
  apply safe_succ 8 4 s4_174 [] (by decide) s4_174_edges
  simp
def s4_175 : State := ⟨[1,4,86,136], 87452568298681267317135241625121153155350, 0, 0, 1, 0⟩
theorem s4_175_edges : next config 4 s4_175 = [] := by decide
theorem s4_175_safe : Safe 9 4 s4_175 := by
  apply safe_succ 8 4 s4_175 [] (by decide) s4_175_edges
  simp
def s4_176 : State := ⟨[1,4,86,136], 87452568298681268525987274263455489655062, 0, 0, 1, 0⟩
theorem s4_176_edges : next config 4 s4_176 = [] := by decide
theorem s4_176_safe : Safe 9 4 s4_176 := by
  apply safe_succ 8 4 s4_176 [] (by decide) s4_176_edges
  simp
def s4_177 : State := ⟨[1,4,86,144], 22301085480897544162206229614770949997003030, 0, 0, 1, 0⟩
theorem s4_177_edges : next config 4 s4_177 = [s5_182] := by decide
theorem s4_177_safe : Safe 9 4 s4_177 := by
  apply safe_succ 8 4 s4_177 [s5_182] (by decide) s4_177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_182_safe
def s4_178 : State := ⟨[1,4,86,144], 22301085480897544163415081647409284333502742, 0, 0, 1, 0⟩
theorem s4_178_edges : next config 4 s4_178 = [s5_183] := by decide
theorem s4_178_safe : Safe 9 4 s4_178 := by
  apply safe_succ 8 4 s4_178 [s5_183] (by decide) s4_178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_183_safe
def s4_179 : State := ⟨[1,4,86,160], 1461501637671185285124705503227625142244423565590, 0, 0, 1, 0⟩
theorem s4_179_edges : next config 4 s4_179 = [] := by decide
theorem s4_179_safe : Safe 9 4 s4_179 := by
  apply safe_succ 8 4 s4_179 [] (by decide) s4_179_edges
  simp
def s4_180 : State := ⟨[1,4,86,160], 1461501637671185285124706712079657780578760065302, 0, 0, 1, 0⟩
theorem s4_180_edges : next config 4 s4_180 = [] := by decide
theorem s4_180_safe : Safe 9 4 s4_180 := by
  apply safe_succ 8 4 s4_180 [] (by decide) s4_180_edges
  simp
def s4_181 : State := ⟨[1,4,86,192], 6277101735386680764176071790128687086613697567052525535510, 0, 0, 1, 0⟩
theorem s4_181_edges : next config 4 s4_181 = [] := by decide
theorem s4_181_safe : Safe 9 4 s4_181 := by
  apply safe_succ 8 4 s4_181 [] (by decide) s4_181_edges
  simp
def s4_182 : State := ⟨[1,4,86,192], 6277101735386680764176071790128688295465730205386862035222, 0, 0, 1, 0⟩
theorem s4_182_edges : next config 4 s4_182 = [] := by decide
theorem s4_182_safe : Safe 9 4 s4_182 := by
  apply safe_succ 8 4 s4_182 [] (by decide) s4_182_edges
  simp
def s4_183 : State := ⟨[1,4,86,194], 25108406941546723055683440059751686334920763900444629074198, 0, 0, 1, 0⟩
theorem s4_183_edges : next config 4 s4_183 = [] := by decide
theorem s4_183_safe : Safe 9 4 s4_183 := by
  apply safe_succ 8 4 s4_183 [] (by decide) s4_183_edges
  simp
def s4_184 : State := ⟨[1,4,86,208], 411376139330301510538742635921704547267563329783155888664674582, 0, 0, 1, 0⟩
theorem s4_184_edges : next config 4 s4_184 = [] := by decide
theorem s4_184_safe : Safe 9 4 s4_184 := by
  apply safe_succ 8 4 s4_184 [] (by decide) s4_184_edges
  simp
def s4_185 : State := ⟨[1,4,86,210], 1645504557321206042154969522839717426003406376975702451839631638, 0, 0, 1, 0⟩
theorem s4_185_edges : next config 4 s4_185 = [] := by decide
theorem s4_185_safe : Safe 9 4 s4_185 := by
  apply safe_succ 8 4 s4_185 [] (by decide) s4_185_edges
  simp
def s4_186 : State := ⟨[1,4,86,210], 1645504557321206042154969522839717426004615229008340786176131350, 0, 0, 1, 0⟩
theorem s4_186_edges : next config 4 s4_186 = [] := by decide
theorem s4_186_safe : Safe 9 4 s4_186 := by
  apply safe_succ 8 4 s4_186 [] (by decide) s4_186_edges
  simp
def s4_187 : State := ⟨[1,4,86,214], 26328072917139296674479507261199975000744444361479400402068766998, 0, 0, 1, 0⟩
theorem s4_187_edges : next config 4 s4_187 = [] := by decide
theorem s4_187_safe : Safe 9 4 s4_187 := by
  apply safe_succ 8 4 s4_187 [] (by decide) s4_187_edges
  simp
def s4_188 : State := ⟨[1,4,86,214], 26328072917139296674479507261199975000745653213512038736405266710, 0, 0, 1, 0⟩
theorem s4_188_edges : next config 4 s4_188 = [] := by decide
theorem s4_188_safe : Safe 9 4 s4_188 := by
  apply safe_succ 8 4 s4_188 [] (by decide) s4_188_edges
  simp
def s4_189 : State := ⟨[1,4,96,129], 1020847100842043552922834903966853169438, 1, 1, 1, 0⟩
theorem s4_189_edges : next config 4 s4_189 = [s5_708, s5_581, s5_306, s5_329, s5_202] := by decide
theorem s4_189_safe : Safe 9 4 s4_189 := by
  apply safe_succ 8 4 s4_189 [s5_708, s5_581, s5_306, s5_329, s5_202] (by decide) s4_189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_708_safe
  · subst z; exact s5_581_safe
  · subst z; exact s5_306_safe
  · subst z; exact s5_329_safe
  · subst z; exact s5_202_safe
def s4_190 : State := ⟨[1,4,96,129], 1020847100842043552922834903966853169942, 1, 1, 1, 0⟩
theorem s4_190_edges : next config 4 s4_190 = [s5_330, s5_203] := by decide
theorem s4_190_safe : Safe 9 4 s4_190 := by
  apply safe_succ 8 4 s4_190 [s5_330, s5_203] (by decide) s4_190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_330_safe
  · subst z; exact s5_203_safe
def s4_191 : State := ⟨[1,4,96,129], 1020847100842043552922834903966853173526, 2, 2, 1, 0⟩
theorem s4_191_edges : next config 4 s4_191 = [s5_1498, s5_814, s5_1147, s5_294, s5_511, s5_331, s5_469, s5_286, s5_190, s5_204, s5_231] := by decide
theorem s4_191_safe : Safe 9 4 s4_191 := by
  apply safe_succ 8 4 s4_191 [s5_1498, s5_814, s5_1147, s5_294, s5_511, s5_331, s5_469, s5_286, s5_190, s5_204, s5_231] (by decide) s4_191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1498_safe
  · subst z; exact s5_814_safe
  · subst z; exact s5_1147_safe
  · subst z; exact s5_294_safe
  · subst z; exact s5_511_safe
  · subst z; exact s5_331_safe
  · subst z; exact s5_469_safe
  · subst z; exact s5_286_safe
  · subst z; exact s5_190_safe
  · subst z; exact s5_204_safe
  · subst z; exact s5_231_safe
def s4_192 : State := ⟨[1,4,96,129], 1020847100842043552922834903975443104022, 1, 1, 1, 0⟩
theorem s4_192_edges : next config 4 s4_192 = [s5_582, s5_332, s5_205] := by decide
theorem s4_192_safe : Safe 9 4 s4_192 := by
  apply safe_succ 8 4 s4_192 [s5_582, s5_332, s5_205] (by decide) s4_192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_582_safe
  · subst z; exact s5_332_safe
  · subst z; exact s5_205_safe
def s4_193 : State := ⟨[1,4,96,129], 1020847100842043552959728392114272272662, 1, 1, 1, 0⟩
theorem s4_193_edges : next config 4 s4_193 = [s5_709, s5_583, s5_307, s5_333, s5_206] := by decide
theorem s4_193_safe : Safe 9 4 s4_193 := by
  apply safe_succ 8 4 s4_193 [s5_709, s5_583, s5_307, s5_333, s5_206] (by decide) s4_193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_709_safe
  · subst z; exact s5_583_safe
  · subst z; exact s5_307_safe
  · subst z; exact s5_333_safe
  · subst z; exact s5_206_safe
def s4_194 : State := ⟨[1,4,96,129], 1020847100842043553217982809146205995286, 2, 2, 1, 0⟩
theorem s4_194_edges : next config 4 s4_194 = [s5_334, s5_207] := by decide
theorem s4_194_safe : Safe 9 4 s4_194 := by
  apply safe_succ 8 4 s4_194 [s5_334, s5_207] (by decide) s4_194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_334_safe
  · subst z; exact s5_207_safe
def s4_195 : State := ⟨[1,4,96,129], 1020847101000499877951363579153941070102, 1, 1, 1, 0⟩
theorem s4_195_edges : next config 4 s4_195 = [s5_584, s5_335, s5_208] := by decide
theorem s4_195_safe : Safe 9 4 s4_195 := by
  apply safe_succ 8 4 s4_195 [s5_584, s5_335, s5_208] (by decide) s4_195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_584_safe
  · subst z; exact s5_335_safe
  · subst z; exact s5_208_safe
def s4_196 : State := ⟨[1,4,96,129], 1020847102109694153151064305463556374806, 2, 2, 1, 0⟩
theorem s4_196_edges : next config 4 s4_196 = [s5_815, s5_336, s5_191, s5_209] := by decide
theorem s4_196_safe : Safe 9 4 s4_196 := by
  apply safe_succ 8 4 s4_196 [s5_815, s5_336, s5_191, s5_209] (by decide) s4_196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_815_safe
  · subst z; exact s5_336_safe
  · subst z; exact s5_191_safe
  · subst z; exact s5_209_safe
def s4_197 : State := ⟨[1,4,96,130], 1701411834683920479849584118830389592350, 1, 1, 1, 0⟩
theorem s4_197_edges : next config 4 s4_197 = [s5_710, s5_585, s5_308, s5_338, s5_218, s5_233] := by decide
theorem s4_197_safe : Safe 9 4 s4_197 := by
  apply safe_succ 8 4 s4_197 [s5_710, s5_585, s5_308, s5_338, s5_218, s5_233] (by decide) s4_197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_710_safe
  · subst z; exact s5_585_safe
  · subst z; exact s5_308_safe
  · subst z; exact s5_338_safe
  · subst z; exact s5_218_safe
  · subst z; exact s5_233_safe
def s4_198 : State := ⟨[1,4,96,130], 1701411834683920479849584118830389592854, 1, 1, 1, 0⟩
theorem s4_198_edges : next config 4 s4_198 = [s5_339, s5_234] := by decide
theorem s4_198_safe : Safe 9 4 s4_198 := by
  apply safe_succ 8 4 s4_198 [s5_339, s5_234] (by decide) s4_198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_339_safe
  · subst z; exact s5_234_safe
def s4_199 : State := ⟨[1,4,96,130], 1701411834683920479849584118830389596438, 2, 2, 1, 0⟩
theorem s4_199_edges : next config 4 s4_199 = [s5_1499, s5_1542, s5_816, s5_1148, s5_295, s5_340, s5_470, s5_192, s5_219, s5_235] := by decide
theorem s4_199_safe : Safe 9 4 s4_199 := by
  apply safe_succ 8 4 s4_199 [s5_1499, s5_1542, s5_816, s5_1148, s5_295, s5_340, s5_470, s5_192, s5_219, s5_235] (by decide) s4_199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1499_safe
  · subst z; exact s5_1542_safe
  · subst z; exact s5_816_safe
  · subst z; exact s5_1148_safe
  · subst z; exact s5_295_safe
  · subst z; exact s5_340_safe
  · subst z; exact s5_470_safe
  · subst z; exact s5_192_safe
  · subst z; exact s5_219_safe
  · subst z; exact s5_235_safe
def s4_200 : State := ⟨[1,4,96,130], 1701411834683920479849584118838979526934, 1, 1, 1, 0⟩
theorem s4_200_edges : next config 4 s4_200 = [s5_586, s5_341] := by decide
theorem s4_200_safe : Safe 9 4 s4_200 := by
  apply safe_succ 8 4 s4_200 [s5_586, s5_341] (by decide) s4_200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_586_safe
  · subst z; exact s5_341_safe
def s4_201 : State := ⟨[1,4,96,130], 1701411834683920479886477606977808695574, 1, 1, 1, 0⟩
theorem s4_201_edges : next config 4 s4_201 = [s5_711, s5_587, s5_309, s5_342, s5_220, s5_236] := by decide
theorem s4_201_safe : Safe 9 4 s4_201 := by
  apply safe_succ 8 4 s4_201 [s5_711, s5_587, s5_309, s5_342, s5_220, s5_236] (by decide) s4_201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_711_safe
  · subst z; exact s5_587_safe
  · subst z; exact s5_309_safe
  · subst z; exact s5_342_safe
  · subst z; exact s5_220_safe
  · subst z; exact s5_236_safe
def s4_202 : State := ⟨[1,4,96,130], 1701411834683920480144732024009742418198, 2, 2, 1, 0⟩
theorem s4_202_edges : next config 4 s4_202 = [s5_343, s5_221] := by decide
theorem s4_202_safe : Safe 9 4 s4_202 := by
  apply safe_succ 8 4 s4_202 [s5_343, s5_221] (by decide) s4_202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_343_safe
  · subst z; exact s5_221_safe
def s4_203 : State := ⟨[1,4,96,130], 1701411834842376804878112794017477493014, 1, 1, 1, 0⟩
theorem s4_203_edges : next config 4 s4_203 = [s5_588, s5_344, s5_237] := by decide
theorem s4_203_safe : Safe 9 4 s4_203 := by
  apply safe_succ 8 4 s4_203 [s5_588, s5_344, s5_237] (by decide) s4_203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_588_safe
  · subst z; exact s5_344_safe
  · subst z; exact s5_237_safe
def s4_204 : State := ⟨[1,4,96,130], 1701411835951571080077813520327092797718, 2, 2, 1, 0⟩
theorem s4_204_edges : next config 4 s4_204 = [s5_1543, s5_817, s5_345, s5_193, s5_222, s5_238] := by decide
theorem s4_204_safe : Safe 9 4 s4_204 := by
  apply safe_succ 8 4 s4_204 [s5_1543, s5_817, s5_345, s5_193, s5_222, s5_238] (by decide) s4_204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1543_safe
  · subst z; exact s5_817_safe
  · subst z; exact s5_345_safe
  · subst z; exact s5_193_safe
  · subst z; exact s5_222_safe
  · subst z; exact s5_238_safe
def s4_205 : State := ⟨[1,4,96,130], 4423670770051428187556580978284535283990, 1, 1, 1, 0⟩
theorem s4_205_edges : next config 4 s4_205 = [s5_712, s5_589, s5_310, s5_347, s5_223, s5_239] := by decide
theorem s4_205_safe : Safe 9 4 s4_205 := by
  apply safe_succ 8 4 s4_205 [s5_712, s5_589, s5_310, s5_347, s5_223, s5_239] (by decide) s4_205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_712_safe
  · subst z; exact s5_589_safe
  · subst z; exact s5_310_safe
  · subst z; exact s5_347_safe
  · subst z; exact s5_223_safe
  · subst z; exact s5_239_safe
def s4_206 : State := ⟨[1,4,96,131], 3062541302367674333703082548557462438174, 1, 1, 1, 0⟩
theorem s4_206_edges : next config 4 s4_206 = [s5_713, s5_590, s5_311, s5_348, s5_249] := by decide
theorem s4_206_safe : Safe 9 4 s4_206 := by
  apply safe_succ 8 4 s4_206 [s5_713, s5_590, s5_311, s5_348, s5_249] (by decide) s4_206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_713_safe
  · subst z; exact s5_590_safe
  · subst z; exact s5_311_safe
  · subst z; exact s5_348_safe
  · subst z; exact s5_249_safe
def s4_207 : State := ⟨[1,4,96,132], 5784800237735182041410079408011608129822, 1, 1, 1, 0⟩
theorem s4_207_edges : next config 4 s4_207 = [s5_714, s5_591, s5_312, s5_512, s5_349, s5_288, s5_194] := by decide
theorem s4_207_safe : Safe 9 4 s4_207 := by
  apply safe_succ 8 4 s4_207 [s5_714, s5_591, s5_312, s5_512, s5_349, s5_288, s5_194] (by decide) s4_207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_714_safe
  · subst z; exact s5_591_safe
  · subst z; exact s5_312_safe
  · subst z; exact s5_512_safe
  · subst z; exact s5_349_safe
  · subst z; exact s5_288_safe
  · subst z; exact s5_194_safe
def s4_208 : State := ⟨[1,4,96,132], 5784800237735182041410079408011608130326, 1, 1, 1, 0⟩
theorem s4_208_edges : next config 4 s4_208 = [s5_350] := by decide
theorem s4_208_safe : Safe 9 4 s4_208 := by
  apply safe_succ 8 4 s4_208 [s5_350] (by decide) s4_208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_350_safe
def s4_209 : State := ⟨[1,4,96,132], 5784800237735182041410079408011608133910, 2, 2, 1, 0⟩
theorem s4_209_edges : next config 4 s4_209 = [s5_1500, s5_820, s5_1149, s5_296, s5_351, s5_471] := by decide
theorem s4_209_safe : Safe 9 4 s4_209 := by
  apply safe_succ 8 4 s4_209 [s5_1500, s5_820, s5_1149, s5_296, s5_351, s5_471] (by decide) s4_209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1500_safe
  · subst z; exact s5_820_safe
  · subst z; exact s5_1149_safe
  · subst z; exact s5_296_safe
  · subst z; exact s5_351_safe
  · subst z; exact s5_471_safe
def s4_210 : State := ⟨[1,4,96,132], 5784800237735182041410079408020198064406, 1, 1, 1, 0⟩
theorem s4_210_edges : next config 4 s4_210 = [s5_592, s5_352, s5_195] := by decide
theorem s4_210_safe : Safe 9 4 s4_210 := by
  apply safe_succ 8 4 s4_210 [s5_592, s5_352, s5_195] (by decide) s4_210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_592_safe
  · subst z; exact s5_352_safe
  · subst z; exact s5_195_safe
def s4_211 : State := ⟨[1,4,96,132], 5784800237735182041446972896159027233046, 1, 1, 1, 0⟩
theorem s4_211_edges : next config 4 s4_211 = [s5_715, s5_593, s5_313, s5_513, s5_353, s5_289, s5_196] := by decide
theorem s4_211_safe : Safe 9 4 s4_211 := by
  apply safe_succ 8 4 s4_211 [s5_715, s5_593, s5_313, s5_513, s5_353, s5_289, s5_196] (by decide) s4_211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_715_safe
  · subst z; exact s5_593_safe
  · subst z; exact s5_313_safe
  · subst z; exact s5_513_safe
  · subst z; exact s5_353_safe
  · subst z; exact s5_289_safe
  · subst z; exact s5_196_safe
def s4_212 : State := ⟨[1,4,96,132], 5784800237735182041705227313190960955670, 2, 2, 1, 0⟩
theorem s4_212_edges : next config 4 s4_212 = [s5_354] := by decide
theorem s4_212_safe : Safe 9 4 s4_212 := by
  apply safe_succ 8 4 s4_212 [s5_354] (by decide) s4_212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_354_safe
def s4_213 : State := ⟨[1,4,96,132], 5784800237893638366438608083198696030486, 1, 1, 1, 0⟩
theorem s4_213_edges : next config 4 s4_213 = [s5_594, s5_355, s5_197] := by decide
theorem s4_213_safe : Safe 9 4 s4_213 := by
  apply safe_succ 8 4 s4_213 [s5_594, s5_355, s5_197] (by decide) s4_213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_594_safe
  · subst z; exact s5_355_safe
  · subst z; exact s5_197_safe
def s4_214 : State := ⟨[1,4,96,132], 5784800239002832641638308809508311335190, 2, 2, 1, 0⟩
theorem s4_214_edges : next config 4 s4_214 = [s5_821, s5_356] := by decide
theorem s4_214_safe : Safe 9 4 s4_214 := by
  apply safe_succ 8 4 s4_214 [s5_821, s5_356] (by decide) s4_214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_821_safe
  · subst z; exact s5_356_safe
def s4_215 : State := ⟨[1,4,96,136], 87452568298760413272619985191635978879262, 1, 1, 1, 0⟩
theorem s4_215_edges : next config 4 s4_215 = [s5_716, s5_766, s5_595, s5_314, s5_358, s5_198] := by decide
theorem s4_215_safe : Safe 9 4 s4_215 := by
  apply safe_succ 8 4 s4_215 [s5_716, s5_766, s5_595, s5_314, s5_358, s5_198] (by decide) s4_215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_716_safe
  · subst z; exact s5_766_safe
  · subst z; exact s5_595_safe
  · subst z; exact s5_314_safe
  · subst z; exact s5_358_safe
  · subst z; exact s5_198_safe
def s4_216 : State := ⟨[1,4,96,136], 87452568298760413272619985191635978879766, 1, 1, 1, 0⟩
theorem s4_216_edges : next config 4 s4_216 = [s5_359] := by decide
theorem s4_216_safe : Safe 9 4 s4_216 := by
  apply safe_succ 8 4 s4_216 [s5_359] (by decide) s4_216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_359_safe
def s4_217 : State := ⟨[1,4,96,136], 87452568298760413272619985191635978883350, 2, 2, 1, 0⟩
theorem s4_217_edges : next config 4 s4_217 = [s5_1501, s5_822, s5_1150, s5_297, s5_360, s5_472] := by decide
theorem s4_217_safe : Safe 9 4 s4_217 := by
  apply safe_succ 8 4 s4_217 [s5_1501, s5_822, s5_1150, s5_297, s5_360, s5_472] (by decide) s4_217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1501_safe
  · subst z; exact s5_822_safe
  · subst z; exact s5_1150_safe
  · subst z; exact s5_297_safe
  · subst z; exact s5_360_safe
  · subst z; exact s5_472_safe
def s4_218 : State := ⟨[1,4,96,136], 87452568298760413272619985191644568813846, 1, 1, 1, 0⟩
theorem s4_218_edges : next config 4 s4_218 = [s5_767, s5_596, s5_361, s5_199] := by decide
theorem s4_218_safe : Safe 9 4 s4_218 := by
  apply safe_succ 8 4 s4_218 [s5_767, s5_596, s5_361, s5_199] (by decide) s4_218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_767_safe
  · subst z; exact s5_596_safe
  · subst z; exact s5_361_safe
  · subst z; exact s5_199_safe
def s4_219 : State := ⟨[1,4,96,136], 87452568298760413272656878679783397982486, 1, 1, 1, 0⟩
theorem s4_219_edges : next config 4 s4_219 = [s5_717, s5_768, s5_597, s5_315, s5_362, s5_200] := by decide
theorem s4_219_safe : Safe 9 4 s4_219 := by
  apply safe_succ 8 4 s4_219 [s5_717, s5_768, s5_597, s5_315, s5_362, s5_200] (by decide) s4_219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_717_safe
  · subst z; exact s5_768_safe
  · subst z; exact s5_597_safe
  · subst z; exact s5_315_safe
  · subst z; exact s5_362_safe
  · subst z; exact s5_200_safe
def s4_220 : State := ⟨[1,4,96,136], 87452568298760413272915133096815331705110, 2, 2, 1, 0⟩
theorem s4_220_edges : next config 4 s4_220 = [s5_363] := by decide
theorem s4_220_safe : Safe 9 4 s4_220 := by
  apply safe_succ 8 4 s4_220 [s5_363] (by decide) s4_220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_363_safe
def s4_221 : State := ⟨[1,4,96,136], 87452568298918869597648513866823066779926, 1, 1, 1, 0⟩
theorem s4_221_edges : next config 4 s4_221 = [s5_769, s5_598, s5_364, s5_201] := by decide
theorem s4_221_safe : Safe 9 4 s4_221 := by
  apply safe_succ 8 4 s4_221 [s5_769, s5_598, s5_364, s5_201] (by decide) s4_221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_769_safe
  · subst z; exact s5_598_safe
  · subst z; exact s5_364_safe
  · subst z; exact s5_201_safe
def s4_222 : State := ⟨[1,4,96,136], 87452568300028063872848214593132682084630, 2, 2, 1, 0⟩
theorem s4_222_edges : next config 4 s4_222 = [s5_823, s5_365] := by decide
theorem s4_222_safe : Safe 9 4 s4_222 := by
  apply safe_succ 8 4 s4_222 [s5_823, s5_365] (by decide) s4_222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_823_safe
  · subst z; exact s5_365_safe
def s4_223 : State := ⟨[1,4,96,136], 261677140162280906565867784196701303144726, 1, 1, 1, 0⟩
theorem s4_223_edges : next config 4 s4_223 = [s5_367] := by decide
theorem s4_223_safe : Safe 9 4 s4_223 := by
  apply safe_succ 8 4 s4_223 [s5_367] (by decide) s4_223_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_367_safe
def s4_224 : State := ⟨[1,4,96,136], 1481249143206924359618602377232158573003030, 2, 2, 1, 0⟩
theorem s4_224_edges : next config 4 s4_224 = [s5_1502, s5_824, s5_1151, s5_298, s5_368, s5_473] := by decide
theorem s4_224_safe : Safe 9 4 s4_224 := by
  apply safe_succ 8 4 s4_224 [s5_1502, s5_824, s5_1151, s5_298, s5_368, s5_473] (by decide) s4_224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1502_safe
  · subst z; exact s5_824_safe
  · subst z; exact s5_1151_safe
  · subst z; exact s5_298_safe
  · subst z; exact s5_368_safe
  · subst z; exact s5_473_safe
def s4_225 : State := ⟨[1,4,96,137], 174564854230520659919243884694168641012502, 1, 1, 1, 0⟩
theorem s4_225_edges : next config 4 s4_225 = [s5_369] := by decide
theorem s4_225_safe : Safe 9 4 s4_225 := by
  apply safe_succ 8 4 s4_225 [s5_369] (by decide) s4_225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_369_safe
def s4_226 : State := ⟨[1,4,96,140], 1394136857275164112971978477729625910874390, 2, 2, 1, 0⟩
theorem s4_226_edges : next config 4 s4_226 = [s5_1503, s5_825, s5_1152, s5_299, s5_370, s5_474] := by decide
theorem s4_226_safe : Safe 9 4 s4_226 := by
  apply safe_succ 8 4 s4_226 [s5_1503, s5_825, s5_1152, s5_299, s5_370, s5_474] (by decide) s4_226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1503_safe
  · subst z; exact s5_825_safe
  · subst z; exact s5_1152_safe
  · subst z; exact s5_299_safe
  · subst z; exact s5_370_safe
  · subst z; exact s5_474_safe
def s4_227 : State := ⟨[1,4,96,144], 22301085480897623308161714358337464822726942, 1, 1, 1, 0⟩
theorem s4_227_edges : next config 4 s4_227 = [s5_718, s5_603, s5_316, s5_371, s5_210, s5_224, s5_260] := by decide
theorem s4_227_safe : Safe 9 4 s4_227 := by
  apply safe_succ 8 4 s4_227 [s5_718, s5_603, s5_316, s5_371, s5_210, s5_224, s5_260] (by decide) s4_227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_718_safe
  · subst z; exact s5_603_safe
  · subst z; exact s5_316_safe
  · subst z; exact s5_371_safe
  · subst z; exact s5_210_safe
  · subst z; exact s5_224_safe
  · subst z; exact s5_260_safe
def s4_228 : State := ⟨[1,4,96,144], 22301085480897623308161714358337464822727446, 1, 1, 1, 0⟩
theorem s4_228_edges : next config 4 s4_228 = [s5_372, s5_211] := by decide
theorem s4_228_safe : Safe 9 4 s4_228 := by
  apply safe_succ 8 4 s4_228 [s5_372, s5_211] (by decide) s4_228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_372_safe
  · subst z; exact s5_211_safe
def s4_229 : State := ⟨[1,4,96,144], 22301085480897623308161714358337464822731030, 2, 2, 1, 0⟩
theorem s4_229_edges : next config 4 s4_229 = [s5_1504, s5_826, s5_1153, s5_300, s5_514, s5_373, s5_475, s5_212, s5_292, s5_225, s5_261] := by decide
theorem s4_229_safe : Safe 9 4 s4_229 := by
  apply safe_succ 8 4 s4_229 [s5_1504, s5_826, s5_1153, s5_300, s5_514, s5_373, s5_475, s5_212, s5_292, s5_225, s5_261] (by decide) s4_229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1504_safe
  · subst z; exact s5_826_safe
  · subst z; exact s5_1153_safe
  · subst z; exact s5_300_safe
  · subst z; exact s5_514_safe
  · subst z; exact s5_373_safe
  · subst z; exact s5_475_safe
  · subst z; exact s5_212_safe
  · subst z; exact s5_292_safe
  · subst z; exact s5_225_safe
  · subst z; exact s5_261_safe
def s4_230 : State := ⟨[1,4,96,144], 22301085480897623308161714358337473412661526, 1, 1, 1, 0⟩
theorem s4_230_edges : next config 4 s4_230 = [s5_604, s5_374, s5_213] := by decide
theorem s4_230_safe : Safe 9 4 s4_230 := by
  apply safe_succ 8 4 s4_230 [s5_604, s5_374, s5_213] (by decide) s4_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_604_safe
  · subst z; exact s5_374_safe
  · subst z; exact s5_213_safe
def s4_231 : State := ⟨[1,4,96,144], 22301085480897623308161751251825612241830166, 1, 1, 1, 0⟩
theorem s4_231_edges : next config 4 s4_231 = [s5_719, s5_605, s5_317, s5_375, s5_214, s5_226, s5_262] := by decide
theorem s4_231_safe : Safe 9 4 s4_231 := by
  apply safe_succ 8 4 s4_231 [s5_719, s5_605, s5_317, s5_375, s5_214, s5_226, s5_262] (by decide) s4_231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_719_safe
  · subst z; exact s5_605_safe
  · subst z; exact s5_317_safe
  · subst z; exact s5_375_safe
  · subst z; exact s5_214_safe
  · subst z; exact s5_226_safe
  · subst z; exact s5_262_safe
def s4_232 : State := ⟨[1,4,96,144], 22301085480897623308162009506242644175552790, 2, 2, 1, 0⟩
theorem s4_232_edges : next config 4 s4_232 = [s5_376, s5_215, s5_227] := by decide
theorem s4_232_safe : Safe 9 4 s4_232 := by
  apply safe_succ 8 4 s4_232 [s5_376, s5_215, s5_227] (by decide) s4_232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_376_safe
  · subst z; exact s5_215_safe
  · subst z; exact s5_227_safe
def s4_233 : State := ⟨[1,4,96,144], 22301085480897781764486742887012651910627606, 1, 1, 1, 0⟩
theorem s4_233_edges : next config 4 s4_233 = [s5_606, s5_377, s5_216] := by decide
theorem s4_233_safe : Safe 9 4 s4_233 := by
  apply safe_succ 8 4 s4_233 [s5_606, s5_377, s5_216] (by decide) s4_233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_606_safe
  · subst z; exact s5_377_safe
  · subst z; exact s5_216_safe
def s4_234 : State := ⟨[1,4,96,144], 22301085480898890958761942587738961525932310, 2, 2, 1, 0⟩
theorem s4_234_edges : next config 4 s4_234 = [s5_827, s5_378, s5_217, s5_228, s5_263] := by decide
theorem s4_234_safe : Safe 9 4 s4_234 := by
  apply safe_succ 8 4 s4_234 [s5_827, s5_378, s5_217, s5_228, s5_263] (by decide) s4_234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_827_safe
  · subst z; exact s5_378_safe
  · subst z; exact s5_217_safe
  · subst z; exact s5_228_safe
  · subst z; exact s5_263_safe
def s4_235 : State := ⟨[1,4,96,145], 44601830679428246449697432630985826328838422, 1, 1, 1, 0⟩
theorem s4_235_edges : next config 4 s4_235 = [s5_1505, s5_828, s5_938, s5_1154, s5_720, s5_607, s5_301, s5_318, s5_515, s5_380, s5_476] := by decide
theorem s4_235_safe : Safe 9 4 s4_235 := by
  apply safe_succ 8 4 s4_235 [s5_1505, s5_828, s5_938, s5_1154, s5_720, s5_607, s5_301, s5_318, s5_515, s5_380, s5_476] (by decide) s4_235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1505_safe
  · subst z; exact s5_828_safe
  · subst z; exact s5_938_safe
  · subst z; exact s5_1154_safe
  · subst z; exact s5_720_safe
  · subst z; exact s5_607_safe
  · subst z; exact s5_301_safe
  · subst z; exact s5_318_safe
  · subst z; exact s5_515_safe
  · subst z; exact s5_380_safe
  · subst z; exact s5_476_safe
def s4_236 : State := ⟨[1,4,96,150], 1516452374911917057544908692124207412796260630, 0, 0, 1, 0⟩
theorem s4_236_edges : next config 4 s4_236 = [s5_381] := by decide
theorem s4_236_safe : Safe 9 4 s4_236 := by
  apply safe_succ 8 4 s4_236 [s5_381] (by decide) s4_236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_381_safe
def s4_237 : State := ⟨[1,4,96,150], 1538751758980979996932590556898426047229395222, 0, 0, 1, 0⟩
theorem s4_237_edges : next config 4 s4_237 = [s5_382] := by decide
theorem s4_237_safe : Safe 9 4 s4_237 := by
  apply safe_succ 8 4 s4_237 [s5_382] (by decide) s4_237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_382_safe
def s4_238 : State := ⟨[1,4,96,160], 1461501637671185285203851458712368708759249289502, 1, 1, 1, 0⟩
theorem s4_238_edges : next config 4 s4_238 = [s5_721, s5_608, s5_319, s5_383, s5_240, s5_264] := by decide
theorem s4_238_safe : Safe 9 4 s4_238 := by
  apply safe_succ 8 4 s4_238 [s5_721, s5_608, s5_319, s5_383, s5_240, s5_264] (by decide) s4_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_721_safe
  · subst z; exact s5_608_safe
  · subst z; exact s5_319_safe
  · subst z; exact s5_383_safe
  · subst z; exact s5_240_safe
  · subst z; exact s5_264_safe
def s4_239 : State := ⟨[1,4,96,160], 1461501637671185285203851458712368708759249290006, 1, 1, 1, 0⟩
theorem s4_239_edges : next config 4 s4_239 = [s5_384, s5_241] := by decide
theorem s4_239_safe : Safe 9 4 s4_239 := by
  apply safe_succ 8 4 s4_239 [s5_384, s5_241] (by decide) s4_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_384_safe
  · subst z; exact s5_241_safe
def s4_240 : State := ⟨[1,4,96,160], 1461501637671185285203851458712368708759249293590, 2, 2, 1, 0⟩
theorem s4_240_edges : next config 4 s4_240 = [s5_1506, s5_1559, s5_831, s5_1155, s5_302, s5_385, s5_477, s5_232, s5_242, s5_265] := by decide
theorem s4_240_safe : Safe 9 4 s4_240 := by
  apply safe_succ 8 4 s4_240 [s5_1506, s5_1559, s5_831, s5_1155, s5_302, s5_385, s5_477, s5_232, s5_242, s5_265] (by decide) s4_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1506_safe
  · subst z; exact s5_1559_safe
  · subst z; exact s5_831_safe
  · subst z; exact s5_1155_safe
  · subst z; exact s5_302_safe
  · subst z; exact s5_385_safe
  · subst z; exact s5_477_safe
  · subst z; exact s5_232_safe
  · subst z; exact s5_242_safe
  · subst z; exact s5_265_safe
def s4_241 : State := ⟨[1,4,96,160], 1461501637671185285203851458712368708767839224086, 1, 1, 1, 0⟩
theorem s4_241_edges : next config 4 s4_241 = [s5_609, s5_386] := by decide
theorem s4_241_safe : Safe 9 4 s4_241 := by
  apply safe_succ 8 4 s4_241 [s5_609, s5_386] (by decide) s4_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_609_safe
  · subst z; exact s5_386_safe
def s4_242 : State := ⟨[1,4,96,160], 1461501637671185285203851458749262196906668392726, 1, 1, 1, 0⟩
theorem s4_242_edges : next config 4 s4_242 = [s5_722, s5_610, s5_320, s5_387, s5_243, s5_266] := by decide
theorem s4_242_safe : Safe 9 4 s4_242 := by
  apply safe_succ 8 4 s4_242 [s5_722, s5_610, s5_320, s5_387, s5_243, s5_266] (by decide) s4_242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_722_safe
  · subst z; exact s5_610_safe
  · subst z; exact s5_320_safe
  · subst z; exact s5_387_safe
  · subst z; exact s5_243_safe
  · subst z; exact s5_266_safe
def s4_243 : State := ⟨[1,4,96,160], 1461501637671185285203851459007516613938602115350, 2, 2, 1, 0⟩
theorem s4_243_edges : next config 4 s4_243 = [s5_388] := by decide
theorem s4_243_safe : Safe 9 4 s4_243 := by
  apply safe_succ 8 4 s4_243 [s5_388] (by decide) s4_243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_388_safe
def s4_244 : State := ⟨[1,4,96,160], 1461501637671185285362307783740897383946337190166, 1, 1, 1, 0⟩
theorem s4_244_edges : next config 4 s4_244 = [s5_611, s5_389, s5_244] := by decide
theorem s4_244_safe : Safe 9 4 s4_244 := by
  apply safe_succ 8 4 s4_244 [s5_611, s5_389, s5_244] (by decide) s4_244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_611_safe
  · subst z; exact s5_389_safe
  · subst z; exact s5_244_safe
def s4_245 : State := ⟨[1,4,96,160], 1461501637671185286471502058940598110255952494870, 2, 2, 1, 0⟩
theorem s4_245_edges : next config 4 s4_245 = [s5_832, s5_390, s5_245, s5_267] := by decide
theorem s4_245_safe : Safe 9 4 s4_245 := by
  apply safe_succ 8 4 s4_245 [s5_832, s5_390, s5_245, s5_267] (by decide) s4_245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_832_safe
  · subst z; exact s5_390_safe
  · subst z; exact s5_245_safe
  · subst z; exact s5_267_safe
def s4_246 : State := ⟨[1,4,96,160], 4384504912332991121611221124144934748071114375446, 1, 1, 1, 0⟩
theorem s4_246_edges : next config 4 s4_246 = [s5_612, s5_392] := by decide
theorem s4_246_safe : Safe 9 4 s4_246 := by
  apply safe_succ 8 4 s4_246 [s5_612, s5_392] (by decide) s4_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_612_safe
  · subst z; exact s5_392_safe
def s4_247 : State := ⟨[1,4,96,161], 2923003275002088203407536291428651728423771767062, 1, 1, 1, 0⟩
theorem s4_247_edges : next config 4 s4_247 = [s5_613, s5_393, s5_251] := by decide
theorem s4_247_safe : Safe 9 4 s4_247 := by
  apply safe_succ 8 4 s4_247 [s5_613, s5_393, s5_251] (by decide) s4_247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_613_safe
  · subst z; exact s5_393_safe
  · subst z; exact s5_251_safe
def s4_248 : State := ⟨[1,4,96,162], 25108406947392729606368181200329325475124137975310257815830, 0, 0, 1, 0⟩
theorem s4_248_edges : next config 4 s4_248 = [s5_614, s5_394] := by decide
theorem s4_248_safe : Safe 9 4 s4_248 := by
  apply safe_succ 8 4 s4_248 [s5_614, s5_394] (by decide) s4_248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_614_safe
  · subst z; exact s5_394_safe
def s4_249 : State := ⟨[1,4,96,162], 31385508682779410368842841155853238037372994990047219482902, 0, 0, 1, 0⟩
theorem s4_249_edges : next config 4 s4_249 = [s5_615, s5_395] := by decide
theorem s4_249_safe : Safe 9 4 s4_249 := by
  apply safe_succ 8 4 s4_249 [s5_615, s5_395] (by decide) s4_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_615_safe
  · subst z; exact s5_395_safe
def s4_250 : State := ⟨[1,4,96,163], 11692013102390329381839029922360095920668459204886, 0, 0, 1, 0⟩
theorem s4_250_edges : next config 4 s4_250 = [s5_616, s5_396, s5_252] := by decide
theorem s4_250_safe : Safe 9 4 s4_250 := by
  apply safe_succ 8 4 s4_250 [s5_616, s5_396, s5_252] (by decide) s4_250_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_616_safe
  · subst z; exact s5_396_safe
  · subst z; exact s5_252_safe
def s4_251 : State := ⟨[1,4,96,163], 11692013103070894115680906849286845135531995627798, 0, 0, 1, 0⟩
theorem s4_251_edges : next config 4 s4_251 = [s5_617, s5_397, s5_253] := by decide
theorem s4_251_safe : Safe 9 4 s4_251 := by
  apply safe_succ 8 4 s4_251 [s5_617, s5_397, s5_253] (by decide) s4_251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_617_safe
  · subst z; exact s5_397_safe
  · subst z; exact s5_253_safe
def s4_252 : State := ⟨[1,4,96,163], 14615016374329876282878891880085665100526178599190, 0, 0, 1, 0⟩
theorem s4_252_edges : next config 4 s4_252 = [s5_618, s5_398, s5_254] := by decide
theorem s4_252_safe : Safe 9 4 s4_252 := by
  apply safe_succ 8 4 s4_252 [s5_618, s5_398, s5_254] (by decide) s4_252_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_618_safe
  · subst z; exact s5_398_safe
  · subst z; exact s5_254_safe
def s4_253 : State := ⟨[1,4,96,163], 16076518010980214467240699785875198905318574719254, 0, 0, 1, 0⟩
theorem s4_253_edges : next config 4 s4_253 = [s5_619, s5_399, s5_255] := by decide
theorem s4_253_safe : Safe 9 4 s4_253 := by
  apply safe_succ 8 4 s4_253 [s5_619, s5_399, s5_255] (by decide) s4_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_619_safe
  · subst z; exact s5_399_safe
  · subst z; exact s5_255_safe
def s4_254 : State := ⟨[1,4,96,163], 17538019649672246853128138472444980354701580108054, 0, 0, 1, 0⟩
theorem s4_254_edges : next config 4 s4_254 = [s5_620, s5_400, s5_256] := by decide
theorem s4_254_safe : Safe 9 4 s4_254 := by
  apply safe_succ 8 4 s4_254 [s5_620, s5_400, s5_256] (by decide) s4_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_620_safe
  · subst z; exact s5_400_safe
  · subst z; exact s5_256_safe
def s4_255 : State := ⟨[1,4,96,163], 18999521285642020303648069451307764944630439805206, 0, 0, 1, 0⟩
theorem s4_255_edges : next config 4 s4_255 = [s5_621, s5_401, s5_257] := by decide
theorem s4_255_safe : Safe 9 4 s4_255 := by
  apply safe_succ 8 4 s4_255 [s5_621, s5_401, s5_257] (by decide) s4_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_621_safe
  · subst z; exact s5_401_safe
  · subst z; exact s5_257_safe
def s4_256 : State := ⟨[1,4,96,170], 1502423683177869611748071928512188528325129043771670, 0, 0, 1, 0⟩
theorem s4_256_edges : next config 4 s4_256 = [s5_1592, s5_402, s5_258] := by decide
theorem s4_256_safe : Safe 9 4 s4_256 := by
  apply safe_succ 8 4 s4_256 [s5_1592, s5_402, s5_258] (by decide) s4_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1592_safe
  · subst z; exact s5_402_safe
  · subst z; exact s5_258_safe
def s4_257 : State := ⟨[1,4,96,170], 1503885184813839385198591859491051312915057903468822, 0, 0, 1, 0⟩
theorem s4_257_edges : next config 4 s4_257 = [s5_1593, s5_403, s5_259] := by decide
theorem s4_257_safe : Safe 9 4 s4_257 := by
  apply safe_succ 8 4 s4_257 [s5_1593, s5_403, s5_259] (by decide) s4_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1593_safe
  · subst z; exact s5_403_safe
  · subst z; exact s5_259_safe
def s4_258 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042098441133567351259422, 1, 1, 1, 0⟩
theorem s4_258_edges : next config 4 s4_258 = [s5_723, s5_622, s5_321, s5_406] := by decide
theorem s4_258_safe : Safe 9 4 s4_258 := by
  apply safe_succ 8 4 s4_258 [s5_723, s5_622, s5_321, s5_406] (by decide) s4_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_723_safe
  · subst z; exact s5_622_safe
  · subst z; exact s5_321_safe
  · subst z; exact s5_406_safe
def s4_259 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042098441133567351259926, 1, 1, 1, 0⟩
theorem s4_259_edges : next config 4 s4_259 = [s5_407] := by decide
theorem s4_259_safe : Safe 9 4 s4_259 := by
  apply safe_succ 8 4 s4_259 [s5_407] (by decide) s4_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_407_safe
def s4_260 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042098441133567351263510, 2, 2, 1, 0⟩
theorem s4_260_edges : next config 4 s4_260 = [s5_1507, s5_1594, s5_835, s5_1159, s5_303, s5_408, s5_478, s5_270, s5_274, s5_277] := by decide
theorem s4_260_safe : Safe 9 4 s4_260 := by
  apply safe_succ 8 4 s4_260 [s5_1507, s5_1594, s5_835, s5_1159, s5_303, s5_408, s5_478, s5_270, s5_274, s5_277] (by decide) s4_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1507_safe
  · subst z; exact s5_1594_safe
  · subst z; exact s5_835_safe
  · subst z; exact s5_1159_safe
  · subst z; exact s5_303_safe
  · subst z; exact s5_408_safe
  · subst z; exact s5_478_safe
  · subst z; exact s5_270_safe
  · subst z; exact s5_274_safe
  · subst z; exact s5_277_safe
def s4_261 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042098441133575941194006, 1, 1, 1, 0⟩
theorem s4_261_edges : next config 4 s4_261 = [s5_623, s5_409] := by decide
theorem s4_261_safe : Safe 9 4 s4_261 := by
  apply safe_succ 8 4 s4_261 [s5_623, s5_409] (by decide) s4_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_623_safe
  · subst z; exact s5_409_safe
def s4_262 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042135334621714770362646, 1, 1, 1, 0⟩
theorem s4_262_edges : next config 4 s4_262 = [s5_724, s5_624, s5_322, s5_410] := by decide
theorem s4_262_safe : Safe 9 4 s4_262 := by
  apply safe_succ 8 4 s4_262 [s5_724, s5_624, s5_322, s5_410] (by decide) s4_262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_724_safe
  · subst z; exact s5_624_safe
  · subst z; exact s5_322_safe
  · subst z; exact s5_410_safe
def s4_263 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042393589038746704085270, 2, 2, 1, 0⟩
theorem s4_263_edges : next config 4 s4_263 = [s5_411] := by decide
theorem s4_263_safe : Safe 9 4 s4_263 := by
  apply safe_succ 8 4 s4_263 [s5_411] (by decide) s4_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_411_safe
def s4_264 : State := ⟨[1,4,96,192], 6277101735386680764176071790366289367126969808754439160086, 1, 1, 1, 0⟩
theorem s4_264_edges : next config 4 s4_264 = [s5_625, s5_412] := by decide
theorem s4_264_safe : Safe 9 4 s4_264 := by
  apply safe_succ 8 4 s4_264 [s5_625, s5_412] (by decide) s4_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_625_safe
  · subst z; exact s5_412_safe
def s4_265 : State := ⟨[1,4,96,192], 6277101735386680764176071791475483642326670535064054464790, 2, 2, 1, 0⟩
theorem s4_265_edges : next config 4 s4_265 = [s5_1595, s5_836, s5_413, s5_271, s5_275] := by decide
theorem s4_265_safe : Safe 9 4 s4_265 := by
  apply safe_succ 8 4 s4_265 [s5_1595, s5_836, s5_413, s5_271, s5_275] (by decide) s4_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1595_safe
  · subst z; exact s5_836_safe
  · subst z; exact s5_413_safe
  · subst z; exact s5_271_safe
  · subst z; exact s5_275_safe
def s4_266 : State := ⟨[1,4,96,192], 18831305206160042291847650636623165874303152022495420285206, 1, 1, 1, 0⟩
theorem s4_266_edges : next config 4 s4_266 = [s5_725, s5_626, s5_323, s5_415] := by decide
theorem s4_266_safe : Safe 9 4 s4_266 := by
  apply safe_succ 8 4 s4_266 [s5_725, s5_626, s5_323, s5_415] (by decide) s4_266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_725_safe
  · subst z; exact s5_626_safe
  · subst z; exact s5_323_safe
  · subst z; exact s5_415_safe
def s4_267 : State := ⟨[1,4,96,192], 106710729501573572985548702561530495699736128244991903465750, 2, 2, 1, 0⟩
theorem s4_267_edges : next config 4 s4_267 = [s5_416] := by decide
theorem s4_267_safe : Safe 9 4 s4_267 := by
  apply safe_succ 8 4 s4_267 [s5_416] (by decide) s4_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_416_safe
def s4_268 : State := ⟨[1,4,96,193], 12554203470773361528011861213415499458237690066178804875542, 1, 1, 1, 0⟩
theorem s4_268_edges : next config 4 s4_268 = [s5_726, s5_627, s5_324, s5_417] := by decide
theorem s4_268_safe : Safe 9 4 s4_268 := by
  apply safe_succ 8 4 s4_268 [s5_726, s5_627, s5_324, s5_417] (by decide) s4_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_726_safe
  · subst z; exact s5_627_safe
  · subst z; exact s5_324_safe
  · subst z; exact s5_417_safe
def s4_269 : State := ⟨[1,4,96,194], 25108406947392729606368181200329325475124137975310257815830, 0, 0, 1, 0⟩
theorem s4_269_edges : next config 4 s4_269 = [s5_628, s5_418] := by decide
theorem s4_269_safe : Safe 9 4 s4_269 := by
  apply safe_succ 8 4 s4_269 [s5_628, s5_418] (by decide) s4_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_628_safe
  · subst z; exact s5_418_safe
def s4_270 : State := ⟨[1,4,96,194], 25108406948854231242337954650849256453986922565239117512982, 0, 0, 1, 0⟩
theorem s4_270_edges : next config 4 s4_270 = [s5_629, s5_419] := by decide
theorem s4_270_safe : Safe 9 4 s4_270 := by
  apply safe_succ 8 4 s4_270 [s5_629, s5_419] (by decide) s4_270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_629_safe
  · subst z; exact s5_419_safe
def s4_271 : State := ⟨[1,4,96,196], 100433627766186892221712913138322829283928920705707221778710, 2, 2, 1, 0⟩
theorem s4_271_edges : next config 4 s4_271 = [s5_420] := by decide
theorem s4_271_safe : Safe 9 4 s4_271 := by
  apply safe_succ 8 4 s4_271 [s5_420] (by decide) s4_271_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_420_safe
def s4_272 : State := ⟨[1,4,96,210], 1645504557321206042244173864763307681469358588308292139762123030, 0, 0, 1, 0⟩
theorem s4_272_edges : next config 4 s4_272 = [s5_778, s5_630, s5_421, s5_280] := by decide
theorem s4_272_safe : Safe 9 4 s4_272 := by
  apply safe_succ 8 4 s4_272 [s5_778, s5_630, s5_421, s5_280] (by decide) s4_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_778_safe
  · subst z; exact s5_630_safe
  · subst z; exact s5_421_safe
  · subst z; exact s5_280_safe
def s4_273 : State := ⟨[1,4,96,210], 1645504557321206042266473248832370620857040453082510774195257622, 0, 0, 1, 0⟩
theorem s4_273_edges : next config 4 s4_273 = [s5_779, s5_631, s5_422, s5_281] := by decide
theorem s4_273_safe : Safe 9 4 s4_273 := by
  apply safe_succ 8 4 s4_273 [s5_779, s5_631, s5_422, s5_281] (by decide) s4_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_779_safe
  · subst z; exact s5_631_safe
  · subst z; exact s5_422_safe
  · subst z; exact s5_281_safe
def s4_274 : State := ⟨[1,4,96,210], 1645529665728147588878026227126878019568880124639476549876252950, 0, 0, 1, 0⟩
theorem s4_274_edges : next config 4 s4_274 = [s5_780, s5_632, s5_423, s5_282] := by decide
theorem s4_274_safe : Safe 9 4 s4_274 := by
  apply safe_succ 8 4 s4_274 [s5_780, s5_632, s5_423, s5_282] (by decide) s4_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_780_safe
  · subst z; exact s5_632_safe
  · subst z; exact s5_423_safe
  · subst z; exact s5_282_safe
def s4_275 : State := ⟨[1,4,96,210], 1645535942829882975558788701786833543481442373496491286837920022, 0, 0, 1, 0⟩
theorem s4_275_edges : next config 4 s4_275 = [s5_781, s5_633, s5_424, s5_283] := by decide
theorem s4_275_safe : Safe 9 4 s4_275 := by
  apply safe_succ 8 4 s4_275 [s5_781, s5_633, s5_424, s5_283] (by decide) s4_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_781_safe
  · subst z; exact s5_633_safe
  · subst z; exact s5_424_safe
  · subst z; exact s5_283_safe
def s4_276 : State := ⟨[1,4,96,210], 2056880696651507552716012563677585754536581546400312294008488214, 0, 0, 1, 0⟩
theorem s4_276_edges : next config 4 s4_276 = [s5_782, s5_634, s5_425, s5_284] := by decide
theorem s4_276_safe : Safe 9 4 s4_276 := by
  apply safe_succ 8 4 s4_276 [s5_782, s5_634, s5_425, s5_284] (by decide) s4_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_782_safe
  · subst z; exact s5_634_safe
  · subst z; exact s5_425_safe
  · subst z; exact s5_284_safe
def s4_277 : State := ⟨[1,4,96,210], 2056886973753242939374475654268478339061461930483108396537020694, 0, 0, 1, 0⟩
theorem s4_277_edges : next config 4 s4_277 = [s5_783, s5_635, s5_426, s5_285] := by decide
theorem s4_277_safe : Safe 9 4 s4_277 := by
  apply safe_succ 8 4 s4_277 [s5_783, s5_635, s5_426, s5_285] (by decide) s4_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_783_safe
  · subst z; exact s5_635_safe
  · subst z; exact s5_426_safe
  · subst z; exact s5_285_safe
def s4_278 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048536658170206926995742, 1, 1, 1, 0⟩
theorem s4_278_edges : next config 4 s4_278 = [s5_727, s5_786, s5_636, s5_325, s5_427, s5_290] := by decide
theorem s4_278_safe : Safe 9 4 s4_278 := by
  apply safe_succ 8 4 s4_278 [s5_727, s5_786, s5_636, s5_325, s5_427, s5_290] (by decide) s4_278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_727_safe
  · subst z; exact s5_786_safe
  · subst z; exact s5_636_safe
  · subst z; exact s5_325_safe
  · subst z; exact s5_427_safe
  · subst z; exact s5_290_safe
def s4_279 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048536658170206926996246, 1, 1, 1, 0⟩
theorem s4_279_edges : next config 4 s4_279 = [s5_428] := by decide
theorem s4_279_safe : Safe 9 4 s4_279 := by
  apply safe_succ 8 4 s4_279 [s5_428] (by decide) s4_279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_428_safe
def s4_280 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048536658170206926999830, 2, 2, 1, 0⟩
theorem s4_280_edges : next config 4 s4_280 = [s5_1508, s5_1600, s5_837, s5_1160, s5_304, s5_429, s5_479, s5_287, s5_293] := by decide
theorem s4_280_safe : Safe 9 4 s4_280 := by
  apply safe_succ 8 4 s4_280 [s5_1508, s5_1600, s5_837, s5_1160, s5_304, s5_429, s5_479, s5_287, s5_293] (by decide) s4_280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1508_safe
  · subst z; exact s5_1600_safe
  · subst z; exact s5_837_safe
  · subst z; exact s5_1160_safe
  · subst z; exact s5_304_safe
  · subst z; exact s5_429_safe
  · subst z; exact s5_479_safe
  · subst z; exact s5_287_safe
  · subst z; exact s5_293_safe
def s4_281 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048536658170215516930326, 1, 1, 1, 0⟩
theorem s4_281_edges : next config 4 s4_281 = [s5_637, s5_430] := by decide
theorem s4_281_safe : Safe 9 4 s4_281 := by
  apply safe_succ 8 4 s4_281 [s5_637, s5_430] (by decide) s4_281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_637_safe
  · subst z; exact s5_430_safe
def s4_282 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048573551658354346098966, 1, 1, 1, 0⟩
theorem s4_282_edges : next config 4 s4_282 = [s5_728, s5_787, s5_638, s5_326, s5_431, s5_291] := by decide
theorem s4_282_safe : Safe 9 4 s4_282 := by
  apply safe_succ 8 4 s4_282 [s5_728, s5_787, s5_638, s5_326, s5_431, s5_291] (by decide) s4_282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_728_safe
  · subst z; exact s5_787_safe
  · subst z; exact s5_638_safe
  · subst z; exact s5_326_safe
  · subst z; exact s5_431_safe
  · subst z; exact s5_291_safe
def s4_283 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048831806075386279821590, 2, 2, 1, 0⟩
theorem s4_283_edges : next config 4 s4_283 = [s5_432] := by decide
theorem s4_283_safe : Safe 9 4 s4_283 := by
  apply safe_succ 8 4 s4_283 [s5_432] (by decide) s4_283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_432_safe
def s4_284 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040795767373565186845394014896406, 1, 1, 1, 0⟩
theorem s4_284_edges : next config 4 s4_284 = [s5_639, s5_433] := by decide
theorem s4_284_safe : Safe 9 4 s4_284 := by
  apply safe_succ 8 4 s4_284 [s5_639, s5_433] (by decide) s4_284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_639_safe
  · subst z; exact s5_433_safe
def s4_285 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913041904961648764887571703630201110, 2, 2, 1, 0⟩
theorem s4_285_edges : next config 4 s4_285 = [s5_838, s5_434] := by decide
theorem s4_285_safe : Safe 9 4 s4_285 := by
  apply safe_succ 8 4 s4_285 [s5_838, s5_434] (by decide) s4_285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_838_safe
  · subst z; exact s5_434_safe
def s4_286 : State := ⟨[1,4,96,224], 80879840001451919384001045261399174387911599893617803132414147494166, 1, 1, 1, 0⟩
theorem s4_286_edges : next config 4 s4_286 = [s5_640, s5_436] := by decide
theorem s4_286_safe : Safe 9 4 s4_286 := by
  apply safe_succ 8 4 s4_286 [s5_640, s5_436] (by decide) s4_286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_640_safe
  · subst z; exact s5_436_safe
def s4_287 : State := ⟨[1,4,96,224], 458319093341560876509339256479674003818831621809185817867864690983190, 2, 2, 1, 0⟩
theorem s4_287_edges : next config 4 s4_287 = [s5_839, s5_437] := by decide
theorem s4_287_safe : Safe 9 4 s4_287 := by
  apply safe_succ 8 4 s4_287 [s5_839, s5_437] (by decide) s4_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_839_safe
  · subst z; exact s5_437_safe
def s4_288 : State := ⟨[1,4,96,225], 53919893334301279589334030174379543714432911796105759326497625145622, 1, 1, 1, 0⟩
theorem s4_288_edges : next config 4 s4_288 = [s5_641, s5_438] := by decide
theorem s4_288_safe : Safe 9 4 s4_288 := by
  apply safe_succ 8 4 s4_288 [s5_641, s5_438] (by decide) s4_288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_641_safe
  · subst z; exact s5_438_safe
def s4_289 : State := ⟨[1,4,96,228], 431359146674410236714672241392654373146462127986873474788257783939350, 2, 2, 1, 0⟩
theorem s4_289_edges : next config 4 s4_289 = [s5_840, s5_439] := by decide
theorem s4_289_safe : Safe 9 4 s4_289 := by
  apply safe_succ 8 4 s4_289 [s5_840, s5_439] (by decide) s4_289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_840_safe
  · subst z; exact s5_439_safe
def s4_290 : State := ⟨[1,4,97,128], 340282367158622951024614364290404651286, 2, 2, 0, 0⟩
theorem s4_290_edges : next config 4 s4_290 = [s5_986, s5_294, s5_296, s5_305, s5_295, s5_297, s5_300, s5_302] := by decide
theorem s4_290_safe : Safe 9 4 s4_290 := by
  apply safe_succ 8 4 s4_290 [s5_986, s5_294, s5_296, s5_305, s5_295, s5_297, s5_300, s5_302] (by decide) s4_290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_986_safe
  · subst z; exact s5_294_safe
  · subst z; exact s5_296_safe
  · subst z; exact s5_305_safe
  · subst z; exact s5_295_safe
  · subst z; exact s5_297_safe
  · subst z; exact s5_300_safe
  · subst z; exact s5_302_safe
def s4_291 : State := ⟨[1,4,97,140], 1399581375146057584712421000123721290154262, 0, 0, 1, 0⟩
theorem s4_291_edges : next config 4 s4_291 = [] := by decide
theorem s4_291_safe : Safe 9 4 s4_291 := by
  apply safe_succ 8 4 s4_291 [] (by decide) s4_291_edges
  simp
def s4_292 : State := ⟨[1,4,97,140], 1481249143207082815943630905907345660903702, 0, 0, 1, 0⟩
theorem s4_292_edges : next config 4 s4_292 = [] := by decide
theorem s4_292_safe : Safe 9 4 s4_292 := by
  apply safe_succ 8 4 s4_292 [] (by decide) s4_292_edges
  simp
def s4_293 : State := ⟨[1,4,97,145], 44602511244162246782949387908875876953030934, 0, 0, 1, 0⟩
theorem s4_293_edges : next config 4 s4_293 = [s5_642] := by decide
theorem s4_293_safe : Safe 9 4 s4_293 := by
  apply safe_succ 8 4 s4_293 [s5_642] (by decide) s4_293_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_642_safe
def s4_294 : State := ⟨[1,4,97,145], 66902575877959028047558179432309374922588438, 0, 0, 1, 0⟩
theorem s4_294_edges : next config 4 s4_294 = [s5_643] := by decide
theorem s4_294_safe : Safe 9 4 s4_294 := by
  apply safe_succ 8 4 s4_294 [s5_643] (by decide) s4_294_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_643_safe
def s4_295 : State := ⟨[1,4,97,162], 5846006551025023507657116135743244872641207664918, 0, 0, 1, 0⟩
theorem s4_295_edges : next config 4 s4_295 = [s5_644] := by decide
theorem s4_295_safe : Safe 9 4 s4_295 := by
  apply safe_succ 8 4 s4_295 [s5_644] (by decide) s4_295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_644_safe
def s4_296 : State := ⟨[1,4,97,162], 7307508186994796958177047114606029462570067362070, 0, 0, 1, 0⟩
theorem s4_296_edges : next config 4 s4_296 = [s5_645] := by decide
theorem s4_296_safe : Safe 9 4 s4_296 := by
  apply safe_succ 8 4 s4_296 [s5_645] (by decide) s4_296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_645_safe
def s4_297 : State := ⟨[1,4,100,128], 340282368267817226224315090600019951902, 1, 1, 0, 0⟩
theorem s4_297_edges : next config 4 s4_297 = [s5_988, s5_306, s5_312, s5_327, s5_308, s5_314, s5_316, s5_319] := by decide
theorem s4_297_safe : Safe 9 4 s4_297 := by
  apply safe_succ 8 4 s4_297 [s5_988, s5_306, s5_312, s5_327, s5_308, s5_314, s5_316, s5_319] (by decide) s4_297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_988_safe
  · subst z; exact s5_306_safe
  · subst z; exact s5_312_safe
  · subst z; exact s5_327_safe
  · subst z; exact s5_308_safe
  · subst z; exact s5_314_safe
  · subst z; exact s5_316_safe
  · subst z; exact s5_319_safe
def s4_298 : State := ⟨[1,4,100,128], 340282368267817226261208578747439055126, 1, 1, 0, 0⟩
theorem s4_298_edges : next config 4 s4_298 = [s5_990, s5_307, s5_313, s5_328, s5_309, s5_315, s5_317, s5_320] := by decide
theorem s4_298_safe : Safe 9 4 s4_298 := by
  apply safe_succ 8 4 s4_298 [s5_990, s5_307, s5_313, s5_328, s5_309, s5_315, s5_317, s5_320] (by decide) s4_298_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_990_safe
  · subst z; exact s5_307_safe
  · subst z; exact s5_313_safe
  · subst z; exact s5_328_safe
  · subst z; exact s5_309_safe
  · subst z; exact s5_315_safe
  · subst z; exact s5_317_safe
  · subst z; exact s5_320_safe
def s4_299 : State := ⟨[1,4,100,131], 3743106037477201860858061164917702066454, 0, 0, 1, 0⟩
theorem s4_299_edges : next config 4 s4_299 = [] := by decide
theorem s4_299_safe : Safe 9 4 s4_299 := by
  apply safe_succ 8 4 s4_299 [] (by decide) s4_299_edges
  simp
def s4_300 : State := ⟨[1,4,100,131], 4423670771319078787784810379781238489366, 0, 0, 1, 0⟩
theorem s4_300_edges : next config 4 s4_300 = [] := by decide
theorem s4_300_safe : Safe 9 4 s4_300 := by
  apply safe_succ 8 4 s4_300 [] (by decide) s4_300_edges
  simp
def s4_301 : State := ⟨[1,4,100,145], 44602511244163355977224587609602186568335638, 0, 0, 1, 0⟩
theorem s4_301_edges : next config 4 s4_301 = [s5_841] := by decide
theorem s4_301_safe : Safe 9 4 s4_301 := by
  apply safe_succ 8 4 s4_301 [s5_841] (by decide) s4_301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_841_safe
def s4_302 : State := ⟨[1,4,100,145], 66902575877960137241833379133035684537893142, 0, 0, 1, 0⟩
theorem s4_302_edges : next config 4 s4_302 = [s5_842] := by decide
theorem s4_302_safe : Safe 9 4 s4_302 := by
  apply safe_succ 8 4 s4_302 [s5_842] (by decide) s4_302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_842_safe
def s4_303 : State := ⟨[1,4,100,146], 89204682205958444137222950904113773116719382, 0, 0, 1, 0⟩
theorem s4_303_edges : next config 4 s4_303 = [] := by decide
theorem s4_303_safe : Safe 9 4 s4_303 := by
  apply safe_succ 8 4 s4_303 [] (by decide) s4_303_edges
  simp
def s4_304 : State := ⟨[1,4,100,146], 111504066275021383524904815678332407549853974, 0, 0, 1, 0⟩
theorem s4_304_edges : next config 4 s4_304 = [] := by decide
theorem s4_304_safe : Safe 9 4 s4_304 := by
  apply safe_succ 8 4 s4_304 [] (by decide) s4_304_edges
  simp
def s4_305 : State := ⟨[1,4,100,162], 5846006551025023508766310410942945598950822969622, 0, 0, 1, 0⟩
theorem s4_305_edges : next config 4 s4_305 = [] := by decide
theorem s4_305_safe : Safe 9 4 s4_305 := by
  apply safe_succ 8 4 s4_305 [] (by decide) s4_305_edges
  simp
def s4_306 : State := ⟨[1,4,100,162], 7307508186994796959286241389805730188879682666774, 0, 0, 1, 0⟩
theorem s4_306_edges : next config 4 s4_306 = [] := by decide
theorem s4_306_safe : Safe 9 4 s4_306 := by
  apply safe_succ 8 4 s4_306 [] (by decide) s4_306_edges
  simp
def s4_307 : State := ⟨[1,4,100,176], 95780971326419139128295580155656266563910156662407446, 0, 0, 1, 0⟩
theorem s4_307_edges : next config 4 s4_307 = [] := by decide
theorem s4_307_safe : Safe 9 4 s4_307 := by
  apply safe_succ 8 4 s4_307 [] (by decide) s4_307_edges
  simp
def s4_308 : State := ⟨[1,4,100,176], 95782432805755724832683160698953264574281451088970006, 0, 0, 1, 0⟩
theorem s4_308_edges : next config 4 s4_308 = [] := by decide
theorem s4_308_safe : Safe 9 4 s4_308 := by
  apply safe_succ 8 4 s4_308 [] (by decide) s4_308_edges
  simp
def s4_309 : State := ⟨[1,4,100,193], 12554203470773361528692425948525026985355775194391625400598, 0, 0, 1, 0⟩
theorem s4_309_edges : next config 4 s4_309 = [] := by decide
theorem s4_309_safe : Safe 9 4 s4_309 := by
  apply safe_succ 8 4 s4_309 [] (by decide) s4_309_edges
  simp
def s4_310 : State := ⟨[1,4,100,193], 18831305206160042291847650637890816474531381423992123490582, 0, 0, 1, 0⟩
theorem s4_310_edges : next config 4 s4_310 = [] := by decide
theorem s4_310_safe : Safe 9 4 s4_310 := by
  apply safe_succ 8 4 s4_310 [] (by decide) s4_310_edges
  simp
def s4_311 : State := ⟨[1,4,100,194], 25108406941546723057044569528782236744487235298183230849302, 0, 0, 1, 0⟩
theorem s4_311_edges : next config 4 s4_311 = [] := by decide
theorem s4_311_safe : Safe 9 4 s4_311 := by
  apply safe_succ 8 4 s4_311 [] (by decide) s4_311_edges
  simp
def s4_312 : State := ⟨[1,4,100,194], 31385508676933403819519229484306149306736092312920192516374, 0, 0, 1, 0⟩
theorem s4_312_edges : next config 4 s4_312 = [] := by decide
theorem s4_312_safe : Safe 9 4 s4_312 := by
  apply safe_succ 8 4 s4_312 [] (by decide) s4_312_edges
  simp
def s4_313 : State := ⟨[1,4,104,128], 340282387282576229647756113050568032542, 1, 1, 0, 0⟩
theorem s4_313_edges : next config 4 s4_313 = [s5_991, s5_747, s5_646, s5_451, s5_329, s5_349, s5_440, s5_338, s5_358, s5_371, s5_383] := by decide
theorem s4_313_safe : Safe 9 4 s4_313 := by
  apply safe_succ 8 4 s4_313 [s5_991, s5_747, s5_646, s5_451, s5_329, s5_349, s5_440, s5_338, s5_358, s5_371, s5_383] (by decide) s4_313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_991_safe
  · subst z; exact s5_747_safe
  · subst z; exact s5_646_safe
  · subst z; exact s5_451_safe
  · subst z; exact s5_329_safe
  · subst z; exact s5_349_safe
  · subst z; exact s5_440_safe
  · subst z; exact s5_338_safe
  · subst z; exact s5_358_safe
  · subst z; exact s5_371_safe
  · subst z; exact s5_383_safe
def s4_314 : State := ⟨[1,4,104,128], 340282387282576229647756113050568033046, 1, 1, 0, 0⟩
theorem s4_314_edges : next config 4 s4_314 = [s5_992, s5_330, s5_350, s5_441, s5_339, s5_359, s5_372, s5_384] := by decide
theorem s4_314_safe : Safe 9 4 s4_314 := by
  apply safe_succ 8 4 s4_314 [s5_992, s5_330, s5_350, s5_441, s5_339, s5_359, s5_372, s5_384] (by decide) s4_314_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_992_safe
  · subst z; exact s5_330_safe
  · subst z; exact s5_350_safe
  · subst z; exact s5_441_safe
  · subst z; exact s5_339_safe
  · subst z; exact s5_359_safe
  · subst z; exact s5_372_safe
  · subst z; exact s5_384_safe
def s4_315 : State := ⟨[1,4,104,128], 340282387282576229647756113050568036630, 2, 2, 0, 0⟩
theorem s4_315_edges : next config 4 s4_315 = [s5_843, s5_993, s5_1161, s5_331, s5_351, s5_442, s5_340, s5_360, s5_373, s5_385] := by decide
theorem s4_315_safe : Safe 9 4 s4_315 := by
  apply safe_succ 8 4 s4_315 [s5_843, s5_993, s5_1161, s5_331, s5_351, s5_442, s5_340, s5_360, s5_373, s5_385] (by decide) s4_315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_843_safe
  · subst z; exact s5_993_safe
  · subst z; exact s5_1161_safe
  · subst z; exact s5_331_safe
  · subst z; exact s5_351_safe
  · subst z; exact s5_442_safe
  · subst z; exact s5_340_safe
  · subst z; exact s5_360_safe
  · subst z; exact s5_373_safe
  · subst z; exact s5_385_safe
def s4_316 : State := ⟨[1,4,104,128], 340282387282576229647756113059157967126, 1, 1, 0, 0⟩
theorem s4_316_edges : next config 4 s4_316 = [s5_995, s5_647, s5_332, s5_352, s5_443, s5_341, s5_361, s5_374, s5_386] := by decide
theorem s4_316_safe : Safe 9 4 s4_316 := by
  apply safe_succ 8 4 s4_316 [s5_995, s5_647, s5_332, s5_352, s5_443, s5_341, s5_361, s5_374, s5_386] (by decide) s4_316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_995_safe
  · subst z; exact s5_647_safe
  · subst z; exact s5_332_safe
  · subst z; exact s5_352_safe
  · subst z; exact s5_443_safe
  · subst z; exact s5_341_safe
  · subst z; exact s5_361_safe
  · subst z; exact s5_374_safe
  · subst z; exact s5_386_safe
def s4_317 : State := ⟨[1,4,104,128], 340282387282576229684649601197987135766, 1, 1, 0, 0⟩
theorem s4_317_edges : next config 4 s4_317 = [s5_996, s5_748, s5_648, s5_452, s5_333, s5_353, s5_444, s5_342, s5_362, s5_375, s5_387] := by decide
theorem s4_317_safe : Safe 9 4 s4_317 := by
  apply safe_succ 8 4 s4_317 [s5_996, s5_748, s5_648, s5_452, s5_333, s5_353, s5_444, s5_342, s5_362, s5_375, s5_387] (by decide) s4_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_996_safe
  · subst z; exact s5_748_safe
  · subst z; exact s5_648_safe
  · subst z; exact s5_452_safe
  · subst z; exact s5_333_safe
  · subst z; exact s5_353_safe
  · subst z; exact s5_444_safe
  · subst z; exact s5_342_safe
  · subst z; exact s5_362_safe
  · subst z; exact s5_375_safe
  · subst z; exact s5_387_safe
def s4_318 : State := ⟨[1,4,104,128], 340282387282576229942904018229920858390, 2, 2, 0, 0⟩
theorem s4_318_edges : next config 4 s4_318 = [s5_997, s5_334, s5_354, s5_445, s5_343, s5_363, s5_376, s5_388] := by decide
theorem s4_318_safe : Safe 9 4 s4_318 := by
  apply safe_succ 8 4 s4_318 [s5_997, s5_334, s5_354, s5_445, s5_343, s5_363, s5_376, s5_388] (by decide) s4_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_997_safe
  · subst z; exact s5_334_safe
  · subst z; exact s5_354_safe
  · subst z; exact s5_445_safe
  · subst z; exact s5_343_safe
  · subst z; exact s5_363_safe
  · subst z; exact s5_376_safe
  · subst z; exact s5_388_safe
def s4_319 : State := ⟨[1,4,104,128], 340282387441032554676284788237655933206, 1, 1, 0, 0⟩
theorem s4_319_edges : next config 4 s4_319 = [s5_998, s5_649, s5_335, s5_355, s5_446, s5_344, s5_364, s5_377, s5_389] := by decide
theorem s4_319_safe : Safe 9 4 s4_319 := by
  apply safe_succ 8 4 s4_319 [s5_998, s5_649, s5_335, s5_355, s5_446, s5_344, s5_364, s5_377, s5_389] (by decide) s4_319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_998_safe
  · subst z; exact s5_649_safe
  · subst z; exact s5_335_safe
  · subst z; exact s5_355_safe
  · subst z; exact s5_446_safe
  · subst z; exact s5_344_safe
  · subst z; exact s5_364_safe
  · subst z; exact s5_377_safe
  · subst z; exact s5_389_safe
def s4_320 : State := ⟨[1,4,104,128], 340282388550226829875985514547271237910, 2, 2, 0, 0⟩
theorem s4_320_edges : next config 4 s4_320 = [s5_844, s5_999, s5_336, s5_356, s5_447, s5_345, s5_365, s5_378, s5_390] := by decide
theorem s4_320_safe : Safe 9 4 s4_320 := by
  apply safe_succ 8 4 s4_320 [s5_844, s5_999, s5_336, s5_356, s5_447, s5_345, s5_365, s5_378, s5_390] (by decide) s4_320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_844_safe
  · subst z; exact s5_999_safe
  · subst z; exact s5_336_safe
  · subst z; exact s5_356_safe
  · subst z; exact s5_447_safe
  · subst z; exact s5_345_safe
  · subst z; exact s5_365_safe
  · subst z; exact s5_378_safe
  · subst z; exact s5_390_safe
def s4_321 : State := ⟨[1,4,104,128], 340282711801129888074482896206588608790, 2, 2, 0, 0⟩
theorem s4_321_edges : next config 4 s4_321 = [s5_845, s5_1000, s5_337, s5_357, s5_448, s5_346, s5_366, s5_379, s5_391] := by decide
theorem s4_321_safe : Safe 9 4 s4_321 := by
  apply safe_succ 8 4 s4_321 [s5_845, s5_1000, s5_337, s5_357, s5_448, s5_346, s5_366, s5_379, s5_391] (by decide) s4_321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_845_safe
  · subst z; exact s5_1000_safe
  · subst z; exact s5_337_safe
  · subst z; exact s5_357_safe
  · subst z; exact s5_448_safe
  · subst z; exact s5_346_safe
  · subst z; exact s5_366_safe
  · subst z; exact s5_379_safe
  · subst z; exact s5_391_safe
def s4_322 : State := ⟨[1,4,104,131], 3743106056491960864281502187368250147094, 0, 0, 1, 0⟩
theorem s4_322_edges : next config 4 s4_322 = [s5_749, s5_650, s5_453, s5_396] := by decide
theorem s4_322_safe : Safe 9 4 s4_322 := by
  apply safe_succ 8 4 s4_322 [s5_749, s5_650, s5_453, s5_396] (by decide) s4_322_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_749_safe
  · subst z; exact s5_650_safe
  · subst z; exact s5_453_safe
  · subst z; exact s5_396_safe
def s4_323 : State := ⟨[1,4,104,131], 4423670790333837791208251402231786570006, 0, 0, 1, 0⟩
theorem s4_323_edges : next config 4 s4_323 = [s5_750, s5_651, s5_454, s5_397] := by decide
theorem s4_323_safe : Safe 9 4 s4_323 := by
  apply safe_succ 8 4 s4_323 [s5_750, s5_651, s5_454, s5_397] (by decide) s4_323_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_750_safe
  · subst z; exact s5_651_safe
  · subst z; exact s5_454_safe
  · subst z; exact s5_397_safe
def s4_324 : State := ⟨[1,4,104,137], 175245418984644946449822304332979428720918, 0, 0, 1, 0⟩
theorem s4_324_edges : next config 4 s4_324 = [] := by decide
theorem s4_324_safe : Safe 9 4 s4_324 := by
  apply safe_succ 8 4 s4_324 [] (by decide) s4_324_edges
  simp
def s4_325 : State := ⟨[1,4,104,137], 261677140182563316169519454620648554430742, 0, 0, 1, 0⟩
theorem s4_325_edges : next config 4 s4_325 = [] := by decide
theorem s4_325_safe : Safe 9 4 s4_325 := by
  apply safe_succ 8 4 s4_325 [] (by decide) s4_325_edges
  simp
def s4_326 : State := ⟨[1,4,104,140], 1399581375166181537991044141872481453539606, 0, 0, 1, 0⟩
theorem s4_326_edges : next config 4 s4_326 = [s5_846, s5_1162] := by decide
theorem s4_326_safe : Safe 9 4 s4_326 := by
  apply safe_succ 8 4 s4_326 [s5_846, s5_1162] (by decide) s4_326_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_846_safe
  · subst z; exact s5_1162_safe
def s4_327 : State := ⟨[1,4,104,140], 1481249143227206769222254047656105824289046, 0, 0, 1, 0⟩
theorem s4_327_edges : next config 4 s4_327 = [s5_847, s5_1163] := by decide
theorem s4_327_safe : Safe 9 4 s4_327 := by
  apply safe_succ 8 4 s4_327 [s5_847, s5_1163] (by decide) s4_327_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_847_safe
  · subst z; exact s5_1163_safe
def s4_328 : State := ⟨[1,4,104,145], 44602511244182370736228011050624637116416278, 0, 0, 1, 0⟩
theorem s4_328_edges : next config 4 s4_328 = [s5_848, s5_941, s5_1164, s5_751, s5_652, s5_455, s5_517, s5_482] := by decide
theorem s4_328_safe : Safe 9 4 s4_328 := by
  apply safe_succ 8 4 s4_328 [s5_848, s5_941, s5_1164, s5_751, s5_652, s5_455, s5_517, s5_482] (by decide) s4_328_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_848_safe
  · subst z; exact s5_941_safe
  · subst z; exact s5_1164_safe
  · subst z; exact s5_751_safe
  · subst z; exact s5_652_safe
  · subst z; exact s5_455_safe
  · subst z; exact s5_517_safe
  · subst z; exact s5_482_safe
def s4_329 : State := ⟨[1,4,104,145], 66902575877979152000836802574058135085973782, 0, 0, 1, 0⟩
theorem s4_329_edges : next config 4 s4_329 = [s5_849, s5_942, s5_1165, s5_752, s5_653, s5_456, s5_518, s5_483] := by decide
theorem s4_329_safe : Safe 9 4 s4_329 := by
  apply safe_succ 8 4 s4_329 [s5_849, s5_942, s5_1165, s5_752, s5_653, s5_456, s5_518, s5_483] (by decide) s4_329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_849_safe
  · subst z; exact s5_942_safe
  · subst z; exact s5_1165_safe
  · subst z; exact s5_752_safe
  · subst z; exact s5_653_safe
  · subst z; exact s5_456_safe
  · subst z; exact s5_518_safe
  · subst z; exact s5_483_safe
def s4_330 : State := ⟨[1,4,104,146], 89204682205977458896226374345136223664800022, 0, 0, 1, 0⟩
theorem s4_330_edges : next config 4 s4_330 = [s5_850, s5_753, s5_770, s5_654, s5_457, s5_381] := by decide
theorem s4_330_safe : Safe 9 4 s4_330 := by
  apply safe_succ 8 4 s4_330 [s5_850, s5_753, s5_770, s5_654, s5_457, s5_381] (by decide) s4_330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_850_safe
  · subst z; exact s5_753_safe
  · subst z; exact s5_770_safe
  · subst z; exact s5_654_safe
  · subst z; exact s5_457_safe
  · subst z; exact s5_381_safe
def s4_331 : State := ⟨[1,4,104,146], 111504066275040398283908239119354858097934614, 0, 0, 1, 0⟩
theorem s4_331_edges : next config 4 s4_331 = [s5_851, s5_754, s5_771, s5_655, s5_458, s5_382] := by decide
theorem s4_331_safe : Safe 9 4 s4_331 := by
  apply safe_succ 8 4 s4_331 [s5_851, s5_754, s5_771, s5_655, s5_458, s5_382] (by decide) s4_331_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_851_safe
  · subst z; exact s5_754_safe
  · subst z; exact s5_771_safe
  · subst z; exact s5_655_safe
  · subst z; exact s5_458_safe
  · subst z; exact s5_382_safe
def s4_332 : State := ⟨[1,4,104,161], 2923003275682652957531822822007071367225969541398, 0, 0, 1, 0⟩
theorem s4_332_edges : next config 4 s4_332 = [s5_656, s5_398] := by decide
theorem s4_332_safe : Safe 9 4 s4_332 := by
  apply safe_succ 8 4 s4_332 [s5_656, s5_398] (by decide) s4_332_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_656_safe
  · subst z; exact s5_398_safe
def s4_333 : State := ⟨[1,4,104,161], 4384504912332991141893630727796605172018365661462, 0, 0, 1, 0⟩
theorem s4_333_edges : next config 4 s4_333 = [s5_657, s5_399] := by decide
theorem s4_333_safe : Safe 9 4 s4_333 := by
  apply safe_succ 8 4 s4_333 [s5_657, s5_399] (by decide) s4_333_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_657_safe
  · subst z; exact s5_399_safe
def s4_334 : State := ⟨[1,4,104,162], 5846006551025023527781069414366386621401371050262, 0, 0, 1, 0⟩
theorem s4_334_edges : next config 4 s4_334 = [s5_1571, s5_852, s5_943, s5_755, s5_658, s5_459, s5_400, s5_402] := by decide
theorem s4_334_safe : Safe 9 4 s4_334 := by
  apply safe_succ 8 4 s4_334 [s5_1571, s5_852, s5_943, s5_755, s5_658, s5_459, s5_400, s5_402] (by decide) s4_334_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1571_safe
  · subst z; exact s5_852_safe
  · subst z; exact s5_943_safe
  · subst z; exact s5_755_safe
  · subst z; exact s5_658_safe
  · subst z; exact s5_459_safe
  · subst z; exact s5_400_safe
  · subst z; exact s5_402_safe
def s4_335 : State := ⟨[1,4,104,162], 7307508186994796978301000393229171211330230747414, 0, 0, 1, 0⟩
theorem s4_335_edges : next config 4 s4_335 = [s5_1572, s5_853, s5_944, s5_756, s5_659, s5_460, s5_401, s5_403] := by decide
theorem s4_335_safe : Safe 9 4 s4_335 := by
  apply safe_succ 8 4 s4_335 [s5_1572, s5_853, s5_944, s5_756, s5_659, s5_460, s5_401, s5_403] (by decide) s4_335_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1572_safe
  · subst z; exact s5_853_safe
  · subst z; exact s5_944_safe
  · subst z; exact s5_756_safe
  · subst z; exact s5_659_safe
  · subst z; exact s5_460_safe
  · subst z; exact s5_401_safe
  · subst z; exact s5_403_safe
def s4_336 : State := ⟨[1,4,104,176], 95780971326419139128314594914659690004932607210488086, 0, 0, 1, 0⟩
theorem s4_336_edges : next config 4 s4_336 = [s5_856, s5_757, s5_660, s5_461] := by decide
theorem s4_336_safe : Safe 9 4 s4_336 := by
  apply safe_succ 8 4 s4_336 [s5_856, s5_757, s5_660, s5_461] (by decide) s4_336_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_856_safe
  · subst z; exact s5_757_safe
  · subst z; exact s5_660_safe
  · subst z; exact s5_461_safe
def s4_337 : State := ⟨[1,4,104,176], 95782432805755724832702175457956688015303901637050646, 0, 0, 1, 0⟩
theorem s4_337_edges : next config 4 s4_337 = [s5_857, s5_758, s5_661, s5_462] := by decide
theorem s4_337_safe : Safe 9 4 s4_337 := by
  apply safe_succ 8 4 s4_337 [s5_857, s5_758, s5_661, s5_462] (by decide) s4_337_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_857_safe
  · subst z; exact s5_758_safe
  · subst z; exact s5_661_safe
  · subst z; exact s5_462_safe
def s4_338 : State := ⟨[1,4,104,193], 12554203470773361528692425967539785988779216216842173481238, 0, 0, 1, 0⟩
theorem s4_338_edges : next config 4 s4_338 = [s5_759, s5_662, s5_463] := by decide
theorem s4_338_safe : Safe 9 4 s4_338 := by
  apply safe_succ 8 4 s4_338 [s5_759, s5_662, s5_463] (by decide) s4_338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_759_safe
  · subst z; exact s5_662_safe
  · subst z; exact s5_463_safe
def s4_339 : State := ⟨[1,4,104,193], 18831305206160042291847650656905575477954822446442671571222, 0, 0, 1, 0⟩
theorem s4_339_edges : next config 4 s4_339 = [s5_760, s5_663, s5_464] := by decide
theorem s4_339_safe : Safe 9 4 s4_339 := by
  apply safe_succ 8 4 s4_339 [s5_760, s5_663, s5_464] (by decide) s4_339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_760_safe
  · subst z; exact s5_663_safe
  · subst z; exact s5_464_safe
def s4_340 : State := ⟨[1,4,104,194], 25108406941546723057044569547796995747910676320633778929942, 0, 0, 1, 0⟩
theorem s4_340_edges : next config 4 s4_340 = [s5_761, s5_664, s5_465, s5_486, s5_484, s5_404, s5_423] := by decide
theorem s4_340_safe : Safe 9 4 s4_340 := by
  apply safe_succ 8 4 s4_340 [s5_761, s5_664, s5_465, s5_486, s5_484, s5_404, s5_423] (by decide) s4_340_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_761_safe
  · subst z; exact s5_664_safe
  · subst z; exact s5_465_safe
  · subst z; exact s5_486_safe
  · subst z; exact s5_484_safe
  · subst z; exact s5_404_safe
  · subst z; exact s5_423_safe
def s4_341 : State := ⟨[1,4,104,194], 31385508676933403819519229503320908310159533335370740597014, 0, 0, 1, 0⟩
theorem s4_341_edges : next config 4 s4_341 = [s5_762, s5_665, s5_466, s5_487, s5_485, s5_405, s5_424] := by decide
theorem s4_341_safe : Safe 9 4 s4_341 := by
  apply safe_succ 8 4 s4_341 [s5_762, s5_665, s5_466, s5_487, s5_485, s5_405, s5_424] (by decide) s4_341_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_762_safe
  · subst z; exact s5_665_safe
  · subst z; exact s5_466_safe
  · subst z; exact s5_487_safe
  · subst z; exact s5_485_safe
  · subst z; exact s5_405_safe
  · subst z; exact s5_424_safe
def s4_342 : State := ⟨[1,4,104,196], 100433627766186892227157431029340254302699436943383411622166, 0, 0, 1, 0⟩
theorem s4_342_edges : next config 4 s4_342 = [] := by decide
theorem s4_342_safe : Safe 9 4 s4_342 := by
  apply safe_succ 8 4 s4_342 [] (by decide) s4_342_edges
  simp
def s4_343 : State := ⟨[1,4,104,196], 106710729501573572985548702581812905303387798668939154751766, 0, 0, 1, 0⟩
theorem s4_343_edges : next config 4 s4_343 = [] := by decide
theorem s4_343_safe : Safe 9 4 s4_343 := by
  apply safe_succ 8 4 s4_343 [] (by decide) s4_343_edges
  simp
def s4_344 : State := ⟨[1,4,104,208], 411376139330301510561043381120255531963449332437156377911165206, 0, 0, 1, 0⟩
theorem s4_344_edges : next config 4 s4_344 = [s5_763, s5_666, s5_467, s5_425] := by decide
theorem s4_344_safe : Safe 9 4 s4_344 := by
  apply safe_succ 8 4 s4_344 [s5_763, s5_666, s5_467, s5_425] (by decide) s4_344_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_763_safe
  · subst z; exact s5_666_safe
  · subst z; exact s5_467_safe
  · subst z; exact s5_425_safe
def s4_345 : State := ⟨[1,4,104,208], 411382416432036897219506471711148116488329716519952480439697686, 0, 0, 1, 0⟩
theorem s4_345_edges : next config 4 s4_345 = [s5_764, s5_667, s5_468, s5_426] := by decide
theorem s4_345_safe : Safe 9 4 s4_345 := by
  apply safe_succ 8 4 s4_345 [s5_764, s5_667, s5_468, s5_426] (by decide) s4_345_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_764_safe
  · subst z; exact s5_667_safe
  · subst z; exact s5_468_safe
  · subst z; exact s5_426_safe
def s4_346 : State := ⟨[1,4,104,225], 53919893334301279589334030175060108468398742001655650290121324953878, 0, 0, 1, 0⟩
theorem s4_346_edges : next config 4 s4_346 = [s5_668] := by decide
theorem s4_346_safe : Safe 9 4 s4_346 := by
  apply safe_succ 8 4 s4_346 [s5_668] (by decide) s4_346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_668_safe
def s4_347 : State := ⟨[1,4,104,225], 80879840001451919384001045261399174408194009497269473556361398780182, 0, 0, 1, 0⟩
theorem s4_347_edges : next config 4 s4_347 = [s5_669] := by decide
theorem s4_347_safe : Safe 9 4 s4_347 := by
  apply safe_succ 8 4 s4_347 [s5_669] (by decide) s4_347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_669_safe
def s4_348 : State := ⟨[1,4,104,228], 431359146674410236714672241398098891036211902405710909529616623403286, 0, 0, 1, 0⟩
theorem s4_348_edges : next config 4 s4_348 = [s5_858] := by decide
theorem s4_348_safe : Safe 9 4 s4_348 := by
  apply safe_succ 8 4 s4_348 [s5_858] (by decide) s4_348_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_858_safe
def s4_349 : State := ⟨[1,4,104,228], 458319093341560876509339256479674003839114031412837488291811942269206, 0, 0, 1, 0⟩
theorem s4_349_edges : next config 4 s4_349 = [s5_859] := by decide
theorem s4_349_safe : Safe 9 4 s4_349 := by
  apply safe_succ 8 4 s4_349 [s5_859] (by decide) s4_349_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_859_safe
def s4_350 : State := ⟨[1,4,104,236], 110427941548649020598956093796438192039475761146371246632432346440204566, 0, 0, 1, 0⟩
theorem s4_350_edges : next config 4 s4_350 = [s5_860] := by decide
theorem s4_350_safe : Safe 9 4 s4_350 := by
  apply safe_succ 8 4 s4_350 [s5_860] (by decide) s4_350_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_860_safe
def s4_351 : State := ⟨[1,4,104,236], 117329687895439584386390849658709772974056135103126219193875962372620566, 0, 0, 1, 0⟩
theorem s4_351_edges : next config 4 s4_351 = [s5_861] := by decide
theorem s4_351_safe : Safe 9 4 s4_351 := by
  apply safe_succ 8 4 s4_351 [s5_861] (by decide) s4_351_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_861_safe
def s4_352 : State := ⟨[1,4,104,240], 1766847064778384329583297500765219601308401802593384324150367613366632726, 0, 0, 1, 0⟩
theorem s4_352_edges : next config 4 s4_352 = [s5_670] := by decide
theorem s4_352_safe : Safe 9 4 s4_352 := by
  apply safe_succ 8 4 s4_352 [s5_670] (by decide) s4_352_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_670_safe
def s4_353 : State := ⟨[1,4,104,240], 1766874024725051480223092167758005875740544816596271146450200355470901526, 0, 0, 1, 0⟩
theorem s4_353_edges : next config 4 s4_353 = [s5_671] := by decide
theorem s4_353_safe : Safe 9 4 s4_353 := by
  apply safe_succ 8 4 s4_353 [s5_671] (by decide) s4_353_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_671_safe
def s4_354 : State := ⟨[1,4,104,248], 452312848583266388373324160190209441137316795505876218645159948942984675606, 0, 0, 1, 0⟩
theorem s4_354_edges : next config 4 s4_354 = [] := by decide
theorem s4_354_safe : Safe 9 4 s4_354 := by
  apply safe_succ 8 4 s4_354 [] (by decide) s4_354_edges
  simp
def s4_355 : State := ⟨[1,4,104,248], 452319750329613178937111594946049417417570715991706853313442463105702494486, 0, 0, 1, 0⟩
theorem s4_355_edges : next config 4 s4_355 = [] := by decide
theorem s4_355_safe : Safe 9 4 s4_355 := by
  apply safe_succ 8 4 s4_355 [] (by decide) s4_355_edges
  simp
def s4_356 : State := ⟨[1,4,108,129], 1020847445643006815001232111070125031702, 0, 0, 1, 0⟩
theorem s4_356_edges : next config 4 s4_356 = [s5_862, s5_453, s5_455] := by decide
theorem s4_356_safe : Safe 9 4 s4_356 := by
  apply safe_succ 8 4 s4_356 [s5_862, s5_453, s5_455] (by decide) s4_356_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_862_safe
  · subst z; exact s5_453_safe
  · subst z; exact s5_455_safe
def s4_357 : State := ⟨[1,4,108,130], 1701412179484883741927981325933661454614, 0, 0, 1, 0⟩
theorem s4_357_edges : next config 4 s4_357 = [s5_1546, s5_863, s5_454, s5_457, s5_459] := by decide
theorem s4_357_safe : Safe 9 4 s4_357 := by
  apply safe_succ 8 4 s4_357 [s5_1546, s5_863, s5_454, s5_457, s5_459] (by decide) s4_357_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1546_safe
  · subst z; exact s5_863_safe
  · subst z; exact s5_454_safe
  · subst z; exact s5_457_safe
  · subst z; exact s5_459_safe
def s4_358 : State := ⟨[1,4,108,132], 5784800582536145303488476615114879992086, 0, 0, 1, 0⟩
theorem s4_358_edges : next config 4 s4_358 = [s5_865] := by decide
theorem s4_358_safe : Safe 9 4 s4_358 := by
  apply safe_succ 8 4 s4_358 [s5_865] (by decide) s4_358_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_865_safe
def s4_359 : State := ⟨[1,4,108,136], 87452568643561376534698382398739250741526, 0, 0, 1, 0⟩
theorem s4_359_edges : next config 4 s4_359 = [s5_866] := by decide
theorem s4_359_safe : Safe 9 4 s4_359 := by
  apply safe_succ 8 4 s4_359 [s5_866] (by decide) s4_359_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_866_safe
def s4_360 : State := ⟨[1,4,108,144], 22301085481242424271423792755544568094589206, 0, 0, 1, 0⟩
theorem s4_360_edges : next config 4 s4_360 = [s5_867, s5_456, s5_458, s5_461] := by decide
theorem s4_360_safe : Safe 9 4 s4_360 := by
  apply safe_succ 8 4 s4_360 [s5_867, s5_456, s5_458, s5_461] (by decide) s4_360_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_867_safe
  · subst z; exact s5_456_safe
  · subst z; exact s5_458_safe
  · subst z; exact s5_461_safe
def s4_361 : State := ⟨[1,4,108,160], 1461501637671185630004814720790765915862521151766, 0, 0, 1, 0⟩
theorem s4_361_edges : next config 4 s4_361 = [s5_868, s5_460, s5_462] := by decide
theorem s4_361_safe : Safe 9 4 s4_361 := by
  apply safe_succ 8 4 s4_361 [s5_868, s5_460, s5_462] (by decide) s4_361_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_868_safe
  · subst z; exact s5_460_safe
  · subst z; exact s5_462_safe
def s4_362 : State := ⟨[1,4,108,192], 6277101735386680764176072135008796304176838340670623121686, 0, 0, 1, 0⟩
theorem s4_362_edges : next config 4 s4_362 = [s5_1596, s5_869, s5_464, s5_466, s5_468] := by decide
theorem s4_362_safe : Safe 9 4 s4_362 := by
  apply safe_succ 8 4 s4_362 [s5_1596, s5_869, s5_464, s5_466, s5_468] (by decide) s4_362_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1596_safe
  · subst z; exact s5_869_safe
  · subst z; exact s5_464_safe
  · subst z; exact s5_466_safe
  · subst z; exact s5_468_safe
def s4_363 : State := ⟨[1,4,108,224], 26959946667150639794667015087359913385438274310615055377310198858006, 0, 0, 1, 0⟩
theorem s4_363_edges : next config 4 s4_363 = [s5_870] := by decide
theorem s4_363_safe : Safe 9 4 s4_363 := by
  apply safe_succ 8 4 s4_363 [s5_870] (by decide) s4_363_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_870_safe
def s4_364 : State := ⟨[1,4,108,232], 6901746346790563787434755862277365735162910102058461038058730812408086, 0, 0, 1, 0⟩
theorem s4_364_edges : next config 4 s4_364 = [s5_871] := by decide
theorem s4_364_safe : Safe 9 4 s4_364 := by
  apply safe_succ 8 4 s4_364 [s5_871] (by decide) s4_364_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_871_safe
def s4_365 : State := ⟨[1,4,108,236], 110427941548649020598956093796432747521929544684614259365496594169397526, 0, 0, 1, 0⟩
theorem s4_365_edges : next config 4 s4_365 = [s5_872] := by decide
theorem s4_365_safe : Safe 9 4 s4_365 := by
  apply safe_succ 8 4 s4_365 [s5_872] (by decide) s4_365_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_872_safe
def s4_366 : State := ⟨[1,4,112,128], 340287559297025160823714219599645970710, 2, 2, 0, 0⟩
theorem s4_366_edges : next config 4 s4_366 = [s5_1002, s5_469, s5_471, s5_480, s5_470, s5_472, s5_475, s5_477] := by decide
theorem s4_366_safe : Safe 9 4 s4_366 := by
  apply safe_succ 8 4 s4_366 [s5_1002, s5_469, s5_471, s5_480, s5_470, s5_472, s5_475, s5_477] (by decide) s4_366_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1002_safe
  · subst z; exact s5_469_safe
  · subst z; exact s5_471_safe
  · subst z; exact s5_480_safe
  · subst z; exact s5_470_safe
  · subst z; exact s5_472_safe
  · subst z; exact s5_475_safe
  · subst z; exact s5_477_safe
def s4_367 : State := ⟨[1,4,112,140], 1399581380338195986922220099979030531473686, 0, 0, 1, 0⟩
theorem s4_367_edges : next config 4 s4_367 = [] := by decide
theorem s4_367_safe : Safe 9 4 s4_367 := by
  apply safe_succ 8 4 s4_367 [] (by decide) s4_367_edges
  simp
def s4_368 : State := ⟨[1,4,112,140], 1481249148399221218153430005762654902223126, 0, 0, 1, 0⟩
theorem s4_368_edges : next config 4 s4_368 = [] := by decide
theorem s4_368_safe : Safe 9 4 s4_368 := by
  apply safe_succ 8 4 s4_368 [] (by decide) s4_368_edges
  simp
def s4_369 : State := ⟨[1,4,112,145], 44602511249354385185159187008731186194350358, 0, 0, 1, 0⟩
theorem s4_369_edges : next config 4 s4_369 = [s5_672] := by decide
theorem s4_369_safe : Safe 9 4 s4_369 := by
  apply safe_succ 8 4 s4_369 [s5_672] (by decide) s4_369_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_672_safe
def s4_370 : State := ⟨[1,4,112,145], 66902575883151166449767978532164684163907862, 0, 0, 1, 0⟩
theorem s4_370_edges : next config 4 s4_370 = [s5_673] := by decide
theorem s4_370_safe : Safe 9 4 s4_370 := by
  apply safe_succ 8 4 s4_370 [s5_673] (by decide) s4_370_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_673_safe
def s4_371 : State := ⟨[1,4,112,194], 25108406941546723057044574719811444679086634427182856864022, 0, 0, 1, 0⟩
theorem s4_371_edges : next config 4 s4_371 = [s5_674] := by decide
theorem s4_371_safe : Safe 9 4 s4_371 := by
  apply safe_succ 8 4 s4_371 [s5_674] (by decide) s4_371_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_674_safe
def s4_372 : State := ⟨[1,4,112,194], 31385508676933403819519234675335357241335491441919818531094, 0, 0, 1, 0⟩
theorem s4_372_edges : next config 4 s4_372 = [s5_675] := by decide
theorem s4_372_safe : Safe 9 4 s4_372 := by
  apply safe_succ 8 4 s4_372 [s5_675] (by decide) s4_372_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_675_safe
def s4_373 : State := ⟨[1,4,120,129], 1022176349120238072447409134974384800022, 0, 0, 1, 0⟩
theorem s4_373_edges : next config 4 s4_373 = [s5_482] := by decide
theorem s4_373_safe : Safe 9 4 s4_373 := by
  apply safe_succ 8 4 s4_373 [s5_482] (by decide) s4_373_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_482_safe
def s4_374 : State := ⟨[1,4,120,130], 1702741082962114999374158349837921222934, 0, 0, 1, 0⟩
theorem s4_374_edges : next config 4 s4_374 = [] := by decide
theorem s4_374_safe : Safe 9 4 s4_374 := by
  apply safe_succ 8 4 s4_374 [] (by decide) s4_374_edges
  simp
def s4_375 : State := ⟨[1,4,120,132], 5786129486013376560934653639019139760406, 0, 0, 1, 0⟩
theorem s4_375_edges : next config 4 s4_375 = [] := by decide
theorem s4_375_safe : Safe 9 4 s4_375 := by
  apply safe_succ 8 4 s4_375 [] (by decide) s4_375_edges
  simp
def s4_376 : State := ⟨[1,4,120,136], 87453897547038607792144559422643510509846, 0, 0, 1, 0⟩
theorem s4_376_edges : next config 4 s4_376 = [] := by decide
theorem s4_376_safe : Safe 9 4 s4_376 := by
  apply safe_succ 8 4 s4_376 [] (by decide) s4_376_edges
  simp
def s4_377 : State := ⟨[1,4,120,144], 22301086810145901502681238932568472354357526, 0, 0, 1, 0⟩
theorem s4_377_edges : next config 4 s4_377 = [s5_483] := by decide
theorem s4_377_safe : Safe 9 4 s4_377 := by
  apply safe_succ 8 4 s4_377 [s5_483] (by decide) s4_377_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_483_safe
def s4_378 : State := ⟨[1,4,120,160], 1461501637672514533482045978236942939766780920086, 0, 0, 1, 0⟩
theorem s4_378_edges : next config 4 s4_378 = [] := by decide
theorem s4_378_safe : Safe 9 4 s4_378 := by
  apply safe_succ 8 4 s4_378 [] (by decide) s4_378_edges
  simp
def s4_379 : State := ⟨[1,4,120,192], 6277101735386680764177401038486027561623015364574882890006, 0, 0, 1, 0⟩
theorem s4_379_edges : next config 4 s4_379 = [s5_485] := by decide
theorem s4_379_safe : Safe 9 4 s4_379 := by
  apply safe_succ 8 4 s4_379 [s5_485] (by decide) s4_379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_485_safe
def s4_380 : State := ⟨[1,4,120,224], 26959946667150639794667015087361242288915505568061232401214458626326, 0, 0, 1, 0⟩
theorem s4_380_edges : next config 4 s4_380 = [] := by decide
theorem s4_380_safe : Safe 9 4 s4_380 := by
  apply safe_succ 8 4 s4_380 [] (by decide) s4_380_edges
  simp
def s4_381 : State := ⟨[1,4,120,232], 6901746346790563787434755862277367064066387333315907215082635072176406, 0, 0, 1, 0⟩
theorem s4_381_edges : next config 4 s4_381 = [] := by decide
theorem s4_381_safe : Safe 9 4 s4_381 := by
  apply safe_succ 8 4 s4_381 [] (by decide) s4_381_edges
  simp
def s4_382 : State := ⟨[1,4,120,248], 452312848583266388373324160190187140393447492878519598799791107641759039766, 0, 0, 1, 0⟩
theorem s4_382_edges : next config 4 s4_382 = [] := by decide
theorem s4_382_safe : Safe 9 4 s4_382 := by
  apply safe_succ 8 4 s4_382 [] (by decide) s4_382_edges
  simp
def s4_383 : State := ⟨[1,4,162,194], 25108406947392729606368181200329325475124137975310257815830, 0, 0, 1, 0⟩
theorem s4_383_edges : next config 4 s4_383 = [s5_676] := by decide
theorem s4_383_safe : Safe 9 4 s4_383 := by
  apply safe_succ 8 4 s4_383 [s5_676] (by decide) s4_383_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_676_safe
def s4_384 : State := ⟨[1,4,162,194], 31385508682779410368842841155853238037372994990047219482902, 0, 0, 1, 0⟩
theorem s4_384_edges : next config 4 s4_384 = [s5_677] := by decide
theorem s4_384_safe : Safe 9 4 s4_384 := by
  apply safe_succ 8 4 s4_384 [s5_677] (by decide) s4_384_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_677_safe
def s4_385 : State := ⟨[1,4,193,129], 12554203470773361528692425947178148222613281455301378248982, 2, 2, 1, 0⟩
theorem s4_385_edges : next config 4 s4_385 = [s5_488] := by decide
theorem s4_385_safe : Safe 9 4 s4_385 := by
  apply safe_succ 8 4 s4_385 [s5_488] (by decide) s4_385_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_488_safe
def s4_386 : State := ⟨[1,4,194,96], 25108406947392729606368181200329325475124137975310257815830, 0, 0, 1, 0⟩
theorem s4_386_edges : next config 4 s4_386 = [s5_678, s5_489] := by decide
theorem s4_386_safe : Safe 9 4 s4_386 := by
  apply safe_succ 8 4 s4_386 [s5_678, s5_489] (by decide) s4_386_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_678_safe
  · subst z; exact s5_489_safe
def s4_387 : State := ⟨[1,4,194,130], 25108406941546723057044569527435357981744741559092983697686, 2, 2, 1, 0⟩
theorem s4_387_edges : next config 4 s4_387 = [s5_496, s5_490, s5_491] := by decide
theorem s4_387_safe : Safe 9 4 s4_387 := by
  apply safe_succ 8 4 s4_387 [s5_496, s5_490, s5_491] (by decide) s4_387_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_496_safe
  · subst z; exact s5_490_safe
  · subst z; exact s5_491_safe
def s4_388 : State := ⟨[1,4,194,162], 25108406947392729606368181200329325475124137975310257815830, 0, 0, 1, 0⟩
theorem s4_388_edges : next config 4 s4_388 = [s5_679] := by decide
theorem s4_388_safe : Safe 9 4 s4_388 := by
  apply safe_succ 8 4 s4_388 [s5_679] (by decide) s4_388_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_679_safe
def s4_389 : State := ⟨[1,4,194,162], 25108406948854231242337954650849256453986922565239117512982, 0, 0, 1, 0⟩
theorem s4_389_edges : next config 4 s4_389 = [s5_680] := by decide
theorem s4_389_safe : Safe 9 4 s4_389 := by
  apply safe_succ 8 4 s4_389 [s5_680] (by decide) s4_389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_680_safe
def s4_390 : State := ⟨[1,4,208,144], 411376139330301510561043381120235170325683166502394837115932950, 2, 2, 1, 0⟩
theorem s4_390_edges : next config 4 s4_390 = [s5_500, s5_492] := by decide
theorem s4_390_safe : Safe 9 4 s4_390 := by
  apply safe_succ 8 4 s4_390 [s5_500, s5_492] (by decide) s4_390_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_500_safe
  · subst z; exact s5_492_safe
def s4_391 : State := ⟨[1,4,209,145], 822752278660603021122086421958103419712902851183438164459192598, 1, 1, 1, 0⟩
theorem s4_391_edges : next config 4 s4_391 = [s5_681] := by decide
theorem s4_391_safe : Safe 9 4 s4_391 := by
  apply safe_succ 8 4 s4_391 [s5_681] (by decide) s4_391_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_681_safe
def s4_392 : State := ⟨[1,4,210,145], 1645504557321206042221871758435309295345806576059852752477552918, 0, 0, 1, 0⟩
theorem s4_392_edges : next config 4 s4_392 = [s5_784, s5_682, s5_507, s5_107] := by decide
theorem s4_392_safe : Safe 9 4 s4_392 := by
  apply safe_succ 8 4 s4_392 [s5_784, s5_682, s5_507, s5_107] (by decide) s4_392_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_784_safe
  · subst z; exact s5_682_safe
  · subst z; exact s5_507_safe
  · subst z; exact s5_107_safe
def s4_393 : State := ⟨[1,4,210,145], 2056880696651507552760614054074646921591490468681271423476498710, 0, 0, 1, 0⟩
theorem s4_393_edges : next config 4 s4_393 = [s5_785, s5_683, s5_508, s5_109] := by decide
theorem s4_393_safe : Safe 9 4 s4_393 := by
  apply safe_succ 8 4 s4_393 [s5_785, s5_683, s5_508, s5_109] (by decide) s4_393_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_785_safe
  · subst z; exact s5_683_safe
  · subst z; exact s5_508_safe
  · subst z; exact s5_109_safe
def s4_394 : State := ⟨[1,4,214,130], 27973577474460502716634477804886793189400035976910253542946701590, 0, 0, 1, 0⟩
theorem s4_394_edges : next config 4 s4_394 = [] := by decide
theorem s4_394_safe : Safe 9 4 s4_394 := by
  apply safe_succ 8 4 s4_394 [] (by decide) s4_394_edges
  simp
def s4_395 : State := ⟨[1,4,214,130], 27973602582867444263357533148044486020064491460512416769910046998, 0, 0, 1, 0⟩
theorem s4_395_edges : next config 4 s4_395 = [] := by decide
theorem s4_395_safe : Safe 9 4 s4_395 := by
  apply safe_succ 8 4 s4_395 [] (by decide) s4_395_edges
  simp
def s4_396 : State := ⟨[1,4,214,132], 26328072917139296674479512705717845735682488523017783043178955030, 0, 0, 1, 0⟩
theorem s4_396_edges : next config 4 s4_396 = [] := by decide
theorem s4_396_safe : Safe 9 4 s4_396 := by
  apply safe_succ 8 4 s4_396 [] (by decide) s4_396_edges
  simp
def s4_397 : State := ⟨[1,4,214,132], 26328072917139296674479512705717845735683697375050421377515454742, 0, 0, 1, 0⟩
theorem s4_397_edges : next config 4 s4_397 = [] := by decide
theorem s4_397_safe : Safe 9 4 s4_397 := by
  apply safe_succ 8 4 s4_397 [] (by decide) s4_397_edges
  simp
def s4_398 : State := ⟨[1,4,214,144], 27973577474460502716656777188955856128786508989651833843043336470, 0, 0, 1, 0⟩
theorem s4_398_edges : next config 4 s4_398 = [s5_507] := by decide
theorem s4_398_safe : Safe 9 4 s4_398 := by
  apply safe_succ 8 4 s4_398 [s5_507] (by decide) s4_398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_507_safe
def s4_399 : State := ⟨[1,4,214,144], 28384953613790804227195519484595193755032192882273252514042282262, 0, 0, 1, 0⟩
theorem s4_399_edges : next config 4 s4_399 = [s5_508] := by decide
theorem s4_399_safe : Safe 9 4 s4_399 := by
  apply safe_succ 8 4 s4_399 [s5_508] (by decide) s4_399_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_508_safe
def s4_400 : State := ⟨[1,4,214,146], 26328072917139296674568711603123565176982234353695557675800133910, 0, 0, 1, 0⟩
theorem s4_400_edges : next config 4 s4_400 = [] := by decide
theorem s4_400_safe : Safe 9 4 s4_400 := by
  apply safe_succ 8 4 s4_400 [] (by decide) s4_400_edges
  simp
def s4_401 : State := ⟨[1,4,214,146], 26328072917139296674591010987192628116369916218469776310233268502, 0, 0, 1, 0⟩
theorem s4_401_edges : next config 4 s4_401 = [] := by decide
theorem s4_401_safe : Safe 9 4 s4_401 := by
  apply safe_succ 8 4 s4_401 [] (by decide) s4_401_edges
  simp
def s4_402 : State := ⟨[1,4,214,146], 27973577474460502716723680785680915681964969924181232359795917078, 0, 0, 1, 0⟩
theorem s4_402_edges : next config 4 s4_402 = [] := by decide
theorem s4_402_safe : Safe 9 4 s4_402 := by
  apply safe_succ 8 4 s4_402 [] (by decide) s4_402_edges
  simp
def s4_403 : State := ⟨[1,4,214,146], 27973577474460502716745980169749978621352651788955450994229051670, 0, 0, 1, 0⟩
theorem s4_403_edges : next config 4 s4_403 = [] := by decide
theorem s4_403_safe : Safe 9 4 s4_403 := by
  apply safe_succ 8 4 s4_403 [] (by decide) s4_403_edges
  simp
def s4_404 : State := ⟨[1,4,214,150], 26328072917139296675995959295829525058040520027997147632830054678, 0, 0, 1, 0⟩
theorem s4_404_edges : next config 4 s4_404 = [] := by decide
theorem s4_404_safe : Safe 9 4 s4_404 := by
  apply safe_succ 8 4 s4_404 [] (by decide) s4_404_edges
  simp
def s4_405 : State := ⟨[1,4,214,150], 26328072917139296676018258679898587997428201892771366267263189270, 0, 0, 1, 0⟩
theorem s4_405_edges : next config 4 s4_405 = [] := by decide
theorem s4_405_safe : Safe 9 4 s4_405 := by
  apply safe_succ 8 4 s4_405 [] (by decide) s4_405_edges
  simp
def s4_406 : State := ⟨[1,4,225,145], 53919893334301279589334074776550505509362615469440525162897085628694, 0, 0, 1, 0⟩
theorem s4_406_edges : next config 4 s4_406 = [s5_684] := by decide
theorem s4_406_safe : Safe 9 4 s4_406 := by
  apply safe_succ 8 4 s4_406 [s5_684] (by decide) s4_406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_684_safe
def s4_407 : State := ⟨[1,4,236,132], 110427941548649020598956093796438192039475761146371246632432346440204566, 0, 0, 1, 0⟩
theorem s4_407_edges : next config 4 s4_407 = [s5_873] := by decide
theorem s4_407_safe : Safe 9 4 s4_407 := by
  apply safe_succ 8 4 s4_407 [s5_873] (by decide) s4_407_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_873_safe
def s4_408 : State := ⟨[1,4,240,145], 1766847064778384329583297500809821091705442766466852109025240389127307542, 0, 0, 1, 0⟩
theorem s4_408_edges : next config 4 s4_408 = [s5_685] := by decide
theorem s4_408_safe : Safe 9 4 s4_408 := by
  apply safe_succ 8 4 s4_408 [s5_685] (by decide) s4_408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_685_safe
def s4_409 : State := ⟨[1,4,241,145], 3533694129556768659166595001530439542899129882077862275623413092450369814, 0, 0, 1, 0⟩
theorem s4_409_edges : next config 4 s4_409 = [s5_874, s5_686] := by decide
theorem s4_409_safe : Safe 9 4 s4_409 := by
  apply safe_succ 8 4 s4_409 [s5_874, s5_686] (by decide) s4_409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_874_safe
  · subst z; exact s5_686_safe
def s4_410 : State := ⟨[1,4,241,145], 3533694129556768659166595001552739607532926663342471067146846590419927318, 0, 0, 1, 0⟩
theorem s4_410_edges : next config 4 s4_410 = [s5_875, s5_687] := by decide
theorem s4_410_safe : Safe 9 4 s4_410 := by
  apply safe_succ 8 4 s4_410 [s5_875, s5_687] (by decide) s4_410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_875_safe
  · subst z; exact s5_687_safe
def s4_411 : State := ⟨[1,4,248,144], 452312848583266388373324160190209441137316795505876218645159948942984675606, 0, 0, 1, 0⟩
theorem s4_411_edges : next config 4 s4_411 = [s5_516] := by decide
theorem s4_411_safe : Safe 9 4 s4_411 := by
  apply safe_succ 8 4 s4_411 [s5_516] (by decide) s4_411_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_516_safe
def s4_412 : State := ⟨[1,12,64,129], 1020847100762815390408570566373309223198, 3, 1, 1, 0⟩
theorem s4_412_edges : next config 4 s4_412 = [s5_0, s5_581, s5_519] := by decide
theorem s4_412_safe : Safe 9 4 s4_412 := by
  apply safe_succ 8 4 s4_412 [s5_0, s5_581, s5_519] (by decide) s4_412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_0_safe
  · subst z; exact s5_581_safe
  · subst z; exact s5_519_safe
def s4_413 : State := ⟨[1,12,64,129], 1020847100762815390408570566381899157782, 3, 1, 1, 0⟩
theorem s4_413_edges : next config 4 s4_413 = [s5_1, s5_582, s5_520] := by decide
theorem s4_413_safe : Safe 9 4 s4_413 := by
  apply safe_succ 8 4 s4_413 [s5_1, s5_582, s5_520] (by decide) s4_413_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1_safe
  · subst z; exact s5_582_safe
  · subst z; exact s5_520_safe
def s4_414 : State := ⟨[1,12,64,129], 1020847100762815390445464054520728326422, 3, 1, 1, 0⟩
theorem s4_414_edges : next config 4 s4_414 = [s5_2, s5_583, s5_521] := by decide
theorem s4_414_safe : Safe 9 4 s4_414 := by
  apply safe_succ 8 4 s4_414 [s5_2, s5_583, s5_521] (by decide) s4_414_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_2_safe
  · subst z; exact s5_583_safe
  · subst z; exact s5_521_safe
def s4_415 : State := ⟨[1,12,64,130], 1701411834604692317335319781236845646110, 3, 1, 1, 0⟩
theorem s4_415_edges : next config 4 s4_415 = [s5_3, s5_585, s5_525, s5_530] := by decide
theorem s4_415_safe : Safe 9 4 s4_415 := by
  apply safe_succ 8 4 s4_415 [s5_3, s5_585, s5_525, s5_530] (by decide) s4_415_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_3_safe
  · subst z; exact s5_585_safe
  · subst z; exact s5_525_safe
  · subst z; exact s5_530_safe
def s4_416 : State := ⟨[1,12,64,130], 1701411834604692317335319781245435580694, 3, 1, 1, 0⟩
theorem s4_416_edges : next config 4 s4_416 = [s5_4, s5_586] := by decide
theorem s4_416_safe : Safe 9 4 s4_416 := by
  apply safe_succ 8 4 s4_416 [s5_4, s5_586] (by decide) s4_416_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_4_safe
  · subst z; exact s5_586_safe
def s4_417 : State := ⟨[1,12,64,130], 1701411834604692317372213269384264749334, 3, 1, 1, 0⟩
theorem s4_417_edges : next config 4 s4_417 = [s5_5, s5_587, s5_526, s5_531] := by decide
theorem s4_417_safe : Safe 9 4 s4_417 := by
  apply safe_succ 8 4 s4_417 [s5_5, s5_587, s5_526, s5_531] (by decide) s4_417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_5_safe
  · subst z; exact s5_587_safe
  · subst z; exact s5_526_safe
  · subst z; exact s5_531_safe
def s4_418 : State := ⟨[1,12,64,130], 4423670769972200025042316640690991337750, 3, 1, 1, 0⟩
theorem s4_418_edges : next config 4 s4_418 = [s5_6, s5_589, s5_527, s5_532] := by decide
theorem s4_418_safe : Safe 9 4 s4_418 := by
  apply safe_succ 8 4 s4_418 [s5_6, s5_589, s5_527, s5_532] (by decide) s4_418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_6_safe
  · subst z; exact s5_589_safe
  · subst z; exact s5_527_safe
  · subst z; exact s5_532_safe
def s4_419 : State := ⟨[1,12,64,131], 3062541302288446171188818210963918491934, 3, 1, 1, 0⟩
theorem s4_419_edges : next config 4 s4_419 = [s5_7, s5_590, s5_538] := by decide
theorem s4_419_safe : Safe 9 4 s4_419 := by
  apply safe_succ 8 4 s4_419 [s5_7, s5_590, s5_538] (by decide) s4_419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_7_safe
  · subst z; exact s5_590_safe
  · subst z; exact s5_538_safe
def s4_420 : State := ⟨[1,12,64,132], 5784800237655953878895815070418064183582, 3, 1, 1, 0⟩
theorem s4_420_edges : next config 4 s4_420 = [s5_8, s5_591] := by decide
theorem s4_420_safe : Safe 9 4 s4_420 := by
  apply safe_succ 8 4 s4_420 [s5_8, s5_591] (by decide) s4_420_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_8_safe
  · subst z; exact s5_591_safe
def s4_421 : State := ⟨[1,12,64,132], 5784800237655953878895815070426654118166, 3, 1, 1, 0⟩
theorem s4_421_edges : next config 4 s4_421 = [s5_9, s5_592] := by decide
theorem s4_421_safe : Safe 9 4 s4_421 := by
  apply safe_succ 8 4 s4_421 [s5_9, s5_592] (by decide) s4_421_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_9_safe
  · subst z; exact s5_592_safe
def s4_422 : State := ⟨[1,12,64,132], 5784800237655953878932708558565483286806, 3, 1, 1, 0⟩
theorem s4_422_edges : next config 4 s4_422 = [s5_10, s5_593] := by decide
theorem s4_422_safe : Safe 9 4 s4_422 := by
  apply safe_succ 8 4 s4_422 [s5_10, s5_593] (by decide) s4_422_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_10_safe
  · subst z; exact s5_593_safe
def s4_423 : State := ⟨[1,12,64,136], 87452568298681185110105720854042434933022, 3, 1, 1, 0⟩
theorem s4_423_edges : next config 4 s4_423 = [s5_11, s5_595] := by decide
theorem s4_423_safe : Safe 9 4 s4_423 := by
  apply safe_succ 8 4 s4_423 [s5_11, s5_595] (by decide) s4_423_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_11_safe
  · subst z; exact s5_595_safe
def s4_424 : State := ⟨[1,12,64,136], 87452568298681185110105720854051024867606, 3, 1, 1, 0⟩
theorem s4_424_edges : next config 4 s4_424 = [s5_12, s5_596] := by decide
theorem s4_424_safe : Safe 9 4 s4_424 := by
  apply safe_succ 8 4 s4_424 [s5_12, s5_596] (by decide) s4_424_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_12_safe
  · subst z; exact s5_596_safe
def s4_425 : State := ⟨[1,12,64,136], 87452568298681185110142614342189854036246, 3, 1, 1, 0⟩
theorem s4_425_edges : next config 4 s4_425 = [s5_13, s5_597] := by decide
theorem s4_425_safe : Safe 9 4 s4_425 := by
  apply safe_succ 8 4 s4_425 [s5_13, s5_597] (by decide) s4_425_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_13_safe
  · subst z; exact s5_597_safe
def s4_426 : State := ⟨[1,12,64,140], 1394136857275084884809464213392032366924062, 3, 1, 1, 0⟩
theorem s4_426_edges : next config 4 s4_426 = [s5_17, s5_599] := by decide
theorem s4_426_safe : Safe 9 4 s4_426 := by
  apply safe_succ 8 4 s4_426 [s5_17, s5_599] (by decide) s4_426_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_17_safe
  · subst z; exact s5_599_safe
def s4_427 : State := ⟨[1,12,64,140], 1394136857275084884809464213392040956858646, 3, 1, 1, 0⟩
theorem s4_427_edges : next config 4 s4_427 = [s5_18, s5_600] := by decide
theorem s4_427_safe : Safe 9 4 s4_427 := by
  apply safe_succ 8 4 s4_427 [s5_18, s5_600] (by decide) s4_427_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_18_safe
  · subst z; exact s5_600_safe
def s4_428 : State := ⟨[1,12,64,140], 1394136857275084884809501106880179786027286, 3, 1, 1, 0⟩
theorem s4_428_edges : next config 4 s4_428 = [s5_19, s5_601] := by decide
theorem s4_428_safe : Safe 9 4 s4_428 := by
  apply safe_succ 8 4 s4_428 [s5_19, s5_601] (by decide) s4_428_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_19_safe
  · subst z; exact s5_601_safe
def s4_429 : State := ⟨[1,12,64,144], 22301085480897544079999200093999871278780702, 3, 1, 1, 0⟩
theorem s4_429_edges : next config 4 s4_429 = [s5_20, s5_603, s5_522, s5_528, s5_541] := by decide
theorem s4_429_safe : Safe 9 4 s4_429 := by
  apply safe_succ 8 4 s4_429 [s5_20, s5_603, s5_522, s5_528, s5_541] (by decide) s4_429_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_20_safe
  · subst z; exact s5_603_safe
  · subst z; exact s5_522_safe
  · subst z; exact s5_528_safe
  · subst z; exact s5_541_safe
def s4_430 : State := ⟨[1,12,64,144], 22301085480897544079999200093999879868715286, 3, 1, 1, 0⟩
theorem s4_430_edges : next config 4 s4_430 = [s5_21, s5_604, s5_523] := by decide
theorem s4_430_safe : Safe 9 4 s4_430 := by
  apply safe_succ 8 4 s4_430 [s5_21, s5_604, s5_523] (by decide) s4_430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_21_safe
  · subst z; exact s5_604_safe
  · subst z; exact s5_523_safe
def s4_431 : State := ⟨[1,12,64,144], 22301085480897544079999236987488018697883926, 3, 1, 1, 0⟩
theorem s4_431_edges : next config 4 s4_431 = [s5_22, s5_605, s5_524, s5_529, s5_542] := by decide
theorem s4_431_safe : Safe 9 4 s4_431 := by
  apply safe_succ 8 4 s4_431 [s5_22, s5_605, s5_524, s5_529, s5_542] (by decide) s4_431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_22_safe
  · subst z; exact s5_605_safe
  · subst z; exact s5_524_safe
  · subst z; exact s5_529_safe
  · subst z; exact s5_542_safe
def s4_432 : State := ⟨[1,12,64,145], 44601830679428167221534918366648232784892182, 3, 1, 1, 0⟩
theorem s4_432_edges : next config 4 s4_432 = [s5_1431, s5_876, s5_1168, s5_23, s5_545, s5_681, s5_546, s5_575, s5_607] := by decide
theorem s4_432_safe : Safe 9 4 s4_432 := by
  apply safe_succ 8 4 s4_432 [s5_1431, s5_876, s5_1168, s5_23, s5_545, s5_681, s5_546, s5_575, s5_607] (by decide) s4_432_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1431_safe
  · subst z; exact s5_876_safe
  · subst z; exact s5_1168_safe
  · subst z; exact s5_23_safe
  · subst z; exact s5_545_safe
  · subst z; exact s5_681_safe
  · subst z; exact s5_546_safe
  · subst z; exact s5_575_safe
  · subst z; exact s5_607_safe
def s4_433 : State := ⟨[1,12,64,160], 1461501637671185285124623296198104371165705343262, 3, 1, 1, 0⟩
theorem s4_433_edges : next config 4 s4_433 = [s5_28, s5_608, s5_533, s5_543] := by decide
theorem s4_433_safe : Safe 9 4 s4_433 := by
  apply safe_succ 8 4 s4_433 [s5_28, s5_608, s5_533, s5_543] (by decide) s4_433_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_28_safe
  · subst z; exact s5_608_safe
  · subst z; exact s5_533_safe
  · subst z; exact s5_543_safe
def s4_434 : State := ⟨[1,12,64,160], 1461501637671185285124623296198104371174295277846, 3, 1, 1, 0⟩
theorem s4_434_edges : next config 4 s4_434 = [s5_29, s5_609] := by decide
theorem s4_434_safe : Safe 9 4 s4_434 := by
  apply safe_succ 8 4 s4_434 [s5_29, s5_609] (by decide) s4_434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_29_safe
  · subst z; exact s5_609_safe
def s4_435 : State := ⟨[1,12,64,160], 1461501637671185285124623296234997859313124446486, 3, 1, 1, 0⟩
theorem s4_435_edges : next config 4 s4_435 = [s5_30, s5_610, s5_534, s5_544] := by decide
theorem s4_435_safe : Safe 9 4 s4_435 := by
  apply safe_succ 8 4 s4_435 [s5_30, s5_610, s5_534, s5_544] (by decide) s4_435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_30_safe
  · subst z; exact s5_610_safe
  · subst z; exact s5_534_safe
  · subst z; exact s5_544_safe
def s4_436 : State := ⟨[1,12,64,160], 4384504912332991121531992961630670410477570429206, 3, 1, 1, 0⟩
theorem s4_436_edges : next config 4 s4_436 = [s5_31, s5_612] := by decide
theorem s4_436_safe : Safe 9 4 s4_436 := by
  apply safe_succ 8 4 s4_436 [s5_31, s5_612] (by decide) s4_436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_31_safe
  · subst z; exact s5_612_safe
def s4_437 : State := ⟨[1,12,64,161], 2923003275002088203328308128914387390830227820822, 3, 1, 1, 0⟩
theorem s4_437_edges : next config 4 s4_437 = [s5_32, s5_613, s5_540] := by decide
theorem s4_437_safe : Safe 9 4 s4_437 := by
  apply safe_succ 8 4 s4_437 [s5_32, s5_613, s5_540] (by decide) s4_437_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_32_safe
  · subst z; exact s5_613_safe
  · subst z; exact s5_540_safe
def s4_438 : State := ⟨[1,12,64,163], 11692013102390329381759801759845831583074915258646, 2, 0, 1, 0⟩
theorem s4_438_edges : next config 4 s4_438 = [s5_33, s5_616] := by decide
theorem s4_438_safe : Safe 9 4 s4_438 := by
  apply safe_succ 8 4 s4_438 [s5_33, s5_616] (by decide) s4_438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_33_safe
  · subst z; exact s5_616_safe
def s4_439 : State := ⟨[1,12,64,163], 11692013103070894115601678686772580797938451681558, 2, 0, 1, 0⟩
theorem s4_439_edges : next config 4 s4_439 = [s5_34, s5_617] := by decide
theorem s4_439_safe : Safe 9 4 s4_439 := by
  apply safe_succ 8 4 s4_439 [s5_34, s5_617] (by decide) s4_439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_34_safe
  · subst z; exact s5_617_safe
def s4_440 : State := ⟨[1,12,64,163], 14615016374329876282799663717571400762932634652950, 2, 0, 1, 0⟩
theorem s4_440_edges : next config 4 s4_440 = [s5_35, s5_618] := by decide
theorem s4_440_safe : Safe 9 4 s4_440 := by
  apply safe_succ 8 4 s4_440 [s5_35, s5_618] (by decide) s4_440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_35_safe
  · subst z; exact s5_618_safe
def s4_441 : State := ⟨[1,12,64,163], 16076518010980214467161471623360934567725030773014, 2, 0, 1, 0⟩
theorem s4_441_edges : next config 4 s4_441 = [s5_36, s5_619] := by decide
theorem s4_441_safe : Safe 9 4 s4_441 := by
  apply safe_succ 8 4 s4_441 [s5_36, s5_619] (by decide) s4_441_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_36_safe
  · subst z; exact s5_619_safe
def s4_442 : State := ⟨[1,12,64,163], 17538019649672246853048910309930716017108036161814, 2, 0, 1, 0⟩
theorem s4_442_edges : next config 4 s4_442 = [s5_37, s5_620] := by decide
theorem s4_442_safe : Safe 9 4 s4_442 := by
  apply safe_succ 8 4 s4_442 [s5_37, s5_620] (by decide) s4_442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_37_safe
  · subst z; exact s5_620_safe
def s4_443 : State := ⟨[1,12,64,163], 18999521285642020303568841288793500607036895858966, 2, 0, 1, 0⟩
theorem s4_443_edges : next config 4 s4_443 = [s5_38, s5_621] := by decide
theorem s4_443_safe : Safe 9 4 s4_443 := by
  apply safe_succ 8 4 s4_443 [s5_38, s5_621] (by decide) s4_443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_38_safe
  · subst z; exact s5_621_safe
def s4_444 : State := ⟨[1,12,64,192], 6277101735386680764176071790128604879584176795973807313182, 3, 1, 1, 0⟩
theorem s4_444_edges : next config 4 s4_444 = [s5_47, s5_622] := by decide
theorem s4_444_safe : Safe 9 4 s4_444 := by
  apply safe_succ 8 4 s4_444 [s5_47, s5_622] (by decide) s4_444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_47_safe
  · subst z; exact s5_622_safe
def s4_445 : State := ⟨[1,12,64,192], 6277101735386680764176071790128604879584176795982397247766, 3, 1, 1, 0⟩
theorem s4_445_edges : next config 4 s4_445 = [s5_48, s5_623] := by decide
theorem s4_445_safe : Safe 9 4 s4_445 := by
  apply safe_succ 8 4 s4_445 [s5_48, s5_623] (by decide) s4_445_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_48_safe
  · subst z; exact s5_623_safe
def s4_446 : State := ⟨[1,12,64,192], 6277101735386680764176071790128604879621070284121226416406, 3, 1, 1, 0⟩
theorem s4_446_edges : next config 4 s4_446 = [s5_49, s5_624] := by decide
theorem s4_446_safe : Safe 9 4 s4_446 := by
  apply safe_succ 8 4 s4_446 [s5_49, s5_624] (by decide) s4_446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_49_safe
  · subst z; exact s5_624_safe
def s4_447 : State := ⟨[1,12,64,192], 18831305206160042291847650636543937711788887684901876338966, 3, 1, 1, 0⟩
theorem s4_447_edges : next config 4 s4_447 = [s5_50, s5_626] := by decide
theorem s4_447_safe : Safe 9 4 s4_447 := by
  apply safe_succ 8 4 s4_447 [s5_50, s5_626] (by decide) s4_447_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_50_safe
  · subst z; exact s5_626_safe
def s4_448 : State := ⟨[1,12,64,193], 12554203470773361528011861213336271295723425728585260929302, 3, 1, 1, 0⟩
theorem s4_448_edges : next config 4 s4_448 = [s5_51, s5_627] := by decide
theorem s4_448_safe : Safe 9 4 s4_448 := by
  apply safe_succ 8 4 s4_448 [s5_51, s5_627] (by decide) s4_448_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_51_safe
  · subst z; exact s5_627_safe
def s4_449 : State := ⟨[1,12,64,210], 1645504557321206042244173864763307602241196074043954546218176790, 2, 0, 1, 0⟩
theorem s4_449_edges : next config 4 s4_449 = [s5_52, s5_630] := by decide
theorem s4_449_safe : Safe 9 4 s4_449 := by
  apply safe_succ 8 4 s4_449 [s5_52, s5_630] (by decide) s4_449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_52_safe
  · subst z; exact s5_630_safe
def s4_450 : State := ⟨[1,12,64,210], 1645504557321206042266473248832370541628877938818173180651311382, 2, 0, 1, 0⟩
theorem s4_450_edges : next config 4 s4_450 = [s5_53, s5_631] := by decide
theorem s4_450_safe : Safe 9 4 s4_450 := by
  apply safe_succ 8 4 s4_450 [s5_53, s5_631] (by decide) s4_450_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_53_safe
  · subst z; exact s5_631_safe
def s4_451 : State := ⟨[1,12,64,210], 1645529665728147588878026227126877940340717610375138956332306710, 2, 0, 1, 0⟩
theorem s4_451_edges : next config 4 s4_451 = [s5_54, s5_632] := by decide
theorem s4_451_safe : Safe 9 4 s4_451 := by
  apply safe_succ 8 4 s4_451 [s5_54, s5_632] (by decide) s4_451_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_54_safe
  · subst z; exact s5_632_safe
def s4_452 : State := ⟨[1,12,64,210], 1645535942829882975558788701786833464253279859232153693293973782, 2, 0, 1, 0⟩
theorem s4_452_edges : next config 4 s4_452 = [s5_55, s5_633] := by decide
theorem s4_452_safe : Safe 9 4 s4_452 := by
  apply safe_succ 8 4 s4_452 [s5_55, s5_633] (by decide) s4_452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_55_safe
  · subst z; exact s5_633_safe
def s4_453 : State := ⟨[1,12,64,210], 2056880696651507552716012563677585675308419032135974700464541974, 2, 0, 1, 0⟩
theorem s4_453_edges : next config 4 s4_453 = [s5_56, s5_634] := by decide
theorem s4_453_safe : Safe 9 4 s4_453 := by
  apply safe_succ 8 4 s4_453 [s5_56, s5_634] (by decide) s4_453_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_56_safe
  · subst z; exact s5_634_safe
def s4_454 : State := ⟨[1,12,64,210], 2056886973753242939374475654268478259833299416218770802993074454, 2, 0, 1, 0⟩
theorem s4_454_edges : next config 4 s4_454 = [s5_57, s5_635] := by decide
theorem s4_454_safe : Safe 9 4 s4_454 := by
  apply safe_succ 8 4 s4_454 [s5_57, s5_635] (by decide) s4_454_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_57_safe
  · subst z; exact s5_635_safe
def s4_455 : State := ⟨[1,12,65,145], 44602511244162009098461882009351243740287254, 2, 0, 1, 0⟩
theorem s4_455_edges : next config 4 s4_455 = [s5_66, s5_554] := by decide
theorem s4_455_safe : Safe 9 4 s4_455 := by
  apply safe_succ 8 4 s4_455 [s5_66, s5_554] (by decide) s4_455_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_66_safe
  · subst z; exact s5_554_safe
def s4_456 : State := ⟨[1,12,65,145], 66902575877958790363070673532784741709844758, 2, 0, 1, 0⟩
theorem s4_456_edges : next config 4 s4_456 = [s5_67, s5_556] := by decide
theorem s4_456_safe : Safe 9 4 s4_456 := by
  apply safe_succ 8 4 s4_456 [s5_67, s5_556] (by decide) s4_456_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_67_safe
  · subst z; exact s5_556_safe
def s4_457 : State := ⟨[1,12,65,146], 89204682205957097258460245303862830288670998, 2, 0, 1, 0⟩
theorem s4_457_edges : next config 4 s4_457 = [s5_68, s5_558] := by decide
theorem s4_457_safe : Safe 9 4 s4_457 := by
  apply safe_succ 8 4 s4_457 [s5_68, s5_558] (by decide) s4_457_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_68_safe
  · subst z; exact s5_558_safe
def s4_458 : State := ⟨[1,12,65,146], 111504066275020036646142110078081464721805590, 2, 0, 1, 0⟩
theorem s4_458_edges : next config 4 s4_458 = [s5_69, s5_560] := by decide
theorem s4_458_safe : Safe 9 4 s4_458 := by
  apply safe_succ 8 4 s4_458 [s5_69, s5_560] (by decide) s4_458_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_69_safe
  · subst z; exact s5_560_safe
def s4_459 : State := ⟨[1,12,65,162], 5846006551025023507419431648237345348007994921238, 2, 0, 1, 0⟩
theorem s4_459_edges : next config 4 s4_459 = [s5_70, s5_563] := by decide
theorem s4_459_safe : Safe 9 4 s4_459 := by
  apply safe_succ 8 4 s4_459 [s5_70, s5_563] (by decide) s4_459_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_70_safe
  · subst z; exact s5_563_safe
def s4_460 : State := ⟨[1,12,65,162], 7307508186994796957939362627100129937936854618390, 2, 0, 1, 0⟩
theorem s4_460_edges : next config 4 s4_460 = [s5_71, s5_565] := by decide
theorem s4_460_safe : Safe 9 4 s4_460 := by
  apply safe_succ 8 4 s4_460 [s5_71, s5_565] (by decide) s4_460_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_71_safe
  · subst z; exact s5_565_safe
def s4_461 : State := ⟨[1,12,65,176], 95780971326419139128294233276893560963659213834359062, 2, 0, 1, 0⟩
theorem s4_461_edges : next config 4 s4_461 = [s5_72, s5_567] := by decide
theorem s4_461_safe : Safe 9 4 s4_461 := by
  apply safe_succ 8 4 s4_461 [s5_72, s5_567] (by decide) s4_461_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_72_safe
  · subst z; exact s5_567_safe
def s4_462 : State := ⟨[1,12,65,176], 95782432805755724832681813820190558974030508260921622, 2, 0, 1, 0⟩
theorem s4_462_edges : next config 4 s4_462 = [s5_73, s5_569] := by decide
theorem s4_462_safe : Safe 9 4 s4_462 := by
  apply safe_succ 8 4 s4_462 [s5_73, s5_569] (by decide) s4_462_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_73_safe
  · subst z; exact s5_569_safe
def s4_463 : State := ⟨[1,12,66,145], 44602511244162009098461918902839391159390486, 2, 0, 1, 0⟩
theorem s4_463_edges : next config 4 s4_463 = [s5_74, s5_555, s5_577] := by decide
theorem s4_463_safe : Safe 9 4 s4_463 := by
  apply safe_succ 8 4 s4_463 [s5_74, s5_555, s5_577] (by decide) s4_463_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_74_safe
  · subst z; exact s5_555_safe
  · subst z; exact s5_577_safe
def s4_464 : State := ⟨[1,12,66,145], 66902575877958790363070710426272889128947990, 2, 0, 1, 0⟩
theorem s4_464_edges : next config 4 s4_464 = [s5_75, s5_557, s5_579] := by decide
theorem s4_464_safe : Safe 9 4 s4_464 := by
  apply safe_succ 8 4 s4_464 [s5_75, s5_557, s5_579] (by decide) s4_464_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_75_safe
  · subst z; exact s5_557_safe
  · subst z; exact s5_579_safe
def s4_465 : State := ⟨[1,12,66,146], 89204682205957097258460282197350977707774230, 2, 0, 1, 0⟩
theorem s4_465_edges : next config 4 s4_465 = [s5_76, s5_559] := by decide
theorem s4_465_safe : Safe 9 4 s4_465 := by
  apply safe_succ 8 4 s4_465 [s5_76, s5_559] (by decide) s4_465_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_76_safe
  · subst z; exact s5_559_safe
def s4_466 : State := ⟨[1,12,66,146], 111504066275020036646142146971569612140908822, 2, 0, 1, 0⟩
theorem s4_466_edges : next config 4 s4_466 = [s5_77, s5_561] := by decide
theorem s4_466_safe : Safe 9 4 s4_466 := by
  apply safe_succ 8 4 s4_466 [s5_77, s5_561] (by decide) s4_466_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_77_safe
  · subst z; exact s5_561_safe
def s4_467 : State := ⟨[1,12,66,162], 5846006551025023507419431648274238836155414024470, 2, 0, 1, 0⟩
theorem s4_467_edges : next config 4 s4_467 = [s5_78, s5_564] := by decide
theorem s4_467_safe : Safe 9 4 s4_467 := by
  apply safe_succ 8 4 s4_467 [s5_78, s5_564] (by decide) s4_467_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_78_safe
  · subst z; exact s5_564_safe
def s4_468 : State := ⟨[1,12,66,162], 7307508186994796957939362627137023426084273721622, 2, 0, 1, 0⟩
theorem s4_468_edges : next config 4 s4_468 = [s5_79, s5_566] := by decide
theorem s4_468_safe : Safe 9 4 s4_468 := by
  apply safe_succ 8 4 s4_468 [s5_79, s5_566] (by decide) s4_468_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_79_safe
  · subst z; exact s5_566_safe
def s4_469 : State := ⟨[1,12,66,176], 95780971326419139128294233276893597857147361253462294, 2, 0, 1, 0⟩
theorem s4_469_edges : next config 4 s4_469 = [s5_80, s5_568] := by decide
theorem s4_469_safe : Safe 9 4 s4_469 := by
  apply safe_succ 8 4 s4_469 [s5_80, s5_568] (by decide) s4_469_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_80_safe
  · subst z; exact s5_568_safe
def s4_470 : State := ⟨[1,12,66,176], 95782432805755724832681813820190595867518655680024854, 2, 0, 1, 0⟩
theorem s4_470_edges : next config 4 s4_470 = [s5_81, s5_570] := by decide
theorem s4_470_safe : Safe 9 4 s4_470 := by
  apply safe_succ 8 4 s4_470 [s5_81, s5_570] (by decide) s4_470_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_81_safe
  · subst z; exact s5_570_safe
def s4_471 : State := ⟨[1,12,66,210], 1645504557321206042177270268038248049062735139514556029465596182, 2, 0, 1, 0⟩
theorem s4_471_edges : next config 4 s4_471 = [s5_82, s5_573] := by decide
theorem s4_471_safe : Safe 9 4 s4_471 := by
  apply safe_succ 8 4 s4_471 [s5_82, s5_573] (by decide) s4_471_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_82_safe
  · subst z; exact s5_573_safe
def s4_472 : State := ⟨[1,12,66,210], 1645529665728147588878024865997410256586863830663685524097667350, 2, 0, 1, 0⟩
theorem s4_472_edges : next config 4 s4_472 = [s5_83, s5_574] := by decide
theorem s4_472_safe : Safe 9 4 s4_472 := by
  apply safe_succ 8 4 s4_472 [s5_83, s5_574] (by decide) s4_472_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_83_safe
  · subst z; exact s5_574_safe
def s4_473 : State := ⟨[1,12,67,128], 340282366920938463629395304099449213214, 3, 1, 0, 0⟩
theorem s4_473_edges : next config 4 s4_473 = [s5_1020, s5_86, s5_547, s5_552, s5_572, s5_548, s5_551, s5_553, s5_562] := by decide
theorem s4_473_safe : Safe 9 4 s4_473 := by
  apply safe_succ 8 4 s4_473 [s5_1020, s5_86, s5_547, s5_552, s5_572, s5_548, s5_551, s5_553, s5_562] (by decide) s4_473_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1020_safe
  · subst z; exact s5_86_safe
  · subst z; exact s5_547_safe
  · subst z; exact s5_552_safe
  · subst z; exact s5_572_safe
  · subst z; exact s5_548_safe
  · subst z; exact s5_551_safe
  · subst z; exact s5_553_safe
  · subst z; exact s5_562_safe
def s4_474 : State := ⟨[1,12,67,129], 1020847100762815390593038007110404739350, 2, 0, 1, 0⟩
theorem s4_474_edges : next config 4 s4_474 = [s5_87, s5_554] := by decide
theorem s4_474_safe : Safe 9 4 s4_474 := by
  apply safe_succ 8 4 s4_474 [s5_87, s5_554] (by decide) s4_474_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_87_safe
  · subst z; exact s5_554_safe
def s4_475 : State := ⟨[1,12,67,129], 1020847100762815390629931495257823842582, 2, 0, 1, 0⟩
theorem s4_475_edges : next config 4 s4_475 = [s5_88, s5_555] := by decide
theorem s4_475_safe : Safe 9 4 s4_475 := by
  apply safe_succ 8 4 s4_475 [s5_88, s5_555] (by decide) s4_475_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_88_safe
  · subst z; exact s5_555_safe
def s4_476 : State := ⟨[1,12,67,130], 1701411834604692317519787221973941162262, 2, 0, 1, 0⟩
theorem s4_476_edges : next config 4 s4_476 = [s5_89, s5_558, s5_563] := by decide
theorem s4_476_safe : Safe 9 4 s4_476 := by
  apply safe_succ 8 4 s4_476 [s5_89, s5_558, s5_563] (by decide) s4_476_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_89_safe
  · subst z; exact s5_558_safe
  · subst z; exact s5_563_safe
def s4_477 : State := ⟨[1,12,67,130], 1701411834604692317556680710121360265494, 2, 0, 1, 0⟩
theorem s4_477_edges : next config 4 s4_477 = [s5_90, s5_559, s5_564] := by decide
theorem s4_477_safe : Safe 9 4 s4_477 := by
  apply safe_succ 8 4 s4_477 [s5_90, s5_559, s5_564] (by decide) s4_477_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_90_safe
  · subst z; exact s5_559_safe
  · subst z; exact s5_564_safe
def s4_478 : State := ⟨[1,12,67,132], 5784800237655953879080282511155159699734, 2, 0, 1, 0⟩
theorem s4_478_edges : next config 4 s4_478 = [s5_91] := by decide
theorem s4_478_safe : Safe 9 4 s4_478 := by
  apply safe_succ 8 4 s4_478 [s5_91] (by decide) s4_478_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_91_safe
def s4_479 : State := ⟨[1,12,67,132], 5784800237655953879117175999302578802966, 2, 0, 1, 0⟩
theorem s4_479_edges : next config 4 s4_479 = [s5_92] := by decide
theorem s4_479_safe : Safe 9 4 s4_479 := by
  apply safe_succ 8 4 s4_479 [s5_92] (by decide) s4_479_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_92_safe
def s4_480 : State := ⟨[1,12,67,136], 87452568298681185110290188294779530449174, 2, 0, 1, 0⟩
theorem s4_480_edges : next config 4 s4_480 = [s5_93] := by decide
theorem s4_480_safe : Safe 9 4 s4_480 := by
  apply safe_succ 8 4 s4_480 [s5_93] (by decide) s4_480_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_93_safe
def s4_481 : State := ⟨[1,12,67,136], 87452568298681185110327081782926949552406, 2, 0, 1, 0⟩
theorem s4_481_edges : next config 4 s4_481 = [s5_94] := by decide
theorem s4_481_safe : Safe 9 4 s4_481 := by
  apply safe_succ 8 4 s4_481 [s5_94] (by decide) s4_481_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_94_safe
def s4_482 : State := ⟨[1,12,67,140], 1394136857275084884809648680832769462440214, 2, 0, 1, 0⟩
theorem s4_482_edges : next config 4 s4_482 = [s5_97] := by decide
theorem s4_482_safe : Safe 9 4 s4_482 := by
  apply safe_succ 8 4 s4_482 [s5_97] (by decide) s4_482_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_97_safe
def s4_483 : State := ⟨[1,12,67,140], 1394136857275084884809685574320916881543446, 2, 0, 1, 0⟩
theorem s4_483_edges : next config 4 s4_483 = [s5_98] := by decide
theorem s4_483_safe : Safe 9 4 s4_483 := by
  apply safe_succ 8 4 s4_483 [s5_98] (by decide) s4_483_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_98_safe
def s4_484 : State := ⟨[1,12,67,144], 22301085480897544079999384561440608374296854, 2, 0, 1, 0⟩
theorem s4_484_edges : next config 4 s4_484 = [s5_101, s5_556, s5_560, s5_567] := by decide
theorem s4_484_safe : Safe 9 4 s4_484 := by
  apply safe_succ 8 4 s4_484 [s5_101, s5_556, s5_560, s5_567] (by decide) s4_484_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_101_safe
  · subst z; exact s5_556_safe
  · subst z; exact s5_560_safe
  · subst z; exact s5_567_safe
def s4_485 : State := ⟨[1,12,67,144], 22301085480897544079999421454928755793400086, 2, 0, 1, 0⟩
theorem s4_485_edges : next config 4 s4_485 = [s5_102, s5_557, s5_561, s5_568] := by decide
theorem s4_485_safe : Safe 9 4 s4_485 := by
  apply safe_succ 8 4 s4_485 [s5_102, s5_557, s5_561, s5_568] (by decide) s4_485_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_102_safe
  · subst z; exact s5_557_safe
  · subst z; exact s5_561_safe
  · subst z; exact s5_568_safe
def s4_486 : State := ⟨[1,12,67,160], 1461501637671185285124623296382571811902800859414, 2, 0, 1, 0⟩
theorem s4_486_edges : next config 4 s4_486 = [s5_112, s5_565, s5_569] := by decide
theorem s4_486_safe : Safe 9 4 s4_486 := by
  apply safe_succ 8 4 s4_486 [s5_112, s5_565, s5_569] (by decide) s4_486_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_112_safe
  · subst z; exact s5_565_safe
  · subst z; exact s5_569_safe
def s4_487 : State := ⟨[1,12,67,160], 1461501637671185285124623296419465300050219962646, 2, 0, 1, 0⟩
theorem s4_487_edges : next config 4 s4_487 = [s5_113, s5_566, s5_570] := by decide
theorem s4_487_safe : Safe 9 4 s4_487 := by
  apply safe_succ 8 4 s4_487 [s5_113, s5_566, s5_570] (by decide) s4_487_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_113_safe
  · subst z; exact s5_566_safe
  · subst z; exact s5_570_safe
def s4_488 : State := ⟨[1,12,67,192], 6277101735386680764176071790128604879768644236710902829334, 2, 0, 1, 0⟩
theorem s4_488_edges : next config 4 s4_488 = [s5_120] := by decide
theorem s4_488_safe : Safe 9 4 s4_488 := by
  apply safe_succ 8 4 s4_488 [s5_120] (by decide) s4_488_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_120_safe
def s4_489 : State := ⟨[1,12,67,192], 6277101735386680764176071790128604879805537724858321932566, 2, 0, 1, 0⟩
theorem s4_489_edges : next config 4 s4_489 = [s5_121] := by decide
theorem s4_489_safe : Safe 9 4 s4_489 := by
  apply safe_succ 8 4 s4_489 [s5_121] (by decide) s4_489_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_121_safe
def s4_490 : State := ⟨[1,12,67,193], 12554203470773361528011861213336271295870999681174937342230, 2, 0, 1, 0⟩
theorem s4_490_edges : next config 4 s4_490 = [s5_122] := by decide
theorem s4_490_safe : Safe 9 4 s4_490 := by
  apply safe_succ 8 4 s4_490 [s5_122] (by decide) s4_490_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_122_safe
def s4_491 : State := ⟨[1,12,67,194], 25108406941546723055683440059751604128112604058250425471254, 2, 0, 1, 0⟩
theorem s4_491_edges : next config 4 s4_491 = [s5_123, s5_574] := by decide
theorem s4_491_safe : Safe 9 4 s4_491 := by
  apply safe_succ 8 4 s4_491 [s5_123, s5_574] (by decide) s4_491_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_123_safe
  · subst z; exact s5_574_safe
def s4_492 : State := ⟨[1,12,67,195], 50216813883093446111026597752582269792485132347959144419606, 2, 0, 1, 0⟩
theorem s4_492_edges : next config 4 s4_492 = [s5_124] := by decide
theorem s4_492_safe : Safe 9 4 s4_492 := by
  apply safe_succ 8 4 s4_492 [s5_124] (by decide) s4_492_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_124_safe
def s4_493 : State := ⟨[1,12,67,195], 50216813883093446111026597752582269792522025836106563522838, 2, 0, 1, 0⟩
theorem s4_493_edges : next config 4 s4_493 = [s5_125] := by decide
theorem s4_493_safe : Safe 9 4 s4_493 := by
  apply safe_succ 8 4 s4_493 [s5_125] (by decide) s4_493_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_125_safe
def s4_494 : State := ⟨[1,12,80,145], 44602511244162009099670770935477725495890198, 2, 0, 1, 0⟩
theorem s4_494_edges : next config 4 s4_494 = [s5_128, s5_578] := by decide
theorem s4_494_safe : Safe 9 4 s4_494 := by
  apply safe_succ 8 4 s4_494 [s5_128, s5_578] (by decide) s4_494_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_128_safe
  · subst z; exact s5_578_safe
def s4_495 : State := ⟨[1,12,80,145], 66902575877958790364279562458911223465447702, 2, 0, 1, 0⟩
theorem s4_495_edges : next config 4 s4_495 = [s5_129, s5_580] := by decide
theorem s4_495_safe : Safe 9 4 s4_495 := by
  apply safe_succ 8 4 s4_495 [s5_129, s5_580] (by decide) s4_495_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_129_safe
  · subst z; exact s5_580_safe
def s4_496 : State := ⟨[1,12,80,210], 1645504557321206042154970883969185109676262126772975729368961302, 2, 0, 1, 0⟩
theorem s4_496_edges : next config 4 s4_496 = [s5_130] := by decide
theorem s4_496_safe : Safe 9 4 s4_496 := by
  apply safe_succ 8 4 s4_496 [s5_130] (by decide) s4_496_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_130_safe
def s4_497 : State := ⟨[1,12,80,210], 2056880696651507552693711818479055052168092239682940968133267734, 2, 0, 1, 0⟩
theorem s4_497_edges : next config 4 s4_497 = [s5_131] := by decide
theorem s4_497_safe : Safe 9 4 s4_497 := by
  apply safe_succ 8 4 s4_497 [s5_131] (by decide) s4_497_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_131_safe
def s4_498 : State := ⟨[1,12,82,129], 1020847100762820226185636001184846254358, 2, 0, 1, 0⟩
theorem s4_498_edges : next config 4 s4_498 = [s5_134, s5_577] := by decide
theorem s4_498_safe : Safe 9 4 s4_498 := by
  apply safe_succ 8 4 s4_498 [s5_134, s5_577] (by decide) s4_498_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_134_safe
  · subst z; exact s5_577_safe
def s4_499 : State := ⟨[1,12,82,129], 1020847100762821435037668639519182754070, 2, 0, 1, 0⟩
theorem s4_499_edges : next config 4 s4_499 = [s5_135, s5_578] := by decide
theorem s4_499_safe : Safe 9 4 s4_499 := by
  apply safe_succ 8 4 s4_499 [s5_135, s5_578] (by decide) s4_499_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_135_safe
  · subst z; exact s5_578_safe
def s4_500 : State := ⟨[1,12,82,130], 1701411834604697153112385216048382677270, 2, 0, 1, 0⟩
theorem s4_500_edges : next config 4 s4_500 = [s5_138] := by decide
theorem s4_500_safe : Safe 9 4 s4_500 := by
  apply safe_succ 8 4 s4_500 [s5_138] (by decide) s4_500_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_138_safe
def s4_501 : State := ⟨[1,12,82,130], 1701411834604698361964417854382719176982, 2, 0, 1, 0⟩
theorem s4_501_edges : next config 4 s4_501 = [s5_139] := by decide
theorem s4_501_safe : Safe 9 4 s4_501 := by
  apply safe_succ 8 4 s4_501 [s5_139] (by decide) s4_501_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_139_safe
def s4_502 : State := ⟨[1,12,82,132], 5784800237655958714672880505229601214742, 2, 0, 1, 0⟩
theorem s4_502_edges : next config 4 s4_502 = [s5_142] := by decide
theorem s4_502_safe : Safe 9 4 s4_502 := by
  apply safe_succ 8 4 s4_502 [s5_142] (by decide) s4_502_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_142_safe
def s4_503 : State := ⟨[1,12,82,132], 5784800237655959923524913143563937714454, 2, 0, 1, 0⟩
theorem s4_503_edges : next config 4 s4_503 = [s5_143] := by decide
theorem s4_503_safe : Safe 9 4 s4_503 := by
  apply safe_succ 8 4 s4_503 [s5_143] (by decide) s4_503_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_143_safe
def s4_504 : State := ⟨[1,12,82,136], 87452568298681189945882786288853971964182, 2, 0, 1, 0⟩
theorem s4_504_edges : next config 4 s4_504 = [s5_146] := by decide
theorem s4_504_safe : Safe 9 4 s4_504 := by
  apply safe_succ 8 4 s4_504 [s5_146] (by decide) s4_504_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_146_safe
def s4_505 : State := ⟨[1,12,82,136], 87452568298681191154734818927188308463894, 2, 0, 1, 0⟩
theorem s4_505_edges : next config 4 s4_505 = [s5_147] := by decide
theorem s4_505_safe : Safe 9 4 s4_505 := by
  apply safe_succ 8 4 s4_505 [s5_147] (by decide) s4_505_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_147_safe
def s4_506 : State := ⟨[1,12,82,140], 1394136857275084889645241278826843903955222, 2, 0, 1, 0⟩
theorem s4_506_edges : next config 4 s4_506 = [s5_152] := by decide
theorem s4_506_safe : Safe 9 4 s4_506 := by
  apply safe_succ 8 4 s4_506 [s5_152] (by decide) s4_506_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_152_safe
def s4_507 : State := ⟨[1,12,82,140], 1394136857275084890854093311465178240454934, 2, 0, 1, 0⟩
theorem s4_507_edges : next config 4 s4_507 = [s5_153] := by decide
theorem s4_507_safe : Safe 9 4 s4_507 := by
  apply safe_succ 8 4 s4_507 [s5_153] (by decide) s4_507_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_153_safe
def s4_508 : State := ⟨[1,12,82,144], 22301085480897544084834977159434682815811862, 2, 0, 1, 0⟩
theorem s4_508_edges : next config 4 s4_508 = [s5_154, s5_579] := by decide
theorem s4_508_safe : Safe 9 4 s4_508 := by
  apply safe_succ 8 4 s4_508 [s5_154, s5_579] (by decide) s4_508_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_154_safe
  · subst z; exact s5_579_safe
def s4_509 : State := ⟨[1,12,82,144], 22301085480897544086043829192073017152311574, 2, 0, 1, 0⟩
theorem s4_509_edges : next config 4 s4_509 = [s5_155, s5_580] := by decide
theorem s4_509_safe : Safe 9 4 s4_509 := by
  apply safe_succ 8 4 s4_509 [s5_155, s5_580] (by decide) s4_509_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_155_safe
  · subst z; exact s5_580_safe
def s4_510 : State := ⟨[1,12,82,160], 1461501637671185285124628131975169805977242374422, 2, 0, 1, 0⟩
theorem s4_510_edges : next config 4 s4_510 = [s5_160] := by decide
theorem s4_510_safe : Safe 9 4 s4_510 := by
  apply safe_succ 8 4 s4_510 [s5_160] (by decide) s4_510_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_160_safe
def s4_511 : State := ⟨[1,12,82,160], 1461501637671185285124629340827202444311578874134, 2, 0, 1, 0⟩
theorem s4_511_edges : next config 4 s4_511 = [s5_161] := by decide
theorem s4_511_safe : Safe 9 4 s4_511 := by
  apply safe_succ 8 4 s4_511 [s5_161] (by decide) s4_511_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_161_safe
def s4_512 : State := ⟨[1,12,82,192], 6277101735386680764176071790128609715361242230785344344342, 2, 0, 1, 0⟩
theorem s4_512_edges : next config 4 s4_512 = [s5_164] := by decide
theorem s4_512_safe : Safe 9 4 s4_512 := by
  apply safe_succ 8 4 s4_512 [s5_164] (by decide) s4_512_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_164_safe
def s4_513 : State := ⟨[1,12,82,192], 6277101735386680764176071790128610924213274869119680844054, 2, 0, 1, 0⟩
theorem s4_513_edges : next config 4 s4_513 = [s5_165] := by decide
theorem s4_513_safe : Safe 9 4 s4_513 := by
  apply safe_succ 8 4 s4_513 [s5_165] (by decide) s4_513_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_165_safe
def s4_514 : State := ⟨[1,12,82,194], 25108406941546723055683440059751608963668308564177447883030, 2, 0, 1, 0⟩
theorem s4_514_edges : next config 4 s4_514 = [s5_168] := by decide
theorem s4_514_safe : Safe 9 4 s4_514 := by
  apply safe_succ 8 4 s4_514 [s5_168] (by decide) s4_514_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_168_safe
def s4_515 : State := ⟨[1,12,82,208], 411376139330301510538742635921704547190192077327819621483483414, 2, 0, 1, 0⟩
theorem s4_515_edges : next config 4 s4_515 = [s5_170] := by decide
theorem s4_515_safe : Safe 9 4 s4_515 := by
  apply safe_succ 8 4 s4_515 [s5_170] (by decide) s4_515_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_170_safe
def s4_516 : State := ⟨[1,12,82,210], 1645504557321206042154969522839717425926035124520366184658440470, 2, 0, 1, 0⟩
theorem s4_516_edges : next config 4 s4_516 = [s5_172] := by decide
theorem s4_516_safe : Safe 9 4 s4_516 := by
  apply safe_succ 8 4 s4_516 [s5_172] (by decide) s4_516_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_172_safe
def s4_517 : State := ⟨[1,12,82,210], 1645504557321206042154969522839717425927243976553004518994940182, 2, 0, 1, 0⟩
theorem s4_517_edges : next config 4 s4_517 = [s5_173] := by decide
theorem s4_517_safe : Safe 9 4 s4_517 := by
  apply safe_succ 8 4 s4_517 [s5_173] (by decide) s4_517_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_173_safe
def s4_518 : State := ⟨[1,12,96,128], 340282367000166625996085689103316750622, 3, 1, 0, 0⟩
theorem s4_518_edges : next config 4 s4_518 = [s5_1029, s5_184, s5_646, s5_581, s5_599, s5_636, s5_585, s5_595, s5_603, s5_608] := by decide
theorem s4_518_safe : Safe 9 4 s4_518 := by
  apply safe_succ 8 4 s4_518 [s5_1029, s5_184, s5_646, s5_581, s5_599, s5_636, s5_585, s5_595, s5_603, s5_608] (by decide) s4_518_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1029_safe
  · subst z; exact s5_184_safe
  · subst z; exact s5_646_safe
  · subst z; exact s5_581_safe
  · subst z; exact s5_599_safe
  · subst z; exact s5_636_safe
  · subst z; exact s5_585_safe
  · subst z; exact s5_595_safe
  · subst z; exact s5_603_safe
  · subst z; exact s5_608_safe
def s4_519 : State := ⟨[1,12,96,128], 340282367000166625996085689111906685206, 3, 1, 0, 0⟩
theorem s4_519_edges : next config 4 s4_519 = [s5_1031, s5_185, s5_647, s5_582, s5_600, s5_637, s5_586, s5_596, s5_604, s5_609] := by decide
theorem s4_519_safe : Safe 9 4 s4_519 := by
  apply safe_succ 8 4 s4_519 [s5_1031, s5_185, s5_647, s5_582, s5_600, s5_637, s5_586, s5_596, s5_604, s5_609] (by decide) s4_519_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1031_safe
  · subst z; exact s5_185_safe
  · subst z; exact s5_647_safe
  · subst z; exact s5_582_safe
  · subst z; exact s5_600_safe
  · subst z; exact s5_637_safe
  · subst z; exact s5_586_safe
  · subst z; exact s5_596_safe
  · subst z; exact s5_604_safe
  · subst z; exact s5_609_safe
def s4_520 : State := ⟨[1,12,96,128], 340282367000166626032979177250735853846, 3, 1, 0, 0⟩
theorem s4_520_edges : next config 4 s4_520 = [s5_1032, s5_186, s5_648, s5_583, s5_601, s5_638, s5_587, s5_597, s5_605, s5_610] := by decide
theorem s4_520_safe : Safe 9 4 s4_520 := by
  apply safe_succ 8 4 s4_520 [s5_1032, s5_186, s5_648, s5_583, s5_601, s5_638, s5_587, s5_597, s5_605, s5_610] (by decide) s4_520_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1032_safe
  · subst z; exact s5_186_safe
  · subst z; exact s5_648_safe
  · subst z; exact s5_583_safe
  · subst z; exact s5_601_safe
  · subst z; exact s5_638_safe
  · subst z; exact s5_587_safe
  · subst z; exact s5_597_safe
  · subst z; exact s5_605_safe
  · subst z; exact s5_610_safe
def s4_521 : State := ⟨[1,12,96,128], 340282367158622951024614364290404651286, 3, 1, 0, 0⟩
theorem s4_521_edges : next config 4 s4_521 = [s5_1033, s5_187, s5_649, s5_584, s5_602, s5_639, s5_588, s5_598, s5_606, s5_611] := by decide
theorem s4_521_safe : Safe 9 4 s4_521 := by
  apply safe_succ 8 4 s4_521 [s5_1033, s5_187, s5_649, s5_584, s5_602, s5_639, s5_588, s5_598, s5_606, s5_611] (by decide) s4_521_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1033_safe
  · subst z; exact s5_187_safe
  · subst z; exact s5_649_safe
  · subst z; exact s5_584_safe
  · subst z; exact s5_602_safe
  · subst z; exact s5_639_safe
  · subst z; exact s5_588_safe
  · subst z; exact s5_598_safe
  · subst z; exact s5_606_safe
  · subst z; exact s5_611_safe
def s4_522 : State := ⟨[1,12,96,131], 3743106036209551260629831763420998865174, 2, 0, 1, 0⟩
theorem s4_522_edges : next config 4 s4_522 = [s5_190, s5_650, s5_616] := by decide
theorem s4_522_safe : Safe 9 4 s4_522 := by
  apply safe_succ 8 4 s4_522 [s5_190, s5_650, s5_616] (by decide) s4_522_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_190_safe
  · subst z; exact s5_650_safe
  · subst z; exact s5_616_safe
def s4_523 : State := ⟨[1,12,96,131], 4423670770051428187556580978284535288086, 2, 0, 1, 0⟩
theorem s4_523_edges : next config 4 s4_523 = [s5_192, s5_651, s5_617] := by decide
theorem s4_523_safe : Safe 9 4 s4_523 := by
  apply safe_succ 8 4 s4_523 [s5_192, s5_651, s5_617] (by decide) s4_523_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_192_safe
  · subst z; exact s5_651_safe
  · subst z; exact s5_617_safe
def s4_524 : State := ⟨[1,12,96,145], 44602511244162088326624359380200689865134358, 2, 0, 1, 0⟩
theorem s4_524_edges : next config 4 s4_524 = [s5_1517, s5_889, s5_1169, s5_204, s5_642, s5_686, s5_652, s5_672] := by decide
theorem s4_524_safe : Safe 9 4 s4_524 := by
  apply safe_succ 8 4 s4_524 [s5_1517, s5_889, s5_1169, s5_204, s5_642, s5_686, s5_652, s5_672] (by decide) s4_524_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1517_safe
  · subst z; exact s5_889_safe
  · subst z; exact s5_1169_safe
  · subst z; exact s5_204_safe
  · subst z; exact s5_642_safe
  · subst z; exact s5_686_safe
  · subst z; exact s5_652_safe
  · subst z; exact s5_672_safe
def s4_525 : State := ⟨[1,12,96,145], 66902575877958869591233150903634187834691862, 2, 0, 1, 0⟩
theorem s4_525_edges : next config 4 s4_525 = [s5_1518, s5_890, s5_1170, s5_212, s5_643, s5_687, s5_653, s5_673] := by decide
theorem s4_525_safe : Safe 9 4 s4_525 := by
  apply safe_succ 8 4 s4_525 [s5_1518, s5_890, s5_1170, s5_212, s5_643, s5_687, s5_653, s5_673] (by decide) s4_525_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1518_safe
  · subst z; exact s5_890_safe
  · subst z; exact s5_1170_safe
  · subst z; exact s5_212_safe
  · subst z; exact s5_643_safe
  · subst z; exact s5_687_safe
  · subst z; exact s5_653_safe
  · subst z; exact s5_673_safe
def s4_526 : State := ⟨[1,12,96,146], 89204682205957176486622722674712276413518102, 2, 0, 1, 0⟩
theorem s4_526_edges : next config 4 s4_526 = [s5_891, s5_219, s5_654] := by decide
theorem s4_526_safe : Safe 9 4 s4_526 := by
  apply safe_succ 8 4 s4_526 [s5_891, s5_219, s5_654] (by decide) s4_526_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_891_safe
  · subst z; exact s5_219_safe
  · subst z; exact s5_654_safe
def s4_527 : State := ⟨[1,12,96,146], 111504066275020115874304587448930910846652694, 2, 0, 1, 0⟩
theorem s4_527_edges : next config 4 s4_527 = [s5_892, s5_225, s5_655] := by decide
theorem s4_527_safe : Safe 9 4 s4_527 := by
  apply safe_succ 8 4 s4_527 [s5_892, s5_225, s5_655] (by decide) s4_527_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_892_safe
  · subst z; exact s5_225_safe
  · subst z; exact s5_655_safe
def s4_528 : State := ⟨[1,12,96,161], 2923003275682652937249413218355400943278718259478, 2, 0, 1, 0⟩
theorem s4_528_edges : next config 4 s4_528 = [s5_231, s5_656, s5_618] := by decide
theorem s4_528_safe : Safe 9 4 s4_528 := by
  apply safe_succ 8 4 s4_528 [s5_231, s5_656, s5_618] (by decide) s4_528_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_231_safe
  · subst z; exact s5_656_safe
  · subst z; exact s5_618_safe
def s4_529 : State := ⟨[1,12,96,161], 4384504912332991121611221124144934748071114379542, 2, 0, 1, 0⟩
theorem s4_529_edges : next config 4 s4_529 = [s5_232, s5_657, s5_619] := by decide
theorem s4_529_safe : Safe 9 4 s4_529 := by
  apply safe_succ 8 4 s4_529 [s5_232, s5_657, s5_619] (by decide) s4_529_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_232_safe
  · subst z; exact s5_657_safe
  · subst z; exact s5_619_safe
def s4_530 : State := ⟨[1,12,96,162], 5846006551025023507498659810714716197454119768342, 2, 0, 1, 0⟩
theorem s4_530_edges : next config 4 s4_530 = [s5_1519, s5_1578, s5_893, s5_235, s5_644, s5_679, s5_658, s5_620, s5_628] := by decide
theorem s4_530_safe : Safe 9 4 s4_530 := by
  apply safe_succ 8 4 s4_530 [s5_1519, s5_1578, s5_893, s5_235, s5_644, s5_679, s5_658, s5_620, s5_628] (by decide) s4_530_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1519_safe
  · subst z; exact s5_1578_safe
  · subst z; exact s5_893_safe
  · subst z; exact s5_235_safe
  · subst z; exact s5_644_safe
  · subst z; exact s5_679_safe
  · subst z; exact s5_658_safe
  · subst z; exact s5_620_safe
  · subst z; exact s5_628_safe
def s4_531 : State := ⟨[1,12,96,162], 7307508186994796958018590789577500787382979465494, 2, 0, 1, 0⟩
theorem s4_531_edges : next config 4 s4_531 = [s5_1520, s5_1579, s5_894, s5_242, s5_645, s5_680, s5_659, s5_621, s5_629] := by decide
theorem s4_531_safe : Safe 9 4 s4_531 := by
  apply safe_succ 8 4 s4_531 [s5_1520, s5_1579, s5_894, s5_242, s5_645, s5_680, s5_659, s5_621, s5_629] (by decide) s4_531_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1520_safe
  · subst z; exact s5_1579_safe
  · subst z; exact s5_894_safe
  · subst z; exact s5_242_safe
  · subst z; exact s5_645_safe
  · subst z; exact s5_680_safe
  · subst z; exact s5_659_safe
  · subst z; exact s5_621_safe
  · subst z; exact s5_629_safe
def s4_532 : State := ⟨[1,12,96,176], 95780971326419139128294312505056038334508659959206166, 2, 0, 1, 0⟩
theorem s4_532_edges : next config 4 s4_532 = [s5_897, s5_261, s5_660] := by decide
theorem s4_532_safe : Safe 9 4 s4_532 := by
  apply safe_succ 8 4 s4_532 [s5_897, s5_261, s5_660] (by decide) s4_532_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_897_safe
  · subst z; exact s5_261_safe
  · subst z; exact s5_660_safe
def s4_533 : State := ⟨[1,12,96,176], 95782432805755724832681893048353036344879954385768726, 2, 0, 1, 0⟩
theorem s4_533_edges : next config 4 s4_533 = [s5_898, s5_265, s5_661] := by decide
theorem s4_533_safe : Safe 9 4 s4_533 := by
  apply safe_succ 8 4 s4_533 [s5_898, s5_265, s5_661] (by decide) s4_533_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_898_safe
  · subst z; exact s5_265_safe
  · subst z; exact s5_661_safe
def s4_534 : State := ⟨[1,12,96,193], 12554203470773361528692425947257376385127545792894922199318, 2, 0, 1, 0⟩
theorem s4_534_edges : next config 4 s4_534 = [s5_268, s5_662] := by decide
theorem s4_534_safe : Safe 9 4 s4_534 := by
  apply safe_succ 8 4 s4_534 [s5_268, s5_662] (by decide) s4_534_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_268_safe
  · subst z; exact s5_662_safe
def s4_535 : State := ⟨[1,12,96,193], 18831305206160042291847650636623165874303152022495420289302, 2, 0, 1, 0⟩
theorem s4_535_edges : next config 4 s4_535 = [s5_270, s5_663] := by decide
theorem s4_535_safe : Safe 9 4 s4_535 := by
  apply safe_succ 8 4 s4_535 [s5_270, s5_663] (by decide) s4_535_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_270_safe
  · subst z; exact s5_663_safe
def s4_536 : State := ⟨[1,12,96,194], 25108406941546723057044569527514586144259005896686527648022, 2, 0, 1, 0⟩
theorem s4_536_edges : next config 4 s4_536 = [s5_272, s5_676, s5_664, s5_674, s5_614, s5_632] := by decide
theorem s4_536_safe : Safe 9 4 s4_536 := by
  apply safe_succ 8 4 s4_536 [s5_272, s5_676, s5_664, s5_674, s5_614, s5_632] (by decide) s4_536_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_272_safe
  · subst z; exact s5_676_safe
  · subst z; exact s5_664_safe
  · subst z; exact s5_674_safe
  · subst z; exact s5_614_safe
  · subst z; exact s5_632_safe
def s4_537 : State := ⟨[1,12,96,194], 31385508676933403819519229483038498706507862911423489315094, 2, 0, 1, 0⟩
theorem s4_537_edges : next config 4 s4_537 = [s5_274, s5_677, s5_665, s5_675, s5_615, s5_633] := by decide
theorem s4_537_safe : Safe 9 4 s4_537 := by
  apply safe_succ 8 4 s4_537 [s5_274, s5_677, s5_665, s5_675, s5_615, s5_633] (by decide) s4_537_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_274_safe
  · subst z; exact s5_677_safe
  · subst z; exact s5_665_safe
  · subst z; exact s5_675_safe
  · subst z; exact s5_615_safe
  · subst z; exact s5_633_safe
def s4_538 : State := ⟨[1,12,96,208], 411376139330301510561043381120235249553845680766732430659883286, 2, 0, 1, 0⟩
theorem s4_538_edges : next config 4 s4_538 = [s5_276, s5_666, s5_634] := by decide
theorem s4_538_safe : Safe 9 4 s4_538 := by
  apply safe_succ 8 4 s4_538 [s5_276, s5_666, s5_634] (by decide) s4_538_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_276_safe
  · subst z; exact s5_666_safe
  · subst z; exact s5_634_safe
def s4_539 : State := ⟨[1,12,96,208], 411382416432036897219506471711127834078726064849528533188415766, 2, 0, 1, 0⟩
theorem s4_539_edges : next config 4 s4_539 = [s5_277, s5_667, s5_635] := by decide
theorem s4_539_safe : Safe 9 4 s4_539 := by
  apply safe_succ 8 4 s4_539 [s5_277, s5_667, s5_635] (by decide) s4_539_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_277_safe
  · subst z; exact s5_667_safe
  · subst z; exact s5_635_safe
def s4_540 : State := ⟨[1,12,96,225], 53919893334301279589334030175060108448116332398003979866174073671958, 2, 0, 1, 0⟩
theorem s4_540_edges : next config 4 s4_540 = [s5_286, s5_668] := by decide
theorem s4_540_safe : Safe 9 4 s4_540 := by
  apply safe_succ 8 4 s4_540 [s5_286, s5_668] (by decide) s4_540_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_286_safe
  · subst z; exact s5_668_safe
def s4_541 : State := ⟨[1,12,96,225], 80879840001451919384001045261399174387911599893617803132414147498262, 2, 0, 1, 0⟩
theorem s4_541_edges : next config 4 s4_541 = [s5_287, s5_669] := by decide
theorem s4_541_safe : Safe 9 4 s4_541 := by
  apply safe_succ 8 4 s4_541 [s5_287, s5_669] (by decide) s4_541_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_287_safe
  · subst z; exact s5_669_safe
def s4_542 : State := ⟨[1,12,96,240], 1766847064778384329583297500765219601308381520183780672479943666115350806, 2, 0, 1, 0⟩
theorem s4_542_edges : next config 4 s4_542 = [s5_292, s5_670] := by decide
theorem s4_542_safe : Safe 9 4 s4_542 := by
  apply safe_succ 8 4 s4_542 [s5_292, s5_670] (by decide) s4_542_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_292_safe
  · subst z; exact s5_670_safe
def s4_543 : State := ⟨[1,12,96,240], 1766874024725051480223092167758005875740524534186667494779776408219619606, 2, 0, 1, 0⟩
theorem s4_543_edges : next config 4 s4_543 = [s5_293, s5_671] := by decide
theorem s4_543_safe : Safe 9 4 s4_543 := by
  apply safe_succ 8 4 s4_543 [s5_293, s5_671] (by decide) s4_543_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_293_safe
  · subst z; exact s5_671_safe
def s4_544 : State := ⟨[1,12,97,129], 1020847101000499877951363579153941074198, 2, 0, 1, 0⟩
theorem s4_544_edges : next config 4 s4_544 = [s5_294, s5_642] := by decide
theorem s4_544_safe : Safe 9 4 s4_544 := by
  apply safe_succ 8 4 s4_544 [s5_294, s5_642] (by decide) s4_544_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_294_safe
  · subst z; exact s5_642_safe
def s4_545 : State := ⟨[1,12,97,130], 1701411834842376804878112794017477497110, 2, 0, 1, 0⟩
theorem s4_545_edges : next config 4 s4_545 = [s5_295, s5_644] := by decide
theorem s4_545_safe : Safe 9 4 s4_545 := by
  apply safe_succ 8 4 s4_545 [s5_295, s5_644] (by decide) s4_545_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_295_safe
  · subst z; exact s5_644_safe
def s4_546 : State := ⟨[1,12,97,132], 5784800237893638366438608083198696034582, 2, 0, 1, 0⟩
theorem s4_546_edges : next config 4 s4_546 = [s5_296] := by decide
theorem s4_546_safe : Safe 9 4 s4_546 := by
  apply safe_succ 8 4 s4_546 [s5_296] (by decide) s4_546_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_296_safe
def s4_547 : State := ⟨[1,12,97,136], 87452568298918869597648513866823066784022, 2, 0, 1, 0⟩
theorem s4_547_edges : next config 4 s4_547 = [s5_297] := by decide
theorem s4_547_safe : Safe 9 4 s4_547 := by
  apply safe_succ 8 4 s4_547 [s5_297] (by decide) s4_547_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_297_safe
def s4_548 : State := ⟨[1,12,97,140], 1394136857275322569297007006404812998775062, 2, 0, 1, 0⟩
theorem s4_548_edges : next config 4 s4_548 = [s5_299] := by decide
theorem s4_548_safe : Safe 9 4 s4_548 := by
  apply safe_succ 8 4 s4_548 [s5_299] (by decide) s4_548_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_299_safe
def s4_549 : State := ⟨[1,12,97,144], 22301085480897781764486742887012651910631702, 2, 0, 1, 0⟩
theorem s4_549_edges : next config 4 s4_549 = [s5_300, s5_643] := by decide
theorem s4_549_safe : Safe 9 4 s4_549 := by
  apply safe_succ 8 4 s4_549 [s5_300, s5_643] (by decide) s4_549_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_300_safe
  · subst z; exact s5_643_safe
def s4_550 : State := ⟨[1,12,97,160], 1461501637671185285362307783740897383946337194262, 2, 0, 1, 0⟩
theorem s4_550_edges : next config 4 s4_550 = [s5_302, s5_645] := by decide
theorem s4_550_safe : Safe 9 4 s4_550 := by
  apply safe_succ 8 4 s4_550 [s5_302, s5_645] (by decide) s4_550_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_302_safe
  · subst z; exact s5_645_safe
def s4_551 : State := ⟨[1,12,97,192], 6277101735386680764176071790366289367126969808754439164182, 2, 0, 1, 0⟩
theorem s4_551_edges : next config 4 s4_551 = [s5_303] := by decide
theorem s4_551_safe : Safe 9 4 s4_551 := by
  apply safe_succ 8 4 s4_551 [s5_303] (by decide) s4_551_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_303_safe
def s4_552 : State := ⟨[1,12,97,224], 26959946667150639794667015087359913040795767373565186845394014900502, 2, 0, 1, 0⟩
theorem s4_552_edges : next config 4 s4_552 = [s5_304] := by decide
theorem s4_552_safe : Safe 9 4 s4_552 := by
  apply safe_succ 8 4 s4_552 [s5_304] (by decide) s4_552_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_304_safe
def s4_553 : State := ⟨[1,12,97,225], 53919893334301279589334030174379543714432911796105759326497625149718, 2, 0, 1, 0⟩
theorem s4_553_edges : next config 4 s4_553 = [s5_305] := by decide
theorem s4_553_safe : Safe 9 4 s4_553 := by
  apply safe_succ 8 4 s4_553 [s5_305] (by decide) s4_553_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_305_safe
def s4_554 : State := ⟨[1,12,104,129], 1020847121124453156574505327914104459542, 2, 0, 1, 0⟩
theorem s4_554_edges : next config 4 s4_554 = [s5_899, s5_1173, s5_331, s5_650, s5_652, s5_656] := by decide
theorem s4_554_safe : Safe 9 4 s4_554 := by
  apply safe_succ 8 4 s4_554 [s5_899, s5_1173, s5_331, s5_650, s5_652, s5_656] (by decide) s4_554_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_899_safe
  · subst z; exact s5_1173_safe
  · subst z; exact s5_331_safe
  · subst z; exact s5_650_safe
  · subst z; exact s5_652_safe
  · subst z; exact s5_656_safe
def s4_555 : State := ⟨[1,12,104,130], 1701411854966330083501254542777640882454, 2, 0, 1, 0⟩
theorem s4_555_edges : next config 4 s4_555 = [s5_1549, s5_900, s5_1174, s5_340, s5_651, s5_654, s5_658] := by decide
theorem s4_555_safe : Safe 9 4 s4_555 := by
  apply safe_succ 8 4 s4_555 [s5_1549, s5_900, s5_1174, s5_340, s5_651, s5_654, s5_658] (by decide) s4_555_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1549_safe
  · subst z; exact s5_900_safe
  · subst z; exact s5_1174_safe
  · subst z; exact s5_340_safe
  · subst z; exact s5_651_safe
  · subst z; exact s5_654_safe
  · subst z; exact s5_658_safe
def s4_556 : State := ⟨[1,12,104,132], 5784800258017591645061749831958859419926, 2, 0, 1, 0⟩
theorem s4_556_edges : next config 4 s4_556 = [s5_902, s5_1175, s5_351] := by decide
theorem s4_556_safe : Safe 9 4 s4_556 := by
  apply safe_succ 8 4 s4_556 [s5_902, s5_1175, s5_351] (by decide) s4_556_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_902_safe
  · subst z; exact s5_1175_safe
  · subst z; exact s5_351_safe
def s4_557 : State := ⟨[1,12,104,136], 87452568319042822876271655615583230169366, 2, 0, 1, 0⟩
theorem s4_557_edges : next config 4 s4_557 = [s5_903, s5_1176, s5_360] := by decide
theorem s4_557_safe : Safe 9 4 s4_557 := by
  apply safe_succ 8 4 s4_557 [s5_903, s5_1176, s5_360] (by decide) s4_557_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_903_safe
  · subst z; exact s5_1176_safe
  · subst z; exact s5_360_safe
def s4_558 : State := ⟨[1,12,104,140], 1394136857295446522575630148153573162160406, 2, 0, 1, 0⟩
theorem s4_558_edges : next config 4 s4_558 = [s5_904, s5_1177, s5_370] := by decide
theorem s4_558_safe : Safe 9 4 s4_558 := by
  apply safe_succ 8 4 s4_558 [s5_904, s5_1177, s5_370] (by decide) s4_558_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_904_safe
  · subst z; exact s5_1177_safe
  · subst z; exact s5_370_safe
def s4_559 : State := ⟨[1,12,104,144], 22301085480917905717765366028761412074017046, 2, 0, 1, 0⟩
theorem s4_559_edges : next config 4 s4_559 = [s5_905, s5_1178, s5_373, s5_653, s5_655, s5_660] := by decide
theorem s4_559_safe : Safe 9 4 s4_559 := by
  apply safe_succ 8 4 s4_559 [s5_905, s5_1178, s5_373, s5_653, s5_655, s5_660] (by decide) s4_559_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_905_safe
  · subst z; exact s5_1178_safe
  · subst z; exact s5_373_safe
  · subst z; exact s5_653_safe
  · subst z; exact s5_655_safe
  · subst z; exact s5_660_safe
def s4_560 : State := ⟨[1,12,104,160], 1461501637671185305486261062364039132706500579606, 2, 0, 1, 0⟩
theorem s4_560_edges : next config 4 s4_560 = [s5_1560, s5_906, s5_1179, s5_385, s5_657, s5_659, s5_661] := by decide
theorem s4_560_safe : Safe 9 4 s4_560 := by
  apply safe_succ 8 4 s4_560 [s5_1560, s5_906, s5_1179, s5_385, s5_657, s5_659, s5_661] (by decide) s4_560_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1560_safe
  · subst z; exact s5_906_safe
  · subst z; exact s5_1179_safe
  · subst z; exact s5_385_safe
  · subst z; exact s5_657_safe
  · subst z; exact s5_659_safe
  · subst z; exact s5_661_safe
def s4_561 : State := ⟨[1,12,104,192], 6277101735386680764176071810490242645750111557514602549526, 2, 0, 1, 0⟩
theorem s4_561_edges : next config 4 s4_561 = [s5_1597, s5_907, s5_1181, s5_408, s5_663, s5_665, s5_667] := by decide
theorem s4_561_safe : Safe 9 4 s4_561 := by
  apply safe_succ 8 4 s4_561 [s5_1597, s5_907, s5_1181, s5_408, s5_663, s5_665, s5_667] (by decide) s4_561_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1597_safe
  · subst z; exact s5_907_safe
  · subst z; exact s5_1181_safe
  · subst z; exact s5_408_safe
  · subst z; exact s5_663_safe
  · subst z; exact s5_665_safe
  · subst z; exact s5_667_safe
def s4_562 : State := ⟨[1,12,104,224], 26959946667150639794667015087359913060919720652188328594154178285846, 2, 0, 1, 0⟩
theorem s4_562_edges : next config 4 s4_562 = [s5_1601, s5_908, s5_1182, s5_429, s5_669, s5_671] := by decide
theorem s4_562_safe : Safe 9 4 s4_562 := by
  apply safe_succ 8 4 s4_562 [s5_1601, s5_908, s5_1182, s5_429, s5_669, s5_671] (by decide) s4_562_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1601_safe
  · subst z; exact s5_908_safe
  · subst z; exact s5_1182_safe
  · subst z; exact s5_429_safe
  · subst z; exact s5_669_safe
  · subst z; exact s5_671_safe
def s4_563 : State := ⟨[1,12,104,232], 6901746346790563787434755862277365734838391548400034311275574791835926, 2, 0, 1, 0⟩
theorem s4_563_edges : next config 4 s4_563 = [s5_909, s5_1183, s5_442] := by decide
theorem s4_563_safe : Safe 9 4 s4_563 := by
  apply safe_succ 8 4 s4_563 [s5_909, s5_1183, s5_442] (by decide) s4_563_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_909_safe
  · subst z; exact s5_1183_safe
  · subst z; exact s5_442_safe
def s4_564 : State := ⟨[1,12,112,129], 1020852293138902087750463434463182393622, 2, 0, 1, 0⟩
theorem s4_564_edges : next config 4 s4_564 = [s5_469, s5_672] := by decide
theorem s4_564_safe : Safe 9 4 s4_564 := by
  apply safe_succ 8 4 s4_564 [s5_469, s5_672] (by decide) s4_564_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_469_safe
  · subst z; exact s5_672_safe
def s4_565 : State := ⟨[1,12,112,130], 1701417026980779014677212649326718816534, 2, 0, 1, 0⟩
theorem s4_565_edges : next config 4 s4_565 = [s5_470] := by decide
theorem s4_565_safe : Safe 9 4 s4_565 := by
  apply safe_succ 8 4 s4_565 [s5_470] (by decide) s4_565_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_470_safe
def s4_566 : State := ⟨[1,12,112,132], 5784805430032040576237707938507937354006, 2, 0, 1, 0⟩
theorem s4_566_edges : next config 4 s4_566 = [s5_471] := by decide
theorem s4_566_safe : Safe 9 4 s4_566 := by
  apply safe_succ 8 4 s4_566 [s5_471] (by decide) s4_566_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_471_safe
def s4_567 : State := ⟨[1,12,112,136], 87452573491057271807447613722132308103446, 2, 0, 1, 0⟩
theorem s4_567_edges : next config 4 s4_567 = [s5_472] := by decide
theorem s4_567_safe : Safe 9 4 s4_567 := by
  apply safe_succ 8 4 s4_567 [s5_472] (by decide) s4_567_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_472_safe
def s4_568 : State := ⟨[1,12,112,140], 1394136862467460971506806106260122240094486, 2, 0, 1, 0⟩
theorem s4_568_edges : next config 4 s4_568 = [s5_474] := by decide
theorem s4_568_safe : Safe 9 4 s4_568 := by
  apply safe_succ 8 4 s4_568 [s5_474] (by decide) s4_568_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_474_safe
def s4_569 : State := ⟨[1,12,112,144], 22301085486089920166696541986867961151951126, 2, 0, 1, 0⟩
theorem s4_569_edges : next config 4 s4_569 = [s5_475, s5_673] := by decide
theorem s4_569_safe : Safe 9 4 s4_569 := by
  apply safe_succ 8 4 s4_569 [s5_475, s5_673] (by decide) s4_569_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_475_safe
  · subst z; exact s5_673_safe
def s4_570 : State := ⟨[1,12,112,160], 1461501637671190477500709993539997239255578513686, 2, 0, 1, 0⟩
theorem s4_570_edges : next config 4 s4_570 = [s5_477] := by decide
theorem s4_570_safe : Safe 9 4 s4_570 := by
  apply safe_succ 8 4 s4_570 [s5_477] (by decide) s4_570_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_477_safe
def s4_571 : State := ⟨[1,12,112,192], 6277101735386680764176076982504691576926069664063680483606, 2, 0, 1, 0⟩
theorem s4_571_edges : next config 4 s4_571 = [s5_478, s5_675] := by decide
theorem s4_571_safe : Safe 9 4 s4_571 := by
  apply safe_succ 8 4 s4_571 [s5_478, s5_675] (by decide) s4_571_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_478_safe
  · subst z; exact s5_675_safe
def s4_572 : State := ⟨[1,12,112,224], 26959946667150639794667015087359918232934169583364286700703256219926, 2, 0, 1, 0⟩
theorem s4_572_edges : next config 4 s4_572 = [s5_479] := by decide
theorem s4_572_safe : Safe 9 4 s4_572 := by
  apply safe_succ 8 4 s4_572 [s5_479] (by decide) s4_572_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_479_safe
def s4_573 : State := ⟨[1,12,112,240], 1766847064778384329583297500742918856115043193900779781835825800938590486, 2, 0, 1, 0⟩
theorem s4_573_edges : next config 4 s4_573 = [s5_480] := by decide
theorem s4_573_safe : Safe 9 4 s4_573 := by
  apply safe_succ 8 4 s4_573 [s5_480] (by decide) s4_573_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_480_safe
def s4_574 : State := ⟨[1,12,193,145], 12554203470773406130182823008424431294049826752024390209814, 2, 0, 1, 0⟩
theorem s4_574_edges : next config 4 s4_574 = [s5_488] := by decide
theorem s4_574_safe : Safe 9 4 s4_574 := by
  apply safe_succ 8 4 s4_574 [s5_488] (by decide) s4_574_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_488_safe
def s4_575 : State := ⟨[1,12,194,146], 25108406941546812260025363649927924124617832152539007619350, 2, 0, 1, 0⟩
theorem s4_575_edges : next config 4 s4_575 = [s5_490] := by decide
theorem s4_575_safe : Safe 9 4 s4_575 := by
  apply safe_succ 8 4 s4_575 [s5_490] (by decide) s4_575_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_490_safe
def s4_576 : State := ⟨[1,12,194,162], 25108406947392729606368181200250097312609873637716713869590, 2, 0, 1, 0⟩
theorem s4_576_edges : next config 4 s4_576 = [s5_491, s5_614, s5_678] := by decide
theorem s4_576_safe : Safe 9 4 s4_576 := by
  apply safe_succ 8 4 s4_576 [s5_491, s5_614, s5_678] (by decide) s4_576_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_491_safe
  · subst z; exact s5_614_safe
  · subst z; exact s5_678_safe
def s4_577 : State := ⟨[1,12,208,145], 411376139330301510605644871517296416608754603047691560127893782, 2, 0, 1, 0⟩
theorem s4_577_edges : next config 4 s4_577 = [s5_492, s5_683] := by decide
theorem s4_577_safe : Safe 9 4 s4_577 := by
  apply safe_succ 8 4 s4_577 [s5_492, s5_683] (by decide) s4_577_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_492_safe
  · subst z; exact s5_683_safe
def s4_578 : State := ⟨[1,12,209,145], 822752278660603021122087102522837261589829777932653027995488534, 2, 0, 1, 0⟩
theorem s4_578_edges : next config 4 s4_578 = [s5_493] := by decide
theorem s4_578_safe : Safe 9 4 s4_578 := by
  apply safe_succ 8 4 s4_578 [s5_493] (by decide) s4_578_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_493_safe
def s4_579 : State := ⟨[1,12,209,145], 822752278660603021144387167156634042854438569456086525965046038, 2, 0, 1, 0⟩
theorem s4_579_edges : next config 4 s4_579 = [s5_494] := by decide
theorem s4_579_safe : Safe 9 4 s4_579 := by
  apply safe_succ 8 4 s4_579 [s5_494] (by decide) s4_579_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_494_safe
def s4_580 : State := ⟨[1,12,210,130], 1645504557321206042154970883969185109676262126772975729368961302, 2, 0, 1, 0⟩
theorem s4_580_edges : next config 4 s4_580 = [s5_495] := by decide
theorem s4_580_safe : Safe 9 4 s4_580 := by
  apply safe_succ 8 4 s4_580 [s5_495] (by decide) s4_580_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_495_safe
def s4_581 : State := ⟨[1,12,210,130], 1645529665728147588878026227126877940340717610375138956332306710, 2, 0, 1, 0⟩
theorem s4_581_edges : next config 4 s4_581 = [s5_496] := by decide
theorem s4_581_safe : Safe 9 4 s4_581 := by
  apply safe_succ 8 4 s4_581 [s5_496] (by decide) s4_581_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_496_safe
def s4_582 : State := ⟨[1,12,210,144], 1645504557321206042177270268038248049062735139514556029465596182, 2, 0, 1, 0⟩
theorem s4_582_edges : next config 4 s4_582 = [s5_499, s5_682] := by decide
theorem s4_582_safe : Safe 9 4 s4_582 := by
  apply safe_succ 8 4 s4_582 [s5_499, s5_682] (by decide) s4_582_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_499_safe
  · subst z; exact s5_682_safe
def s4_583 : State := ⟨[1,12,210,144], 2056880696651507552716012563677585675308419032135974700464541974, 2, 0, 1, 0⟩
theorem s4_583_edges : next config 4 s4_583 = [s5_500, s5_683] := by decide
theorem s4_583_safe : Safe 9 4 s4_583 := by
  apply safe_succ 8 4 s4_583 [s5_500, s5_683] (by decide) s4_583_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_500_safe
  · subst z; exact s5_683_safe
def s4_584 : State := ⟨[1,12,210,146], 1645504557321206042244173864763307602241196074043954546218176790, 2, 0, 1, 0⟩
theorem s4_584_edges : next config 4 s4_584 = [s5_503] := by decide
theorem s4_584_safe : Safe 9 4 s4_584 := by
  apply safe_succ 8 4 s4_584 [s5_503] (by decide) s4_584_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_503_safe
def s4_585 : State := ⟨[1,12,210,146], 1645504557321206042266473248832370541628877938818173180651311382, 2, 0, 1, 0⟩
theorem s4_585_edges : next config 4 s4_585 = [s5_504] := by decide
theorem s4_585_safe : Safe 9 4 s4_585 := by
  apply safe_succ 8 4 s4_585 [s5_504] (by decide) s4_585_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_504_safe
def s4_586 : State := ⟨[1,12,225,129], 53919893334301279589334030175060108448116332398003979866174073671958, 2, 0, 1, 0⟩
theorem s4_586_edges : next config 4 s4_586 = [s5_511, s5_684] := by decide
theorem s4_586_safe : Safe 9 4 s4_586 := by
  apply safe_succ 8 4 s4_586 [s5_511, s5_684] (by decide) s4_586_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_511_safe
  · subst z; exact s5_684_safe
def s4_587 : State := ⟨[1,12,240,144], 1766847064778384329583297500765219601308381520183780672479943666115350806, 2, 0, 1, 0⟩
theorem s4_587_edges : next config 4 s4_587 = [s5_514, s5_685] := by decide
theorem s4_587_safe : Safe 9 4 s4_587 := by
  apply safe_succ 8 4 s4_587 [s5_514, s5_685] (by decide) s4_587_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_514_safe
  · subst z; exact s5_685_safe
def s4_588 : State := ⟨[1,21,64,145], 44601830679428167221534918366648232786985238, 3, 1, 1, 0⟩
theorem s4_588_edges : next config 4 s4_588 = [s5_1451, s5_910, s5_945, s5_1184, s5_695, s5_696, s5_688, s5_694, s5_689, s5_691, s5_693] := by decide
theorem s4_588_safe : Safe 9 4 s4_588 := by
  apply safe_succ 8 4 s4_588 [s5_1451, s5_910, s5_945, s5_1184, s5_695, s5_696, s5_688, s5_694, s5_689, s5_691, s5_693] (by decide) s4_588_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1451_safe
  · subst z; exact s5_910_safe
  · subst z; exact s5_945_safe
  · subst z; exact s5_1184_safe
  · subst z; exact s5_695_safe
  · subst z; exact s5_696_safe
  · subst z; exact s5_688_safe
  · subst z; exact s5_694_safe
  · subst z; exact s5_689_safe
  · subst z; exact s5_691_safe
  · subst z; exact s5_693_safe
def s4_589 : State := ⟨[1,68,64,145], 44601830679428167221535213514553412137713942, 3, 1, 1, 0⟩
theorem s4_589_edges : next config 4 s4_589 = [s5_25, s5_697] := by decide
theorem s4_589_safe : Safe 9 4 s4_589 := by
  apply safe_succ 8 4 s4_589 [s5_25, s5_697] (by decide) s4_589_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_25_safe
  · subst z; exact s5_697_safe
def s4_590 : State := ⟨[1,68,64,214], 26328072917139296674568711603123565176982234353695557675800133910, 2, 0, 1, 0⟩
theorem s4_590_edges : next config 4 s4_590 = [s5_64, s5_698] := by decide
theorem s4_590_safe : Safe 9 4 s4_590 := by
  apply safe_succ 8 4 s4_590 [s5_64, s5_698] (by decide) s4_590_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_64_safe
  · subst z; exact s5_698_safe
def s4_591 : State := ⟨[1,68,64,214], 26328072917139296674591010987192628116369916218469776310233268502, 2, 0, 1, 0⟩
theorem s4_591_edges : next config 4 s4_591 = [s5_65, s5_699] := by decide
theorem s4_591_safe : Safe 9 4 s4_591 := by
  apply safe_succ 8 4 s4_591 [s5_65, s5_699] (by decide) s4_591_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_65_safe
  · subst z; exact s5_699_safe
def s4_592 : State := ⟨[1,68,96,145], 44602511244162088326624654528105869217956118, 2, 0, 1, 0⟩
theorem s4_592_edges : next config 4 s4_592 = [s5_700] := by decide
theorem s4_592_safe : Safe 9 4 s4_592 := by
  apply safe_succ 8 4 s4_592 [s5_700] (by decide) s4_592_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_700_safe
def s4_593 : State := ⟨[1,68,96,145], 66902575877958869591233446051539367187513622, 2, 0, 1, 0⟩
theorem s4_593_edges : next config 4 s4_593 = [s5_701] := by decide
theorem s4_593_safe : Safe 9 4 s4_593 := by
  apply safe_succ 8 4 s4_593 [s5_701] (by decide) s4_593_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_701_safe
def s4_594 : State := ⟨[1,68,96,146], 89204682205957176486623017822617455766339862, 2, 0, 1, 0⟩
theorem s4_594_edges : next config 4 s4_594 = [s5_774, s5_702, s5_698] := by decide
theorem s4_594_safe : Safe 9 4 s4_594 := by
  apply safe_succ 8 4 s4_594 [s5_774, s5_702, s5_698] (by decide) s4_594_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_774_safe
  · subst z; exact s5_702_safe
  · subst z; exact s5_698_safe
def s4_595 : State := ⟨[1,68,96,146], 111504066275020115874304882596836090199474454, 2, 0, 1, 0⟩
theorem s4_595_edges : next config 4 s4_595 = [s5_775, s5_703, s5_699] := by decide
theorem s4_595_safe : Safe 9 4 s4_595 := by
  apply safe_succ 8 4 s4_595 [s5_775, s5_703, s5_699] (by decide) s4_595_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_775_safe
  · subst z; exact s5_703_safe
  · subst z; exact s5_699_safe
def s4_596 : State := ⟨[1,68,104,129], 1020847121124453156869653233093457281302, 2, 0, 1, 0⟩
theorem s4_596_edges : next config 4 s4_596 = [s5_700] := by decide
theorem s4_596_safe : Safe 9 4 s4_596 := by
  apply safe_succ 8 4 s4_596 [s5_700] (by decide) s4_596_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_700_safe
def s4_597 : State := ⟨[1,68,104,130], 1701411854966330083796402447956993704214, 2, 0, 1, 0⟩
theorem s4_597_edges : next config 4 s4_597 = [s5_702] := by decide
theorem s4_597_safe : Safe 9 4 s4_597 := by
  apply safe_succ 8 4 s4_597 [s5_702] (by decide) s4_597_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_702_safe
def s4_598 : State := ⟨[1,68,104,132], 5784800258017591645356897737138212241686, 2, 0, 1, 0⟩
theorem s4_598_edges : next config 4 s4_598 = [] := by decide
theorem s4_598_safe : Safe 9 4 s4_598 := by
  apply safe_succ 8 4 s4_598 [] (by decide) s4_598_edges
  simp
def s4_599 : State := ⟨[1,68,104,136], 87452568319042822876566803520762582991126, 2, 0, 1, 0⟩
theorem s4_599_edges : next config 4 s4_599 = [] := by decide
theorem s4_599_safe : Safe 9 4 s4_599 := by
  apply safe_succ 8 4 s4_599 [] (by decide) s4_599_edges
  simp
def s4_600 : State := ⟨[1,68,104,144], 22301085480917905717765661176666591426838806, 2, 0, 1, 0⟩
theorem s4_600_edges : next config 4 s4_600 = [s5_701, s5_703] := by decide
theorem s4_600_safe : Safe 9 4 s4_600 := by
  apply safe_succ 8 4 s4_600 [s5_701, s5_703] (by decide) s4_600_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_701_safe
  · subst z; exact s5_703_safe
def s4_601 : State := ⟨[1,68,104,160], 1461501637671185305486261062659187037885853401366, 2, 0, 1, 0⟩
theorem s4_601_edges : next config 4 s4_601 = [] := by decide
theorem s4_601_safe : Safe 9 4 s4_601 := by
  apply safe_succ 8 4 s4_601 [] (by decide) s4_601_edges
  simp
def s4_602 : State := ⟨[1,68,104,192], 6277101735386680764176071810490242646045259462693955371286, 2, 0, 1, 0⟩
theorem s4_602_edges : next config 4 s4_602 = [] := by decide
theorem s4_602_safe : Safe 9 4 s4_602 := by
  apply safe_succ 8 4 s4_602 [] (by decide) s4_602_edges
  simp
def s4_603 : State := ⟨[1,68,104,196], 100433627766186892221712913158605238887580591129654473064726, 2, 0, 1, 0⟩
theorem s4_603_edges : next config 4 s4_603 = [] := by decide
theorem s4_603_safe : Safe 9 4 s4_603 := by
  apply safe_succ 8 4 s4_603 [] (by decide) s4_603_edges
  simp
def s4_604 : State := ⟨[1,68,104,224], 26959946667150639794667015087359913060919720652483476499333531107606, 2, 0, 1, 0⟩
theorem s4_604_edges : next config 4 s4_604 = [] := by decide
theorem s4_604_safe : Safe 9 4 s4_604 := by
  apply safe_succ 8 4 s4_604 [] (by decide) s4_604_edges
  simp
def s4_605 : State := ⟨[1,68,104,232], 6901746346790563787434755862277365734838391548400329459180754144657686, 2, 0, 1, 0⟩
theorem s4_605_edges : next config 4 s4_605 = [] := by decide
theorem s4_605_safe : Safe 9 4 s4_605 := by
  apply safe_succ 8 4 s4_605 [] (by decide) s4_605_edges
  simp
def s4_606 : State := ⟨[1,86,82,129], 1020847100762897597438091337452027445526, 2, 0, 1, 0⟩
theorem s4_606_edges : next config 4 s4_606 = [s5_136, s5_704] := by decide
theorem s4_606_safe : Safe 9 4 s4_606 := by
  apply safe_succ 8 4 s4_606 [s5_136, s5_704] (by decide) s4_606_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_136_safe
  · subst z; exact s5_704_safe
def s4_607 : State := ⟨[1,86,82,129], 1020847100762898806290123975786363945238, 2, 0, 1, 0⟩
theorem s4_607_edges : next config 4 s4_607 = [s5_137, s5_705] := by decide
theorem s4_607_safe : Safe 9 4 s4_607 := by
  apply safe_succ 8 4 s4_607 [s5_137, s5_705] (by decide) s4_607_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_137_safe
  · subst z; exact s5_705_safe
def s4_608 : State := ⟨[1,86,82,130], 1701411834604774524364840552315563868438, 2, 0, 1, 0⟩
theorem s4_608_edges : next config 4 s4_608 = [s5_140] := by decide
theorem s4_608_safe : Safe 9 4 s4_608 := by
  apply safe_succ 8 4 s4_608 [s5_140] (by decide) s4_608_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_140_safe
def s4_609 : State := ⟨[1,86,82,130], 1701411834604775733216873190649900368150, 2, 0, 1, 0⟩
theorem s4_609_edges : next config 4 s4_609 = [s5_141] := by decide
theorem s4_609_safe : Safe 9 4 s4_609 := by
  apply safe_succ 8 4 s4_609 [s5_141] (by decide) s4_609_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_141_safe
def s4_610 : State := ⟨[1,86,82,132], 5784800237656036085925335841496782405910, 2, 0, 1, 0⟩
theorem s4_610_edges : next config 4 s4_610 = [s5_144] := by decide
theorem s4_610_safe : Safe 9 4 s4_610 := by
  apply safe_succ 8 4 s4_610 [s5_144] (by decide) s4_610_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_144_safe
def s4_611 : State := ⟨[1,86,82,132], 5784800237656037294777368479831118905622, 2, 0, 1, 0⟩
theorem s4_611_edges : next config 4 s4_611 = [s5_145] := by decide
theorem s4_611_safe : Safe 9 4 s4_611 := by
  apply safe_succ 8 4 s4_611 [s5_145] (by decide) s4_611_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_145_safe
def s4_612 : State := ⟨[1,86,82,136], 87452568298681267317135241625121153155350, 2, 0, 1, 0⟩
theorem s4_612_edges : next config 4 s4_612 = [s5_148] := by decide
theorem s4_612_safe : Safe 9 4 s4_612 := by
  apply safe_succ 8 4 s4_612 [s5_148] (by decide) s4_612_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_148_safe
def s4_613 : State := ⟨[1,86,82,136], 87452568298681268525987274263455489655062, 2, 0, 1, 0⟩
theorem s4_613_edges : next config 4 s4_613 = [s5_149] := by decide
theorem s4_613_safe : Safe 9 4 s4_613 := by
  apply safe_succ 8 4 s4_613 [s5_149] (by decide) s4_613_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_149_safe
def s4_614 : State := ⟨[1,86,82,144], 22301085480897544162206229614770949997003030, 2, 0, 1, 0⟩
theorem s4_614_edges : next config 4 s4_614 = [s5_156, s5_706] := by decide
theorem s4_614_safe : Safe 9 4 s4_614 := by
  apply safe_succ 8 4 s4_614 [s5_156, s5_706] (by decide) s4_614_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_156_safe
  · subst z; exact s5_706_safe
def s4_615 : State := ⟨[1,86,82,144], 22301085480897544163415081647409284333502742, 2, 0, 1, 0⟩
theorem s4_615_edges : next config 4 s4_615 = [s5_157, s5_707] := by decide
theorem s4_615_safe : Safe 9 4 s4_615 := by
  apply safe_succ 8 4 s4_615 [s5_157, s5_707] (by decide) s4_615_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_157_safe
  · subst z; exact s5_707_safe
def s4_616 : State := ⟨[1,86,82,160], 1461501637671185285124705503227625142244423565590, 2, 0, 1, 0⟩
theorem s4_616_edges : next config 4 s4_616 = [s5_162] := by decide
theorem s4_616_safe : Safe 9 4 s4_616 := by
  apply safe_succ 8 4 s4_616 [s5_162] (by decide) s4_616_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_162_safe
def s4_617 : State := ⟨[1,86,82,160], 1461501637671185285124706712079657780578760065302, 2, 0, 1, 0⟩
theorem s4_617_edges : next config 4 s4_617 = [s5_163] := by decide
theorem s4_617_safe : Safe 9 4 s4_617 := by
  apply safe_succ 8 4 s4_617 [s5_163] (by decide) s4_617_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_163_safe
def s4_618 : State := ⟨[1,86,82,192], 6277101735386680764176071790128687086613697567052525535510, 2, 0, 1, 0⟩
theorem s4_618_edges : next config 4 s4_618 = [s5_166] := by decide
theorem s4_618_safe : Safe 9 4 s4_618 := by
  apply safe_succ 8 4 s4_618 [s5_166] (by decide) s4_618_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_166_safe
def s4_619 : State := ⟨[1,86,82,192], 6277101735386680764176071790128688295465730205386862035222, 2, 0, 1, 0⟩
theorem s4_619_edges : next config 4 s4_619 = [s5_167] := by decide
theorem s4_619_safe : Safe 9 4 s4_619 := by
  apply safe_succ 8 4 s4_619 [s5_167] (by decide) s4_619_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_167_safe
def s4_620 : State := ⟨[1,86,82,194], 25108406941546723055683440059751686334920763900444629074198, 2, 0, 1, 0⟩
theorem s4_620_edges : next config 4 s4_620 = [s5_169] := by decide
theorem s4_620_safe : Safe 9 4 s4_620 := by
  apply safe_succ 8 4 s4_620 [s5_169] (by decide) s4_620_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_169_safe
def s4_621 : State := ⟨[1,86,82,208], 411376139330301510538742635921704547267563329783155888664674582, 2, 0, 1, 0⟩
theorem s4_621_edges : next config 4 s4_621 = [s5_171] := by decide
theorem s4_621_safe : Safe 9 4 s4_621 := by
  apply safe_succ 8 4 s4_621 [s5_171] (by decide) s4_621_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_171_safe
def s4_622 : State := ⟨[1,86,82,210], 1645504557321206042154969522839717426003406376975702451839631638, 2, 0, 1, 0⟩
theorem s4_622_edges : next config 4 s4_622 = [s5_174] := by decide
theorem s4_622_safe : Safe 9 4 s4_622 := by
  apply safe_succ 8 4 s4_622 [s5_174] (by decide) s4_622_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_174_safe
def s4_623 : State := ⟨[1,86,82,210], 1645504557321206042154969522839717426004615229008340786176131350, 2, 0, 1, 0⟩
theorem s4_623_edges : next config 4 s4_623 = [s5_175] := by decide
theorem s4_623_safe : Safe 9 4 s4_623 := by
  apply safe_succ 8 4 s4_623 [s5_175] (by decide) s4_623_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_175_safe
def s4_624 : State := ⟨[1,86,82,214], 26328072917139296674479507261199975000744444361479400402068766998, 2, 0, 1, 0⟩
theorem s4_624_edges : next config 4 s4_624 = [s5_178] := by decide
theorem s4_624_safe : Safe 9 4 s4_624 := by
  apply safe_succ 8 4 s4_624 [s5_178] (by decide) s4_624_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_178_safe
def s4_625 : State := ⟨[1,86,82,214], 26328072917139296674479507261199975000745653213512038736405266710, 2, 0, 1, 0⟩
theorem s4_625_edges : next config 4 s4_625 = [s5_179] := by decide
theorem s4_625_safe : Safe 9 4 s4_625 := by
  apply safe_succ 8 4 s4_625 [s5_179] (by decide) s4_625_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_179_safe
def s4_626 : State := ⟨[1,100,96,128], 340282368267817226224315090600019951902, 3, 1, 0, 0⟩
theorem s4_626_edges : next config 4 s4_626 = [s5_1098, s5_188, s5_731, s5_708, s5_729, s5_727, s5_710, s5_716, s5_718, s5_721] := by decide
theorem s4_626_safe : Safe 9 4 s4_626 := by
  apply safe_succ 8 4 s4_626 [s5_1098, s5_188, s5_731, s5_708, s5_729, s5_727, s5_710, s5_716, s5_718, s5_721] (by decide) s4_626_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1098_safe
  · subst z; exact s5_188_safe
  · subst z; exact s5_731_safe
  · subst z; exact s5_708_safe
  · subst z; exact s5_729_safe
  · subst z; exact s5_727_safe
  · subst z; exact s5_710_safe
  · subst z; exact s5_716_safe
  · subst z; exact s5_718_safe
  · subst z; exact s5_721_safe
def s4_627 : State := ⟨[1,100,96,128], 340282368267817226261208578747439055126, 3, 1, 0, 0⟩
theorem s4_627_edges : next config 4 s4_627 = [s5_1100, s5_189, s5_732, s5_709, s5_730, s5_728, s5_711, s5_717, s5_719, s5_722] := by decide
theorem s4_627_safe : Safe 9 4 s4_627 := by
  apply safe_succ 8 4 s4_627 [s5_1100, s5_189, s5_732, s5_709, s5_730, s5_728, s5_711, s5_717, s5_719, s5_722] (by decide) s4_627_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1100_safe
  · subst z; exact s5_189_safe
  · subst z; exact s5_732_safe
  · subst z; exact s5_709_safe
  · subst z; exact s5_730_safe
  · subst z; exact s5_728_safe
  · subst z; exact s5_711_safe
  · subst z; exact s5_717_safe
  · subst z; exact s5_719_safe
  · subst z; exact s5_722_safe
def s4_628 : State := ⟨[1,100,96,131], 3743106037477201860858061164917702066454, 2, 0, 1, 0⟩
theorem s4_628_edges : next config 4 s4_628 = [s5_191, s5_733] := by decide
theorem s4_628_safe : Safe 9 4 s4_628 := by
  apply safe_succ 8 4 s4_628 [s5_191, s5_733] (by decide) s4_628_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_191_safe
  · subst z; exact s5_733_safe
def s4_629 : State := ⟨[1,100,96,131], 4423670771319078787784810379781238489366, 2, 0, 1, 0⟩
theorem s4_629_edges : next config 4 s4_629 = [s5_193, s5_734] := by decide
theorem s4_629_safe : Safe 9 4 s4_629 := by
  apply safe_succ 8 4 s4_629 [s5_193, s5_734] (by decide) s4_629_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_193_safe
  · subst z; exact s5_734_safe
def s4_630 : State := ⟨[1,100,96,145], 44602511244163355977224587609602186568335638, 2, 0, 1, 0⟩
theorem s4_630_edges : next config 4 s4_630 = [s5_911, s5_209, s5_735] := by decide
theorem s4_630_safe : Safe 9 4 s4_630 := by
  apply safe_succ 8 4 s4_630 [s5_911, s5_209, s5_735] (by decide) s4_630_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_911_safe
  · subst z; exact s5_209_safe
  · subst z; exact s5_735_safe
def s4_631 : State := ⟨[1,100,96,145], 66902575877960137241833379133035684537893142, 2, 0, 1, 0⟩
theorem s4_631_edges : next config 4 s4_631 = [s5_912, s5_217, s5_736] := by decide
theorem s4_631_safe : Safe 9 4 s4_631 := by
  apply safe_succ 8 4 s4_631 [s5_912, s5_217, s5_736] (by decide) s4_631_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_912_safe
  · subst z; exact s5_217_safe
  · subst z; exact s5_736_safe
def s4_632 : State := ⟨[1,100,96,146], 89204682205958444137222950904113773116719382, 2, 0, 1, 0⟩
theorem s4_632_edges : next config 4 s4_632 = [s5_222, s5_737] := by decide
theorem s4_632_safe : Safe 9 4 s4_632 := by
  apply safe_succ 8 4 s4_632 [s5_222, s5_737] (by decide) s4_632_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_222_safe
  · subst z; exact s5_737_safe
def s4_633 : State := ⟨[1,100,96,146], 111504066275021383524904815678332407549853974, 2, 0, 1, 0⟩
theorem s4_633_edges : next config 4 s4_633 = [s5_228, s5_738] := by decide
theorem s4_633_safe : Safe 9 4 s4_633 := by
  apply safe_succ 8 4 s4_633 [s5_228, s5_738] (by decide) s4_633_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_228_safe
  · subst z; exact s5_738_safe
def s4_634 : State := ⟨[1,100,96,162], 5846006551025023508766310410942945598950822969622, 2, 0, 1, 0⟩
theorem s4_634_edges : next config 4 s4_634 = [s5_238, s5_739] := by decide
theorem s4_634_safe : Safe 9 4 s4_634 := by
  apply safe_succ 8 4 s4_634 [s5_238, s5_739] (by decide) s4_634_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_238_safe
  · subst z; exact s5_739_safe
def s4_635 : State := ⟨[1,100,96,162], 7307508186994796959286241389805730188879682666774, 2, 0, 1, 0⟩
theorem s4_635_edges : next config 4 s4_635 = [s5_245, s5_740] := by decide
theorem s4_635_safe : Safe 9 4 s4_635 := by
  apply safe_succ 8 4 s4_635 [s5_245, s5_740] (by decide) s4_635_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_245_safe
  · subst z; exact s5_740_safe
def s4_636 : State := ⟨[1,100,96,176], 95780971326419139128295580155656266563910156662407446, 2, 0, 1, 0⟩
theorem s4_636_edges : next config 4 s4_636 = [s5_263, s5_741] := by decide
theorem s4_636_safe : Safe 9 4 s4_636 := by
  apply safe_succ 8 4 s4_636 [s5_263, s5_741] (by decide) s4_636_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_263_safe
  · subst z; exact s5_741_safe
def s4_637 : State := ⟨[1,100,96,176], 95782432805755724832683160698953264574281451088970006, 2, 0, 1, 0⟩
theorem s4_637_edges : next config 4 s4_637 = [s5_267, s5_742] := by decide
theorem s4_637_safe : Safe 9 4 s4_637 := by
  apply safe_succ 8 4 s4_637 [s5_267, s5_742] (by decide) s4_637_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_267_safe
  · subst z; exact s5_742_safe
def s4_638 : State := ⟨[1,100,96,193], 12554203470773361528692425948525026985355775194391625400598, 2, 0, 1, 0⟩
theorem s4_638_edges : next config 4 s4_638 = [s5_269, s5_743] := by decide
theorem s4_638_safe : Safe 9 4 s4_638 := by
  apply safe_succ 8 4 s4_638 [s5_269, s5_743] (by decide) s4_638_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_269_safe
  · subst z; exact s5_743_safe
def s4_639 : State := ⟨[1,100,96,193], 18831305206160042291847650637890816474531381423992123490582, 2, 0, 1, 0⟩
theorem s4_639_edges : next config 4 s4_639 = [s5_271, s5_744] := by decide
theorem s4_639_safe : Safe 9 4 s4_639 := by
  apply safe_succ 8 4 s4_639 [s5_271, s5_744] (by decide) s4_639_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_271_safe
  · subst z; exact s5_744_safe
def s4_640 : State := ⟨[1,100,96,194], 25108406941546723057044569528782236744487235298183230849302, 2, 0, 1, 0⟩
theorem s4_640_edges : next config 4 s4_640 = [s5_273, s5_745] := by decide
theorem s4_640_safe : Safe 9 4 s4_640 := by
  apply safe_succ 8 4 s4_640 [s5_273, s5_745] (by decide) s4_640_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_273_safe
  · subst z; exact s5_745_safe
def s4_641 : State := ⟨[1,100,96,194], 31385508676933403819519229484306149306736092312920192516374, 2, 0, 1, 0⟩
theorem s4_641_edges : next config 4 s4_641 = [s5_275, s5_746] := by decide
theorem s4_641_safe : Safe 9 4 s4_641 := by
  apply safe_succ 8 4 s4_641 [s5_275, s5_746] (by decide) s4_641_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_275_safe
  · subst z; exact s5_746_safe
def s4_642 : State := ⟨[1,100,104,129], 1020847122392103756802734729410807660822, 2, 0, 1, 0⟩
theorem s4_642_edges : next config 4 s4_642 = [s5_913, s5_733, s5_735] := by decide
theorem s4_642_safe : Safe 9 4 s4_642 := by
  apply safe_succ 8 4 s4_642 [s5_913, s5_733, s5_735] (by decide) s4_642_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_913_safe
  · subst z; exact s5_733_safe
  · subst z; exact s5_735_safe
def s4_643 : State := ⟨[1,100,104,130], 1701411856233980683729483944274344083734, 2, 0, 1, 0⟩
theorem s4_643_edges : next config 4 s4_643 = [s5_1550, s5_914, s5_734, s5_737, s5_739] := by decide
theorem s4_643_safe : Safe 9 4 s4_643 := by
  apply safe_succ 8 4 s4_643 [s5_1550, s5_914, s5_734, s5_737, s5_739] (by decide) s4_643_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1550_safe
  · subst z; exact s5_914_safe
  · subst z; exact s5_734_safe
  · subst z; exact s5_737_safe
  · subst z; exact s5_739_safe
def s4_644 : State := ⟨[1,100,104,132], 5784800259285242245289979233455562621206, 2, 0, 1, 0⟩
theorem s4_644_edges : next config 4 s4_644 = [s5_916] := by decide
theorem s4_644_safe : Safe 9 4 s4_644 := by
  apply safe_succ 8 4 s4_644 [s5_916] (by decide) s4_644_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_916_safe
def s4_645 : State := ⟨[1,100,104,136], 87452568320310473476499885017079933370646, 2, 0, 1, 0⟩
theorem s4_645_edges : next config 4 s4_645 = [s5_917] := by decide
theorem s4_645_safe : Safe 9 4 s4_645 := by
  apply safe_succ 8 4 s4_645 [s5_917] (by decide) s4_645_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_917_safe
def s4_646 : State := ⟨[1,100,104,144], 22301085480919173368365594258162908777218326, 2, 0, 1, 0⟩
theorem s4_646_edges : next config 4 s4_646 = [s5_918, s5_736, s5_738, s5_741] := by decide
theorem s4_646_safe : Safe 9 4 s4_646 := by
  apply safe_succ 8 4 s4_646 [s5_918, s5_736, s5_738, s5_741] (by decide) s4_646_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_918_safe
  · subst z; exact s5_736_safe
  · subst z; exact s5_738_safe
  · subst z; exact s5_741_safe
def s4_647 : State := ⟨[1,100,104,160], 1461501637671185306753911662592268534203203780886, 2, 0, 1, 0⟩
theorem s4_647_edges : next config 4 s4_647 = [s5_919, s5_740, s5_742] := by decide
theorem s4_647_safe : Safe 9 4 s4_647 := by
  apply safe_succ 8 4 s4_647 [s5_919, s5_740, s5_742] (by decide) s4_647_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_919_safe
  · subst z; exact s5_740_safe
  · subst z; exact s5_742_safe
def s4_648 : State := ⟨[1,100,104,192], 6277101735386680764176071811757893245978340959011305750806, 2, 0, 1, 0⟩
theorem s4_648_edges : next config 4 s4_648 = [s5_1598, s5_920, s5_744, s5_746] := by decide
theorem s4_648_safe : Safe 9 4 s4_648 := by
  apply safe_succ 8 4 s4_648 [s5_1598, s5_920, s5_744, s5_746] (by decide) s4_648_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1598_safe
  · subst z; exact s5_920_safe
  · subst z; exact s5_744_safe
  · subst z; exact s5_746_safe
def s4_649 : State := ⟨[1,100,104,224], 26959946667150639794667015087359913062187371252416557995650881487126, 2, 0, 1, 0⟩
theorem s4_649_edges : next config 4 s4_649 = [s5_921] := by decide
theorem s4_649_safe : Safe 9 4 s4_649 := by
  apply safe_succ 8 4 s4_649 [s5_921] (by decide) s4_649_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_921_safe
def s4_650 : State := ⟨[1,100,104,228], 431359146674410236714672241392654373166744537590525145212205035225366, 2, 0, 1, 0⟩
theorem s4_650_edges : next config 4 s4_650 = [s5_922] := by decide
theorem s4_650_safe : Safe 9 4 s4_650 := by
  apply safe_succ 8 4 s4_650 [s5_922] (by decide) s4_650_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_922_safe
def s4_651 : State := ⟨[1,100,104,232], 6901746346790563787434755862277365734839659199000262540677071495037206, 2, 0, 1, 0⟩
theorem s4_651_edges : next config 4 s4_651 = [s5_923] := by decide
theorem s4_651_safe : Safe 9 4 s4_651 := by
  apply safe_succ 8 4 s4_651 [s5_923] (by decide) s4_651_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_923_safe
def s4_652 : State := ⟨[1,108,104,129], 1020847445643006815001232111070125031702, 2, 0, 1, 0⟩
theorem s4_652_edges : next config 4 s4_652 = [s5_924, s5_337, s5_749, s5_751] := by decide
theorem s4_652_safe : Safe 9 4 s4_652 := by
  apply safe_succ 8 4 s4_652 [s5_924, s5_337, s5_749, s5_751] (by decide) s4_652_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_924_safe
  · subst z; exact s5_337_safe
  · subst z; exact s5_749_safe
  · subst z; exact s5_751_safe
def s4_653 : State := ⟨[1,108,104,130], 1701412179484883741927981325933661454614, 2, 0, 1, 0⟩
theorem s4_653_edges : next config 4 s4_653 = [s5_1551, s5_925, s5_346, s5_750, s5_753, s5_755] := by decide
theorem s4_653_safe : Safe 9 4 s4_653 := by
  apply safe_succ 8 4 s4_653 [s5_1551, s5_925, s5_346, s5_750, s5_753, s5_755] (by decide) s4_653_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1551_safe
  · subst z; exact s5_925_safe
  · subst z; exact s5_346_safe
  · subst z; exact s5_750_safe
  · subst z; exact s5_753_safe
  · subst z; exact s5_755_safe
def s4_654 : State := ⟨[1,108,104,132], 5784800582536145303488476615114879992086, 2, 0, 1, 0⟩
theorem s4_654_edges : next config 4 s4_654 = [s5_927, s5_357] := by decide
theorem s4_654_safe : Safe 9 4 s4_654 := by
  apply safe_succ 8 4 s4_654 [s5_927, s5_357] (by decide) s4_654_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_927_safe
  · subst z; exact s5_357_safe
def s4_655 : State := ⟨[1,108,104,136], 87452568643561376534698382398739250741526, 2, 0, 1, 0⟩
theorem s4_655_edges : next config 4 s4_655 = [s5_928, s5_366] := by decide
theorem s4_655_safe : Safe 9 4 s4_655 := by
  apply safe_succ 8 4 s4_655 [s5_928, s5_366] (by decide) s4_655_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_928_safe
  · subst z; exact s5_366_safe
def s4_656 : State := ⟨[1,108,104,144], 22301085481242424271423792755544568094589206, 2, 0, 1, 0⟩
theorem s4_656_edges : next config 4 s4_656 = [s5_929, s5_379, s5_752, s5_754, s5_757] := by decide
theorem s4_656_safe : Safe 9 4 s4_656 := by
  apply safe_succ 8 4 s4_656 [s5_929, s5_379, s5_752, s5_754, s5_757] (by decide) s4_656_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_929_safe
  · subst z; exact s5_379_safe
  · subst z; exact s5_752_safe
  · subst z; exact s5_754_safe
  · subst z; exact s5_757_safe
def s4_657 : State := ⟨[1,108,104,160], 1461501637671185630004814720790765915862521151766, 2, 0, 1, 0⟩
theorem s4_657_edges : next config 4 s4_657 = [s5_930, s5_391, s5_756, s5_758] := by decide
theorem s4_657_safe : Safe 9 4 s4_657 := by
  apply safe_succ 8 4 s4_657 [s5_930, s5_391, s5_756, s5_758] (by decide) s4_657_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_930_safe
  · subst z; exact s5_391_safe
  · subst z; exact s5_756_safe
  · subst z; exact s5_758_safe
def s4_658 : State := ⟨[1,108,104,192], 6277101735386680764176072135008796304176838340670623121686, 2, 0, 1, 0⟩
theorem s4_658_edges : next config 4 s4_658 = [s5_1599, s5_931, s5_414, s5_760, s5_762, s5_764] := by decide
theorem s4_658_safe : Safe 9 4 s4_658 := by
  apply safe_succ 8 4 s4_658 [s5_1599, s5_931, s5_414, s5_760, s5_762, s5_764] (by decide) s4_658_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1599_safe
  · subst z; exact s5_931_safe
  · subst z; exact s5_414_safe
  · subst z; exact s5_760_safe
  · subst z; exact s5_762_safe
  · subst z; exact s5_764_safe
def s4_659 : State := ⟨[1,108,104,224], 26959946667150639794667015087359913385438274310615055377310198858006, 2, 0, 1, 0⟩
theorem s4_659_edges : next config 4 s4_659 = [s5_932, s5_435] := by decide
theorem s4_659_safe : Safe 9 4 s4_659 := by
  apply safe_succ 8 4 s4_659 [s5_932, s5_435] (by decide) s4_659_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_932_safe
  · subst z; exact s5_435_safe
def s4_660 : State := ⟨[1,108,104,232], 6901746346790563787434755862277365735162910102058461038058730812408086, 2, 0, 1, 0⟩
theorem s4_660_edges : next config 4 s4_660 = [s5_933, s5_448] := by decide
theorem s4_660_safe : Safe 9 4 s4_660 := by
  apply safe_succ 8 4 s4_660 [s5_933, s5_448] (by decide) s4_660_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_933_safe
  · subst z; exact s5_448_safe
def s4_661 : State := ⟨[1,108,104,236], 110427941548649020598956093796432747521929544684614259365496594169397526, 2, 0, 1, 0⟩
theorem s4_661_edges : next config 4 s4_661 = [s5_934, s5_450] := by decide
theorem s4_661_safe : Safe 9 4 s4_661 := by
  apply safe_succ 8 4 s4_661 [s5_934, s5_450] (by decide) s4_661_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_934_safe
  · subst z; exact s5_450_safe
def s4_662 : State := ⟨[1,140,64,136], 1481249143206845131456088112894565029052702, 3, 1, 1, 0⟩
theorem s4_662_edges : next config 4 s4_662 = [s5_14, s5_766] := by decide
theorem s4_662_safe : Safe 9 4 s4_662 := by
  apply safe_succ 8 4 s4_662 [s5_14, s5_766] (by decide) s4_662_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_14_safe
  · subst z; exact s5_766_safe
def s4_663 : State := ⟨[1,140,64,136], 1481249143206845131456088112894573618987286, 3, 1, 1, 0⟩
theorem s4_663_edges : next config 4 s4_663 = [s5_15, s5_767] := by decide
theorem s4_663_safe : Safe 9 4 s4_663 := by
  apply safe_succ 8 4 s4_663 [s5_15, s5_767] (by decide) s4_663_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_15_safe
  · subst z; exact s5_767_safe
def s4_664 : State := ⟨[1,140,64,136], 1481249143206845131456125006382712448155926, 3, 1, 1, 0⟩
theorem s4_664_edges : next config 4 s4_664 = [s5_16, s5_768] := by decide
theorem s4_664_safe : Safe 9 4 s4_664 := by
  apply safe_succ 8 4 s4_664 [s5_16, s5_768] (by decide) s4_664_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_16_safe
  · subst z; exact s5_768_safe
def s4_665 : State := ⟨[1,140,67,136], 1481249143206845131456272580335302124568854, 2, 0, 1, 0⟩
theorem s4_665_edges : next config 4 s4_665 = [s5_95] := by decide
theorem s4_665_safe : Safe 9 4 s4_665 := by
  apply safe_succ 8 4 s4_665 [s5_95] (by decide) s4_665_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_95_safe
def s4_666 : State := ⟨[1,140,67,136], 1481249143206845131456309473823449543672086, 2, 0, 1, 0⟩
theorem s4_666_edges : next config 4 s4_666 = [s5_96] := by decide
theorem s4_666_safe : Safe 9 4 s4_666 := by
  apply safe_succ 8 4 s4_666 [s5_96] (by decide) s4_666_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_96_safe
def s4_667 : State := ⟨[1,140,82,136], 1481249143206845136291865178329376566083862, 2, 0, 1, 0⟩
theorem s4_667_edges : next config 4 s4_667 = [s5_150] := by decide
theorem s4_667_safe : Safe 9 4 s4_667 := by
  apply safe_succ 8 4 s4_667 [s5_150] (by decide) s4_667_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_150_safe
def s4_668 : State := ⟨[1,140,82,136], 1481249143206845137500717210967710902583574, 2, 0, 1, 0⟩
theorem s4_668_edges : next config 4 s4_668 = [s5_151] := by decide
theorem s4_668_safe : Safe 9 4 s4_668 := by
  apply safe_succ 8 4 s4_668 [s5_151] (by decide) s4_668_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_151_safe
def s4_669 : State := ⟨[1,140,97,136], 1481249143207082815943630905907345660903702, 2, 0, 1, 0⟩
theorem s4_669_edges : next config 4 s4_669 = [s5_298] := by decide
theorem s4_669_safe : Safe 9 4 s4_669 := by
  apply safe_succ 8 4 s4_669 [s5_298] (by decide) s4_669_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_298_safe
def s4_670 : State := ⟨[1,140,104,136], 1481249143227206769222254047656105824289046, 2, 0, 1, 0⟩
theorem s4_670_edges : next config 4 s4_670 = [s5_935, s5_1185, s5_368] := by decide
theorem s4_670_safe : Safe 9 4 s4_670 := by
  apply safe_succ 8 4 s4_670 [s5_935, s5_1185, s5_368] (by decide) s4_670_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_935_safe
  · subst z; exact s5_1185_safe
  · subst z; exact s5_368_safe
def s4_671 : State := ⟨[1,140,112,136], 1481249148399221218153430005762654902223126, 2, 0, 1, 0⟩
theorem s4_671_edges : next config 4 s4_671 = [s5_473] := by decide
theorem s4_671_safe : Safe 9 4 s4_671 := by
  apply safe_succ 8 4 s4_671 [s5_473] (by decide) s4_671_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_473_safe
def s4_672 : State := ⟨[1,150,96,146], 1516452374911917057544908692124207412796260630, 2, 0, 1, 0⟩
theorem s4_672_edges : next config 4 s4_672 = [s5_229, s5_770] := by decide
theorem s4_672_safe : Safe 9 4 s4_672 := by
  apply safe_succ 8 4 s4_672 [s5_229, s5_770] (by decide) s4_672_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_229_safe
  · subst z; exact s5_770_safe
def s4_673 : State := ⟨[1,150,96,146], 1538751758980979996932590556898426047229395222, 2, 0, 1, 0⟩
theorem s4_673_edges : next config 4 s4_673 = [s5_230, s5_771] := by decide
theorem s4_673_safe : Safe 9 4 s4_673 := by
  apply safe_succ 8 4 s4_673 [s5_230, s5_771] (by decide) s4_673_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_230_safe
  · subst z; exact s5_771_safe
def s4_674 : State := ⟨[1,150,214,146], 26328072917139296675995959295829525058040520027997147632830054678, 2, 0, 1, 0⟩
theorem s4_674_edges : next config 4 s4_674 = [s5_509] := by decide
theorem s4_674_safe : Safe 9 4 s4_674 := by
  apply safe_succ 8 4 s4_674 [s5_509] (by decide) s4_674_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_509_safe
def s4_675 : State := ⟨[1,150,214,146], 26328072917139296676018258679898587997428201892771366267263189270, 2, 0, 1, 0⟩
theorem s4_675_edges : next config 4 s4_675 = [s5_510] := by decide
theorem s4_675_safe : Safe 9 4 s4_675 := by
  apply safe_succ 8 4 s4_675 [s5_510] (by decide) s4_675_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_510_safe
def s4_676 : State := ⟨[1,196,104,192], 106710729501573572985548702581812905303387798668939154751766, 2, 0, 1, 0⟩
theorem s4_676_edges : next config 4 s4_676 = [s5_416] := by decide
theorem s4_676_safe : Safe 9 4 s4_676 := by
  apply safe_succ 8 4 s4_676 [s5_416] (by decide) s4_676_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_416_safe
def s4_677 : State := ⟨[1,214,64,146], 26328072917139296674568711603123565176982234353695557675800133910, 2, 0, 1, 0⟩
theorem s4_677_edges : next config 4 s4_677 = [s5_774] := by decide
theorem s4_677_safe : Safe 9 4 s4_677 := by
  apply safe_succ 8 4 s4_677 [s5_774] (by decide) s4_677_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_774_safe
def s4_678 : State := ⟨[1,214,64,146], 26328072917139296674591010987192628116369916218469776310233268502, 2, 0, 1, 0⟩
theorem s4_678_edges : next config 4 s4_678 = [s5_775] := by decide
theorem s4_678_safe : Safe 9 4 s4_678 := by
  apply safe_succ 8 4 s4_678 [s5_775] (by decide) s4_678_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_775_safe
def s4_679 : State := ⟨[1,214,64,146], 26328072917139296675995959295829525058040520027997147632830054678, 2, 0, 1, 0⟩
theorem s4_679_edges : next config 4 s4_679 = [s5_776] := by decide
theorem s4_679_safe : Safe 9 4 s4_679 := by
  apply safe_succ 8 4 s4_679 [s5_776] (by decide) s4_679_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_776_safe
def s4_680 : State := ⟨[1,214,64,146], 26328072917139296676018258679898587997428201892771366267263189270, 2, 0, 1, 0⟩
theorem s4_680_edges : next config 4 s4_680 = [s5_777] := by decide
theorem s4_680_safe : Safe 9 4 s4_680 := by
  apply safe_succ 8 4 s4_680 [s5_777] (by decide) s4_680_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_777_safe
def s4_681 : State := ⟨[1,214,64,210], 27973577474460502716723680785680915681964969924181232359795917078, 2, 0, 1, 0⟩
theorem s4_681_edges : next config 4 s4_681 = [s5_58, s5_778] := by decide
theorem s4_681_safe : Safe 9 4 s4_681 := by
  apply safe_succ 8 4 s4_681 [s5_58, s5_778] (by decide) s4_681_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_58_safe
  · subst z; exact s5_778_safe
def s4_682 : State := ⟨[1,214,64,210], 27973577474460502716745980169749978621352651788955450994229051670, 2, 0, 1, 0⟩
theorem s4_682_edges : next config 4 s4_682 = [s5_59, s5_779] := by decide
theorem s4_682_safe : Safe 9 4 s4_682 := by
  apply safe_succ 8 4 s4_682 [s5_59, s5_779] (by decide) s4_682_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_59_safe
  · subst z; exact s5_779_safe
def s4_683 : State := ⟨[1,214,64,210], 27973602582867444263357533148044486020064491460512416769910046998, 2, 0, 1, 0⟩
theorem s4_683_edges : next config 4 s4_683 = [s5_60, s5_780] := by decide
theorem s4_683_safe : Safe 9 4 s4_683 := by
  apply safe_succ 8 4 s4_683 [s5_60, s5_780] (by decide) s4_683_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_60_safe
  · subst z; exact s5_780_safe
def s4_684 : State := ⟨[1,214,64,210], 27973608859969179650038295622704441543977053709369431506871714070, 2, 0, 1, 0⟩
theorem s4_684_edges : next config 4 s4_684 = [s5_61, s5_781] := by decide
theorem s4_684_safe : Safe 9 4 s4_684 := by
  apply safe_succ 8 4 s4_684 [s5_61, s5_781] (by decide) s4_684_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_61_safe
  · subst z; exact s5_781_safe
def s4_685 : State := ⟨[1,214,64,210], 28384953613790804227195519484595193755032192882273252514042282262, 2, 0, 1, 0⟩
theorem s4_685_edges : next config 4 s4_685 = [s5_62, s5_782] := by decide
theorem s4_685_safe : Safe 9 4 s4_685 := by
  apply safe_succ 8 4 s4_685 [s5_62, s5_782] (by decide) s4_685_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_62_safe
  · subst z; exact s5_782_safe
def s4_686 : State := ⟨[1,214,64,210], 28384959890892539613853982575186086339557073266356048616570814742, 2, 0, 1, 0⟩
theorem s4_686_edges : next config 4 s4_686 = [s5_63, s5_783] := by decide
theorem s4_686_safe : Safe 9 4 s4_686 := by
  apply safe_succ 8 4 s4_686 [s5_63, s5_783] (by decide) s4_686_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_63_safe
  · subst z; exact s5_783_safe
def s4_687 : State := ⟨[1,214,66,210], 27973577474460502716656777188955856128786508989651833843043336470, 2, 0, 1, 0⟩
theorem s4_687_edges : next config 4 s4_687 = [s5_84, s5_772] := by decide
theorem s4_687_safe : Safe 9 4 s4_687 := by
  apply safe_succ 8 4 s4_687 [s5_84, s5_772] (by decide) s4_687_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_84_safe
  · subst z; exact s5_772_safe
def s4_688 : State := ⟨[1,214,66,210], 27973602582867444263357531786915018336310637680800963337675407638, 2, 0, 1, 0⟩
theorem s4_688_edges : next config 4 s4_688 = [s5_85, s5_773] := by decide
theorem s4_688_safe : Safe 9 4 s4_688 := by
  apply safe_succ 8 4 s4_688 [s5_85, s5_773] (by decide) s4_688_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_85_safe
  · subst z; exact s5_773_safe
def s4_689 : State := ⟨[1,214,80,210], 27973577474460502716634477804886793189400035976910253542946701590, 2, 0, 1, 0⟩
theorem s4_689_edges : next config 4 s4_689 = [s5_132] := by decide
theorem s4_689_safe : Safe 9 4 s4_689 := by
  apply safe_succ 8 4 s4_689 [s5_132] (by decide) s4_689_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_132_safe
def s4_690 : State := ⟨[1,214,80,210], 28384953613790804227173218739396663131891866089820218781711008022, 2, 0, 1, 0⟩
theorem s4_690_edges : next config 4 s4_690 = [s5_133] := by decide
theorem s4_690_safe : Safe 9 4 s4_690 := by
  apply safe_succ 8 4 s4_690 [s5_133] (by decide) s4_690_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_133_safe
def s4_691 : State := ⟨[1,214,82,210], 27973577474460502716634476443757325505649808974657643998236180758, 2, 0, 1, 0⟩
theorem s4_691_edges : next config 4 s4_691 = [s5_176] := by decide
theorem s4_691_safe : Safe 9 4 s4_691 := by
  apply safe_succ 8 4 s4_691 [s5_176] (by decide) s4_691_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_176_safe
def s4_692 : State := ⟨[1,214,82,210], 27973577474460502716634476443757325505651017826690282332572680470, 2, 0, 1, 0⟩
theorem s4_692_edges : next config 4 s4_692 = [s5_177] := by decide
theorem s4_692_safe : Safe 9 4 s4_692 := by
  apply safe_succ 8 4 s4_692 [s5_177] (by decide) s4_692_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_177_safe
def s4_693 : State := ⟨[1,214,210,130], 27973577474460502716634477804886793189400035976910253542946701590, 2, 0, 1, 0⟩
theorem s4_693_edges : next config 4 s4_693 = [s5_497] := by decide
theorem s4_693_safe : Safe 9 4 s4_693 := by
  apply safe_succ 8 4 s4_693 [s5_497] (by decide) s4_693_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_497_safe
def s4_694 : State := ⟨[1,214,210,130], 27973602582867444263357533148044486020064491460512416769910046998, 2, 0, 1, 0⟩
theorem s4_694_edges : next config 4 s4_694 = [s5_498] := by decide
theorem s4_694_safe : Safe 9 4 s4_694 := by
  apply safe_succ 8 4 s4_694 [s5_498] (by decide) s4_694_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_498_safe
def s4_695 : State := ⟨[1,214,210,144], 27973577474460502716656777188955856128786508989651833843043336470, 2, 0, 1, 0⟩
theorem s4_695_edges : next config 4 s4_695 = [s5_501, s5_784] := by decide
theorem s4_695_safe : Safe 9 4 s4_695 := by
  apply safe_succ 8 4 s4_695 [s5_501, s5_784] (by decide) s4_695_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_501_safe
  · subst z; exact s5_784_safe
def s4_696 : State := ⟨[1,214,210,144], 28384953613790804227195519484595193755032192882273252514042282262, 2, 0, 1, 0⟩
theorem s4_696_edges : next config 4 s4_696 = [s5_502, s5_785] := by decide
theorem s4_696_safe : Safe 9 4 s4_696 := by
  apply safe_succ 8 4 s4_696 [s5_502, s5_785] (by decide) s4_696_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_502_safe
  · subst z; exact s5_785_safe
def s4_697 : State := ⟨[1,214,210,146], 27973577474460502716723680785680915681964969924181232359795917078, 2, 0, 1, 0⟩
theorem s4_697_edges : next config 4 s4_697 = [s5_505] := by decide
theorem s4_697_safe : Safe 9 4 s4_697 := by
  apply safe_succ 8 4 s4_697 [s5_505] (by decide) s4_697_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_505_safe
def s4_698 : State := ⟨[1,214,210,146], 27973577474460502716745980169749978621352651788955450994229051670, 2, 0, 1, 0⟩
theorem s4_698_edges : next config 4 s4_698 = [s5_506] := by decide
theorem s4_698_safe : Safe 9 4 s4_698 := by
  apply safe_succ 8 4 s4_698 [s5_506] (by decide) s4_698_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_506_safe
def s4_699 : State := ⟨[1,228,104,224], 458319093341560876509339256479674003839114031412837488291811942269206, 2, 0, 1, 0⟩
theorem s4_699_edges : next config 4 s4_699 = [s5_936, s5_437] := by decide
theorem s4_699_safe : Safe 9 4 s4_699 := by
  apply safe_succ 8 4 s4_699 [s5_936, s5_437] (by decide) s4_699_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_936_safe
  · subst z; exact s5_437_safe
def s4_700 : State := ⟨[1,236,104,232], 117329687895439584386390849658709772974056135103126219193875962372620566, 2, 0, 1, 0⟩
theorem s4_700_edges : next config 4 s4_700 = [s5_937, s5_449] := by decide
theorem s4_700_safe : Safe 9 4 s4_700 := by
  apply safe_succ 8 4 s4_700 [s5_937, s5_449] (by decide) s4_700_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_937_safe
  · subst z; exact s5_449_safe
def s4_701 : State := ⟨[3,4,64,129], 1020847100762815390408570566373309223198, 3, 2, 1, 0⟩
theorem s4_701_edges : next config 4 s4_701 = [s5_0, s5_1186, s5_798, s5_814, s5_788] := by decide
theorem s4_701_safe : Safe 9 4 s4_701 := by
  apply safe_succ 8 4 s4_701 [s5_0, s5_1186, s5_798, s5_814, s5_788] (by decide) s4_701_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_0_safe
  · subst z; exact s5_1186_safe
  · subst z; exact s5_798_safe
  · subst z; exact s5_814_safe
  · subst z; exact s5_788_safe
def s4_702 : State := ⟨[3,4,64,130], 1701411834604692317335319781236845646110, 3, 2, 1, 0⟩
theorem s4_702_edges : next config 4 s4_702 = [s5_3, s5_1188, s5_799, s5_816, s5_790, s5_792] := by decide
theorem s4_702_safe : Safe 9 4 s4_702 := by
  apply safe_succ 8 4 s4_702 [s5_3, s5_1188, s5_799, s5_816, s5_790, s5_792] (by decide) s4_702_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_3_safe
  · subst z; exact s5_1188_safe
  · subst z; exact s5_799_safe
  · subst z; exact s5_816_safe
  · subst z; exact s5_790_safe
  · subst z; exact s5_792_safe
def s4_703 : State := ⟨[3,4,64,131], 3062541302288446171188818210963918491934, 3, 2, 1, 0⟩
theorem s4_703_edges : next config 4 s4_703 = [s5_7, s5_1190, s5_800, s5_818, s5_794] := by decide
theorem s4_703_safe : Safe 9 4 s4_703 := by
  apply safe_succ 8 4 s4_703 [s5_7, s5_1190, s5_800, s5_818, s5_794] (by decide) s4_703_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_7_safe
  · subst z; exact s5_1190_safe
  · subst z; exact s5_800_safe
  · subst z; exact s5_818_safe
  · subst z; exact s5_794_safe
def s4_704 : State := ⟨[3,4,64,132], 5784800237655953878895815070418064183582, 3, 2, 1, 0⟩
theorem s4_704_edges : next config 4 s4_704 = [s5_8, s5_1191, s5_801, s5_820] := by decide
theorem s4_704_safe : Safe 9 4 s4_704 := by
  apply safe_succ 8 4 s4_704 [s5_8, s5_1191, s5_801, s5_820] (by decide) s4_704_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_8_safe
  · subst z; exact s5_1191_safe
  · subst z; exact s5_801_safe
  · subst z; exact s5_820_safe
def s4_705 : State := ⟨[3,4,64,136], 87452568298681185110105720854042434933022, 3, 2, 1, 0⟩
theorem s4_705_edges : next config 4 s4_705 = [s5_11, s5_1193, s5_802, s5_822] := by decide
theorem s4_705_safe : Safe 9 4 s4_705 := by
  apply safe_succ 8 4 s4_705 [s5_11, s5_1193, s5_802, s5_822] (by decide) s4_705_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_11_safe
  · subst z; exact s5_1193_safe
  · subst z; exact s5_802_safe
  · subst z; exact s5_822_safe
def s4_706 : State := ⟨[3,4,64,136], 1481249143206845131456088112894565029052702, 3, 2, 1, 0⟩
theorem s4_706_edges : next config 4 s4_706 = [s5_14, s5_1195, s5_803, s5_824] := by decide
theorem s4_706_safe : Safe 9 4 s4_706 := by
  apply safe_succ 8 4 s4_706 [s5_14, s5_1195, s5_803, s5_824] (by decide) s4_706_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_14_safe
  · subst z; exact s5_1195_safe
  · subst z; exact s5_803_safe
  · subst z; exact s5_824_safe
def s4_707 : State := ⟨[3,4,64,140], 1394136857275084884809464213392032366924062, 3, 2, 1, 0⟩
theorem s4_707_edges : next config 4 s4_707 = [s5_17, s5_1197, s5_804, s5_825] := by decide
theorem s4_707_safe : Safe 9 4 s4_707 := by
  apply safe_succ 8 4 s4_707 [s5_17, s5_1197, s5_804, s5_825] (by decide) s4_707_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_17_safe
  · subst z; exact s5_1197_safe
  · subst z; exact s5_804_safe
  · subst z; exact s5_825_safe
def s4_708 : State := ⟨[3,4,64,144], 22301085480897544079999200093999871278780702, 3, 2, 1, 0⟩
theorem s4_708_edges : next config 4 s4_708 = [s5_20, s5_1199, s5_805, s5_826, s5_791, s5_796] := by decide
theorem s4_708_safe : Safe 9 4 s4_708 := by
  apply safe_succ 8 4 s4_708 [s5_20, s5_1199, s5_805, s5_826, s5_791, s5_796] (by decide) s4_708_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_20_safe
  · subst z; exact s5_1199_safe
  · subst z; exact s5_805_safe
  · subst z; exact s5_826_safe
  · subst z; exact s5_791_safe
  · subst z; exact s5_796_safe
def s4_709 : State := ⟨[3,4,64,145], 44601830679428167221534918366648232784888094, 1, 1, 1, 0⟩
theorem s4_709_edges : next config 4 s4_709 = [s5_1552, s5_1201, s5_876, s5_806, s5_828] := by decide
theorem s4_709_safe : Safe 9 4 s4_709 := by
  apply safe_succ 8 4 s4_709 [s5_1552, s5_1201, s5_876, s5_806, s5_828] (by decide) s4_709_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1552_safe
  · subst z; exact s5_1201_safe
  · subst z; exact s5_876_safe
  · subst z; exact s5_806_safe
  · subst z; exact s5_828_safe
def s4_710 : State := ⟨[3,4,64,145], 133806172603018343541531644955671405881524510, 1, 0, 1, 0⟩
theorem s4_710_edges : next config 4 s4_710 = [s5_26, s5_877, s5_807, s5_829] := by decide
theorem s4_710_safe : Safe 9 4 s4_710 := by
  apply safe_succ 8 4 s4_710 [s5_26, s5_877, s5_807, s5_829] (by decide) s4_710_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_26_safe
  · subst z; exact s5_877_safe
  · subst z; exact s5_807_safe
  · subst z; exact s5_829_safe
def s4_711 : State := ⟨[3,4,64,145], 156105556672081282929213509729890040314659102, 1, 0, 1, 0⟩
theorem s4_711_edges : next config 4 s4_711 = [s5_27, s5_878, s5_808, s5_830] := by decide
theorem s4_711_safe : Safe 9 4 s4_711 := by
  apply safe_succ 8 4 s4_711 [s5_27, s5_878, s5_808, s5_830] (by decide) s4_711_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_27_safe
  · subst z; exact s5_878_safe
  · subst z; exact s5_808_safe
  · subst z; exact s5_830_safe
def s4_712 : State := ⟨[3,4,64,160], 1461501637671185285124623296198104371165705343262, 3, 2, 1, 0⟩
theorem s4_712_edges : next config 4 s4_712 = [s5_1563, s5_28, s5_1203, s5_809, s5_831, s5_795, s5_793, s5_797] := by decide
theorem s4_712_safe : Safe 9 4 s4_712 := by
  apply safe_succ 8 4 s4_712 [s5_1563, s5_28, s5_1203, s5_809, s5_831, s5_795, s5_793, s5_797] (by decide) s4_712_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1563_safe
  · subst z; exact s5_28_safe
  · subst z; exact s5_1203_safe
  · subst z; exact s5_809_safe
  · subst z; exact s5_831_safe
  · subst z; exact s5_795_safe
  · subst z; exact s5_793_safe
  · subst z; exact s5_797_safe
def s4_713 : State := ⟨[3,4,64,171], 3004847366355398941129064462235866706623561226846494, 1, 0, 1, 0⟩
theorem s4_713_edges : next config 4 s4_713 = [s5_44, s5_810, s5_833] := by decide
theorem s4_713_safe : Safe 9 4 s4_713 := by
  apply safe_succ 8 4 s4_713 [s5_44, s5_810, s5_833] (by decide) s4_713_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_44_safe
  · subst z; exact s5_810_safe
  · subst z; exact s5_833_safe
def s4_714 : State := ⟨[3,4,64,171], 3006308867990007585111900639360875992783763013697822, 1, 0, 1, 0⟩
theorem s4_714_edges : next config 4 s4_714 = [s5_45, s5_811, s5_834] := by decide
theorem s4_714_safe : Safe 9 4 s4_714 := by
  apply safe_succ 8 4 s4_714 [s5_45, s5_811, s5_834] (by decide) s4_714_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_45_safe
  · subst z; exact s5_811_safe
  · subst z; exact s5_834_safe
def s4_715 : State := ⟨[3,4,64,192], 6277101735386680764176071790128604879584176795973807313182, 3, 2, 1, 0⟩
theorem s4_715_edges : next config 4 s4_715 = [s5_47, s5_1208, s5_812, s5_835] := by decide
theorem s4_715_safe : Safe 9 4 s4_715 := by
  apply safe_succ 8 4 s4_715 [s5_47, s5_1208, s5_812, s5_835] (by decide) s4_715_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_47_safe
  · subst z; exact s5_1208_safe
  · subst z; exact s5_812_safe
  · subst z; exact s5_835_safe
def s4_716 : State := ⟨[3,4,67,128], 340282366920938463629395304099449213214, 3, 2, 0, 0⟩
theorem s4_716_edges : next config 4 s4_716 = [s5_86, s5_1210, s5_800, s5_801, s5_813, s5_799, s5_802, s5_805, s5_809] := by decide
theorem s4_716_safe : Safe 9 4 s4_716 := by
  apply safe_succ 8 4 s4_716 [s5_86, s5_1210, s5_800, s5_801, s5_813, s5_799, s5_802, s5_805, s5_809] (by decide) s4_716_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_86_safe
  · subst z; exact s5_1210_safe
  · subst z; exact s5_800_safe
  · subst z; exact s5_801_safe
  · subst z; exact s5_813_safe
  · subst z; exact s5_799_safe
  · subst z; exact s5_802_safe
  · subst z; exact s5_805_safe
  · subst z; exact s5_809_safe
def s4_717 : State := ⟨[3,4,67,140], 1399581375145819900225025781063530334716190, 1, 0, 1, 0⟩
theorem s4_717_edges : next config 4 s4_717 = [s5_99, s5_1220] := by decide
theorem s4_717_safe : Safe 9 4 s4_717 := by
  apply safe_succ 8 4 s4_717 [s5_99, s5_1220] (by decide) s4_717_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_99_safe
  · subst z; exact s5_1220_safe
def s4_718 : State := ⟨[3,4,67,140], 1481249143206845131456235686847154705465630, 1, 0, 1, 0⟩
theorem s4_718_edges : next config 4 s4_718 = [s5_100, s5_1221] := by decide
theorem s4_718_safe : Safe 9 4 s4_718 := by
  apply safe_succ 8 4 s4_718 [s5_100, s5_1221] (by decide) s4_718_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_100_safe
  · subst z; exact s5_1221_safe
def s4_719 : State := ⟨[3,4,67,145], 44602511244162009098461992689815685997592862, 1, 0, 1, 0⟩
theorem s4_719_edges : next config 4 s4_719 = [s5_1553, s5_105, s5_1224, s5_879] := by decide
theorem s4_719_safe : Safe 9 4 s4_719 := by
  apply safe_succ 8 4 s4_719 [s5_1553, s5_105, s5_1224, s5_879] (by decide) s4_719_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1553_safe
  · subst z; exact s5_105_safe
  · subst z; exact s5_1224_safe
  · subst z; exact s5_879_safe
def s4_720 : State := ⟨[3,4,67,145], 66902575877958790363070784213249183967150366, 1, 0, 1, 0⟩
theorem s4_720_edges : next config 4 s4_720 = [s5_1554, s5_106, s5_1225, s5_880] := by decide
theorem s4_720_safe : Safe 9 4 s4_720 := by
  apply safe_succ 8 4 s4_720 [s5_1554, s5_106, s5_1225, s5_880] (by decide) s4_720_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1554_safe
  · subst z; exact s5_106_safe
  · subst z; exact s5_1225_safe
  · subst z; exact s5_880_safe
def s4_721 : State := ⟨[3,4,67,146], 89204682205957097258460355984327272545976606, 1, 0, 1, 0⟩
theorem s4_721_edges : next config 4 s4_721 = [s5_110, s5_881, s5_807] := by decide
theorem s4_721_safe : Safe 9 4 s4_721 := by
  apply safe_succ 8 4 s4_721 [s5_110, s5_881, s5_807] (by decide) s4_721_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_110_safe
  · subst z; exact s5_881_safe
  · subst z; exact s5_807_safe
def s4_722 : State := ⟨[3,4,67,146], 111504066275020036646142220758545906979111198, 1, 0, 1, 0⟩
theorem s4_722_edges : next config 4 s4_722 = [s5_111, s5_882, s5_808] := by decide
theorem s4_722_safe : Safe 9 4 s4_722 := by
  apply safe_succ 8 4 s4_722 [s5_111, s5_882, s5_808] (by decide) s4_722_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_111_safe
  · subst z; exact s5_882_safe
  · subst z; exact s5_808_safe
def s4_723 : State := ⟨[3,4,67,162], 5846006551025023507419431648348025812450252226846, 1, 0, 1, 0⟩
theorem s4_723_edges : next config 4 s4_723 = [s5_114, s5_883] := by decide
theorem s4_723_safe : Safe 9 4 s4_723 := by
  apply safe_succ 8 4 s4_723 [s5_114, s5_883] (by decide) s4_723_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_114_safe
  · subst z; exact s5_883_safe
def s4_724 : State := ⟨[3,4,67,162], 7307508186994796957939362627210810402379111923998, 1, 0, 1, 0⟩
theorem s4_724_edges : next config 4 s4_724 = [s5_115, s5_884] := by decide
theorem s4_724_safe : Safe 9 4 s4_724 := by
  apply safe_succ 8 4 s4_724 [s5_115, s5_884] (by decide) s4_724_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_115_safe
  · subst z; exact s5_884_safe
def s4_725 : State := ⟨[3,4,67,163], 11692013101709764647917924833066656320801055244574, 1, 0, 1, 0⟩
theorem s4_725_edges : next config 4 s4_725 = [s5_116, s5_885, s5_810] := by decide
theorem s4_725_safe : Safe 9 4 s4_725 := by
  apply safe_succ 8 4 s4_725 [s5_116, s5_885, s5_810] (by decide) s4_725_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_116_safe
  · subst z; exact s5_885_safe
  · subst z; exact s5_810_safe
def s4_726 : State := ⟨[3,4,67,163], 13153514736318408630754101958075942481002842095902, 1, 0, 1, 0⟩
theorem s4_726_edges : next config 4 s4_726 = [s5_117, s5_886, s5_811] := by decide
theorem s4_726_safe : Safe 9 4 s4_726 := by
  apply safe_succ 8 4 s4_726 [s5_117, s5_886, s5_811] (by decide) s4_726_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_117_safe
  · subst z; exact s5_886_safe
  · subst z; exact s5_811_safe
def s4_727 : State := ⟨[3,4,67,176], 95780971326419139128294233276893671644123656091664670, 1, 0, 1, 0⟩
theorem s4_727_edges : next config 4 s4_727 = [s5_118, s5_887] := by decide
theorem s4_727_safe : Safe 9 4 s4_727 := by
  apply safe_succ 8 4 s4_727 [s5_118, s5_887] (by decide) s4_727_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_118_safe
  · subst z; exact s5_887_safe
def s4_728 : State := ⟨[3,4,67,176], 95782432805755724832681813820190669654494950518227230, 1, 0, 1, 0⟩
theorem s4_728_edges : next config 4 s4_728 = [s5_119, s5_888] := by decide
theorem s4_728_safe : Safe 9 4 s4_728 := by
  apply safe_succ 8 4 s4_728 [s5_119, s5_888] (by decide) s4_728_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_119_safe
  · subst z; exact s5_888_safe
def s4_729 : State := ⟨[3,4,96,128], 340282367000166625996085689103316750622, 3, 2, 0, 0⟩
theorem s4_729_edges : next config 4 s4_729 = [s5_184, s5_1239, s5_843, s5_818, s5_820, s5_837, s5_816, s5_822, s5_826, s5_831] := by decide
theorem s4_729_safe : Safe 9 4 s4_729 := by
  apply safe_succ 8 4 s4_729 [s5_184, s5_1239, s5_843, s5_818, s5_820, s5_837, s5_816, s5_822, s5_826, s5_831] (by decide) s4_729_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_184_safe
  · subst z; exact s5_1239_safe
  · subst z; exact s5_843_safe
  · subst z; exact s5_818_safe
  · subst z; exact s5_820_safe
  · subst z; exact s5_837_safe
  · subst z; exact s5_816_safe
  · subst z; exact s5_822_safe
  · subst z; exact s5_826_safe
  · subst z; exact s5_831_safe
def s4_730 : State := ⟨[3,4,96,128], 340282368267817226224315090600019951902, 3, 2, 0, 0⟩
theorem s4_730_edges : next config 4 s4_730 = [s5_188, s5_844, s5_819, s5_821, s5_838, s5_817, s5_823, s5_827, s5_832] := by decide
theorem s4_730_safe : Safe 9 4 s4_730 := by
  apply safe_succ 8 4 s4_730 [s5_188, s5_844, s5_819, s5_821, s5_838, s5_817, s5_823, s5_827, s5_832] (by decide) s4_730_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_188_safe
  · subst z; exact s5_844_safe
  · subst z; exact s5_819_safe
  · subst z; exact s5_821_safe
  · subst z; exact s5_838_safe
  · subst z; exact s5_817_safe
  · subst z; exact s5_823_safe
  · subst z; exact s5_827_safe
  · subst z; exact s5_832_safe
def s4_731 : State := ⟨[3,4,96,140], 1399581375145899128387392471448534202253598, 1, 0, 1, 0⟩
theorem s4_731_edges : next config 4 s4_731 = [s5_194, s5_1241, s5_846] := by decide
theorem s4_731_safe : Safe 9 4 s4_731 := by
  apply safe_succ 8 4 s4_731 [s5_194, s5_1241, s5_846] (by decide) s4_731_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_194_safe
  · subst z; exact s5_1241_safe
  · subst z; exact s5_846_safe
def s4_732 : State := ⟨[3,4,96,140], 1481249143206924359618602377232158573003038, 1, 0, 1, 0⟩
theorem s4_732_edges : next config 4 s4_732 = [s5_198, s5_1243, s5_847] := by decide
theorem s4_732_safe : Safe 9 4 s4_732 := by
  apply safe_succ 8 4 s4_732 [s5_198, s5_1243, s5_847] (by decide) s4_732_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_198_safe
  · subst z; exact s5_1243_safe
  · subst z; exact s5_847_safe
def s4_733 : State := ⟨[3,4,96,145], 44602511244162088326624359380200689865130270, 1, 0, 1, 0⟩
theorem s4_733_edges : next config 4 s4_733 = [s5_1555, s5_202, s5_1245, s5_911, s5_889, s5_841, s5_874, s5_848] := by decide
theorem s4_733_safe : Safe 9 4 s4_733 := by
  apply safe_succ 8 4 s4_733 [s5_1555, s5_202, s5_1245, s5_911, s5_889, s5_841, s5_874, s5_848] (by decide) s4_733_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1555_safe
  · subst z; exact s5_202_safe
  · subst z; exact s5_1245_safe
  · subst z; exact s5_911_safe
  · subst z; exact s5_889_safe
  · subst z; exact s5_841_safe
  · subst z; exact s5_874_safe
  · subst z; exact s5_848_safe
def s4_734 : State := ⟨[3,4,96,145], 66902575877958869591233150903634187834687774, 1, 0, 1, 0⟩
theorem s4_734_edges : next config 4 s4_734 = [s5_1556, s5_210, s5_1247, s5_912, s5_890, s5_842, s5_875, s5_849] := by decide
theorem s4_734_safe : Safe 9 4 s4_734 := by
  apply safe_succ 8 4 s4_734 [s5_1556, s5_210, s5_1247, s5_912, s5_890, s5_842, s5_875, s5_849] (by decide) s4_734_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1556_safe
  · subst z; exact s5_210_safe
  · subst z; exact s5_1247_safe
  · subst z; exact s5_912_safe
  · subst z; exact s5_890_safe
  · subst z; exact s5_842_safe
  · subst z; exact s5_875_safe
  · subst z; exact s5_849_safe
def s4_735 : State := ⟨[3,4,96,146], 89204682205957176486622722674712276413514014, 1, 0, 1, 0⟩
theorem s4_735_edges : next config 4 s4_735 = [s5_218, s5_891, s5_850, s5_829] := by decide
theorem s4_735_safe : Safe 9 4 s4_735 := by
  apply safe_succ 8 4 s4_735 [s5_218, s5_891, s5_850, s5_829] (by decide) s4_735_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_218_safe
  · subst z; exact s5_891_safe
  · subst z; exact s5_850_safe
  · subst z; exact s5_829_safe
def s4_736 : State := ⟨[3,4,96,146], 111504066275020115874304587448930910846648606, 1, 0, 1, 0⟩
theorem s4_736_edges : next config 4 s4_736 = [s5_224, s5_892, s5_851, s5_830] := by decide
theorem s4_736_safe : Safe 9 4 s4_736 := by
  apply safe_succ 8 4 s4_736 [s5_224, s5_892, s5_851, s5_830] (by decide) s4_736_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_224_safe
  · subst z; exact s5_892_safe
  · subst z; exact s5_851_safe
  · subst z; exact s5_830_safe
def s4_737 : State := ⟨[3,4,96,162], 5846006551025023507498659810714716197454119764254, 1, 0, 1, 0⟩
theorem s4_737_edges : next config 4 s4_737 = [s5_233, s5_893, s5_852] := by decide
theorem s4_737_safe : Safe 9 4 s4_737 := by
  apply safe_succ 8 4 s4_737 [s5_233, s5_893, s5_852] (by decide) s4_737_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_233_safe
  · subst z; exact s5_893_safe
  · subst z; exact s5_852_safe
def s4_738 : State := ⟨[3,4,96,162], 7307508186994796958018590789577500787382979461406, 1, 0, 1, 0⟩
theorem s4_738_edges : next config 4 s4_738 = [s5_240, s5_894, s5_853] := by decide
theorem s4_738_safe : Safe 9 4 s4_738 := by
  apply safe_succ 8 4 s4_738 [s5_240, s5_894, s5_853] (by decide) s4_738_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_240_safe
  · subst z; exact s5_894_safe
  · subst z; exact s5_853_safe
def s4_739 : State := ⟨[3,4,96,163], 11692013101709764647997152995433346705804922781982, 1, 0, 1, 0⟩
theorem s4_739_edges : next config 4 s4_739 = [s5_249, s5_895, s5_854, s5_833] := by decide
theorem s4_739_safe : Safe 9 4 s4_739 := by
  apply safe_succ 8 4 s4_739 [s5_249, s5_895, s5_854, s5_833] (by decide) s4_739_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_249_safe
  · subst z; exact s5_895_safe
  · subst z; exact s5_854_safe
  · subst z; exact s5_833_safe
def s4_740 : State := ⟨[3,4,96,163], 13153514736318408630833330120442632866006709633310, 1, 0, 1, 0⟩
theorem s4_740_edges : next config 4 s4_740 = [s5_250, s5_896, s5_855, s5_834] := by decide
theorem s4_740_safe : Safe 9 4 s4_740 := by
  apply safe_succ 8 4 s4_740 [s5_250, s5_896, s5_855, s5_834] (by decide) s4_740_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_250_safe
  · subst z; exact s5_896_safe
  · subst z; exact s5_855_safe
  · subst z; exact s5_834_safe
def s4_741 : State := ⟨[3,4,96,176], 95780971326419139128294312505056038334508659959202078, 1, 0, 1, 0⟩
theorem s4_741_edges : next config 4 s4_741 = [s5_260, s5_897, s5_856] := by decide
theorem s4_741_safe : Safe 9 4 s4_741 := by
  apply safe_succ 8 4 s4_741 [s5_260, s5_897, s5_856] (by decide) s4_741_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_260_safe
  · subst z; exact s5_897_safe
  · subst z; exact s5_856_safe
def s4_742 : State := ⟨[3,4,96,176], 95782432805755724832681893048353036344879954385764638, 1, 0, 1, 0⟩
theorem s4_742_edges : next config 4 s4_742 = [s5_264, s5_898, s5_857] := by decide
theorem s4_742_safe : Safe 9 4 s4_742 := by
  apply safe_succ 8 4 s4_742 [s5_264, s5_898, s5_857] (by decide) s4_742_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_264_safe
  · subst z; exact s5_898_safe
  · subst z; exact s5_857_safe
def s4_743 : State := ⟨[3,4,96,228], 431359146674410236714672241398098891015929492802059239105669372117278, 1, 0, 1, 0⟩
theorem s4_743_edges : next config 4 s4_743 = [s5_288, s5_858] := by decide
theorem s4_743_safe : Safe 9 4 s4_743 := by
  apply safe_succ 8 4 s4_743 [s5_288, s5_858] (by decide) s4_743_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_288_safe
  · subst z; exact s5_858_safe
def s4_744 : State := ⟨[3,4,96,228], 458319093341560876509339256479674003818831621809185817867864690983198, 1, 0, 1, 0⟩
theorem s4_744_edges : next config 4 s4_744 = [s5_290, s5_859] := by decide
theorem s4_744_safe : Safe 9 4 s4_744 := by
  apply safe_succ 8 4 s4_744 [s5_290, s5_859] (by decide) s4_744_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_290_safe
  · subst z; exact s5_859_safe
def s4_745 : State := ⟨[3,4,100,129], 1020847102109694153151064305463556374814, 1, 0, 1, 0⟩
theorem s4_745_edges : next config 4 s4_745 = [s5_306, s5_841] := by decide
theorem s4_745_safe : Safe 9 4 s4_745 := by
  apply safe_succ 8 4 s4_745 [s5_306, s5_841] (by decide) s4_745_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_306_safe
  · subst z; exact s5_841_safe
def s4_746 : State := ⟨[3,4,100,130], 1701411835951571080077813520327092797726, 1, 0, 1, 0⟩
theorem s4_746_edges : next config 4 s4_746 = [s5_308] := by decide
theorem s4_746_safe : Safe 9 4 s4_746 := by
  apply safe_succ 8 4 s4_746 [s5_308] (by decide) s4_746_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_308_safe
def s4_747 : State := ⟨[3,4,100,131], 3062541303635324933931311950054165643550, 1, 0, 1, 0⟩
theorem s4_747_edges : next config 4 s4_747 = [s5_311] := by decide
theorem s4_747_safe : Safe 9 4 s4_747 := by
  apply safe_succ 8 4 s4_747 [s5_311] (by decide) s4_747_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_311_safe
def s4_748 : State := ⟨[3,4,100,132], 5784800239002832641638308809508311335198, 1, 0, 1, 0⟩
theorem s4_748_edges : next config 4 s4_748 = [s5_312] := by decide
theorem s4_748_safe : Safe 9 4 s4_748 := by
  apply safe_succ 8 4 s4_748 [s5_312] (by decide) s4_748_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_312_safe
def s4_749 : State := ⟨[3,4,100,136], 87452568300028063872848214593132682084638, 1, 0, 1, 0⟩
theorem s4_749_edges : next config 4 s4_749 = [s5_314] := by decide
theorem s4_749_safe : Safe 9 4 s4_749 := by
  apply safe_succ 8 4 s4_749 [s5_314] (by decide) s4_749_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_314_safe
def s4_750 : State := ⟨[3,4,100,144], 22301085480898890958761942587738961525932318, 1, 0, 1, 0⟩
theorem s4_750_edges : next config 4 s4_750 = [s5_316] := by decide
theorem s4_750_safe : Safe 9 4 s4_750 := by
  apply safe_succ 8 4 s4_750 [s5_316] (by decide) s4_750_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_316_safe
def s4_751 : State := ⟨[3,4,100,160], 1461501637671185286471502058940598110255952494878, 1, 0, 1, 0⟩
theorem s4_751_edges : next config 4 s4_751 = [s5_319] := by decide
theorem s4_751_safe : Safe 9 4 s4_751 := by
  apply safe_succ 8 4 s4_751 [s5_319] (by decide) s4_751_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_319_safe
def s4_752 : State := ⟨[3,4,100,192], 6277101735386680764176071791475483642326670535064054464798, 1, 0, 1, 0⟩
theorem s4_752_edges : next config 4 s4_752 = [s5_321] := by decide
theorem s4_752_safe : Safe 9 4 s4_752 := by
  apply safe_succ 8 4 s4_752 [s5_321] (by decide) s4_752_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_321_safe
def s4_753 : State := ⟨[3,4,100,224], 26959946667150639794667015087359913041904961648764887571703630201118, 1, 0, 1, 0⟩
theorem s4_753_edges : next config 4 s4_753 = [s5_325] := by decide
theorem s4_753_safe : Safe 9 4 s4_753 := by
  apply safe_succ 8 4 s4_753 [s5_325] (by decide) s4_753_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_325_safe
def s4_754 : State := ⟨[3,4,100,228], 431359146674410236714672241392654373146462127986873474788257783939358, 1, 0, 1, 0⟩
theorem s4_754_edges : next config 4 s4_754 = [s5_327] := by decide
theorem s4_754_safe : Safe 9 4 s4_754 := by
  apply safe_succ 8 4 s4_754 [s5_327] (by decide) s4_754_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_327_safe
def s4_755 : State := ⟨[3,4,104,129], 1020847121124453156574505327914104455454, 1, 0, 1, 0⟩
theorem s4_755_edges : next config 4 s4_755 = [s5_329, s5_1253, s5_924, s5_899, s5_862, s5_848] := by decide
theorem s4_755_safe : Safe 9 4 s4_755 := by
  apply safe_succ 8 4 s4_755 [s5_329, s5_1253, s5_924, s5_899, s5_862, s5_848] (by decide) s4_755_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_329_safe
  · subst z; exact s5_1253_safe
  · subst z; exact s5_924_safe
  · subst z; exact s5_899_safe
  · subst z; exact s5_862_safe
  · subst z; exact s5_848_safe
def s4_756 : State := ⟨[3,4,104,130], 1701411854966330083501254542777640878366, 1, 0, 1, 0⟩
theorem s4_756_edges : next config 4 s4_756 = [s5_338, s5_1255, s5_925, s5_900, s5_863, s5_850, s5_852] := by decide
theorem s4_756_safe : Safe 9 4 s4_756 := by
  apply safe_succ 8 4 s4_756 [s5_338, s5_1255, s5_925, s5_900, s5_863, s5_850, s5_852] (by decide) s4_756_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_338_safe
  · subst z; exact s5_1255_safe
  · subst z; exact s5_925_safe
  · subst z; exact s5_900_safe
  · subst z; exact s5_863_safe
  · subst z; exact s5_850_safe
  · subst z; exact s5_852_safe
def s4_757 : State := ⟨[3,4,104,131], 3062541322650083937354752972504713724190, 1, 0, 1, 0⟩
theorem s4_757_edges : next config 4 s4_757 = [s5_348, s5_1257, s5_926, s5_901, s5_864, s5_854] := by decide
theorem s4_757_safe : Safe 9 4 s4_757 := by
  apply safe_succ 8 4 s4_757 [s5_348, s5_1257, s5_926, s5_901, s5_864, s5_854] (by decide) s4_757_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_348_safe
  · subst z; exact s5_1257_safe
  · subst z; exact s5_926_safe
  · subst z; exact s5_901_safe
  · subst z; exact s5_864_safe
  · subst z; exact s5_854_safe
def s4_758 : State := ⟨[3,4,104,132], 5784800258017591645061749831958859415838, 1, 0, 1, 0⟩
theorem s4_758_edges : next config 4 s4_758 = [s5_349, s5_1258, s5_927, s5_902, s5_865, s5_873, s5_860, s5_846] := by decide
theorem s4_758_safe : Safe 9 4 s4_758 := by
  apply safe_succ 8 4 s4_758 [s5_349, s5_1258, s5_927, s5_902, s5_865, s5_873, s5_860, s5_846] (by decide) s4_758_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_349_safe
  · subst z; exact s5_1258_safe
  · subst z; exact s5_927_safe
  · subst z; exact s5_902_safe
  · subst z; exact s5_865_safe
  · subst z; exact s5_873_safe
  · subst z; exact s5_860_safe
  · subst z; exact s5_846_safe
def s4_759 : State := ⟨[3,4,104,136], 87452568319042822876271655615583230165278, 1, 0, 1, 0⟩
theorem s4_759_edges : next config 4 s4_759 = [s5_358, s5_1260, s5_928, s5_935, s5_903, s5_866, s5_847] := by decide
theorem s4_759_safe : Safe 9 4 s4_759 := by
  apply safe_succ 8 4 s4_759 [s5_358, s5_1260, s5_928, s5_935, s5_903, s5_866, s5_847] (by decide) s4_759_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_358_safe
  · subst z; exact s5_1260_safe
  · subst z; exact s5_928_safe
  · subst z; exact s5_935_safe
  · subst z; exact s5_903_safe
  · subst z; exact s5_866_safe
  · subst z; exact s5_847_safe
def s4_760 : State := ⟨[3,4,104,144], 22301085480917905717765366028761412074012958, 1, 0, 1, 0⟩
theorem s4_760_edges : next config 4 s4_760 = [s5_371, s5_1262, s5_929, s5_905, s5_867, s5_851, s5_856] := by decide
theorem s4_760_safe : Safe 9 4 s4_760 := by
  apply safe_succ 8 4 s4_760 [s5_371, s5_1262, s5_929, s5_905, s5_867, s5_851, s5_856] (by decide) s4_760_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_371_safe
  · subst z; exact s5_1262_safe
  · subst z; exact s5_929_safe
  · subst z; exact s5_905_safe
  · subst z; exact s5_867_safe
  · subst z; exact s5_851_safe
  · subst z; exact s5_856_safe
def s4_761 : State := ⟨[3,4,104,160], 1461501637671185305486261062364039132706500575518, 1, 0, 1, 0⟩
theorem s4_761_edges : next config 4 s4_761 = [s5_1569, s5_383, s5_1264, s5_930, s5_906, s5_868, s5_855, s5_853, s5_857] := by decide
theorem s4_761_safe : Safe 9 4 s4_761 := by
  apply safe_succ 8 4 s4_761 [s5_1569, s5_383, s5_1264, s5_930, s5_906, s5_868, s5_855, s5_853, s5_857] (by decide) s4_761_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1569_safe
  · subst z; exact s5_383_safe
  · subst z; exact s5_1264_safe
  · subst z; exact s5_930_safe
  · subst z; exact s5_906_safe
  · subst z; exact s5_868_safe
  · subst z; exact s5_855_safe
  · subst z; exact s5_853_safe
  · subst z; exact s5_857_safe
def s4_762 : State := ⟨[3,4,104,192], 6277101735386680764176071810490242645750111557514602545438, 1, 0, 1, 0⟩
theorem s4_762_edges : next config 4 s4_762 = [s5_406, s5_1269, s5_931, s5_907, s5_869] := by decide
theorem s4_762_safe : Safe 9 4 s4_762 := by
  apply safe_succ 8 4 s4_762 [s5_406, s5_1269, s5_931, s5_907, s5_869] (by decide) s4_762_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_406_safe
  · subst z; exact s5_1269_safe
  · subst z; exact s5_931_safe
  · subst z; exact s5_907_safe
  · subst z; exact s5_869_safe
def s4_763 : State := ⟨[3,4,104,224], 26959946667150639794667015087359913060919720652188328594154178281758, 1, 0, 1, 0⟩
theorem s4_763_edges : next config 4 s4_763 = [s5_427, s5_1271, s5_932, s5_936, s5_908, s5_870, s5_859] := by decide
theorem s4_763_safe : Safe 9 4 s4_763 := by
  apply safe_succ 8 4 s4_763 [s5_427, s5_1271, s5_932, s5_936, s5_908, s5_870, s5_859] (by decide) s4_763_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_427_safe
  · subst z; exact s5_1271_safe
  · subst z; exact s5_932_safe
  · subst z; exact s5_936_safe
  · subst z; exact s5_908_safe
  · subst z; exact s5_870_safe
  · subst z; exact s5_859_safe
def s4_764 : State := ⟨[3,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791831838, 1, 0, 1, 0⟩
theorem s4_764_edges : next config 4 s4_764 = [s5_440, s5_1273, s5_933, s5_937, s5_909, s5_871, s5_861] := by decide
theorem s4_764_safe : Safe 9 4 s4_764 := by
  apply safe_succ 8 4 s4_764 [s5_440, s5_1273, s5_933, s5_937, s5_909, s5_871, s5_861] (by decide) s4_764_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_440_safe
  · subst z; exact s5_1273_safe
  · subst z; exact s5_933_safe
  · subst z; exact s5_937_safe
  · subst z; exact s5_909_safe
  · subst z; exact s5_871_safe
  · subst z; exact s5_861_safe
def s4_765 : State := ⟨[3,4,108,128], 340282711801129888074482896206588608798, 1, 0, 0, 0⟩
theorem s4_765_edges : next config 4 s4_765 = [s5_451, s5_864, s5_865, s5_872, s5_863, s5_866, s5_867, s5_868] := by decide
theorem s4_765_safe : Safe 9 4 s4_765 := by
  apply safe_succ 8 4 s4_765 [s5_451, s5_864, s5_865, s5_872, s5_863, s5_866, s5_867, s5_868] (by decide) s4_765_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_451_safe
  · subst z; exact s5_864_safe
  · subst z; exact s5_865_safe
  · subst z; exact s5_872_safe
  · subst z; exact s5_863_safe
  · subst z; exact s5_866_safe
  · subst z; exact s5_867_safe
  · subst z; exact s5_868_safe
def s4_766 : State := ⟨[3,4,228,132], 431359146674410236714672241398098891015929492802059239105669372117278, 1, 0, 1, 0⟩
theorem s4_766_edges : next config 4 s4_766 = [s5_512] := by decide
theorem s4_766_safe : Safe 9 4 s4_766 := by
  apply safe_succ 8 4 s4_766 [s5_512] (by decide) s4_766_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_512_safe
def s4_767 : State := ⟨[3,12,64,145], 44602511244162009098461845115863096321184030, 3, 0, 1, 0⟩
theorem s4_767_edges : next config 4 s4_767 = [s5_1557, s5_519, s5_1275, s5_788, s5_879, s5_889] := by decide
theorem s4_767_safe : Safe 9 4 s4_767 := by
  apply safe_succ 8 4 s4_767 [s5_1557, s5_519, s5_1275, s5_788, s5_879, s5_889] (by decide) s4_767_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1557_safe
  · subst z; exact s5_519_safe
  · subst z; exact s5_1275_safe
  · subst z; exact s5_788_safe
  · subst z; exact s5_879_safe
  · subst z; exact s5_889_safe
def s4_768 : State := ⟨[3,12,64,145], 66902575877958790363070636639296594290741534, 3, 0, 1, 0⟩
theorem s4_768_edges : next config 4 s4_768 = [s5_1558, s5_522, s5_1277, s5_789, s5_880, s5_890] := by decide
theorem s4_768_safe : Safe 9 4 s4_768 := by
  apply safe_succ 8 4 s4_768 [s5_1558, s5_522, s5_1277, s5_789, s5_880, s5_890] (by decide) s4_768_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1558_safe
  · subst z; exact s5_522_safe
  · subst z; exact s5_1277_safe
  · subst z; exact s5_789_safe
  · subst z; exact s5_880_safe
  · subst z; exact s5_890_safe
def s4_769 : State := ⟨[3,12,64,146], 89204682205957097258460208410374682869567774, 3, 0, 1, 0⟩
theorem s4_769_edges : next config 4 s4_769 = [s5_525, s5_790, s5_881, s5_891, s5_877] := by decide
theorem s4_769_safe : Safe 9 4 s4_769 := by
  apply safe_succ 8 4 s4_769 [s5_525, s5_790, s5_881, s5_891, s5_877] (by decide) s4_769_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_525_safe
  · subst z; exact s5_790_safe
  · subst z; exact s5_881_safe
  · subst z; exact s5_891_safe
  · subst z; exact s5_877_safe
def s4_770 : State := ⟨[3,12,64,146], 111504066275020036646142073184593317302702366, 3, 0, 1, 0⟩
theorem s4_770_edges : next config 4 s4_770 = [s5_528, s5_791, s5_882, s5_892, s5_878] := by decide
theorem s4_770_safe : Safe 9 4 s4_770 := by
  apply safe_succ 8 4 s4_770 [s5_528, s5_791, s5_882, s5_892, s5_878] (by decide) s4_770_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_528_safe
  · subst z; exact s5_791_safe
  · subst z; exact s5_882_safe
  · subst z; exact s5_892_safe
  · subst z; exact s5_878_safe
def s4_771 : State := ⟨[3,12,64,162], 5846006551025023507419431648200451859860575818014, 3, 0, 1, 0⟩
theorem s4_771_edges : next config 4 s4_771 = [s5_530, s5_792, s5_883, s5_893] := by decide
theorem s4_771_safe : Safe 9 4 s4_771 := by
  apply safe_succ 8 4 s4_771 [s5_530, s5_792, s5_883, s5_893] (by decide) s4_771_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_530_safe
  · subst z; exact s5_792_safe
  · subst z; exact s5_883_safe
  · subst z; exact s5_893_safe
def s4_772 : State := ⟨[3,12,64,162], 7307508186994796957939362627063236449789435515166, 3, 0, 1, 0⟩
theorem s4_772_edges : next config 4 s4_772 = [s5_533, s5_793, s5_884, s5_894] := by decide
theorem s4_772_safe : Safe 9 4 s4_772 := by
  apply safe_succ 8 4 s4_772 [s5_533, s5_793, s5_884, s5_894] (by decide) s4_772_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_533_safe
  · subst z; exact s5_793_safe
  · subst z; exact s5_884_safe
  · subst z; exact s5_894_safe
def s4_773 : State := ⟨[3,12,64,163], 11692013101709764647917924832919082368211378835742, 3, 0, 1, 0⟩
theorem s4_773_edges : next config 4 s4_773 = [s5_538, s5_794, s5_885, s5_895] := by decide
theorem s4_773_safe : Safe 9 4 s4_773 := by
  apply safe_succ 8 4 s4_773 [s5_538, s5_794, s5_885, s5_895] (by decide) s4_773_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_538_safe
  · subst z; exact s5_794_safe
  · subst z; exact s5_885_safe
  · subst z; exact s5_895_safe
def s4_774 : State := ⟨[3,12,64,163], 13153514736318408630754101957928368528413165687070, 3, 0, 1, 0⟩
theorem s4_774_edges : next config 4 s4_774 = [s5_539, s5_795, s5_886, s5_896] := by decide
theorem s4_774_safe : Safe 9 4 s4_774 := by
  apply safe_succ 8 4 s4_774 [s5_539, s5_795, s5_886, s5_896] (by decide) s4_774_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_539_safe
  · subst z; exact s5_795_safe
  · subst z; exact s5_886_safe
  · subst z; exact s5_896_safe
def s4_775 : State := ⟨[3,12,64,176], 95780971326419139128294233276893524070171066415255838, 3, 0, 1, 0⟩
theorem s4_775_edges : next config 4 s4_775 = [s5_541, s5_796, s5_887, s5_897] := by decide
theorem s4_775_safe : Safe 9 4 s4_775 := by
  apply safe_succ 8 4 s4_775 [s5_541, s5_796, s5_887, s5_897] (by decide) s4_775_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_541_safe
  · subst z; exact s5_796_safe
  · subst z; exact s5_887_safe
  · subst z; exact s5_897_safe
def s4_776 : State := ⟨[3,12,64,176], 95782432805755724832681813820190522080542360841818398, 3, 0, 1, 0⟩
theorem s4_776_edges : next config 4 s4_776 = [s5_543, s5_797, s5_888, s5_898] := by decide
theorem s4_776_safe : Safe 9 4 s4_776 := by
  apply safe_succ 8 4 s4_776 [s5_543, s5_797, s5_888, s5_898] (by decide) s4_776_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_543_safe
  · subst z; exact s5_797_safe
  · subst z; exact s5_888_safe
  · subst z; exact s5_898_safe
def s4_777 : State := ⟨[3,12,67,129], 1020847100762815390556144518962985636126, 3, 0, 1, 0⟩
theorem s4_777_edges : next config 4 s4_777 = [s5_547, s5_1281, s5_798, s5_879] := by decide
theorem s4_777_safe : Safe 9 4 s4_777 := by
  apply safe_succ 8 4 s4_777 [s5_547, s5_1281, s5_798, s5_879] (by decide) s4_777_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_547_safe
  · subst z; exact s5_1281_safe
  · subst z; exact s5_798_safe
  · subst z; exact s5_879_safe
def s4_778 : State := ⟨[3,12,67,130], 1701411834604692317482893733826522059038, 3, 0, 1, 0⟩
theorem s4_778_edges : next config 4 s4_778 = [s5_548, s5_1282, s5_799, s5_881, s5_883] := by decide
theorem s4_778_safe : Safe 9 4 s4_778 := by
  apply safe_succ 8 4 s4_778 [s5_548, s5_1282, s5_799, s5_881, s5_883] (by decide) s4_778_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_548_safe
  · subst z; exact s5_1282_safe
  · subst z; exact s5_799_safe
  · subst z; exact s5_881_safe
  · subst z; exact s5_883_safe
def s4_779 : State := ⟨[3,12,67,131], 3062541302288446171336392163553594904862, 3, 0, 1, 0⟩
theorem s4_779_edges : next config 4 s4_779 = [s5_549, s5_1283, s5_800, s5_885] := by decide
theorem s4_779_safe : Safe 9 4 s4_779 := by
  apply safe_succ 8 4 s4_779 [s5_549, s5_1283, s5_800, s5_885] (by decide) s4_779_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_549_safe
  · subst z; exact s5_1283_safe
  · subst z; exact s5_800_safe
  · subst z; exact s5_885_safe
def s4_780 : State := ⟨[3,12,67,132], 5784800237655953879043389023007740596510, 3, 0, 1, 0⟩
theorem s4_780_edges : next config 4 s4_780 = [s5_550, s5_1284, s5_801] := by decide
theorem s4_780_safe : Safe 9 4 s4_780 := by
  apply safe_succ 8 4 s4_780 [s5_550, s5_1284, s5_801] (by decide) s4_780_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_550_safe
  · subst z; exact s5_1284_safe
  · subst z; exact s5_801_safe
def s4_781 : State := ⟨[3,12,67,136], 87452568298681185110253294806632111345950, 3, 0, 1, 0⟩
theorem s4_781_edges : next config 4 s4_781 = [s5_551, s5_1285, s5_802] := by decide
theorem s4_781_safe : Safe 9 4 s4_781 := by
  apply safe_succ 8 4 s4_781 [s5_551, s5_1285, s5_802] (by decide) s4_781_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_551_safe
  · subst z; exact s5_1285_safe
  · subst z; exact s5_802_safe
def s4_782 : State := ⟨[3,12,67,140], 1394136857275084884809611787344622043336990, 3, 0, 1, 0⟩
theorem s4_782_edges : next config 4 s4_782 = [s5_552, s5_1286, s5_804] := by decide
theorem s4_782_safe : Safe 9 4 s4_782 := by
  apply safe_succ 8 4 s4_782 [s5_552, s5_1286, s5_804] (by decide) s4_782_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_552_safe
  · subst z; exact s5_1286_safe
  · subst z; exact s5_804_safe
def s4_783 : State := ⟨[3,12,67,144], 22301085480897544079999347667952460955193630, 3, 0, 1, 0⟩
theorem s4_783_edges : next config 4 s4_783 = [s5_553, s5_1287, s5_805, s5_882, s5_887] := by decide
theorem s4_783_safe : Safe 9 4 s4_783 := by
  apply safe_succ 8 4 s4_783 [s5_553, s5_1287, s5_805, s5_882, s5_887] (by decide) s4_783_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_553_safe
  · subst z; exact s5_1287_safe
  · subst z; exact s5_805_safe
  · subst z; exact s5_882_safe
  · subst z; exact s5_887_safe
def s4_784 : State := ⟨[3,12,67,160], 1461501637671185285124623296345678323755381756190, 3, 0, 1, 0⟩
theorem s4_784_edges : next config 4 s4_784 = [s5_1573, s5_562, s5_1288, s5_809, s5_886, s5_884, s5_888] := by decide
theorem s4_784_safe : Safe 9 4 s4_784 := by
  apply safe_succ 8 4 s4_784 [s5_1573, s5_562, s5_1288, s5_809, s5_886, s5_884, s5_888] (by decide) s4_784_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1573_safe
  · subst z; exact s5_562_safe
  · subst z; exact s5_1288_safe
  · subst z; exact s5_809_safe
  · subst z; exact s5_886_safe
  · subst z; exact s5_884_safe
  · subst z; exact s5_888_safe
def s4_785 : State := ⟨[3,12,67,192], 6277101735386680764176071790128604879731750748563483726110, 3, 0, 1, 0⟩
theorem s4_785_edges : next config 4 s4_785 = [s5_571, s5_1290, s5_812] := by decide
theorem s4_785_safe : Safe 9 4 s4_785 := by
  apply safe_succ 8 4 s4_785 [s5_571, s5_1290, s5_812] (by decide) s4_785_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_571_safe
  · subst z; exact s5_1290_safe
  · subst z; exact s5_812_safe
def s4_786 : State := ⟨[3,12,67,195], 50216813883093446111026597752582269792448238859811725316382, 3, 0, 1, 0⟩
theorem s4_786_edges : next config 4 s4_786 = [s5_572, s5_1291, s5_813] := by decide
theorem s4_786_safe : Safe 9 4 s4_786 := by
  apply safe_succ 8 4 s4_786 [s5_572, s5_1291, s5_813] (by decide) s4_786_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_572_safe
  · subst z; exact s5_1291_safe
  · subst z; exact s5_813_safe
def s4_787 : State := ⟨[3,12,96,129], 1020847100842043552922834903966853173534, 3, 0, 1, 0⟩
theorem s4_787_edges : next config 4 s4_787 = [s5_581, s5_1292, s5_814, s5_899, s5_889] := by decide
theorem s4_787_safe : Safe 9 4 s4_787 := by
  apply safe_succ 8 4 s4_787 [s5_581, s5_1292, s5_814, s5_899, s5_889] (by decide) s4_787_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_581_safe
  · subst z; exact s5_1292_safe
  · subst z; exact s5_814_safe
  · subst z; exact s5_899_safe
  · subst z; exact s5_889_safe
def s4_788 : State := ⟨[3,12,96,130], 1701411834683920479849584118830389596446, 3, 0, 1, 0⟩
theorem s4_788_edges : next config 4 s4_788 = [s5_585, s5_1294, s5_816, s5_900, s5_891, s5_893] := by decide
theorem s4_788_safe : Safe 9 4 s4_788 := by
  apply safe_succ 8 4 s4_788 [s5_585, s5_1294, s5_816, s5_900, s5_891, s5_893] (by decide) s4_788_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_585_safe
  · subst z; exact s5_1294_safe
  · subst z; exact s5_816_safe
  · subst z; exact s5_900_safe
  · subst z; exact s5_891_safe
  · subst z; exact s5_893_safe
def s4_789 : State := ⟨[3,12,96,131], 3062541302367674333703082548557462442270, 3, 0, 1, 0⟩
theorem s4_789_edges : next config 4 s4_789 = [s5_590, s5_1296, s5_818, s5_901, s5_895] := by decide
theorem s4_789_safe : Safe 9 4 s4_789 := by
  apply safe_succ 8 4 s4_789 [s5_590, s5_1296, s5_818, s5_901, s5_895] (by decide) s4_789_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_590_safe
  · subst z; exact s5_1296_safe
  · subst z; exact s5_818_safe
  · subst z; exact s5_901_safe
  · subst z; exact s5_895_safe
def s4_790 : State := ⟨[3,12,96,132], 5784800237735182041410079408011608133918, 3, 0, 1, 0⟩
theorem s4_790_edges : next config 4 s4_790 = [s5_591, s5_1297, s5_820, s5_902] := by decide
theorem s4_790_safe : Safe 9 4 s4_790 := by
  apply safe_succ 8 4 s4_790 [s5_591, s5_1297, s5_820, s5_902] (by decide) s4_790_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_591_safe
  · subst z; exact s5_1297_safe
  · subst z; exact s5_820_safe
  · subst z; exact s5_902_safe
def s4_791 : State := ⟨[3,12,96,136], 87452568298760413272619985191635978883358, 3, 0, 1, 0⟩
theorem s4_791_edges : next config 4 s4_791 = [s5_595, s5_1299, s5_822, s5_903] := by decide
theorem s4_791_safe : Safe 9 4 s4_791 := by
  apply safe_succ 8 4 s4_791 [s5_595, s5_1299, s5_822, s5_903] (by decide) s4_791_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_595_safe
  · subst z; exact s5_1299_safe
  · subst z; exact s5_822_safe
  · subst z; exact s5_903_safe
def s4_792 : State := ⟨[3,12,96,140], 1394136857275164112971978477729625910874398, 3, 0, 1, 0⟩
theorem s4_792_edges : next config 4 s4_792 = [s5_599, s5_1301, s5_825, s5_904] := by decide
theorem s4_792_safe : Safe 9 4 s4_792 := by
  apply safe_succ 8 4 s4_792 [s5_599, s5_1301, s5_825, s5_904] (by decide) s4_792_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_599_safe
  · subst z; exact s5_1301_safe
  · subst z; exact s5_825_safe
  · subst z; exact s5_904_safe
def s4_793 : State := ⟨[3,12,96,144], 22301085480897623308161714358337464822731038, 3, 0, 1, 0⟩
theorem s4_793_edges : next config 4 s4_793 = [s5_603, s5_1303, s5_826, s5_905, s5_892, s5_897] := by decide
theorem s4_793_safe : Safe 9 4 s4_793 := by
  apply safe_succ 8 4 s4_793 [s5_603, s5_1303, s5_826, s5_905, s5_892, s5_897] (by decide) s4_793_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_603_safe
  · subst z; exact s5_1303_safe
  · subst z; exact s5_826_safe
  · subst z; exact s5_905_safe
  · subst z; exact s5_892_safe
  · subst z; exact s5_897_safe
def s4_794 : State := ⟨[3,12,96,160], 1461501637671185285203851458712368708759249293598, 3, 0, 1, 0⟩
theorem s4_794_edges : next config 4 s4_794 = [s5_1576, s5_608, s5_1305, s5_831, s5_906, s5_896, s5_894, s5_898] := by decide
theorem s4_794_safe : Safe 9 4 s4_794 := by
  apply safe_succ 8 4 s4_794 [s5_1576, s5_608, s5_1305, s5_831, s5_906, s5_896, s5_894, s5_898] (by decide) s4_794_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1576_safe
  · subst z; exact s5_608_safe
  · subst z; exact s5_1305_safe
  · subst z; exact s5_831_safe
  · subst z; exact s5_906_safe
  · subst z; exact s5_896_safe
  · subst z; exact s5_894_safe
  · subst z; exact s5_898_safe
def s4_795 : State := ⟨[3,12,96,192], 6277101735386680764176071790207833042098441133567351263518, 3, 0, 1, 0⟩
theorem s4_795_edges : next config 4 s4_795 = [s5_622, s5_1310, s5_835, s5_907] := by decide
theorem s4_795_safe : Safe 9 4 s4_795 := by
  apply safe_succ 8 4 s4_795 [s5_622, s5_1310, s5_835, s5_907] (by decide) s4_795_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_622_safe
  · subst z; exact s5_1310_safe
  · subst z; exact s5_835_safe
  · subst z; exact s5_907_safe
def s4_796 : State := ⟨[3,12,96,224], 26959946667150639794667015087359913040637311048536658170206926999838, 3, 0, 1, 0⟩
theorem s4_796_edges : next config 4 s4_796 = [s5_636, s5_1312, s5_837, s5_908] := by decide
theorem s4_796_safe : Safe 9 4 s4_796 := by
  apply safe_succ 8 4 s4_796 [s5_636, s5_1312, s5_837, s5_908] (by decide) s4_796_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_636_safe
  · subst z; exact s5_1312_safe
  · subst z; exact s5_837_safe
  · subst z; exact s5_908_safe
def s4_797 : State := ⟨[3,12,104,128], 340282387282576229647756113050568036638, 3, 0, 0, 0⟩
theorem s4_797_edges : next config 4 s4_797 = [s5_646, s5_1314, s5_843, s5_901, s5_904, s5_909, s5_900, s5_903, s5_905, s5_906] := by decide
theorem s4_797_safe : Safe 9 4 s4_797 := by
  apply safe_succ 8 4 s4_797 [s5_646, s5_1314, s5_843, s5_901, s5_904, s5_909, s5_900, s5_903, s5_905, s5_906] (by decide) s4_797_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_646_safe
  · subst z; exact s5_1314_safe
  · subst z; exact s5_843_safe
  · subst z; exact s5_901_safe
  · subst z; exact s5_904_safe
  · subst z; exact s5_909_safe
  · subst z; exact s5_900_safe
  · subst z; exact s5_903_safe
  · subst z; exact s5_905_safe
  · subst z; exact s5_906_safe
def s4_798 : State := ⟨[3,100,96,129], 1020847102109694153151064305463556374814, 3, 0, 1, 0⟩
theorem s4_798_edges : next config 4 s4_798 = [s5_708, s5_815, s5_913, s5_911] := by decide
theorem s4_798_safe : Safe 9 4 s4_798 := by
  apply safe_succ 8 4 s4_798 [s5_708, s5_815, s5_913, s5_911] (by decide) s4_798_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_708_safe
  · subst z; exact s5_815_safe
  · subst z; exact s5_913_safe
  · subst z; exact s5_911_safe
def s4_799 : State := ⟨[3,100,96,130], 1701411835951571080077813520327092797726, 3, 0, 1, 0⟩
theorem s4_799_edges : next config 4 s4_799 = [s5_710, s5_817, s5_914] := by decide
theorem s4_799_safe : Safe 9 4 s4_799 := by
  apply safe_succ 8 4 s4_799 [s5_710, s5_817, s5_914] (by decide) s4_799_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_710_safe
  · subst z; exact s5_817_safe
  · subst z; exact s5_914_safe
def s4_800 : State := ⟨[3,100,96,131], 3062541303635324933931311950054165643550, 3, 0, 1, 0⟩
theorem s4_800_edges : next config 4 s4_800 = [s5_713, s5_819, s5_915] := by decide
theorem s4_800_safe : Safe 9 4 s4_800 := by
  apply safe_succ 8 4 s4_800 [s5_713, s5_819, s5_915] (by decide) s4_800_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_713_safe
  · subst z; exact s5_819_safe
  · subst z; exact s5_915_safe
def s4_801 : State := ⟨[3,100,96,132], 5784800239002832641638308809508311335198, 3, 0, 1, 0⟩
theorem s4_801_edges : next config 4 s4_801 = [s5_714, s5_821, s5_916] := by decide
theorem s4_801_safe : Safe 9 4 s4_801 := by
  apply safe_succ 8 4 s4_801 [s5_714, s5_821, s5_916] (by decide) s4_801_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_714_safe
  · subst z; exact s5_821_safe
  · subst z; exact s5_916_safe
def s4_802 : State := ⟨[3,100,96,136], 87452568300028063872848214593132682084638, 3, 0, 1, 0⟩
theorem s4_802_edges : next config 4 s4_802 = [s5_716, s5_823, s5_917] := by decide
theorem s4_802_safe : Safe 9 4 s4_802 := by
  apply safe_succ 8 4 s4_802 [s5_716, s5_823, s5_917] (by decide) s4_802_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_716_safe
  · subst z; exact s5_823_safe
  · subst z; exact s5_917_safe
def s4_803 : State := ⟨[3,100,96,144], 22301085480898890958761942587738961525932318, 3, 0, 1, 0⟩
theorem s4_803_edges : next config 4 s4_803 = [s5_718, s5_827, s5_918] := by decide
theorem s4_803_safe : Safe 9 4 s4_803 := by
  apply safe_succ 8 4 s4_803 [s5_718, s5_827, s5_918] (by decide) s4_803_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_718_safe
  · subst z; exact s5_827_safe
  · subst z; exact s5_918_safe
def s4_804 : State := ⟨[3,100,96,160], 1461501637671185286471502058940598110255952494878, 3, 0, 1, 0⟩
theorem s4_804_edges : next config 4 s4_804 = [s5_721, s5_832, s5_919] := by decide
theorem s4_804_safe : Safe 9 4 s4_804 := by
  apply safe_succ 8 4 s4_804 [s5_721, s5_832, s5_919] (by decide) s4_804_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_721_safe
  · subst z; exact s5_832_safe
  · subst z; exact s5_919_safe
def s4_805 : State := ⟨[3,100,96,192], 6277101735386680764176071791475483642326670535064054464798, 3, 0, 1, 0⟩
theorem s4_805_edges : next config 4 s4_805 = [s5_723, s5_836, s5_920] := by decide
theorem s4_805_safe : Safe 9 4 s4_805 := by
  apply safe_succ 8 4 s4_805 [s5_723, s5_836, s5_920] (by decide) s4_805_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_723_safe
  · subst z; exact s5_836_safe
  · subst z; exact s5_920_safe
def s4_806 : State := ⟨[3,100,96,224], 26959946667150639794667015087359913041904961648764887571703630201118, 3, 0, 1, 0⟩
theorem s4_806_edges : next config 4 s4_806 = [s5_727, s5_838, s5_921] := by decide
theorem s4_806_safe : Safe 9 4 s4_806 := by
  apply safe_succ 8 4 s4_806 [s5_727, s5_838, s5_921] (by decide) s4_806_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_727_safe
  · subst z; exact s5_838_safe
  · subst z; exact s5_921_safe
def s4_807 : State := ⟨[3,100,96,228], 431359146674410236714672241392654373146462127986873474788257783939358, 3, 0, 1, 0⟩
theorem s4_807_edges : next config 4 s4_807 = [s5_729, s5_840, s5_922] := by decide
theorem s4_807_safe : Safe 9 4 s4_807 := by
  apply safe_succ 8 4 s4_807 [s5_729, s5_840, s5_922] (by decide) s4_807_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_729_safe
  · subst z; exact s5_840_safe
  · subst z; exact s5_922_safe
def s4_808 : State := ⟨[3,100,104,128], 340282388550226829875985514547271237918, 3, 0, 0, 0⟩
theorem s4_808_edges : next config 4 s4_808 = [s5_731, s5_915, s5_922, s5_923, s5_914, s5_917, s5_918, s5_919] := by decide
theorem s4_808_safe : Safe 9 4 s4_808 := by
  apply safe_succ 8 4 s4_808 [s5_731, s5_915, s5_922, s5_923, s5_914, s5_917, s5_918, s5_919] (by decide) s4_808_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_731_safe
  · subst z; exact s5_915_safe
  · subst z; exact s5_922_safe
  · subst z; exact s5_923_safe
  · subst z; exact s5_914_safe
  · subst z; exact s5_917_safe
  · subst z; exact s5_918_safe
  · subst z; exact s5_919_safe
def s4_809 : State := ⟨[3,108,104,128], 340282711801129888074482896206588608798, 3, 0, 0, 0⟩
theorem s4_809_edges : next config 4 s4_809 = [s5_747, s5_845, s5_926, s5_934, s5_933, s5_925, s5_928, s5_929, s5_930] := by decide
theorem s4_809_safe : Safe 9 4 s4_809 := by
  apply safe_succ 8 4 s4_809 [s5_747, s5_845, s5_926, s5_934, s5_933, s5_925, s5_928, s5_929, s5_930] (by decide) s4_809_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_747_safe
  · subst z; exact s5_845_safe
  · subst z; exact s5_926_safe
  · subst z; exact s5_934_safe
  · subst z; exact s5_933_safe
  · subst z; exact s5_925_safe
  · subst z; exact s5_928_safe
  · subst z; exact s5_929_safe
  · subst z; exact s5_930_safe
def s4_810 : State := ⟨[3,140,67,136], 1481249143206845131456235686847154705465630, 3, 0, 1, 0⟩
theorem s4_810_edges : next config 4 s4_810 = [s5_765, s5_1316, s5_803] := by decide
theorem s4_810_safe : Safe 9 4 s4_810 := by
  apply safe_succ 8 4 s4_810 [s5_765, s5_1316, s5_803] (by decide) s4_810_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_765_safe
  · subst z; exact s5_1316_safe
  · subst z; exact s5_803_safe
def s4_811 : State := ⟨[3,140,96,136], 1481249143206924359618602377232158573003038, 3, 0, 1, 0⟩
theorem s4_811_edges : next config 4 s4_811 = [s5_766, s5_1317, s5_824, s5_935] := by decide
theorem s4_811_safe : Safe 9 4 s4_811 := by
  apply safe_succ 8 4 s4_811 [s5_766, s5_1317, s5_824, s5_935] (by decide) s4_811_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_766_safe
  · subst z; exact s5_1317_safe
  · subst z; exact s5_824_safe
  · subst z; exact s5_935_safe
def s4_812 : State := ⟨[3,228,96,224], 458319093341560876509339256479674003818831621809185817867864690983198, 3, 0, 1, 0⟩
theorem s4_812_edges : next config 4 s4_812 = [s5_786, s5_839, s5_936] := by decide
theorem s4_812_safe : Safe 9 4 s4_812 := by
  apply safe_succ 8 4 s4_812 [s5_786, s5_839, s5_936] (by decide) s4_812_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_786_safe
  · subst z; exact s5_839_safe
  · subst z; exact s5_936_safe
def s4_813 : State := ⟨[9,4,64,145], 44601830679428167221534918366648232784888598, 1, 1, 1, 0⟩
theorem s4_813_edges : next config 4 s4_813 = [s5_938] := by decide
theorem s4_813_safe : Safe 9 4 s4_813 := by
  apply safe_succ 8 4 s4_813 [s5_938] (by decide) s4_813_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_938_safe
def s4_814 : State := ⟨[9,4,64,171], 2999001359804714199988565969051148076115210423829270, 1, 0, 1, 0⟩
theorem s4_814_edges : next config 4 s4_814 = [s5_41, s5_939] := by decide
theorem s4_814_safe : Safe 9 4 s4_814 := by
  apply safe_succ 8 4 s4_814 [s5_41, s5_939] (by decide) s4_814_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_41_safe
  · subst z; exact s5_939_safe
def s4_815 : State := ⟨[9,4,64,171], 3000462861440683973439085900030010860705139283526422, 1, 0, 1, 0⟩
theorem s4_815_edges : next config 4 s4_815 = [s5_42, s5_940] := by decide
theorem s4_815_safe : Safe 9 4 s4_815 := by
  apply safe_succ 8 4 s4_815 [s5_42, s5_940] (by decide) s4_815_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_42_safe
  · subst z; exact s5_940_safe
def s4_816 : State := ⟨[9,4,96,145], 44602511244162088326624359380200689865130774, 1, 0, 1, 0⟩
theorem s4_816_edges : next config 4 s4_816 = [s5_203, s5_941] := by decide
theorem s4_816_safe : Safe 9 4 s4_816 := by
  apply safe_succ 8 4 s4_816 [s5_203, s5_941] (by decide) s4_816_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_203_safe
  · subst z; exact s5_941_safe
def s4_817 : State := ⟨[9,4,96,145], 66902575877958869591233150903634187834688278, 1, 0, 1, 0⟩
theorem s4_817_edges : next config 4 s4_817 = [s5_211, s5_942] := by decide
theorem s4_817_safe : Safe 9 4 s4_817 := by
  apply safe_succ 8 4 s4_817 [s5_211, s5_942] (by decide) s4_817_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_211_safe
  · subst z; exact s5_942_safe
def s4_818 : State := ⟨[9,4,96,162], 5846006551025023507498659810714716197454119764758, 1, 0, 1, 0⟩
theorem s4_818_edges : next config 4 s4_818 = [s5_1588, s5_234, s5_943, s5_939] := by decide
theorem s4_818_safe : Safe 9 4 s4_818 := by
  apply safe_succ 8 4 s4_818 [s5_1588, s5_234, s5_943, s5_939] (by decide) s4_818_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1588_safe
  · subst z; exact s5_234_safe
  · subst z; exact s5_943_safe
  · subst z; exact s5_939_safe
def s4_819 : State := ⟨[9,4,96,162], 7307508186994796958018590789577500787382979461910, 1, 0, 1, 0⟩
theorem s4_819_edges : next config 4 s4_819 = [s5_1589, s5_241, s5_944, s5_940] := by decide
theorem s4_819_safe : Safe 9 4 s4_819 := by
  apply safe_succ 8 4 s4_819 [s5_1589, s5_241, s5_944, s5_940] (by decide) s4_819_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1589_safe
  · subst z; exact s5_241_safe
  · subst z; exact s5_944_safe
  · subst z; exact s5_940_safe
def s4_820 : State := ⟨[9,4,104,129], 1020847121124453156574505327914104455958, 1, 0, 1, 0⟩
theorem s4_820_edges : next config 4 s4_820 = [s5_330, s5_941] := by decide
theorem s4_820_safe : Safe 9 4 s4_820 := by
  apply safe_succ 8 4 s4_820 [s5_330, s5_941] (by decide) s4_820_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_330_safe
  · subst z; exact s5_941_safe
def s4_821 : State := ⟨[9,4,104,130], 1701411854966330083501254542777640878870, 1, 0, 1, 0⟩
theorem s4_821_edges : next config 4 s4_821 = [s5_339, s5_943] := by decide
theorem s4_821_safe : Safe 9 4 s4_821 := by
  apply safe_succ 8 4 s4_821 [s5_339, s5_943] (by decide) s4_821_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_339_safe
  · subst z; exact s5_943_safe
def s4_822 : State := ⟨[9,4,104,132], 5784800258017591645061749831958859416342, 1, 0, 1, 0⟩
theorem s4_822_edges : next config 4 s4_822 = [s5_350] := by decide
theorem s4_822_safe : Safe 9 4 s4_822 := by
  apply safe_succ 8 4 s4_822 [s5_350] (by decide) s4_822_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_350_safe
def s4_823 : State := ⟨[9,4,104,136], 87452568319042822876271655615583230165782, 1, 0, 1, 0⟩
theorem s4_823_edges : next config 4 s4_823 = [s5_359] := by decide
theorem s4_823_safe : Safe 9 4 s4_823 := by
  apply safe_succ 8 4 s4_823 [s5_359] (by decide) s4_823_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_359_safe
def s4_824 : State := ⟨[9,4,104,137], 174564854250803069522895555118115892298518, 1, 0, 1, 0⟩
theorem s4_824_edges : next config 4 s4_824 = [s5_369] := by decide
theorem s4_824_safe : Safe 9 4 s4_824 := by
  apply safe_succ 8 4 s4_824 [s5_369] (by decide) s4_824_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_369_safe
def s4_825 : State := ⟨[9,4,104,144], 22301085480917905717765366028761412074013462, 1, 0, 1, 0⟩
theorem s4_825_edges : next config 4 s4_825 = [s5_372] := by decide
theorem s4_825_safe : Safe 9 4 s4_825 := by
  apply safe_succ 8 4 s4_825 [s5_372] (by decide) s4_825_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_372_safe
def s4_826 : State := ⟨[9,4,104,160], 1461501637671185305486261062364039132706500576022, 1, 0, 1, 0⟩
theorem s4_826_edges : next config 4 s4_826 = [s5_384, s5_944] := by decide
theorem s4_826_safe : Safe 9 4 s4_826 := by
  apply safe_succ 8 4 s4_826 [s5_384, s5_944] (by decide) s4_826_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_384_safe
  · subst z; exact s5_944_safe
def s4_827 : State := ⟨[9,4,104,192], 6277101735386680764176071810490242645750111557514602545942, 1, 0, 1, 0⟩
theorem s4_827_edges : next config 4 s4_827 = [s5_407] := by decide
theorem s4_827_safe : Safe 9 4 s4_827 := by
  apply safe_succ 8 4 s4_827 [s5_407] (by decide) s4_827_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_407_safe
def s4_828 : State := ⟨[9,4,104,224], 26959946667150639794667015087359913060919720652188328594154178282262, 1, 0, 1, 0⟩
theorem s4_828_edges : next config 4 s4_828 = [s5_428] := by decide
theorem s4_828_safe : Safe 9 4 s4_828 := by
  apply safe_succ 8 4 s4_828 [s5_428] (by decide) s4_828_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_428_safe
def s4_829 : State := ⟨[9,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791832342, 1, 0, 1, 0⟩
theorem s4_829_edges : next config 4 s4_829 = [s5_441] := by decide
theorem s4_829_safe : Safe 9 4 s4_829 := by
  apply safe_succ 8 4 s4_829 [s5_441] (by decide) s4_829_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_441_safe
def s4_830 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232784888094, 1, 1, 1, 0⟩
theorem s4_830_edges : next config 4 s4_830 = [s5_1106, s5_1131, s5_1360, s5_1039, s5_1014, s5_977] := by decide
theorem s4_830_safe : Safe 9 4 s4_830 := by
  apply safe_succ 8 4 s4_830 [s5_1106, s5_1131, s5_1360, s5_1039, s5_1014, s5_977] (by decide) s4_830_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1106_safe
  · subst z; exact s5_1131_safe
  · subst z; exact s5_1360_safe
  · subst z; exact s5_1039_safe
  · subst z; exact s5_1014_safe
  · subst z; exact s5_977_safe
def s4_831 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232784888598, 1, 1, 1, 0⟩
theorem s4_831_edges : next config 4 s4_831 = [s5_1107, s5_1040, s5_978] := by decide
theorem s4_831_safe : Safe 9 4 s4_831 := by
  apply safe_succ 8 4 s4_831 [s5_1107, s5_1040, s5_978] (by decide) s4_831_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1107_safe
  · subst z; exact s5_1040_safe
  · subst z; exact s5_978_safe
def s4_832 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232784892182, 3, 2, 1, 0⟩
theorem s4_832_edges : next config 4 s4_832 = [s5_1108, s5_1479, s5_23, s5_1361, s5_1041, s5_967, s5_1011, s5_955, s5_965, s5_979] := by decide
theorem s4_832_safe : Safe 9 4 s4_832 := by
  apply safe_succ 8 4 s4_832 [s5_1108, s5_1479, s5_23, s5_1361, s5_1041, s5_967, s5_1011, s5_955, s5_965, s5_979] (by decide) s4_832_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1108_safe
  · subst z; exact s5_1479_safe
  · subst z; exact s5_23_safe
  · subst z; exact s5_1361_safe
  · subst z; exact s5_1041_safe
  · subst z; exact s5_967_safe
  · subst z; exact s5_1011_safe
  · subst z; exact s5_955_safe
  · subst z; exact s5_965_safe
  · subst z; exact s5_979_safe
def s4_833 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232786985238, 3, 2, 1, 0⟩
theorem s4_833_edges : next config 4 s4_833 = [s5_1480, s5_1132, s5_24, s5_1362, s5_1089, s5_1015, s5_968, s5_964, s5_1012, s5_956, s5_966, s5_980] := by decide
theorem s4_833_safe : Safe 9 4 s4_833 := by
  apply safe_succ 8 4 s4_833 [s5_1480, s5_1132, s5_24, s5_1362, s5_1089, s5_1015, s5_968, s5_964, s5_1012, s5_956, s5_966, s5_980] (by decide) s4_833_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1480_safe
  · subst z; exact s5_1132_safe
  · subst z; exact s5_24_safe
  · subst z; exact s5_1362_safe
  · subst z; exact s5_1089_safe
  · subst z; exact s5_1015_safe
  · subst z; exact s5_968_safe
  · subst z; exact s5_964_safe
  · subst z; exact s5_1012_safe
  · subst z; exact s5_956_safe
  · subst z; exact s5_966_safe
  · subst z; exact s5_980_safe
def s4_834 : State := ⟨[17,4,64,145], 44601830679428167221534918366648241374822678, 1, 1, 1, 0⟩
theorem s4_834_edges : next config 4 s4_834 = [s5_1109, s5_1042, s5_1016, s5_981] := by decide
theorem s4_834_safe : Safe 9 4 s4_834 := by
  apply safe_succ 8 4 s4_834 [s5_1109, s5_1042, s5_1016, s5_981] (by decide) s4_834_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1109_safe
  · subst z; exact s5_1042_safe
  · subst z; exact s5_1016_safe
  · subst z; exact s5_981_safe
def s4_835 : State := ⟨[17,4,64,145], 44601830679428167221534955260136380203991318, 1, 1, 1, 0⟩
theorem s4_835_edges : next config 4 s4_835 = [s5_1110, s5_1133, s5_1043, s5_1017, s5_982] := by decide
theorem s4_835_safe : Safe 9 4 s4_835 := by
  apply safe_succ 8 4 s4_835 [s5_1110, s5_1133, s5_1043, s5_1017, s5_982] (by decide) s4_835_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1110_safe
  · subst z; exact s5_1133_safe
  · subst z; exact s5_1043_safe
  · subst z; exact s5_1017_safe
  · subst z; exact s5_982_safe
def s4_836 : State := ⟨[17,4,64,145], 44601830679428167221535213514553412137713942, 3, 2, 1, 0⟩
theorem s4_836_edges : next config 4 s4_836 = [s5_1111, s5_25, s5_1044, s5_983] := by decide
theorem s4_836_safe : Safe 9 4 s4_836 := by
  apply safe_succ 8 4 s4_836 [s5_1111, s5_25, s5_1044, s5_983] (by decide) s4_836_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1111_safe
  · subst z; exact s5_25_safe
  · subst z; exact s5_1044_safe
  · subst z; exact s5_983_safe
def s4_837 : State := ⟨[17,4,65,128], 340282366920938463518714839657192034582, 3, 2, 0, 0⟩
theorem s4_837_edges : next config 4 s4_837 = [s5_1045, s5_957, s5_953] := by decide
theorem s4_837_safe : Safe 9 4 s4_837 := by
  apply safe_succ 8 4 s4_837 [s5_1045, s5_957, s5_953] (by decide) s4_837_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1045_safe
  · subst z; exact s5_957_safe
  · subst z; exact s5_953_safe
def s4_838 : State := ⟨[17,4,65,128], 340282366920938463518714839657194127638, 3, 2, 0, 0⟩
theorem s4_838_edges : next config 4 s4_838 = [s5_1018, s5_958, s5_954] := by decide
theorem s4_838_safe : Safe 9 4 s4_838 := by
  apply safe_succ 8 4 s4_838 [s5_1018, s5_958, s5_954] (by decide) s4_838_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1018_safe
  · subst z; exact s5_958_safe
  · subst z; exact s5_954_safe
def s4_839 : State := ⟨[17,4,66,128], 340282366920938463555608327804611137814, 3, 2, 0, 0⟩
theorem s4_839_edges : next config 4 s4_839 = [s5_1046, s5_969, s5_955] := by decide
theorem s4_839_safe : Safe 9 4 s4_839 := by
  apply safe_succ 8 4 s4_839 [s5_1046, s5_969, s5_955] (by decide) s4_839_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1046_safe
  · subst z; exact s5_969_safe
  · subst z; exact s5_955_safe
def s4_840 : State := ⟨[17,4,66,128], 340282366920938463555608327804613230870, 3, 2, 0, 0⟩
theorem s4_840_edges : next config 4 s4_840 = [s5_1019, s5_970, s5_956] := by decide
theorem s4_840_safe : Safe 9 4 s4_840 := by
  apply safe_succ 8 4 s4_840 [s5_1019, s5_970, s5_956] (by decide) s4_840_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1019_safe
  · subst z; exact s5_970_safe
  · subst z; exact s5_956_safe
def s4_841 : State := ⟨[17,4,67,128], 340282366920938463629395304099449340190, 1, 1, 0, 0⟩
theorem s4_841_edges : next config 4 s4_841 = [s5_1047, s5_1020, s5_961] := by decide
theorem s4_841_safe : Safe 9 4 s4_841 := by
  apply safe_succ 8 4 s4_841 [s5_1047, s5_1020, s5_961] (by decide) s4_841_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1047_safe
  · subst z; exact s5_1020_safe
  · subst z; exact s5_961_safe
def s4_842 : State := ⟨[17,4,67,128], 340282366920943299406460738910986371350, 1, 0, 0, 0⟩
theorem s4_842_edges : next config 4 s4_842 = [s5_1048, s5_1021, s5_962] := by decide
theorem s4_842_safe : Safe 9 4 s4_842 := by
  apply safe_succ 8 4 s4_842 [s5_1048, s5_1021, s5_962] (by decide) s4_842_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1048_safe
  · subst z; exact s5_1021_safe
  · subst z; exact s5_962_safe
def s4_843 : State := ⟨[17,4,67,128], 340282366920944508258493377245322871062, 1, 0, 0, 0⟩
theorem s4_843_edges : next config 4 s4_843 = [s5_1049, s5_1022, s5_963] := by decide
theorem s4_843_safe : Safe 9 4 s4_843 := by
  apply safe_succ 8 4 s4_843 [s5_1049, s5_1022, s5_963] (by decide) s4_843_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1049_safe
  · subst z; exact s5_1022_safe
  · subst z; exact s5_963_safe
def s4_844 : State := ⟨[17,4,67,145], 44601830679428167221535102834088969880404246, 1, 0, 1, 0⟩
theorem s4_844_edges : next config 4 s4_844 = [s5_1112, s5_1484, s5_1134, s5_103, s5_1050, s5_1023] := by decide
theorem s4_844_safe : Safe 9 4 s4_844 := by
  apply safe_succ 8 4 s4_844 [s5_1112, s5_1484, s5_1134, s5_103, s5_1050, s5_1023] (by decide) s4_844_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1112_safe
  · subst z; exact s5_1484_safe
  · subst z; exact s5_1134_safe
  · subst z; exact s5_103_safe
  · subst z; exact s5_1050_safe
  · subst z; exact s5_1023_safe
def s4_845 : State := ⟨[17,4,67,145], 44601830679428167221535139727577117299507478, 1, 0, 1, 0⟩
theorem s4_845_edges : next config 4 s4_845 = [s5_1113, s5_1485, s5_1135, s5_104, s5_1051, s5_1024] := by decide
theorem s4_845_safe : Safe 9 4 s4_845 := by
  apply safe_succ 8 4 s4_845 [s5_1113, s5_1485, s5_1135, s5_104, s5_1051, s5_1024] (by decide) s4_845_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1113_safe
  · subst z; exact s5_1485_safe
  · subst z; exact s5_1135_safe
  · subst z; exact s5_104_safe
  · subst z; exact s5_1051_safe
  · subst z; exact s5_1024_safe
def s4_846 : State := ⟨[17,4,68,128], 340282366920938463776969256689127850262, 3, 2, 0, 0⟩
theorem s4_846_edges : next config 4 s4_846 = [s5_964] := by decide
theorem s4_846_safe : Safe 9 4 s4_846 := by
  apply safe_succ 8 4 s4_846 [s5_964] (by decide) s4_846_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_964_safe
def s4_847 : State := ⟨[17,4,80,128], 340282366920939672407640966138947637526, 3, 2, 0, 0⟩
theorem s4_847_edges : next config 4 s4_847 = [s5_1052, s5_971, s5_965] := by decide
theorem s4_847_safe : Safe 9 4 s4_847 := by
  apply safe_succ 8 4 s4_847 [s5_1052, s5_971, s5_965] (by decide) s4_847_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1052_safe
  · subst z; exact s5_971_safe
  · subst z; exact s5_965_safe
def s4_848 : State := ⟨[17,4,80,128], 340282366920939672407640966138949730582, 3, 2, 0, 0⟩
theorem s4_848_edges : next config 4 s4_848 = [s5_1025, s5_972, s5_966] := by decide
theorem s4_848_safe : Safe 9 4 s4_848 := by
  apply safe_succ 8 4 s4_848 [s5_1025, s5_972, s5_966] (by decide) s4_848_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1025_safe
  · subst z; exact s5_972_safe
  · subst z; exact s5_966_safe
def s4_849 : State := ⟨[17,4,81,128], 340282366920940881333460580768122343702, 3, 2, 0, 0⟩
theorem s4_849_edges : next config 4 s4_849 = [s5_1053, s5_967] := by decide
theorem s4_849_safe : Safe 9 4 s4_849 := by
  apply safe_succ 8 4 s4_849 [s5_1053, s5_967] (by decide) s4_849_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1053_safe
  · subst z; exact s5_967_safe
def s4_850 : State := ⟨[17,4,81,128], 340282366920940881333460580768124436758, 3, 2, 0, 0⟩
theorem s4_850_edges : next config 4 s4_850 = [s5_1026, s5_968] := by decide
theorem s4_850_safe : Safe 9 4 s4_850 := by
  apply safe_succ 8 4 s4_850 [s5_1026, s5_968] (by decide) s4_850_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1026_safe
  · subst z; exact s5_968_safe
def s4_851 : State := ⟨[17,4,82,145], 44601830679428167226370695432083044321919254, 1, 0, 1, 0⟩
theorem s4_851_edges : next config 4 s4_851 = [s5_1114, s5_158, s5_1054, s5_1096, s5_1027, s5_962, s5_975] := by decide
theorem s4_851_safe : Safe 9 4 s4_851 := by
  apply safe_succ 8 4 s4_851 [s5_1114, s5_158, s5_1054, s5_1096, s5_1027, s5_962, s5_975] (by decide) s4_851_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1114_safe
  · subst z; exact s5_158_safe
  · subst z; exact s5_1054_safe
  · subst z; exact s5_1096_safe
  · subst z; exact s5_1027_safe
  · subst z; exact s5_962_safe
  · subst z; exact s5_975_safe
def s4_852 : State := ⟨[17,4,82,145], 44601830679428167227579547464721378658418966, 1, 0, 1, 0⟩
theorem s4_852_edges : next config 4 s4_852 = [s5_1115, s5_159, s5_1055, s5_1097, s5_1028, s5_963, s5_976] := by decide
theorem s4_852_safe : Safe 9 4 s4_852 := by
  apply safe_succ 8 4 s4_852 [s5_1115, s5_159, s5_1055, s5_1097, s5_1028, s5_963, s5_976] (by decide) s4_852_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1115_safe
  · subst z; exact s5_159_safe
  · subst z; exact s5_1055_safe
  · subst z; exact s5_1097_safe
  · subst z; exact s5_1028_safe
  · subst z; exact s5_963_safe
  · subst z; exact s5_976_safe
def s4_853 : State := ⟨[17,4,86,128], 340282366921020670511342122588491153686, 1, 0, 0, 0⟩
theorem s4_853_edges : next config 4 s4_853 = [s5_1056, s5_975] := by decide
theorem s4_853_safe : Safe 9 4 s4_853 := by
  apply safe_succ 8 4 s4_853 [s5_1056, s5_975] (by decide) s4_853_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1056_safe
  · subst z; exact s5_975_safe
def s4_854 : State := ⟨[17,4,86,128], 340282366921021879363374760922827653398, 1, 0, 0, 0⟩
theorem s4_854_edges : next config 4 s4_854 = [s5_1057, s5_976] := by decide
theorem s4_854_safe : Safe 9 4 s4_854 := by
  apply safe_succ 8 4 s4_854 [s5_1057, s5_976] (by decide) s4_854_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1057_safe
  · subst z; exact s5_976_safe
def s4_855 : State := ⟨[17,4,96,128], 340282367000166625996085689103316877598, 1, 1, 0, 0⟩
theorem s4_855_edges : next config 4 s4_855 = [s5_1058, s5_1098, s5_1029, s5_1004, s5_988, s5_991, s5_977] := by decide
theorem s4_855_safe : Safe 9 4 s4_855 := by
  apply safe_succ 8 4 s4_855 [s5_1058, s5_1098, s5_1029, s5_1004, s5_988, s5_991, s5_977] (by decide) s4_855_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1058_safe
  · subst z; exact s5_1098_safe
  · subst z; exact s5_1029_safe
  · subst z; exact s5_1004_safe
  · subst z; exact s5_988_safe
  · subst z; exact s5_991_safe
  · subst z; exact s5_977_safe
def s4_856 : State := ⟨[17,4,96,128], 340282367000166625996085689103316878102, 1, 1, 0, 0⟩
theorem s4_856_edges : next config 4 s4_856 = [s5_1059, s5_992, s5_978] := by decide
theorem s4_856_safe : Safe 9 4 s4_856 := by
  apply safe_succ 8 4 s4_856 [s5_1059, s5_992, s5_978] (by decide) s4_856_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1059_safe
  · subst z; exact s5_992_safe
  · subst z; exact s5_978_safe
def s4_857 : State := ⟨[17,4,96,128], 340282367000166625996085689103316881686, 3, 2, 0, 0⟩
theorem s4_857_edges : next config 4 s4_857 = [s5_1060, s5_1005, s5_993, s5_1002, s5_979] := by decide
theorem s4_857_safe : Safe 9 4 s4_857 := by
  apply safe_succ 8 4 s4_857 [s5_1060, s5_1005, s5_993, s5_1002, s5_979] (by decide) s4_857_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1060_safe
  · subst z; exact s5_1005_safe
  · subst z; exact s5_993_safe
  · subst z; exact s5_1002_safe
  · subst z; exact s5_979_safe
def s4_858 : State := ⟨[17,4,96,128], 340282367000166625996085689103318974742, 3, 2, 0, 0⟩
theorem s4_858_edges : next config 4 s4_858 = [s5_1099, s5_1030, s5_1006, s5_989, s5_994, s5_1003, s5_980] := by decide
theorem s4_858_safe : Safe 9 4 s4_858 := by
  apply safe_succ 8 4 s4_858 [s5_1099, s5_1030, s5_1006, s5_989, s5_994, s5_1003, s5_980] (by decide) s4_858_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1099_safe
  · subst z; exact s5_1030_safe
  · subst z; exact s5_1006_safe
  · subst z; exact s5_989_safe
  · subst z; exact s5_994_safe
  · subst z; exact s5_1003_safe
  · subst z; exact s5_980_safe
def s4_859 : State := ⟨[17,4,96,128], 340282367000166625996085689111906812182, 1, 1, 0, 0⟩
theorem s4_859_edges : next config 4 s4_859 = [s5_1061, s5_1031, s5_995, s5_981] := by decide
theorem s4_859_safe : Safe 9 4 s4_859 := by
  apply safe_succ 8 4 s4_859 [s5_1061, s5_1031, s5_995, s5_981] (by decide) s4_859_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1061_safe
  · subst z; exact s5_1031_safe
  · subst z; exact s5_995_safe
  · subst z; exact s5_981_safe
def s4_860 : State := ⟨[17,4,96,128], 340282367000166626032979177250735980822, 1, 1, 0, 0⟩
theorem s4_860_edges : next config 4 s4_860 = [s5_1062, s5_1100, s5_1032, s5_1007, s5_990, s5_996, s5_982] := by decide
theorem s4_860_safe : Safe 9 4 s4_860 := by
  apply safe_succ 8 4 s4_860 [s5_1062, s5_1100, s5_1032, s5_1007, s5_990, s5_996, s5_982] (by decide) s4_860_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1062_safe
  · subst z; exact s5_1100_safe
  · subst z; exact s5_1032_safe
  · subst z; exact s5_1007_safe
  · subst z; exact s5_990_safe
  · subst z; exact s5_996_safe
  · subst z; exact s5_982_safe
def s4_861 : State := ⟨[17,4,96,128], 340282367000166626291233594282669703446, 3, 2, 0, 0⟩
theorem s4_861_edges : next config 4 s4_861 = [s5_1063, s5_997, s5_983] := by decide
theorem s4_861_safe : Safe 9 4 s4_861 := by
  apply safe_succ 8 4 s4_861 [s5_1063, s5_997, s5_983] (by decide) s4_861_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1063_safe
  · subst z; exact s5_997_safe
  · subst z; exact s5_983_safe
def s4_862 : State := ⟨[17,4,96,128], 340282367158622951024614364290404778262, 1, 1, 0, 0⟩
theorem s4_862_edges : next config 4 s4_862 = [s5_1064, s5_1033, s5_998, s5_984] := by decide
theorem s4_862_safe : Safe 9 4 s4_862 := by
  apply safe_succ 8 4 s4_862 [s5_1064, s5_1033, s5_998, s5_984] (by decide) s4_862_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1064_safe
  · subst z; exact s5_1033_safe
  · subst z; exact s5_998_safe
  · subst z; exact s5_984_safe
def s4_863 : State := ⟨[17,4,96,128], 340282368267817226224315090600020082966, 3, 2, 0, 0⟩
theorem s4_863_edges : next config 4 s4_863 = [s5_1065, s5_999, s5_985] := by decide
theorem s4_863_safe : Safe 9 4 s4_863 := by
  apply safe_succ 8 4 s4_863 [s5_1065, s5_999, s5_985] (by decide) s4_863_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1065_safe
  · subst z; exact s5_999_safe
  · subst z; exact s5_985_safe
def s4_864 : State := ⟨[17,4,97,145], 44601830679428404906022461159661013416739094, 1, 0, 1, 0⟩
theorem s4_864_edges : next config 4 s4_864 = [s5_1116, s5_301, s5_1066, s5_1034] := by decide
theorem s4_864_safe : Safe 9 4 s4_864 := by
  apply safe_succ 8 4 s4_864 [s5_1116, s5_301, s5_1066, s5_1034] (by decide) s4_864_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1116_safe
  · subst z; exact s5_301_safe
  · subst z; exact s5_1066_safe
  · subst z; exact s5_1034_safe
def s4_865 : State := ⟨[17,4,100,145], 44601830679429514100297660860387323032043798, 1, 0, 1, 0⟩
theorem s4_865_edges : next config 4 s4_865 = [s5_1117, s5_318, s5_1067] := by decide
theorem s4_865_safe : Safe 9 4 s4_865 := by
  apply safe_succ 8 4 s4_865 [s5_1117, s5_318, s5_1067] (by decide) s4_865_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1117_safe
  · subst z; exact s5_318_safe
  · subst z; exact s5_1067_safe
def s4_866 : State := ⟨[17,4,104,145], 44601830679448528859301084301409773580124438, 1, 0, 1, 0⟩
theorem s4_866_edges : next config 4 s4_866 = [s5_1118, s5_1539, s5_1136, s5_380, s5_1363, s5_1068, s5_1102, s5_1035, s5_1010, s5_1001, s5_1013, s5_1009] := by decide
theorem s4_866_safe : Safe 9 4 s4_866 := by
  apply safe_succ 8 4 s4_866 [s5_1118, s5_1539, s5_1136, s5_380, s5_1363, s5_1068, s5_1102, s5_1035, s5_1010, s5_1001, s5_1013, s5_1009] (by decide) s4_866_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1118_safe
  · subst z; exact s5_1539_safe
  · subst z; exact s5_1136_safe
  · subst z; exact s5_380_safe
  · subst z; exact s5_1363_safe
  · subst z; exact s5_1068_safe
  · subst z; exact s5_1102_safe
  · subst z; exact s5_1035_safe
  · subst z; exact s5_1010_safe
  · subst z; exact s5_1001_safe
  · subst z; exact s5_1013_safe
  · subst z; exact s5_1009_safe
def s4_867 : State := ⟨[17,4,108,128], 340282711801129888074482896206588739862, 1, 0, 0, 0⟩
theorem s4_867_edges : next config 4 s4_867 = [s5_1069, s5_1001] := by decide
theorem s4_867_safe : Safe 9 4 s4_867 := by
  apply safe_succ 8 4 s4_867 [s5_1069, s5_1001] (by decide) s4_867_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1069_safe
  · subst z; exact s5_1001_safe
def s4_868 : State := ⟨[17,4,112,145], 44601830684620543308232260259516322658058518, 1, 0, 1, 0⟩
theorem s4_868_edges : next config 4 s4_868 = [s5_1119, s5_476, s5_1070, s5_1036] := by decide
theorem s4_868_safe : Safe 9 4 s4_868 := by
  apply safe_succ 8 4 s4_868 [s5_1119, s5_476, s5_1070, s5_1036] (by decide) s4_868_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1119_safe
  · subst z; exact s5_476_safe
  · subst z; exact s5_1070_safe
  · subst z; exact s5_1036_safe
def s4_869 : State := ⟨[17,4,113,145], 44601830689812840166767087888046818987278614, 1, 0, 1, 0⟩
theorem s4_869_edges : next config 4 s4_869 = [s5_1120, s5_481, s5_1071, s5_1037] := by decide
theorem s4_869_safe : Safe 9 4 s4_869 := by
  apply safe_succ 8 4 s4_869 [s5_1120, s5_481, s5_1071, s5_1037] (by decide) s4_869_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1120_safe
  · subst z; exact s5_481_safe
  · subst z; exact s5_1071_safe
  · subst z; exact s5_1037_safe
def s4_870 : State := ⟨[17,4,120,128], 341611615278361145520659920110848508182, 1, 0, 0, 0⟩
theorem s4_870_edges : next config 4 s4_870 = [s5_1073, s5_1009] := by decide
theorem s4_870_safe : Safe 9 4 s4_870 := by
  apply safe_succ 8 4 s4_870 [s5_1073, s5_1009] (by decide) s4_870_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1073_safe
  · subst z; exact s5_1009_safe
def s4_871 : State := ⟨[17,4,121,128], 342940843274146061393563727171128852758, 1, 0, 0, 0⟩
theorem s4_871_edges : next config 4 s4_871 = [s5_1074, s5_1010] := by decide
theorem s4_871_safe : Safe 9 4 s4_871 := by
  apply safe_succ 8 4 s4_871 [s5_1074, s5_1010] (by decide) s4_871_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1074_safe
  · subst z; exact s5_1010_safe
def s4_872 : State := ⟨[17,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914077974, 1, 0, 1, 0⟩
theorem s4_872_edges : next config 4 s4_872 = [s5_1122, s5_515, s5_1076, s5_1038] := by decide
theorem s4_872_safe : Safe 9 4 s4_872 := by
  apply safe_succ 8 4 s4_872 [s5_1122, s5_515, s5_1076, s5_1038] (by decide) s4_872_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1122_safe
  · subst z; exact s5_515_safe
  · subst z; exact s5_1076_safe
  · subst z; exact s5_1038_safe
def s4_873 : State := ⟨[17,12,64,128], 340282366920938463481821351509772931358, 3, 1, 0, 0⟩
theorem s4_873_edges : next config 4 s4_873 = [s5_946, s5_1029, s5_1014] := by decide
theorem s4_873_safe : Safe 9 4 s4_873 := by
  apply safe_succ 8 4 s4_873 [s5_946, s5_1029, s5_1014] (by decide) s4_873_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_946_safe
  · subst z; exact s5_1029_safe
  · subst z; exact s5_1014_safe
def s4_874 : State := ⟨[17,12,64,128], 340282366920938463481821351509775028502, 3, 2, 0, 0⟩
theorem s4_874_edges : next config 4 s4_874 = [s5_1026, s5_1019, s5_1025, s5_1030, s5_1015] := by decide
theorem s4_874_safe : Safe 9 4 s4_874 := by
  apply safe_succ 8 4 s4_874 [s5_1026, s5_1019, s5_1025, s5_1030, s5_1015] (by decide) s4_874_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1026_safe
  · subst z; exact s5_1019_safe
  · subst z; exact s5_1025_safe
  · subst z; exact s5_1030_safe
  · subst z; exact s5_1015_safe
def s4_875 : State := ⟨[17,12,64,128], 340282366920938463481821351518362865942, 3, 1, 0, 0⟩
theorem s4_875_edges : next config 4 s4_875 = [s5_949, s5_1031, s5_1016] := by decide
theorem s4_875_safe : Safe 9 4 s4_875 := by
  apply safe_succ 8 4 s4_875 [s5_949, s5_1031, s5_1016] (by decide) s4_875_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_949_safe
  · subst z; exact s5_1031_safe
  · subst z; exact s5_1016_safe
def s4_876 : State := ⟨[17,12,64,128], 340282366920938463518714839657192034582, 3, 1, 0, 0⟩
theorem s4_876_edges : next config 4 s4_876 = [s5_951, s5_1032, s5_1017] := by decide
theorem s4_876_safe : Safe 9 4 s4_876 := by
  apply safe_succ 8 4 s4_876 [s5_951, s5_1032, s5_1017] (by decide) s4_876_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_951_safe
  · subst z; exact s5_1032_safe
  · subst z; exact s5_1017_safe
def s4_877 : State := ⟨[17,12,65,145], 44601830679428167221534955260136380203995414, 3, 0, 1, 0⟩
theorem s4_877_edges : next config 4 s4_877 = [s5_545, s5_953, s5_1023] := by decide
theorem s4_877_safe : Safe 9 4 s4_877 := by
  apply safe_succ 8 4 s4_877 [s5_545, s5_953, s5_1023] (by decide) s4_877_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_545_safe
  · subst z; exact s5_953_safe
  · subst z; exact s5_1023_safe
def s4_878 : State := ⟨[17,12,66,145], 44601830679428167221534992153624527623098646, 3, 0, 1, 0⟩
theorem s4_878_edges : next config 4 s4_878 = [s5_546, s5_955, s5_1027] := by decide
theorem s4_878_safe : Safe 9 4 s4_878 := by
  apply safe_succ 8 4 s4_878 [s5_546, s5_955, s5_1027] (by decide) s4_878_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_546_safe
  · subst z; exact s5_955_safe
  · subst z; exact s5_1027_safe
def s4_879 : State := ⟨[17,12,67,128], 340282366920938463666288792246868447510, 3, 0, 0, 0⟩
theorem s4_879_edges : next config 4 s4_879 = [s5_957, s5_1023] := by decide
theorem s4_879_safe : Safe 9 4 s4_879 := by
  apply safe_succ 8 4 s4_879 [s5_957, s5_1023] (by decide) s4_879_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_957_safe
  · subst z; exact s5_1023_safe
def s4_880 : State := ⟨[17,12,67,128], 340282366920938463703182280394287550742, 3, 0, 0, 0⟩
theorem s4_880_edges : next config 4 s4_880 = [s5_959, s5_1024] := by decide
theorem s4_880_safe : Safe 9 4 s4_880 := by
  apply safe_succ 8 4 s4_880 [s5_959, s5_1024] (by decide) s4_880_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_959_safe
  · subst z; exact s5_1024_safe
def s4_881 : State := ⟨[17,12,80,145], 44601830679428167222743844186262861959598358, 3, 0, 1, 0⟩
theorem s4_881_edges : next config 4 s4_881 = [s5_575, s5_965, s5_1028] := by decide
theorem s4_881_safe : Safe 9 4 s4_881 := by
  apply safe_succ 8 4 s4_881 [s5_575, s5_965, s5_1028] (by decide) s4_881_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_575_safe
  · subst z; exact s5_965_safe
  · subst z; exact s5_1028_safe
def s4_882 : State := ⟨[17,12,81,145], 44601830679428167223952770005877491134304534, 3, 0, 1, 0⟩
theorem s4_882_edges : next config 4 s4_882 = [s5_576, s5_967] := by decide
theorem s4_882_safe : Safe 9 4 s4_882 := by
  apply safe_succ 8 4 s4_882 [s5_576, s5_967] (by decide) s4_882_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_576_safe
  · subst z; exact s5_967_safe
def s4_883 : State := ⟨[17,12,82,128], 340282366920943299258886786321309962518, 3, 0, 0, 0⟩
theorem s4_883_edges : next config 4 s4_883 = [s5_969, s5_1021, s5_1027] := by decide
theorem s4_883_safe : Safe 9 4 s4_883 := by
  apply safe_succ 8 4 s4_883 [s5_969, s5_1021, s5_1027] (by decide) s4_883_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_969_safe
  · subst z; exact s5_1021_safe
  · subst z; exact s5_1027_safe
def s4_884 : State := ⟨[17,12,82,128], 340282366920944508110919424655646462230, 3, 0, 0, 0⟩
theorem s4_884_edges : next config 4 s4_884 = [s5_971, s5_1022, s5_1028] := by decide
theorem s4_884_safe : Safe 9 4 s4_884 := by
  apply safe_succ 8 4 s4_884 [s5_971, s5_1022, s5_1028] (by decide) s4_884_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_971_safe
  · subst z; exact s5_1022_safe
  · subst z; exact s5_1028_safe
def s4_885 : State := ⟨[17,12,96,145], 44601830679428246449697432630985826328842518, 3, 0, 1, 0⟩
theorem s4_885_edges : next config 4 s4_885 = [s5_1536, s5_607, s5_1364, s5_979, s5_1037, s5_1038, s5_1035, s5_1036] := by decide
theorem s4_885_safe : Safe 9 4 s4_885 := by
  apply safe_succ 8 4 s4_885 [s5_1536, s5_607, s5_1364, s5_979, s5_1037, s5_1038, s5_1035, s5_1036] (by decide) s4_885_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1536_safe
  · subst z; exact s5_607_safe
  · subst z; exact s5_1364_safe
  · subst z; exact s5_979_safe
  · subst z; exact s5_1037_safe
  · subst z; exact s5_1038_safe
  · subst z; exact s5_1035_safe
  · subst z; exact s5_1036_safe
def s4_886 : State := ⟨[17,12,97,128], 340282367158622951024614364290404782358, 3, 0, 0, 0⟩
theorem s4_886_edges : next config 4 s4_886 = [s5_986, s5_1034] := by decide
theorem s4_886_safe : Safe 9 4 s4_886 := by
  apply safe_succ 8 4 s4_886 [s5_986, s5_1034] (by decide) s4_886_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_986_safe
  · subst z; exact s5_1034_safe
def s4_887 : State := ⟨[17,12,104,128], 340282387282576229647756113050568167702, 3, 0, 0, 0⟩
theorem s4_887_edges : next config 4 s4_887 = [s5_993, s5_1035] := by decide
theorem s4_887_safe : Safe 9 4 s4_887 := by
  apply safe_succ 8 4 s4_887 [s5_993, s5_1035] (by decide) s4_887_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_993_safe
  · subst z; exact s5_1035_safe
def s4_888 : State := ⟨[17,12,112,128], 340287559297025160823714219599646101782, 3, 0, 0, 0⟩
theorem s4_888_edges : next config 4 s4_888 = [s5_1002, s5_1036] := by decide
theorem s4_888_safe : Safe 9 4 s4_888 := by
  apply safe_succ 8 4 s4_888 [s5_1002, s5_1036] (by decide) s4_888_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1002_safe
  · subst z; exact s5_1036_safe
def s4_889 : State := ⟨[17,12,113,128], 340292751593883695651342750095975321878, 3, 0, 0, 0⟩
theorem s4_889_edges : next config 4 s4_889 = [s5_1005, s5_1037] := by decide
theorem s4_889_safe : Safe 9 4 s4_889 := by
  apply safe_succ 8 4 s4_889 [s5_1005, s5_1037] (by decide) s4_889_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1005_safe
  · subst z; exact s5_1037_safe
def s4_890 : State := ⟨[17,12,209,145], 822752278660603021122086421958103419712902851183438164459196694, 3, 0, 1, 0⟩
theorem s4_890_edges : next config 4 s4_890 = [s5_681, s5_1011] := by decide
theorem s4_890_safe : Safe 9 4 s4_890 := by
  apply safe_succ 8 4 s4_890 [s5_681, s5_1011] (by decide) s4_890_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_681_safe
  · subst z; exact s5_1011_safe
def s4_891 : State := ⟨[17,21,64,128], 340282366920938463481821351509775024414, 3, 1, 0, 0⟩
theorem s4_891_edges : next config 4 s4_891 = [s5_947, s5_1077, s5_1086, s5_1058, s5_1039] := by decide
theorem s4_891_safe : Safe 9 4 s4_891 := by
  apply safe_succ 8 4 s4_891 [s5_947, s5_1077, s5_1086, s5_1058, s5_1039] (by decide) s4_891_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_947_safe
  · subst z; exact s5_1077_safe
  · subst z; exact s5_1086_safe
  · subst z; exact s5_1058_safe
  · subst z; exact s5_1039_safe
def s4_892 : State := ⟨[17,21,64,128], 340282366920938463481821351509775024918, 3, 1, 0, 0⟩
theorem s4_892_edges : next config 4 s4_892 = [s5_948, s5_1059, s5_1040] := by decide
theorem s4_892_safe : Safe 9 4 s4_892 := by
  apply safe_succ 8 4 s4_892 [s5_948, s5_1059, s5_1040] (by decide) s4_892_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_948_safe
  · subst z; exact s5_1059_safe
  · subst z; exact s5_1040_safe
def s4_893 : State := ⟨[17,21,64,128], 340282366920938463481821351509775028502, 3, 2, 0, 0⟩
theorem s4_893_edges : next config 4 s4_893 = [s5_1053, s5_1046, s5_1052, s5_1060, s5_1041] := by decide
theorem s4_893_safe : Safe 9 4 s4_893 := by
  apply safe_succ 8 4 s4_893 [s5_1053, s5_1046, s5_1052, s5_1060, s5_1041] (by decide) s4_893_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1053_safe
  · subst z; exact s5_1046_safe
  · subst z; exact s5_1052_safe
  · subst z; exact s5_1060_safe
  · subst z; exact s5_1041_safe
def s4_894 : State := ⟨[17,21,64,128], 340282366920938463481821351518364958998, 3, 1, 0, 0⟩
theorem s4_894_edges : next config 4 s4_894 = [s5_950, s5_1078, s5_1061, s5_1042] := by decide
theorem s4_894_safe : Safe 9 4 s4_894 := by
  apply safe_succ 8 4 s4_894 [s5_950, s5_1078, s5_1061, s5_1042] (by decide) s4_894_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_950_safe
  · subst z; exact s5_1078_safe
  · subst z; exact s5_1061_safe
  · subst z; exact s5_1042_safe
def s4_895 : State := ⟨[17,21,64,128], 340282366920938463518714839657194127638, 3, 1, 0, 0⟩
theorem s4_895_edges : next config 4 s4_895 = [s5_952, s5_1079, s5_1062, s5_1043] := by decide
theorem s4_895_safe : Safe 9 4 s4_895 := by
  apply safe_succ 8 4 s4_895 [s5_952, s5_1079, s5_1062, s5_1043] (by decide) s4_895_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_952_safe
  · subst z; exact s5_1079_safe
  · subst z; exact s5_1062_safe
  · subst z; exact s5_1043_safe
def s4_896 : State := ⟨[17,21,64,128], 340282366920938463776969256689127850262, 3, 2, 0, 0⟩
theorem s4_896_edges : next config 4 s4_896 = [s5_1063, s5_1044] := by decide
theorem s4_896_safe : Safe 9 4 s4_896 := by
  apply safe_succ 8 4 s4_896 [s5_1063, s5_1044] (by decide) s4_896_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1063_safe
  · subst z; exact s5_1044_safe
def s4_897 : State := ⟨[17,21,65,145], 44601830679428167221534955260136380206088470, 3, 0, 1, 0⟩
theorem s4_897_edges : next config 4 s4_897 = [s5_1137, s5_688, s5_954, s5_1080, s5_1050] := by decide
theorem s4_897_safe : Safe 9 4 s4_897 := by
  apply safe_succ 8 4 s4_897 [s5_1137, s5_688, s5_954, s5_1080, s5_1050] (by decide) s4_897_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1137_safe
  · subst z; exact s5_688_safe
  · subst z; exact s5_954_safe
  · subst z; exact s5_1080_safe
  · subst z; exact s5_1050_safe
def s4_898 : State := ⟨[17,21,66,145], 44601830679428167221534992153624527625191702, 3, 0, 1, 0⟩
theorem s4_898_edges : next config 4 s4_898 = [s5_1138, s5_689, s5_956, s5_1081, s5_1054] := by decide
theorem s4_898_safe : Safe 9 4 s4_898 := by
  apply safe_succ 8 4 s4_898 [s5_1138, s5_689, s5_956, s5_1081, s5_1054] (by decide) s4_898_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1138_safe
  · subst z; exact s5_689_safe
  · subst z; exact s5_956_safe
  · subst z; exact s5_1081_safe
  · subst z; exact s5_1054_safe
def s4_899 : State := ⟨[17,21,67,128], 340282366920938463666288792246870540566, 3, 0, 0, 0⟩
theorem s4_899_edges : next config 4 s4_899 = [s5_958, s5_1092, s5_1082, s5_1050] := by decide
theorem s4_899_safe : Safe 9 4 s4_899 := by
  apply safe_succ 8 4 s4_899 [s5_958, s5_1092, s5_1082, s5_1050] (by decide) s4_899_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_958_safe
  · subst z; exact s5_1092_safe
  · subst z; exact s5_1082_safe
  · subst z; exact s5_1050_safe
def s4_900 : State := ⟨[17,21,67,128], 340282366920938463703182280394289643798, 3, 0, 0, 0⟩
theorem s4_900_edges : next config 4 s4_900 = [s5_960, s5_1093, s5_1083, s5_1051] := by decide
theorem s4_900_safe : Safe 9 4 s4_900 := by
  apply safe_succ 8 4 s4_900 [s5_960, s5_1093, s5_1083, s5_1051] (by decide) s4_900_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_960_safe
  · subst z; exact s5_1093_safe
  · subst z; exact s5_1083_safe
  · subst z; exact s5_1051_safe
def s4_901 : State := ⟨[17,21,68,145], 44601830679428167221535213514553412139811094, 3, 0, 1, 0⟩
theorem s4_901_edges : next config 4 s4_901 = [s5_690, s5_964] := by decide
theorem s4_901_safe : Safe 9 4 s4_901 := by
  apply safe_succ 8 4 s4_901 [s5_690, s5_964] (by decide) s4_901_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_690_safe
  · subst z; exact s5_964_safe
def s4_902 : State := ⟨[17,21,80,145], 44601830679428167222743844186262861961691414, 3, 0, 1, 0⟩
theorem s4_902_edges : next config 4 s4_902 = [s5_691, s5_966, s5_1055] := by decide
theorem s4_902_safe : Safe 9 4 s4_902 := by
  apply safe_succ 8 4 s4_902 [s5_691, s5_966, s5_1055] (by decide) s4_902_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_691_safe
  · subst z; exact s5_966_safe
  · subst z; exact s5_1055_safe
def s4_903 : State := ⟨[17,21,81,145], 44601830679428167223952770005877491136397590, 3, 0, 1, 0⟩
theorem s4_903_edges : next config 4 s4_903 = [s5_692, s5_968] := by decide
theorem s4_903_safe : Safe 9 4 s4_903 := by
  apply safe_succ 8 4 s4_903 [s5_692, s5_968] (by decide) s4_903_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_692_safe
  · subst z; exact s5_968_safe
def s4_904 : State := ⟨[17,21,82,128], 340282366920943299258886786321312055574, 3, 0, 0, 0⟩
theorem s4_904_edges : next config 4 s4_904 = [s5_970, s5_1048, s5_1054] := by decide
theorem s4_904_safe : Safe 9 4 s4_904 := by
  apply safe_succ 8 4 s4_904 [s5_970, s5_1048, s5_1054] (by decide) s4_904_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_970_safe
  · subst z; exact s5_1048_safe
  · subst z; exact s5_1054_safe
def s4_905 : State := ⟨[17,21,82,128], 340282366920944508110919424655648555286, 3, 0, 0, 0⟩
theorem s4_905_edges : next config 4 s4_905 = [s5_972, s5_1049, s5_1055] := by decide
theorem s4_905_safe : Safe 9 4 s4_905 := by
  apply safe_succ 8 4 s4_905 [s5_972, s5_1049, s5_1055] (by decide) s4_905_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_972_safe
  · subst z; exact s5_1049_safe
  · subst z; exact s5_1055_safe
def s4_906 : State := ⟨[17,21,96,145], 44601830679428246449697432630985826330935574, 3, 0, 1, 0⟩
theorem s4_906_edges : next config 4 s4_906 = [s5_1537, s5_1139, s5_693, s5_1365, s5_980, s5_1103, s5_1084, s5_1087, s5_1071, s5_1072, s5_1076, s5_1068, s5_1070] := by decide
theorem s4_906_safe : Safe 9 4 s4_906 := by
  apply safe_succ 8 4 s4_906 [s5_1537, s5_1139, s5_693, s5_1365, s5_980, s5_1103, s5_1084, s5_1087, s5_1071, s5_1072, s5_1076, s5_1068, s5_1070] (by decide) s4_906_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1537_safe
  · subst z; exact s5_1139_safe
  · subst z; exact s5_693_safe
  · subst z; exact s5_1365_safe
  · subst z; exact s5_980_safe
  · subst z; exact s5_1103_safe
  · subst z; exact s5_1084_safe
  · subst z; exact s5_1087_safe
  · subst z; exact s5_1071_safe
  · subst z; exact s5_1072_safe
  · subst z; exact s5_1076_safe
  · subst z; exact s5_1068_safe
  · subst z; exact s5_1070_safe
def s4_907 : State := ⟨[17,21,97,128], 340282367158622951024614364290406875414, 3, 0, 0, 0⟩
theorem s4_907_edges : next config 4 s4_907 = [s5_987, s5_1066] := by decide
theorem s4_907_safe : Safe 9 4 s4_907 := by
  apply safe_succ 8 4 s4_907 [s5_987, s5_1066] (by decide) s4_907_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_987_safe
  · subst z; exact s5_1066_safe
def s4_908 : State := ⟨[17,21,100,128], 340282368267817226224315090600022180118, 3, 0, 0, 0⟩
theorem s4_908_edges : next config 4 s4_908 = [s5_989, s5_1067] := by decide
theorem s4_908_safe : Safe 9 4 s4_908 := by
  apply safe_succ 8 4 s4_908 [s5_989, s5_1067] (by decide) s4_908_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_989_safe
  · subst z; exact s5_1067_safe
def s4_909 : State := ⟨[17,21,104,128], 340282387282576229647756113050570260758, 3, 0, 0, 0⟩
theorem s4_909_edges : next config 4 s4_909 = [s5_994, s5_1105, s5_1085, s5_1088, s5_1074, s5_1075, s5_1073, s5_1068] := by decide
theorem s4_909_safe : Safe 9 4 s4_909 := by
  apply safe_succ 8 4 s4_909 [s5_994, s5_1105, s5_1085, s5_1088, s5_1074, s5_1075, s5_1073, s5_1068] (by decide) s4_909_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_994_safe
  · subst z; exact s5_1105_safe
  · subst z; exact s5_1085_safe
  · subst z; exact s5_1088_safe
  · subst z; exact s5_1074_safe
  · subst z; exact s5_1075_safe
  · subst z; exact s5_1073_safe
  · subst z; exact s5_1068_safe
def s4_910 : State := ⟨[17,21,112,128], 340287559297025160823714219599648194838, 3, 0, 0, 0⟩
theorem s4_910_edges : next config 4 s4_910 = [s5_1003, s5_1070] := by decide
theorem s4_910_safe : Safe 9 4 s4_910 := by
  apply safe_succ 8 4 s4_910 [s5_1003, s5_1070] (by decide) s4_910_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1003_safe
  · subst z; exact s5_1070_safe
def s4_911 : State := ⟨[17,21,113,128], 340292751593883695651342750095977414934, 3, 0, 0, 0⟩
theorem s4_911_edges : next config 4 s4_911 = [s5_1006, s5_1071] := by decide
theorem s4_911_safe : Safe 9 4 s4_911 := by
  apply safe_succ 8 4 s4_911 [s5_1006, s5_1071] (by decide) s4_911_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1006_safe
  · subst z; exact s5_1071_safe
def s4_912 : State := ⟨[17,21,117,128], 340448520499639740480198664985854017814, 3, 0, 0, 0⟩
theorem s4_912_edges : next config 4 s4_912 = [s5_1008, s5_1072] := by decide
theorem s4_912_safe : Safe 9 4 s4_912 := by
  apply safe_succ 8 4 s4_912 [s5_1008, s5_1072] (by decide) s4_912_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1008_safe
  · subst z; exact s5_1072_safe
def s4_913 : State := ⟨[17,21,209,145], 822752278660603021122086421958103419712902851183438164461289750, 3, 0, 1, 0⟩
theorem s4_913_edges : next config 4 s4_913 = [s5_694, s5_1012] := by decide
theorem s4_913_safe : Safe 9 4 s4_913 := by
  apply safe_succ 8 4 s4_913 [s5_694, s5_1012] (by decide) s4_913_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_694_safe
  · subst z; exact s5_1012_safe
def s4_914 : State := ⟨[17,29,64,145], 44601830679428167221534918366648233323856150, 3, 0, 1, 0⟩
theorem s4_914_edges : next config 4 s4_914 = [s5_695, s5_1081, s5_1084] := by decide
theorem s4_914_safe : Safe 9 4 s4_914 := by
  apply safe_succ 8 4 s4_914 [s5_695, s5_1081, s5_1084] (by decide) s4_914_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_695_safe
  · subst z; exact s5_1081_safe
  · subst z; exact s5_1084_safe
def s4_915 : State := ⟨[17,29,65,128], 340282366920938463518714839657730998550, 3, 0, 0, 0⟩
theorem s4_915_edges : next config 4 s4_915 = [s5_1082, s5_1080] := by decide
theorem s4_915_safe : Safe 9 4 s4_915 := by
  apply safe_succ 8 4 s4_915 [s5_1082, s5_1080] (by decide) s4_915_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1082_safe
  · subst z; exact s5_1080_safe
def s4_916 : State := ⟨[17,29,66,128], 340282366920938463555608327805150101782, 3, 0, 0, 0⟩
theorem s4_916_edges : next config 4 s4_916 = [s5_1081] := by decide
theorem s4_916_safe : Safe 9 4 s4_916 := by
  apply safe_succ 8 4 s4_916 [s5_1081] (by decide) s4_916_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1081_safe
def s4_917 : State := ⟨[17,29,96,128], 340282367000166625996085689103855845654, 3, 0, 0, 0⟩
theorem s4_917_edges : next config 4 s4_917 = [s5_1085, s5_1084] := by decide
theorem s4_917_safe : Safe 9 4 s4_917 := by
  apply safe_succ 8 4 s4_917 [s5_1085, s5_1084] (by decide) s4_917_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1085_safe
  · subst z; exact s5_1084_safe
def s4_918 : State := ⟨[17,53,64,145], 44601830679428167221534918375655432041726230, 3, 0, 1, 0⟩
theorem s4_918_edges : next config 4 s4_918 = [s5_696, s5_1087] := by decide
theorem s4_918_safe : Safe 9 4 s4_918 := by
  apply safe_succ 8 4 s4_918 [s5_696, s5_1087] (by decide) s4_918_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_696_safe
  · subst z; exact s5_1087_safe
def s4_919 : State := ⟨[17,53,96,128], 340282367000166625996094696302573715734, 3, 0, 0, 0⟩
theorem s4_919_edges : next config 4 s4_919 = [s5_1088, s5_1087] := by decide
theorem s4_919_safe : Safe 9 4 s4_919 := by
  apply safe_succ 8 4 s4_919 [s5_1088, s5_1087] (by decide) s4_919_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1088_safe
  · subst z; exact s5_1087_safe
def s4_920 : State := ⟨[17,68,64,128], 340282366920938463776969256689127850262, 3, 2, 0, 0⟩
theorem s4_920_edges : next config 4 s4_920 = [s5_1090, s5_1089] := by decide
theorem s4_920_safe : Safe 9 4 s4_920 := by
  apply safe_succ 8 4 s4_920 [s5_1090, s5_1089] (by decide) s4_920_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1090_safe
  · subst z; exact s5_1089_safe
def s4_921 : State := ⟨[17,68,96,145], 44601830679428246449697727778891005681664278, 3, 0, 1, 0⟩
theorem s4_921_edges : next config 4 s4_921 = [s5_697, s5_1091] := by decide
theorem s4_921_safe : Safe 9 4 s4_921 := by
  apply safe_succ 8 4 s4_921 [s5_697, s5_1091] (by decide) s4_921_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_697_safe
  · subst z; exact s5_1091_safe
def s4_922 : State := ⟨[17,68,104,128], 340282387282576229942904018229920989462, 3, 0, 0, 0⟩
theorem s4_922_edges : next config 4 s4_922 = [s5_1091] := by decide
theorem s4_922_safe : Safe 9 4 s4_922 := by
  apply safe_succ 8 4 s4_922 [s5_1091] (by decide) s4_922_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1091_safe
def s4_923 : State := ⟨[17,86,82,128], 340282366921020670511342122588491153686, 3, 0, 0, 0⟩
theorem s4_923_edges : next config 4 s4_923 = [s5_973, s5_1094, s5_1096] := by decide
theorem s4_923_safe : Safe 9 4 s4_923 := by
  apply safe_succ 8 4 s4_923 [s5_973, s5_1094, s5_1096] (by decide) s4_923_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_973_safe
  · subst z; exact s5_1094_safe
  · subst z; exact s5_1096_safe
def s4_924 : State := ⟨[17,86,82,128], 340282366921021879363374760922827653398, 3, 0, 0, 0⟩
theorem s4_924_edges : next config 4 s4_924 = [s5_974, s5_1095, s5_1097] := by decide
theorem s4_924_safe : Safe 9 4 s4_924 := by
  apply safe_succ 8 4 s4_924 [s5_974, s5_1095, s5_1097] (by decide) s4_924_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_974_safe
  · subst z; exact s5_1095_safe
  · subst z; exact s5_1097_safe
def s4_925 : State := ⟨[17,100,96,145], 44601830679429514100297660860387323032043798, 3, 0, 1, 0⟩
theorem s4_925_edges : next config 4 s4_925 = [s5_720, s5_985, s5_1101] := by decide
theorem s4_925_safe : Safe 9 4 s4_925 := by
  apply safe_succ 8 4 s4_925 [s5_720, s5_985, s5_1101] (by decide) s4_925_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_720_safe
  · subst z; exact s5_985_safe
  · subst z; exact s5_1101_safe
def s4_926 : State := ⟨[17,100,104,128], 340282388550226829875985514547271368982, 3, 0, 0, 0⟩
theorem s4_926_edges : next config 4 s4_926 = [s5_1101] := by decide
theorem s4_926_safe : Safe 9 4 s4_926 := by
  apply safe_succ 8 4 s4_926 [s5_1101] (by decide) s4_926_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1101_safe
def s4_927 : State := ⟨[17,108,104,128], 340282711801129888074482896206588739862, 3, 0, 0, 0⟩
theorem s4_927_edges : next config 4 s4_927 = [s5_1000, s5_1102] := by decide
theorem s4_927_safe : Safe 9 4 s4_927 := by
  apply safe_succ 8 4 s4_927 [s5_1000, s5_1102] (by decide) s4_927_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1000_safe
  · subst z; exact s5_1102_safe
def s4_928 : State := ⟨[17,117,96,128], 340448520499639740480198664985854017814, 3, 0, 0, 0⟩
theorem s4_928_edges : next config 4 s4_928 = [s5_1104, s5_1103] := by decide
theorem s4_928_safe : Safe 9 4 s4_928 := by
  apply safe_succ 8 4 s4_928 [s5_1104, s5_1103] (by decide) s4_928_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1104_safe
  · subst z; exact s5_1103_safe
def s4_929 : State := ⟨[21,4,65,145], 44601830679428167221534955260136380206088470, 1, 0, 1, 0⟩
theorem s4_929_edges : next config 4 s4_929 = [s5_1140, s5_1123, s5_1112] := by decide
theorem s4_929_safe : Safe 9 4 s4_929 := by
  apply safe_succ 8 4 s4_929 [s5_1140, s5_1123, s5_1112] (by decide) s4_929_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1140_safe
  · subst z; exact s5_1123_safe
  · subst z; exact s5_1112_safe
def s4_930 : State := ⟨[21,4,66,145], 44601830679428167221534992153624527625191702, 1, 0, 1, 0⟩
theorem s4_930_edges : next config 4 s4_930 = [s5_1141, s5_1124, s5_1114] := by decide
theorem s4_930_safe : Safe 9 4 s4_930 := by
  apply safe_succ 8 4 s4_930 [s5_1141, s5_1124, s5_1114] (by decide) s4_930_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1141_safe
  · subst z; exact s5_1124_safe
  · subst z; exact s5_1114_safe
def s4_931 : State := ⟨[21,4,68,145], 44601830679428167221535213514553412139811094, 1, 0, 1, 0⟩
theorem s4_931_edges : next config 4 s4_931 = [] := by decide
theorem s4_931_safe : Safe 9 4 s4_931 := by
  apply safe_succ 8 4 s4_931 [] (by decide) s4_931_edges
  simp
def s4_932 : State := ⟨[21,4,80,145], 44601830679428167222743844186262861961691414, 1, 0, 1, 0⟩
theorem s4_932_edges : next config 4 s4_932 = [s5_1125, s5_1115] := by decide
theorem s4_932_safe : Safe 9 4 s4_932 := by
  apply safe_succ 8 4 s4_932 [s5_1125, s5_1115] (by decide) s4_932_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1125_safe
  · subst z; exact s5_1115_safe
def s4_933 : State := ⟨[21,4,81,145], 44601830679428167223952770005877491136397590, 1, 0, 1, 0⟩
theorem s4_933_edges : next config 4 s4_933 = [s5_1126] := by decide
theorem s4_933_safe : Safe 9 4 s4_933 := by
  apply safe_succ 8 4 s4_933 [s5_1126] (by decide) s4_933_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1126_safe
def s4_934 : State := ⟨[21,4,96,145], 44601830679428246449697432630985826330935574, 1, 0, 1, 0⟩
theorem s4_934_edges : next config 4 s4_934 = [s5_1538, s5_1142, s5_1366, s5_1130, s5_1127, s5_1121, s5_1117, s5_1122, s5_1118, s5_1119] := by decide
theorem s4_934_safe : Safe 9 4 s4_934 := by
  apply safe_succ 8 4 s4_934 [s5_1538, s5_1142, s5_1366, s5_1130, s5_1127, s5_1121, s5_1117, s5_1122, s5_1118, s5_1119] (by decide) s4_934_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1538_safe
  · subst z; exact s5_1142_safe
  · subst z; exact s5_1366_safe
  · subst z; exact s5_1130_safe
  · subst z; exact s5_1127_safe
  · subst z; exact s5_1121_safe
  · subst z; exact s5_1117_safe
  · subst z; exact s5_1122_safe
  · subst z; exact s5_1118_safe
  · subst z; exact s5_1119_safe
def s4_935 : State := ⟨[21,4,209,145], 822752278660603021122086421958103419712902851183438164461289750, 1, 0, 1, 0⟩
theorem s4_935_edges : next config 4 s4_935 = [s5_1128] := by decide
theorem s4_935_safe : Safe 9 4 s4_935 := by
  apply safe_succ 8 4 s4_935 [s5_1128] (by decide) s4_935_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1128_safe
def s4_936 : State := ⟨[21,12,64,145], 44601830679428167221534918366648232786989334, 3, 0, 1, 0⟩
theorem s4_936_edges : next config 4 s4_936 = [s5_1108, s5_1128, s5_1124, s5_1125, s5_1127] := by decide
theorem s4_936_safe : Safe 9 4 s4_936 := by
  apply safe_succ 8 4 s4_936 [s5_1108, s5_1128, s5_1124, s5_1125, s5_1127] (by decide) s4_936_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1108_safe
  · subst z; exact s5_1128_safe
  · subst z; exact s5_1124_safe
  · subst z; exact s5_1125_safe
  · subst z; exact s5_1127_safe
def s4_937 : State := ⟨[21,68,64,145], 44601830679428167221535213514553412139811094, 3, 0, 1, 0⟩
theorem s4_937_edges : next config 4 s4_937 = [s5_1111, s5_1129] := by decide
theorem s4_937_safe : Safe 9 4 s4_937 := by
  apply safe_succ 8 4 s4_937 [s5_1111, s5_1129] (by decide) s4_937_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1111_safe
  · subst z; exact s5_1129_safe
def s4_938 : State := ⟨[25,4,65,145], 44601830679428167221534955260136380237545750, 1, 0, 1, 0⟩
theorem s4_938_edges : next config 4 s4_938 = [s5_1134] := by decide
theorem s4_938_safe : Safe 9 4 s4_938 := by
  apply safe_succ 8 4 s4_938 [s5_1134] (by decide) s4_938_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1134_safe
def s4_939 : State := ⟨[25,4,66,145], 44601830679428167221534992153624527656648982, 1, 0, 1, 0⟩
theorem s4_939_edges : next config 4 s4_939 = [] := by decide
theorem s4_939_safe : Safe 9 4 s4_939 := by
  apply safe_succ 8 4 s4_939 [] (by decide) s4_939_edges
  simp
def s4_940 : State := ⟨[25,4,96,145], 44601830679428246449697432630985826362392854, 1, 0, 1, 0⟩
theorem s4_940_edges : next config 4 s4_940 = [s5_1136] := by decide
theorem s4_940_safe : Safe 9 4 s4_940 := by
  apply safe_succ 8 4 s4_940 [s5_1136] (by decide) s4_940_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1136_safe
def s4_941 : State := ⟨[25,21,64,145], 44601830679428167221534918366648232820539670, 3, 0, 1, 0⟩
theorem s4_941_edges : next config 4 s4_941 = [s5_1138, s5_1139] := by decide
theorem s4_941_safe : Safe 9 4 s4_941 := by
  apply safe_succ 8 4 s4_941 [s5_1138, s5_1139] (by decide) s4_941_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1138_safe
  · subst z; exact s5_1139_safe
def s4_942 : State := ⟨[29,4,64,145], 44601830679428167221534918366648233323856150, 1, 0, 1, 0⟩
theorem s4_942_edges : next config 4 s4_942 = [s5_1141, s5_1142] := by decide
theorem s4_942_safe : Safe 9 4 s4_942 := by
  apply safe_succ 8 4 s4_942 [s5_1141, s5_1142] (by decide) s4_942_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1141_safe
  · subst z; exact s5_1142_safe
def s4_943 : State := ⟨[33,4,64,129], 1020847100762815390408570566381899157782, 3, 2, 1, 0⟩
theorem s4_943_edges : next config 4 s4_943 = [s5_1187, s5_1, s5_1147, s5_1143] := by decide
theorem s4_943_safe : Safe 9 4 s4_943 := by
  apply safe_succ 8 4 s4_943 [s5_1187, s5_1, s5_1147, s5_1143] (by decide) s4_943_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1187_safe
  · subst z; exact s5_1_safe
  · subst z; exact s5_1147_safe
  · subst z; exact s5_1143_safe
def s4_944 : State := ⟨[33,4,64,130], 1701411834604692317335319781245435580694, 3, 2, 1, 0⟩
theorem s4_944_edges : next config 4 s4_944 = [s5_1561, s5_1189, s5_4, s5_1148, s5_1145] := by decide
theorem s4_944_safe : Safe 9 4 s4_944 := by
  apply safe_succ 8 4 s4_944 [s5_1561, s5_1189, s5_4, s5_1148, s5_1145] (by decide) s4_944_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1561_safe
  · subst z; exact s5_1189_safe
  · subst z; exact s5_4_safe
  · subst z; exact s5_1148_safe
  · subst z; exact s5_1145_safe
def s4_945 : State := ⟨[33,4,64,132], 5784800237655953878895815070426654118166, 3, 2, 1, 0⟩
theorem s4_945_edges : next config 4 s4_945 = [s5_1192, s5_9, s5_1149] := by decide
theorem s4_945_safe : Safe 9 4 s4_945 := by
  apply safe_succ 8 4 s4_945 [s5_1192, s5_9, s5_1149] (by decide) s4_945_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1192_safe
  · subst z; exact s5_9_safe
  · subst z; exact s5_1149_safe
def s4_946 : State := ⟨[33,4,64,136], 87452568298681185110105720854051024867606, 3, 2, 1, 0⟩
theorem s4_946_edges : next config 4 s4_946 = [s5_1194, s5_12, s5_1150] := by decide
theorem s4_946_safe : Safe 9 4 s4_946 := by
  apply safe_succ 8 4 s4_946 [s5_1194, s5_12, s5_1150] (by decide) s4_946_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1194_safe
  · subst z; exact s5_12_safe
  · subst z; exact s5_1150_safe
def s4_947 : State := ⟨[33,4,64,136], 1481249143206845131456088112894573618987286, 3, 2, 1, 0⟩
theorem s4_947_edges : next config 4 s4_947 = [s5_1196, s5_15, s5_1151] := by decide
theorem s4_947_safe : Safe 9 4 s4_947 := by
  apply safe_succ 8 4 s4_947 [s5_1196, s5_15, s5_1151] (by decide) s4_947_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1196_safe
  · subst z; exact s5_15_safe
  · subst z; exact s5_1151_safe
def s4_948 : State := ⟨[33,4,64,140], 1394136857275084884809464213392040956858646, 3, 2, 1, 0⟩
theorem s4_948_edges : next config 4 s4_948 = [s5_1198, s5_18, s5_1152] := by decide
theorem s4_948_safe : Safe 9 4 s4_948 := by
  apply safe_succ 8 4 s4_948 [s5_1198, s5_18, s5_1152] (by decide) s4_948_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1198_safe
  · subst z; exact s5_18_safe
  · subst z; exact s5_1152_safe
def s4_949 : State := ⟨[33,4,64,144], 22301085480897544079999200093999879868715286, 3, 2, 1, 0⟩
theorem s4_949_edges : next config 4 s4_949 = [s5_1200, s5_21, s5_1153] := by decide
theorem s4_949_safe : Safe 9 4 s4_949 := by
  apply safe_succ 8 4 s4_949 [s5_1200, s5_21, s5_1153] (by decide) s4_949_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1200_safe
  · subst z; exact s5_21_safe
  · subst z; exact s5_1153_safe
def s4_950 : State := ⟨[33,4,64,145], 44601830679428167221534918366648241374822678, 1, 1, 1, 0⟩
theorem s4_950_edges : next config 4 s4_950 = [s5_1202, s5_1168, s5_1154] := by decide
theorem s4_950_safe : Safe 9 4 s4_950 := by
  apply safe_succ 8 4 s4_950 [s5_1202, s5_1168, s5_1154] (by decide) s4_950_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1202_safe
  · subst z; exact s5_1168_safe
  · subst z; exact s5_1154_safe
def s4_951 : State := ⟨[33,4,64,160], 1461501637671185285124623296198104371174295277846, 3, 2, 1, 0⟩
theorem s4_951_edges : next config 4 s4_951 = [s5_1204, s5_29, s5_1155] := by decide
theorem s4_951_safe : Safe 9 4 s4_951 := by
  apply safe_succ 8 4 s4_951 [s5_1204, s5_29, s5_1155] (by decide) s4_951_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1204_safe
  · subst z; exact s5_29_safe
  · subst z; exact s5_1155_safe
def s4_952 : State := ⟨[33,4,64,161], 2923003275002088203328308128914387390830227820822, 3, 2, 1, 0⟩
theorem s4_952_edges : next config 4 s4_952 = [s5_1205, s5_32, s5_1156, s5_1146] := by decide
theorem s4_952_safe : Safe 9 4 s4_952 := by
  apply safe_succ 8 4 s4_952 [s5_1205, s5_32, s5_1156, s5_1146] (by decide) s4_952_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1205_safe
  · subst z; exact s5_32_safe
  · subst z; exact s5_1156_safe
  · subst z; exact s5_1146_safe
def s4_953 : State := ⟨[33,4,64,171], 3004847366354037811661380708382013208193842743935254, 1, 0, 1, 0⟩
theorem s4_953_edges : next config 4 s4_953 = [s5_43, s5_1157] := by decide
theorem s4_953_safe : Safe 9 4 s4_953 := by
  apply safe_succ 8 4 s4_953 [s5_43, s5_1157] (by decide) s4_953_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_43_safe
  · subst z; exact s5_1157_safe
def s4_954 : State := ⟨[33,4,64,171], 3007770369627338488030104324193592275803427536175382, 1, 0, 1, 0⟩
theorem s4_954_edges : next config 4 s4_954 = [s5_46, s5_1158] := by decide
theorem s4_954_safe : Safe 9 4 s4_954 := by
  apply safe_succ 8 4 s4_954 [s5_46, s5_1158] (by decide) s4_954_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_46_safe
  · subst z; exact s5_1158_safe
def s4_955 : State := ⟨[33,4,64,192], 6277101735386680764176071790128604879584176795982397247766, 3, 2, 1, 0⟩
theorem s4_955_edges : next config 4 s4_955 = [s5_1209, s5_48, s5_1159] := by decide
theorem s4_955_safe : Safe 9 4 s4_955 := by
  apply safe_succ 8 4 s4_955 [s5_1209, s5_48, s5_1159] (by decide) s4_955_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1209_safe
  · subst z; exact s5_48_safe
  · subst z; exact s5_1159_safe
def s4_956 : State := ⟨[33,4,96,128], 340282367000166625996085689111906685206, 3, 2, 0, 0⟩
theorem s4_956_edges : next config 4 s4_956 = [s5_1240, s5_185, s5_1161, s5_1156, s5_1149, s5_1160, s5_1148, s5_1150, s5_1153, s5_1155] := by decide
theorem s4_956_safe : Safe 9 4 s4_956 := by
  apply safe_succ 8 4 s4_956 [s5_1240, s5_185, s5_1161, s5_1156, s5_1149, s5_1160, s5_1148, s5_1150, s5_1153, s5_1155] (by decide) s4_956_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1240_safe
  · subst z; exact s5_185_safe
  · subst z; exact s5_1161_safe
  · subst z; exact s5_1156_safe
  · subst z; exact s5_1149_safe
  · subst z; exact s5_1160_safe
  · subst z; exact s5_1148_safe
  · subst z; exact s5_1150_safe
  · subst z; exact s5_1153_safe
  · subst z; exact s5_1155_safe
def s4_957 : State := ⟨[33,4,96,140], 1399581375145899128387392471448542792188182, 1, 0, 1, 0⟩
theorem s4_957_edges : next config 4 s4_957 = [s5_1242, s5_195, s5_1162] := by decide
theorem s4_957_safe : Safe 9 4 s4_957 := by
  apply safe_succ 8 4 s4_957 [s5_1242, s5_195, s5_1162] (by decide) s4_957_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1242_safe
  · subst z; exact s5_195_safe
  · subst z; exact s5_1162_safe
def s4_958 : State := ⟨[33,4,96,140], 1481249143206924359618602377232167162937622, 1, 0, 1, 0⟩
theorem s4_958_edges : next config 4 s4_958 = [s5_1244, s5_199, s5_1163] := by decide
theorem s4_958_safe : Safe 9 4 s4_958 := by
  apply safe_succ 8 4 s4_958 [s5_1244, s5_199, s5_1163] (by decide) s4_958_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1244_safe
  · subst z; exact s5_199_safe
  · subst z; exact s5_1163_safe
def s4_959 : State := ⟨[33,4,96,145], 44602511244162088326624359380200698455064854, 1, 0, 1, 0⟩
theorem s4_959_edges : next config 4 s4_959 = [s5_1246, s5_205, s5_1169, s5_1164] := by decide
theorem s4_959_safe : Safe 9 4 s4_959 := by
  apply safe_succ 8 4 s4_959 [s5_1246, s5_205, s5_1169, s5_1164] (by decide) s4_959_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1246_safe
  · subst z; exact s5_205_safe
  · subst z; exact s5_1169_safe
  · subst z; exact s5_1164_safe
def s4_960 : State := ⟨[33,4,96,145], 66902575877958869591233150903634196424622358, 1, 0, 1, 0⟩
theorem s4_960_edges : next config 4 s4_960 = [s5_1248, s5_213, s5_1170, s5_1165] := by decide
theorem s4_960_safe : Safe 9 4 s4_960 := by
  apply safe_succ 8 4 s4_960 [s5_1248, s5_213, s5_1170, s5_1165] (by decide) s4_960_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1248_safe
  · subst z; exact s5_213_safe
  · subst z; exact s5_1170_safe
  · subst z; exact s5_1165_safe
def s4_961 : State := ⟨[33,4,96,163], 11692013100348635180313399141579848276086439870742, 1, 0, 1, 0⟩
theorem s4_961_edges : next config 4 s4_961 = [s5_248, s5_1171, s5_1166, s5_1157] := by decide
theorem s4_961_safe : Safe 9 4 s4_961 := by
  apply safe_succ 8 4 s4_961 [s5_248, s5_1171, s5_1166, s5_1157] (by decide) s4_961_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_248_safe
  · subst z; exact s5_1171_safe
  · subst z; exact s5_1166_safe
  · subst z; exact s5_1157_safe
def s4_962 : State := ⟨[33,4,96,163], 14615016373649311549037014953158915885671232110870, 1, 0, 1, 0⟩
theorem s4_962_edges : next config 4 s4_962 = [s5_251, s5_1172, s5_1167, s5_1158] := by decide
theorem s4_962_safe : Safe 9 4 s4_962 := by
  apply safe_succ 8 4 s4_962 [s5_251, s5_1172, s5_1167, s5_1158] (by decide) s4_962_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_251_safe
  · subst z; exact s5_1172_safe
  · subst z; exact s5_1167_safe
  · subst z; exact s5_1158_safe
def s4_963 : State := ⟨[33,4,104,129], 1020847121124453156574505327922694390038, 1, 0, 1, 0⟩
theorem s4_963_edges : next config 4 s4_963 = [s5_1254, s5_332, s5_1173, s5_1164] := by decide
theorem s4_963_safe : Safe 9 4 s4_963 := by
  apply safe_succ 8 4 s4_963 [s5_1254, s5_332, s5_1173, s5_1164] (by decide) s4_963_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1254_safe
  · subst z; exact s5_332_safe
  · subst z; exact s5_1173_safe
  · subst z; exact s5_1164_safe
def s4_964 : State := ⟨[33,4,104,130], 1701411854966330083501254542786230812950, 1, 0, 1, 0⟩
theorem s4_964_edges : next config 4 s4_964 = [s5_1567, s5_1256, s5_341, s5_1174, s5_1166] := by decide
theorem s4_964_safe : Safe 9 4 s4_964 := by
  apply safe_succ 8 4 s4_964 [s5_1567, s5_1256, s5_341, s5_1174, s5_1166] (by decide) s4_964_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1567_safe
  · subst z; exact s5_1256_safe
  · subst z; exact s5_341_safe
  · subst z; exact s5_1174_safe
  · subst z; exact s5_1166_safe
def s4_965 : State := ⟨[33,4,104,132], 5784800258017591645061749831967449350422, 1, 0, 1, 0⟩
theorem s4_965_edges : next config 4 s4_965 = [s5_1259, s5_352, s5_1175, s5_1162] := by decide
theorem s4_965_safe : Safe 9 4 s4_965 := by
  apply safe_succ 8 4 s4_965 [s5_1259, s5_352, s5_1175, s5_1162] (by decide) s4_965_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1259_safe
  · subst z; exact s5_352_safe
  · subst z; exact s5_1175_safe
  · subst z; exact s5_1162_safe
def s4_966 : State := ⟨[33,4,104,136], 87452568319042822876271655615591820099862, 1, 0, 1, 0⟩
theorem s4_966_edges : next config 4 s4_966 = [s5_1261, s5_361, s5_1185, s5_1176, s5_1163] := by decide
theorem s4_966_safe : Safe 9 4 s4_966 := by
  apply safe_succ 8 4 s4_966 [s5_1261, s5_361, s5_1185, s5_1176, s5_1163] (by decide) s4_966_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1261_safe
  · subst z; exact s5_361_safe
  · subst z; exact s5_1185_safe
  · subst z; exact s5_1176_safe
  · subst z; exact s5_1163_safe
def s4_967 : State := ⟨[33,4,104,144], 22301085480917905717765366028761420663947542, 1, 0, 1, 0⟩
theorem s4_967_edges : next config 4 s4_967 = [s5_1263, s5_374, s5_1178] := by decide
theorem s4_967_safe : Safe 9 4 s4_967 := by
  apply safe_succ 8 4 s4_967 [s5_1263, s5_374, s5_1178] (by decide) s4_967_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1263_safe
  · subst z; exact s5_374_safe
  · subst z; exact s5_1178_safe
def s4_968 : State := ⟨[33,4,104,160], 1461501637671185305486261062364039132715090510102, 1, 0, 1, 0⟩
theorem s4_968_edges : next config 4 s4_968 = [s5_1265, s5_386, s5_1179] := by decide
theorem s4_968_safe : Safe 9 4 s4_968 := by
  apply safe_succ 8 4 s4_968 [s5_1265, s5_386, s5_1179] (by decide) s4_968_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1265_safe
  · subst z; exact s5_386_safe
  · subst z; exact s5_1179_safe
def s4_969 : State := ⟨[33,4,104,161], 2923003275002088223689945895080322152371023053078, 1, 0, 1, 0⟩
theorem s4_969_edges : next config 4 s4_969 = [s5_1266, s5_393, s5_1180, s5_1167] := by decide
theorem s4_969_safe : Safe 9 4 s4_969 := by
  apply safe_succ 8 4 s4_969 [s5_1266, s5_393, s5_1180, s5_1167] (by decide) s4_969_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1266_safe
  · subst z; exact s5_393_safe
  · subst z; exact s5_1180_safe
  · subst z; exact s5_1167_safe
def s4_970 : State := ⟨[33,4,104,192], 6277101735386680764176071810490242645750111557523192480022, 1, 0, 1, 0⟩
theorem s4_970_edges : next config 4 s4_970 = [s5_1270, s5_409, s5_1181] := by decide
theorem s4_970_safe : Safe 9 4 s4_970 := by
  apply safe_succ 8 4 s4_970 [s5_1270, s5_409, s5_1181] (by decide) s4_970_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1270_safe
  · subst z; exact s5_409_safe
  · subst z; exact s5_1181_safe
def s4_971 : State := ⟨[33,4,104,224], 26959946667150639794667015087359913060919720652188328594162768216342, 1, 0, 1, 0⟩
theorem s4_971_edges : next config 4 s4_971 = [s5_1272, s5_430, s5_1182] := by decide
theorem s4_971_safe : Safe 9 4 s4_971 := by
  apply safe_succ 8 4 s4_971 [s5_1272, s5_430, s5_1182] (by decide) s4_971_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1272_safe
  · subst z; exact s5_430_safe
  · subst z; exact s5_1182_safe
def s4_972 : State := ⟨[33,4,104,232], 6901746346790563787434755862277365734838391548400034311275583381766422, 1, 0, 1, 0⟩
theorem s4_972_edges : next config 4 s4_972 = [s5_1274, s5_443, s5_1183] := by decide
theorem s4_972_safe : Safe 9 4 s4_972 := by
  apply safe_succ 8 4 s4_972 [s5_1274, s5_443, s5_1183] (by decide) s4_972_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1274_safe
  · subst z; exact s5_443_safe
  · subst z; exact s5_1183_safe
def s4_973 : State := ⟨[33,12,64,145], 44602511244162009098461845115863104911118614, 3, 0, 1, 0⟩
theorem s4_973_edges : next config 4 s4_973 = [s5_1276, s5_520, s5_1143, s5_1169] := by decide
theorem s4_973_safe : Safe 9 4 s4_973 := by
  apply safe_succ 8 4 s4_973 [s5_1276, s5_520, s5_1143, s5_1169] (by decide) s4_973_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1276_safe
  · subst z; exact s5_520_safe
  · subst z; exact s5_1143_safe
  · subst z; exact s5_1169_safe
def s4_974 : State := ⟨[33,12,64,145], 66902575877958790363070636639296602880676118, 3, 0, 1, 0⟩
theorem s4_974_edges : next config 4 s4_974 = [s5_1278, s5_523, s5_1144, s5_1170] := by decide
theorem s4_974_safe : Safe 9 4 s4_974 := by
  apply safe_succ 8 4 s4_974 [s5_1278, s5_523, s5_1144, s5_1170] (by decide) s4_974_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1278_safe
  · subst z; exact s5_523_safe
  · subst z; exact s5_1144_safe
  · subst z; exact s5_1170_safe
def s4_975 : State := ⟨[33,12,64,163], 11692013100348635180234170979065583938492895924502, 3, 0, 1, 0⟩
theorem s4_975_edges : next config 4 s4_975 = [s5_537, s5_1145, s5_1171] := by decide
theorem s4_975_safe : Safe 9 4 s4_975 := by
  apply safe_succ 8 4 s4_975 [s5_537, s5_1145, s5_1171] (by decide) s4_975_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_537_safe
  · subst z; exact s5_1145_safe
  · subst z; exact s5_1171_safe
def s4_976 : State := ⟨[33,12,64,163], 14615016373649311548957786790644651548077688164630, 3, 0, 1, 0⟩
theorem s4_976_edges : next config 4 s4_976 = [s5_540, s5_1146, s5_1172] := by decide
theorem s4_976_safe : Safe 9 4 s4_976 := by
  apply safe_succ 8 4 s4_976 [s5_540, s5_1146, s5_1172] (by decide) s4_976_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_540_safe
  · subst z; exact s5_1146_safe
  · subst z; exact s5_1172_safe
def s4_977 : State := ⟨[33,12,96,129], 1020847100842043552922834903975443108118, 3, 0, 1, 0⟩
theorem s4_977_edges : next config 4 s4_977 = [s5_1293, s5_582, s5_1147, s5_1173, s5_1169] := by decide
theorem s4_977_safe : Safe 9 4 s4_977 := by
  apply safe_succ 8 4 s4_977 [s5_1293, s5_582, s5_1147, s5_1173, s5_1169] (by decide) s4_977_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1293_safe
  · subst z; exact s5_582_safe
  · subst z; exact s5_1147_safe
  · subst z; exact s5_1173_safe
  · subst z; exact s5_1169_safe
def s4_978 : State := ⟨[33,12,96,130], 1701411834683920479849584118838979531030, 3, 0, 1, 0⟩
theorem s4_978_edges : next config 4 s4_978 = [s5_1574, s5_1295, s5_586, s5_1148, s5_1174, s5_1171] := by decide
theorem s4_978_safe : Safe 9 4 s4_978 := by
  apply safe_succ 8 4 s4_978 [s5_1574, s5_1295, s5_586, s5_1148, s5_1174, s5_1171] (by decide) s4_978_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1574_safe
  · subst z; exact s5_1295_safe
  · subst z; exact s5_586_safe
  · subst z; exact s5_1148_safe
  · subst z; exact s5_1174_safe
  · subst z; exact s5_1171_safe
def s4_979 : State := ⟨[33,12,96,132], 5784800237735182041410079408020198068502, 3, 0, 1, 0⟩
theorem s4_979_edges : next config 4 s4_979 = [s5_1298, s5_592, s5_1149, s5_1175] := by decide
theorem s4_979_safe : Safe 9 4 s4_979 := by
  apply safe_succ 8 4 s4_979 [s5_1298, s5_592, s5_1149, s5_1175] (by decide) s4_979_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1298_safe
  · subst z; exact s5_592_safe
  · subst z; exact s5_1149_safe
  · subst z; exact s5_1175_safe
def s4_980 : State := ⟨[33,12,96,136], 87452568298760413272619985191644568817942, 3, 0, 1, 0⟩
theorem s4_980_edges : next config 4 s4_980 = [s5_1300, s5_596, s5_1150, s5_1176] := by decide
theorem s4_980_safe : Safe 9 4 s4_980 := by
  apply safe_succ 8 4 s4_980 [s5_1300, s5_596, s5_1150, s5_1176] (by decide) s4_980_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1300_safe
  · subst z; exact s5_596_safe
  · subst z; exact s5_1150_safe
  · subst z; exact s5_1176_safe
def s4_981 : State := ⟨[33,12,96,140], 1394136857275164112971978477729634500808982, 3, 0, 1, 0⟩
theorem s4_981_edges : next config 4 s4_981 = [s5_1302, s5_600, s5_1152, s5_1177] := by decide
theorem s4_981_safe : Safe 9 4 s4_981 := by
  apply safe_succ 8 4 s4_981 [s5_1302, s5_600, s5_1152, s5_1177] (by decide) s4_981_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1302_safe
  · subst z; exact s5_600_safe
  · subst z; exact s5_1152_safe
  · subst z; exact s5_1177_safe
def s4_982 : State := ⟨[33,12,96,144], 22301085480897623308161714358337473412665622, 3, 0, 1, 0⟩
theorem s4_982_edges : next config 4 s4_982 = [s5_1304, s5_604, s5_1153, s5_1178] := by decide
theorem s4_982_safe : Safe 9 4 s4_982 := by
  apply safe_succ 8 4 s4_982 [s5_1304, s5_604, s5_1153, s5_1178] (by decide) s4_982_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1304_safe
  · subst z; exact s5_604_safe
  · subst z; exact s5_1153_safe
  · subst z; exact s5_1178_safe
def s4_983 : State := ⟨[33,12,96,160], 1461501637671185285203851458712368708767839228182, 3, 0, 1, 0⟩
theorem s4_983_edges : next config 4 s4_983 = [s5_1306, s5_609, s5_1155, s5_1179] := by decide
theorem s4_983_safe : Safe 9 4 s4_983 := by
  apply safe_succ 8 4 s4_983 [s5_1306, s5_609, s5_1155, s5_1179] (by decide) s4_983_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1306_safe
  · subst z; exact s5_609_safe
  · subst z; exact s5_1155_safe
  · subst z; exact s5_1179_safe
def s4_984 : State := ⟨[33,12,96,161], 2923003275002088203407536291428651728423771771158, 3, 0, 1, 0⟩
theorem s4_984_edges : next config 4 s4_984 = [s5_1307, s5_613, s5_1156, s5_1180, s5_1172] := by decide
theorem s4_984_safe : Safe 9 4 s4_984 := by
  apply safe_succ 8 4 s4_984 [s5_1307, s5_613, s5_1156, s5_1180, s5_1172] (by decide) s4_984_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1307_safe
  · subst z; exact s5_613_safe
  · subst z; exact s5_1156_safe
  · subst z; exact s5_1180_safe
  · subst z; exact s5_1172_safe
def s4_985 : State := ⟨[33,12,96,192], 6277101735386680764176071790207833042098441133575941198102, 3, 0, 1, 0⟩
theorem s4_985_edges : next config 4 s4_985 = [s5_1311, s5_623, s5_1159, s5_1181] := by decide
theorem s4_985_safe : Safe 9 4 s4_985 := by
  apply safe_succ 8 4 s4_985 [s5_1311, s5_623, s5_1159, s5_1181] (by decide) s4_985_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1311_safe
  · subst z; exact s5_623_safe
  · subst z; exact s5_1159_safe
  · subst z; exact s5_1181_safe
def s4_986 : State := ⟨[33,12,96,224], 26959946667150639794667015087359913040637311048536658170215516934422, 3, 0, 1, 0⟩
theorem s4_986_edges : next config 4 s4_986 = [s5_1313, s5_637, s5_1160, s5_1182] := by decide
theorem s4_986_safe : Safe 9 4 s4_986 := by
  apply safe_succ 8 4 s4_986 [s5_1313, s5_637, s5_1160, s5_1182] (by decide) s4_986_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1313_safe
  · subst z; exact s5_637_safe
  · subst z; exact s5_1160_safe
  · subst z; exact s5_1182_safe
def s4_987 : State := ⟨[33,12,104,128], 340282387282576229647756113059157971222, 3, 0, 0, 0⟩
theorem s4_987_edges : next config 4 s4_987 = [s5_1315, s5_647, s5_1161, s5_1180, s5_1177, s5_1183, s5_1174, s5_1176, s5_1178, s5_1179] := by decide
theorem s4_987_safe : Safe 9 4 s4_987 := by
  apply safe_succ 8 4 s4_987 [s5_1315, s5_647, s5_1161, s5_1180, s5_1177, s5_1183, s5_1174, s5_1176, s5_1178, s5_1179] (by decide) s4_987_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1315_safe
  · subst z; exact s5_647_safe
  · subst z; exact s5_1161_safe
  · subst z; exact s5_1180_safe
  · subst z; exact s5_1177_safe
  · subst z; exact s5_1183_safe
  · subst z; exact s5_1174_safe
  · subst z; exact s5_1176_safe
  · subst z; exact s5_1178_safe
  · subst z; exact s5_1179_safe
def s4_988 : State := ⟨[33,140,96,136], 1481249143206924359618602377232167162937622, 3, 0, 1, 0⟩
theorem s4_988_edges : next config 4 s4_988 = [s5_1318, s5_767, s5_1151, s5_1185] := by decide
theorem s4_988_safe : Safe 9 4 s4_988 := by
  apply safe_succ 8 4 s4_988 [s5_1318, s5_767, s5_1151, s5_1185] (by decide) s4_988_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1318_safe
  · subst z; exact s5_767_safe
  · subst z; exact s5_1151_safe
  · subst z; exact s5_1185_safe
def s4_989 : State := ⟨[35,4,64,128], 340282366920938463481821351544132538654, 3, 2, 0, 0⟩
theorem s4_989_edges : next config 4 s4_989 = [s5_1239, s5_1206, s5_1191, s5_1208, s5_1188, s5_1193, s5_1199, s5_1203] := by decide
theorem s4_989_safe : Safe 9 4 s4_989 := by
  apply safe_succ 8 4 s4_989 [s5_1239, s5_1206, s5_1191, s5_1208, s5_1188, s5_1193, s5_1199, s5_1203] (by decide) s4_989_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1239_safe
  · subst z; exact s5_1206_safe
  · subst z; exact s5_1191_safe
  · subst z; exact s5_1208_safe
  · subst z; exact s5_1188_safe
  · subst z; exact s5_1193_safe
  · subst z; exact s5_1199_safe
  · subst z; exact s5_1203_safe
def s4_990 : State := ⟨[35,4,64,128], 340282366920938463481821351552722473238, 3, 2, 0, 0⟩
theorem s4_990_edges : next config 4 s4_990 = [s5_1240, s5_1207, s5_1192, s5_1209, s5_1189, s5_1194, s5_1200, s5_1204] := by decide
theorem s4_990_safe : Safe 9 4 s4_990 := by
  apply safe_succ 8 4 s4_990 [s5_1240, s5_1207, s5_1192, s5_1209, s5_1189, s5_1194, s5_1200, s5_1204] (by decide) s4_990_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1240_safe
  · subst z; exact s5_1207_safe
  · subst z; exact s5_1192_safe
  · subst z; exact s5_1209_safe
  · subst z; exact s5_1189_safe
  · subst z; exact s5_1194_safe
  · subst z; exact s5_1200_safe
  · subst z; exact s5_1204_safe
def s4_991 : State := ⟨[35,4,64,140], 1399581375145819900224878207110975018041630, 1, 0, 1, 0⟩
theorem s4_991_edges : next config 4 s4_991 = [s5_1241] := by decide
theorem s4_991_safe : Safe 9 4 s4_991 := by
  apply safe_succ 8 4 s4_991 [s5_1241] (by decide) s4_991_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1241_safe
def s4_992 : State := ⟨[35,4,64,140], 1399581375145819900224878207110983607976214, 1, 0, 1, 0⟩
theorem s4_992_edges : next config 4 s4_992 = [s5_1242] := by decide
theorem s4_992_safe : Safe 9 4 s4_992 := by
  apply safe_succ 8 4 s4_992 [s5_1242] (by decide) s4_992_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1242_safe
def s4_993 : State := ⟨[35,4,64,140], 1481249143206845131456088112894599388791070, 1, 0, 1, 0⟩
theorem s4_993_edges : next config 4 s4_993 = [s5_1243] := by decide
theorem s4_993_safe : Safe 9 4 s4_993 := by
  apply safe_succ 8 4 s4_993 [s5_1243] (by decide) s4_993_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1243_safe
def s4_994 : State := ⟨[35,4,64,140], 1481249143206845131456088112894607978725654, 1, 0, 1, 0⟩
theorem s4_994_edges : next config 4 s4_994 = [s5_1244] := by decide
theorem s4_994_safe : Safe 9 4 s4_994 := by
  apply safe_succ 8 4 s4_994 [s5_1244] (by decide) s4_994_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1244_safe
def s4_995 : State := ⟨[35,4,64,145], 44602511244162009098461845115863130680918302, 1, 0, 1, 0⟩
theorem s4_995_edges : next config 4 s4_995 = [s5_1319, s5_1275, s5_1245] := by decide
theorem s4_995_safe : Safe 9 4 s4_995 := by
  apply safe_succ 8 4 s4_995 [s5_1319, s5_1275, s5_1245] (by decide) s4_995_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1319_safe
  · subst z; exact s5_1275_safe
  · subst z; exact s5_1245_safe
def s4_996 : State := ⟨[35,4,64,145], 44602511244162009098461845115863139270852886, 1, 0, 1, 0⟩
theorem s4_996_edges : next config 4 s4_996 = [s5_1320, s5_1276, s5_1246] := by decide
theorem s4_996_safe : Safe 9 4 s4_996 := by
  apply safe_succ 8 4 s4_996 [s5_1320, s5_1276, s5_1246] (by decide) s4_996_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1320_safe
  · subst z; exact s5_1276_safe
  · subst z; exact s5_1246_safe
def s4_997 : State := ⟨[35,4,64,145], 66902575877958790363070636639296628650475806, 1, 0, 1, 0⟩
theorem s4_997_edges : next config 4 s4_997 = [s5_1321, s5_1277, s5_1247] := by decide
theorem s4_997_safe : Safe 9 4 s4_997 := by
  apply safe_succ 8 4 s4_997 [s5_1321, s5_1277, s5_1247] (by decide) s4_997_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1321_safe
  · subst z; exact s5_1277_safe
  · subst z; exact s5_1247_safe
def s4_998 : State := ⟨[35,4,64,145], 66902575877958790363070636639296637240410390, 1, 0, 1, 0⟩
theorem s4_998_edges : next config 4 s4_998 = [s5_1322, s5_1278, s5_1248] := by decide
theorem s4_998_safe : Safe 9 4 s4_998 := by
  apply safe_succ 8 4 s4_998 [s5_1322, s5_1278, s5_1248] (by decide) s4_998_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1322_safe
  · subst z; exact s5_1278_safe
  · subst z; exact s5_1248_safe
def s4_999 : State := ⟨[35,4,64,171], 2993155353341141744779827722513053345109426642682142, 1, 0, 1, 0⟩
theorem s4_999_edges : next config 4 s4_999 = [s5_1249] := by decide
theorem s4_999_safe : Safe 9 4 s4_999 := by
  apply safe_succ 8 4 s4_999 [s5_1249] (by decide) s4_999_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1249_safe
def s4_1000 : State := ⟨[35,4,64,171], 2993155353341141744779827722513053345109435232616726, 1, 0, 1, 0⟩
theorem s4_1000_edges : next config 4 s4_1000 = [s5_1250] := by decide
theorem s4_1000_safe : Safe 9 4 s4_1000 := by
  apply safe_succ 8 4 s4_1000 [s5_1250] (by decide) s4_1000_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1250_safe
def s4_1001 : State := ⟨[35,4,64,171], 3004847366352676682193696954528159709764141440893214, 1, 0, 1, 0⟩
theorem s4_1001_edges : next config 4 s4_1001 = [s5_1251] := by decide
theorem s4_1001_safe : Safe 9 4 s4_1001 := by
  apply safe_succ 8 4 s4_1001 [s5_1251] (by decide) s4_1001_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1251_safe
def s4_1002 : State := ⟨[35,4,64,171], 3004847366352676682193696954528159709764150030827798, 1, 0, 1, 0⟩
theorem s4_1002_edges : next config 4 s4_1002 = [s5_1252] := by decide
theorem s4_1002_safe : Safe 9 4 s4_1002 := by
  apply safe_succ 8 4 s4_1002 [s5_1252] (by decide) s4_1002_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1252_safe
def s4_1003 : State := ⟨[35,4,67,128], 340282367000166626143659641727352897822, 1, 0, 0, 0⟩
theorem s4_1003_edges : next config 4 s4_1003 = [s5_1323, s5_1279, s5_1229, s5_1216, s5_1235, s5_1213, s5_1218, s5_1222, s5_1226] := by decide
theorem s4_1003_safe : Safe 9 4 s4_1003 := by
  apply safe_succ 8 4 s4_1003 [s5_1323, s5_1279, s5_1229, s5_1216, s5_1235, s5_1213, s5_1218, s5_1222, s5_1226] (by decide) s4_1003_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1323_safe
  · subst z; exact s5_1279_safe
  · subst z; exact s5_1229_safe
  · subst z; exact s5_1216_safe
  · subst z; exact s5_1235_safe
  · subst z; exact s5_1213_safe
  · subst z; exact s5_1218_safe
  · subst z; exact s5_1222_safe
  · subst z; exact s5_1226_safe
def s4_1004 : State := ⟨[35,4,67,128], 340282367000166626143659641735942832406, 1, 0, 0, 0⟩
theorem s4_1004_edges : next config 4 s4_1004 = [s5_1324, s5_1280, s5_1230, s5_1217, s5_1236, s5_1214, s5_1219, s5_1223, s5_1227] := by decide
theorem s4_1004_safe : Safe 9 4 s4_1004 := by
  apply safe_succ 8 4 s4_1004 [s5_1324, s5_1280, s5_1230, s5_1217, s5_1236, s5_1214, s5_1219, s5_1223, s5_1227] (by decide) s4_1004_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1324_safe
  · subst z; exact s5_1280_safe
  · subst z; exact s5_1230_safe
  · subst z; exact s5_1217_safe
  · subst z; exact s5_1236_safe
  · subst z; exact s5_1214_safe
  · subst z; exact s5_1219_safe
  · subst z; exact s5_1223_safe
  · subst z; exact s5_1227_safe
def s4_1005 : State := ⟨[35,4,67,129], 1020847100762815390556144518997345370398, 1, 0, 1, 0⟩
theorem s4_1005_edges : next config 4 s4_1005 = [s5_1486, s5_1325, s5_1281, s5_1224] := by decide
theorem s4_1005_safe : Safe 9 4 s4_1005 := by
  apply safe_succ 8 4 s4_1005 [s5_1486, s5_1325, s5_1281, s5_1224] (by decide) s4_1005_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1486_safe
  · subst z; exact s5_1325_safe
  · subst z; exact s5_1281_safe
  · subst z; exact s5_1224_safe
def s4_1006 : State := ⟨[35,4,67,130], 1701411834604692317482893733860881793310, 1, 0, 1, 0⟩
theorem s4_1006_edges : next config 4 s4_1006 = [s5_1487, s5_1326, s5_1282] := by decide
theorem s4_1006_safe : Safe 9 4 s4_1006 := by
  apply safe_succ 8 4 s4_1006 [s5_1487, s5_1326, s5_1282] (by decide) s4_1006_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1487_safe
  · subst z; exact s5_1326_safe
  · subst z; exact s5_1282_safe
def s4_1007 : State := ⟨[35,4,67,131], 3062541302288446171336392163587954639134, 1, 0, 1, 0⟩
theorem s4_1007_edges : next config 4 s4_1007 = [s5_1488, s5_1327, s5_1283] := by decide
theorem s4_1007_safe : Safe 9 4 s4_1007 := by
  apply safe_succ 8 4 s4_1007 [s5_1488, s5_1327, s5_1283] (by decide) s4_1007_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1488_safe
  · subst z; exact s5_1327_safe
  · subst z; exact s5_1283_safe
def s4_1008 : State := ⟨[35,4,67,132], 5784800237655953879043389023042100330782, 1, 0, 1, 0⟩
theorem s4_1008_edges : next config 4 s4_1008 = [s5_1489, s5_1328, s5_1284, s5_1220] := by decide
theorem s4_1008_safe : Safe 9 4 s4_1008 := by
  apply safe_succ 8 4 s4_1008 [s5_1489, s5_1328, s5_1284, s5_1220] (by decide) s4_1008_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1489_safe
  · subst z; exact s5_1328_safe
  · subst z; exact s5_1284_safe
  · subst z; exact s5_1220_safe
def s4_1009 : State := ⟨[35,4,67,136], 87452568298681185110253294806666471080222, 1, 0, 1, 0⟩
theorem s4_1009_edges : next config 4 s4_1009 = [s5_1490, s5_1580, s5_1329, s5_1316, s5_1285, s5_1231, s5_1221] := by decide
theorem s4_1009_safe : Safe 9 4 s4_1009 := by
  apply safe_succ 8 4 s4_1009 [s5_1490, s5_1580, s5_1329, s5_1316, s5_1285, s5_1231, s5_1221] (by decide) s4_1009_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1490_safe
  · subst z; exact s5_1580_safe
  · subst z; exact s5_1329_safe
  · subst z; exact s5_1316_safe
  · subst z; exact s5_1285_safe
  · subst z; exact s5_1231_safe
  · subst z; exact s5_1221_safe
def s4_1010 : State := ⟨[35,4,67,144], 22301085480897544079999347667952495314927902, 1, 0, 1, 0⟩
theorem s4_1010_edges : next config 4 s4_1010 = [s5_1491, s5_1330, s5_1287] := by decide
theorem s4_1010_safe : Safe 9 4 s4_1010 := by
  apply safe_succ 8 4 s4_1010 [s5_1491, s5_1330, s5_1287] (by decide) s4_1010_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1491_safe
  · subst z; exact s5_1330_safe
  · subst z; exact s5_1287_safe
def s4_1011 : State := ⟨[35,4,67,160], 1461501637671185285124623296345678323789741490462, 1, 0, 1, 0⟩
theorem s4_1011_edges : next config 4 s4_1011 = [s5_1492, s5_1331, s5_1288] := by decide
theorem s4_1011_safe : Safe 9 4 s4_1011 := by
  apply safe_succ 8 4 s4_1011 [s5_1492, s5_1331, s5_1288] (by decide) s4_1011_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1492_safe
  · subst z; exact s5_1331_safe
  · subst z; exact s5_1288_safe
def s4_1012 : State := ⟨[35,4,67,163], 11692013098987505712550417125359659461381269291294, 1, 0, 1, 0⟩
theorem s4_1012_edges : next config 4 s4_1012 = [s5_1493, s5_1332, s5_1289, s5_1232] := by decide
theorem s4_1012_safe : Safe 9 4 s4_1012 := by
  apply safe_succ 8 4 s4_1012 [s5_1493, s5_1332, s5_1289, s5_1232] (by decide) s4_1012_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1493_safe
  · subst z; exact s5_1332_safe
  · subst z; exact s5_1289_safe
  · subst z; exact s5_1232_safe
def s4_1013 : State := ⟨[35,4,67,192], 6277101735386680764176071790128604879731750748597843460382, 1, 0, 1, 0⟩
theorem s4_1013_edges : next config 4 s4_1013 = [s5_1494, s5_1334, s5_1290] := by decide
theorem s4_1013_safe : Safe 9 4 s4_1013 := by
  apply safe_succ 8 4 s4_1013 [s5_1494, s5_1334, s5_1290] (by decide) s4_1013_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1494_safe
  · subst z; exact s5_1334_safe
  · subst z; exact s5_1290_safe
def s4_1014 : State := ⟨[35,4,67,195], 50216813883093446111026597752582269792448238859846085050654, 1, 0, 1, 0⟩
theorem s4_1014_edges : next config 4 s4_1014 = [s5_1495, s5_1335, s5_1291] := by decide
theorem s4_1014_safe : Safe 9 4 s4_1014 := by
  apply safe_succ 8 4 s4_1014 [s5_1495, s5_1335, s5_1291] (by decide) s4_1014_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1495_safe
  · subst z; exact s5_1335_safe
  · subst z; exact s5_1291_safe
def s4_1015 : State := ⟨[35,4,96,129], 1020847100842043552922834904001212907806, 1, 0, 1, 0⟩
theorem s4_1015_edges : next config 4 s4_1015 = [s5_1336, s5_1292, s5_1211, s5_1253, s5_1245] := by decide
theorem s4_1015_safe : Safe 9 4 s4_1015 := by
  apply safe_succ 8 4 s4_1015 [s5_1336, s5_1292, s5_1211, s5_1253, s5_1245] (by decide) s4_1015_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1336_safe
  · subst z; exact s5_1292_safe
  · subst z; exact s5_1211_safe
  · subst z; exact s5_1253_safe
  · subst z; exact s5_1245_safe
def s4_1016 : State := ⟨[35,4,96,129], 1020847100842043552922834904009802842390, 1, 0, 1, 0⟩
theorem s4_1016_edges : next config 4 s4_1016 = [s5_1337, s5_1293, s5_1212, s5_1254, s5_1246] := by decide
theorem s4_1016_safe : Safe 9 4 s4_1016 := by
  apply safe_succ 8 4 s4_1016 [s5_1337, s5_1293, s5_1212, s5_1254, s5_1246] (by decide) s4_1016_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1337_safe
  · subst z; exact s5_1293_safe
  · subst z; exact s5_1212_safe
  · subst z; exact s5_1254_safe
  · subst z; exact s5_1246_safe
def s4_1017 : State := ⟨[35,4,96,130], 1701411834683920479849584118864749330718, 1, 0, 1, 0⟩
theorem s4_1017_edges : next config 4 s4_1017 = [s5_1338, s5_1294, s5_1213, s5_1255] := by decide
theorem s4_1017_safe : Safe 9 4 s4_1017 := by
  apply safe_succ 8 4 s4_1017 [s5_1338, s5_1294, s5_1213, s5_1255] (by decide) s4_1017_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1338_safe
  · subst z; exact s5_1294_safe
  · subst z; exact s5_1213_safe
  · subst z; exact s5_1255_safe
def s4_1018 : State := ⟨[35,4,96,130], 1701411834683920479849584118873339265302, 1, 0, 1, 0⟩
theorem s4_1018_edges : next config 4 s4_1018 = [s5_1339, s5_1295, s5_1214, s5_1256] := by decide
theorem s4_1018_safe : Safe 9 4 s4_1018 := by
  apply safe_succ 8 4 s4_1018 [s5_1339, s5_1295, s5_1214, s5_1256] (by decide) s4_1018_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1339_safe
  · subst z; exact s5_1295_safe
  · subst z; exact s5_1214_safe
  · subst z; exact s5_1256_safe
def s4_1019 : State := ⟨[35,4,96,131], 3062541302367674333703082548591822176542, 1, 0, 1, 0⟩
theorem s4_1019_edges : next config 4 s4_1019 = [s5_1340, s5_1296, s5_1215, s5_1257] := by decide
theorem s4_1019_safe : Safe 9 4 s4_1019 := by
  apply safe_succ 8 4 s4_1019 [s5_1340, s5_1296, s5_1215, s5_1257] (by decide) s4_1019_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1340_safe
  · subst z; exact s5_1296_safe
  · subst z; exact s5_1215_safe
  · subst z; exact s5_1257_safe
def s4_1020 : State := ⟨[35,4,96,132], 5784800237735182041410079408045967868190, 1, 0, 1, 0⟩
theorem s4_1020_edges : next config 4 s4_1020 = [s5_1341, s5_1297, s5_1216, s5_1258, s5_1241] := by decide
theorem s4_1020_safe : Safe 9 4 s4_1020 := by
  apply safe_succ 8 4 s4_1020 [s5_1341, s5_1297, s5_1216, s5_1258, s5_1241] (by decide) s4_1020_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1341_safe
  · subst z; exact s5_1297_safe
  · subst z; exact s5_1216_safe
  · subst z; exact s5_1258_safe
  · subst z; exact s5_1241_safe
def s4_1021 : State := ⟨[35,4,96,132], 5784800237735182041410079408054557802774, 1, 0, 1, 0⟩
theorem s4_1021_edges : next config 4 s4_1021 = [s5_1342, s5_1298, s5_1217, s5_1259, s5_1242] := by decide
theorem s4_1021_safe : Safe 9 4 s4_1021 := by
  apply safe_succ 8 4 s4_1021 [s5_1342, s5_1298, s5_1217, s5_1259, s5_1242] (by decide) s4_1021_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1342_safe
  · subst z; exact s5_1298_safe
  · subst z; exact s5_1217_safe
  · subst z; exact s5_1259_safe
  · subst z; exact s5_1242_safe
def s4_1022 : State := ⟨[35,4,96,136], 87452568298760413272619985191670338617630, 1, 0, 1, 0⟩
theorem s4_1022_edges : next config 4 s4_1022 = [s5_1584, s5_1343, s5_1317, s5_1299, s5_1218, s5_1260, s5_1249, s5_1243] := by decide
theorem s4_1022_safe : Safe 9 4 s4_1022 := by
  apply safe_succ 8 4 s4_1022 [s5_1584, s5_1343, s5_1317, s5_1299, s5_1218, s5_1260, s5_1249, s5_1243] (by decide) s4_1022_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1584_safe
  · subst z; exact s5_1343_safe
  · subst z; exact s5_1317_safe
  · subst z; exact s5_1299_safe
  · subst z; exact s5_1218_safe
  · subst z; exact s5_1260_safe
  · subst z; exact s5_1249_safe
  · subst z; exact s5_1243_safe
def s4_1023 : State := ⟨[35,4,96,136], 87452568298760413272619985191678928552214, 1, 0, 1, 0⟩
theorem s4_1023_edges : next config 4 s4_1023 = [s5_1585, s5_1344, s5_1318, s5_1300, s5_1219, s5_1261, s5_1250, s5_1244] := by decide
theorem s4_1023_safe : Safe 9 4 s4_1023 := by
  apply safe_succ 8 4 s4_1023 [s5_1585, s5_1344, s5_1318, s5_1300, s5_1219, s5_1261, s5_1250, s5_1244] (by decide) s4_1023_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1585_safe
  · subst z; exact s5_1344_safe
  · subst z; exact s5_1318_safe
  · subst z; exact s5_1300_safe
  · subst z; exact s5_1219_safe
  · subst z; exact s5_1261_safe
  · subst z; exact s5_1250_safe
  · subst z; exact s5_1244_safe
def s4_1024 : State := ⟨[35,4,96,144], 22301085480897623308161714358337499182465310, 1, 0, 1, 0⟩
theorem s4_1024_edges : next config 4 s4_1024 = [s5_1345, s5_1303, s5_1222, s5_1262] := by decide
theorem s4_1024_safe : Safe 9 4 s4_1024 := by
  apply safe_succ 8 4 s4_1024 [s5_1345, s5_1303, s5_1222, s5_1262] (by decide) s4_1024_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1345_safe
  · subst z; exact s5_1303_safe
  · subst z; exact s5_1222_safe
  · subst z; exact s5_1262_safe
def s4_1025 : State := ⟨[35,4,96,144], 22301085480897623308161714358337507772399894, 1, 0, 1, 0⟩
theorem s4_1025_edges : next config 4 s4_1025 = [s5_1346, s5_1304, s5_1223, s5_1263] := by decide
theorem s4_1025_safe : Safe 9 4 s4_1025 := by
  apply safe_succ 8 4 s4_1025 [s5_1346, s5_1304, s5_1223, s5_1263] (by decide) s4_1025_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1346_safe
  · subst z; exact s5_1304_safe
  · subst z; exact s5_1223_safe
  · subst z; exact s5_1263_safe
def s4_1026 : State := ⟨[35,4,96,160], 1461501637671185285203851458712368708793609027870, 1, 0, 1, 0⟩
theorem s4_1026_edges : next config 4 s4_1026 = [s5_1347, s5_1305, s5_1226, s5_1264] := by decide
theorem s4_1026_safe : Safe 9 4 s4_1026 := by
  apply safe_succ 8 4 s4_1026 [s5_1347, s5_1305, s5_1226, s5_1264] (by decide) s4_1026_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1347_safe
  · subst z; exact s5_1305_safe
  · subst z; exact s5_1226_safe
  · subst z; exact s5_1264_safe
def s4_1027 : State := ⟨[35,4,96,160], 1461501637671185285203851458712368708802198962454, 1, 0, 1, 0⟩
theorem s4_1027_edges : next config 4 s4_1027 = [s5_1348, s5_1306, s5_1227, s5_1265] := by decide
theorem s4_1027_safe : Safe 9 4 s4_1027 := by
  apply safe_succ 8 4 s4_1027 [s5_1348, s5_1306, s5_1227, s5_1265] (by decide) s4_1027_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1348_safe
  · subst z; exact s5_1306_safe
  · subst z; exact s5_1227_safe
  · subst z; exact s5_1265_safe
def s4_1028 : State := ⟨[35,4,96,161], 2923003275002088203407536291428651728458131505430, 1, 0, 1, 0⟩
theorem s4_1028_edges : next config 4 s4_1028 = [s5_1349, s5_1307, s5_1228, s5_1266] := by decide
theorem s4_1028_safe : Safe 9 4 s4_1028 := by
  apply safe_succ 8 4 s4_1028 [s5_1349, s5_1307, s5_1228, s5_1266] (by decide) s4_1028_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1349_safe
  · subst z; exact s5_1307_safe
  · subst z; exact s5_1228_safe
  · subst z; exact s5_1266_safe
def s4_1029 : State := ⟨[35,4,96,163], 11692013098987505712629645287726349846385136828702, 1, 0, 1, 0⟩
theorem s4_1029_edges : next config 4 s4_1029 = [s5_1350, s5_1308, s5_1229, s5_1267, s5_1251] := by decide
theorem s4_1029_safe : Safe 9 4 s4_1029 := by
  apply safe_succ 8 4 s4_1029 [s5_1350, s5_1308, s5_1229, s5_1267, s5_1251] (by decide) s4_1029_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1350_safe
  · subst z; exact s5_1308_safe
  · subst z; exact s5_1229_safe
  · subst z; exact s5_1267_safe
  · subst z; exact s5_1251_safe
def s4_1030 : State := ⟨[35,4,96,163], 11692013098987505712629645287726349846393726763286, 1, 0, 1, 0⟩
theorem s4_1030_edges : next config 4 s4_1030 = [s5_1351, s5_1309, s5_1230, s5_1268, s5_1252] := by decide
theorem s4_1030_safe : Safe 9 4 s4_1030 := by
  apply safe_succ 8 4 s4_1030 [s5_1351, s5_1309, s5_1230, s5_1268, s5_1252] (by decide) s4_1030_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1351_safe
  · subst z; exact s5_1309_safe
  · subst z; exact s5_1230_safe
  · subst z; exact s5_1268_safe
  · subst z; exact s5_1252_safe
def s4_1031 : State := ⟨[35,4,96,192], 6277101735386680764176071790207833042098441133601710997790, 1, 0, 1, 0⟩
theorem s4_1031_edges : next config 4 s4_1031 = [s5_1354, s5_1310, s5_1233, s5_1269] := by decide
theorem s4_1031_safe : Safe 9 4 s4_1031 := by
  apply safe_succ 8 4 s4_1031 [s5_1354, s5_1310, s5_1233, s5_1269] (by decide) s4_1031_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1354_safe
  · subst z; exact s5_1310_safe
  · subst z; exact s5_1233_safe
  · subst z; exact s5_1269_safe
def s4_1032 : State := ⟨[35,4,96,192], 6277101735386680764176071790207833042098441133610300932374, 1, 0, 1, 0⟩
theorem s4_1032_edges : next config 4 s4_1032 = [s5_1355, s5_1311, s5_1234, s5_1270] := by decide
theorem s4_1032_safe : Safe 9 4 s4_1032 := by
  apply safe_succ 8 4 s4_1032 [s5_1355, s5_1311, s5_1234, s5_1270] (by decide) s4_1032_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1355_safe
  · subst z; exact s5_1311_safe
  · subst z; exact s5_1234_safe
  · subst z; exact s5_1270_safe
def s4_1033 : State := ⟨[35,4,96,224], 26959946667150639794667015087359913040637311048536658170241286734110, 1, 0, 1, 0⟩
theorem s4_1033_edges : next config 4 s4_1033 = [s5_1356, s5_1312, s5_1237, s5_1271] := by decide
theorem s4_1033_safe : Safe 9 4 s4_1033 := by
  apply safe_succ 8 4 s4_1033 [s5_1356, s5_1312, s5_1237, s5_1271] (by decide) s4_1033_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1356_safe
  · subst z; exact s5_1312_safe
  · subst z; exact s5_1237_safe
  · subst z; exact s5_1271_safe
def s4_1034 : State := ⟨[35,4,96,224], 26959946667150639794667015087359913040637311048536658170249876668694, 1, 0, 1, 0⟩
theorem s4_1034_edges : next config 4 s4_1034 = [s5_1357, s5_1313, s5_1238, s5_1272] := by decide
theorem s4_1034_safe : Safe 9 4 s4_1034 := by
  apply safe_succ 8 4 s4_1034 [s5_1357, s5_1313, s5_1238, s5_1272] (by decide) s4_1034_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1357_safe
  · subst z; exact s5_1313_safe
  · subst z; exact s5_1238_safe
  · subst z; exact s5_1272_safe
def s4_1035 : State := ⟨[35,4,104,128], 340282387282576229647756113084927770910, 1, 0, 0, 0⟩
theorem s4_1035_edges : next config 4 s4_1035 = [s5_1358, s5_1314, s5_1267, s5_1258, s5_1273, s5_1255, s5_1260, s5_1262, s5_1264] := by decide
theorem s4_1035_safe : Safe 9 4 s4_1035 := by
  apply safe_succ 8 4 s4_1035 [s5_1358, s5_1314, s5_1267, s5_1258, s5_1273, s5_1255, s5_1260, s5_1262, s5_1264] (by decide) s4_1035_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1358_safe
  · subst z; exact s5_1314_safe
  · subst z; exact s5_1267_safe
  · subst z; exact s5_1258_safe
  · subst z; exact s5_1273_safe
  · subst z; exact s5_1255_safe
  · subst z; exact s5_1260_safe
  · subst z; exact s5_1262_safe
  · subst z; exact s5_1264_safe
def s4_1036 : State := ⟨[35,4,104,128], 340282387282576229647756113093517705494, 1, 0, 0, 0⟩
theorem s4_1036_edges : next config 4 s4_1036 = [s5_1359, s5_1315, s5_1268, s5_1259, s5_1274, s5_1256, s5_1261, s5_1263, s5_1265] := by decide
theorem s4_1036_safe : Safe 9 4 s4_1036 := by
  apply safe_succ 8 4 s4_1036 [s5_1359, s5_1315, s5_1268, s5_1259, s5_1274, s5_1256, s5_1261, s5_1263, s5_1265] (by decide) s4_1036_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1359_safe
  · subst z; exact s5_1315_safe
  · subst z; exact s5_1268_safe
  · subst z; exact s5_1259_safe
  · subst z; exact s5_1274_safe
  · subst z; exact s5_1256_safe
  · subst z; exact s5_1261_safe
  · subst z; exact s5_1263_safe
  · subst z; exact s5_1265_safe
def s4_1037 : State := ⟨[35,12,64,129], 1020847100762815390408570566407668961566, 3, 0, 1, 0⟩
theorem s4_1037_edges : next config 4 s4_1037 = [s5_1186, s5_1292, s5_1275] := by decide
theorem s4_1037_safe : Safe 9 4 s4_1037 := by
  apply safe_succ 8 4 s4_1037 [s5_1186, s5_1292, s5_1275] (by decide) s4_1037_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1186_safe
  · subst z; exact s5_1292_safe
  · subst z; exact s5_1275_safe
def s4_1038 : State := ⟨[35,12,64,129], 1020847100762815390408570566416258896150, 3, 0, 1, 0⟩
theorem s4_1038_edges : next config 4 s4_1038 = [s5_1187, s5_1293, s5_1276] := by decide
theorem s4_1038_safe : Safe 9 4 s4_1038 := by
  apply safe_succ 8 4 s4_1038 [s5_1187, s5_1293, s5_1276] (by decide) s4_1038_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1187_safe
  · subst z; exact s5_1293_safe
  · subst z; exact s5_1276_safe
def s4_1039 : State := ⟨[35,12,64,130], 1701411834604692317335319781271205384478, 3, 0, 1, 0⟩
theorem s4_1039_edges : next config 4 s4_1039 = [s5_1188, s5_1294] := by decide
theorem s4_1039_safe : Safe 9 4 s4_1039 := by
  apply safe_succ 8 4 s4_1039 [s5_1188, s5_1294] (by decide) s4_1039_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1188_safe
  · subst z; exact s5_1294_safe
def s4_1040 : State := ⟨[35,12,64,130], 1701411834604692317335319781279795319062, 3, 0, 1, 0⟩
theorem s4_1040_edges : next config 4 s4_1040 = [s5_1189, s5_1295] := by decide
theorem s4_1040_safe : Safe 9 4 s4_1040 := by
  apply safe_succ 8 4 s4_1040 [s5_1189, s5_1295] (by decide) s4_1040_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1189_safe
  · subst z; exact s5_1295_safe
def s4_1041 : State := ⟨[35,12,64,131], 3062541302288446171188818210998278230302, 3, 0, 1, 0⟩
theorem s4_1041_edges : next config 4 s4_1041 = [s5_1190, s5_1296] := by decide
theorem s4_1041_safe : Safe 9 4 s4_1041 := by
  apply safe_succ 8 4 s4_1041 [s5_1190, s5_1296] (by decide) s4_1041_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1190_safe
  · subst z; exact s5_1296_safe
def s4_1042 : State := ⟨[35,12,64,132], 5784800237655953878895815070452423921950, 3, 0, 1, 0⟩
theorem s4_1042_edges : next config 4 s4_1042 = [s5_1191, s5_1297] := by decide
theorem s4_1042_safe : Safe 9 4 s4_1042 := by
  apply safe_succ 8 4 s4_1042 [s5_1191, s5_1297] (by decide) s4_1042_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1191_safe
  · subst z; exact s5_1297_safe
def s4_1043 : State := ⟨[35,12,64,132], 5784800237655953878895815070461013856534, 3, 0, 1, 0⟩
theorem s4_1043_edges : next config 4 s4_1043 = [s5_1192, s5_1298] := by decide
theorem s4_1043_safe : Safe 9 4 s4_1043 := by
  apply safe_succ 8 4 s4_1043 [s5_1192, s5_1298] (by decide) s4_1043_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1192_safe
  · subst z; exact s5_1298_safe
def s4_1044 : State := ⟨[35,12,64,136], 87452568298681185110105720854076794671390, 3, 0, 1, 0⟩
theorem s4_1044_edges : next config 4 s4_1044 = [s5_1193, s5_1299] := by decide
theorem s4_1044_safe : Safe 9 4 s4_1044 := by
  apply safe_succ 8 4 s4_1044 [s5_1193, s5_1299] (by decide) s4_1044_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1193_safe
  · subst z; exact s5_1299_safe
def s4_1045 : State := ⟨[35,12,64,136], 87452568298681185110105720854085384605974, 3, 0, 1, 0⟩
theorem s4_1045_edges : next config 4 s4_1045 = [s5_1194, s5_1300] := by decide
theorem s4_1045_safe : Safe 9 4 s4_1045 := by
  apply safe_succ 8 4 s4_1045 [s5_1194, s5_1300] (by decide) s4_1045_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1194_safe
  · subst z; exact s5_1300_safe
def s4_1046 : State := ⟨[35,12,64,140], 1394136857275084884809464213392066726662430, 3, 0, 1, 0⟩
theorem s4_1046_edges : next config 4 s4_1046 = [s5_1197, s5_1301] := by decide
theorem s4_1046_safe : Safe 9 4 s4_1046 := by
  apply safe_succ 8 4 s4_1046 [s5_1197, s5_1301] (by decide) s4_1046_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1197_safe
  · subst z; exact s5_1301_safe
def s4_1047 : State := ⟨[35,12,64,140], 1394136857275084884809464213392075316597014, 3, 0, 1, 0⟩
theorem s4_1047_edges : next config 4 s4_1047 = [s5_1198, s5_1302] := by decide
theorem s4_1047_safe : Safe 9 4 s4_1047 := by
  apply safe_succ 8 4 s4_1047 [s5_1198, s5_1302] (by decide) s4_1047_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1198_safe
  · subst z; exact s5_1302_safe
def s4_1048 : State := ⟨[35,12,64,144], 22301085480897544079999200093999905638519070, 3, 0, 1, 0⟩
theorem s4_1048_edges : next config 4 s4_1048 = [s5_1199, s5_1303] := by decide
theorem s4_1048_safe : Safe 9 4 s4_1048 := by
  apply safe_succ 8 4 s4_1048 [s5_1199, s5_1303] (by decide) s4_1048_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1199_safe
  · subst z; exact s5_1303_safe
def s4_1049 : State := ⟨[35,12,64,144], 22301085480897544079999200093999914228453654, 3, 0, 1, 0⟩
theorem s4_1049_edges : next config 4 s4_1049 = [s5_1200, s5_1304] := by decide
theorem s4_1049_safe : Safe 9 4 s4_1049 := by
  apply safe_succ 8 4 s4_1049 [s5_1200, s5_1304] (by decide) s4_1049_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1200_safe
  · subst z; exact s5_1304_safe
def s4_1050 : State := ⟨[35,12,64,160], 1461501637671185285124623296198104371200065081630, 3, 0, 1, 0⟩
theorem s4_1050_edges : next config 4 s4_1050 = [s5_1203, s5_1305] := by decide
theorem s4_1050_safe : Safe 9 4 s4_1050 := by
  apply safe_succ 8 4 s4_1050 [s5_1203, s5_1305] (by decide) s4_1050_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1203_safe
  · subst z; exact s5_1305_safe
def s4_1051 : State := ⟨[35,12,64,160], 1461501637671185285124623296198104371208655016214, 3, 0, 1, 0⟩
theorem s4_1051_edges : next config 4 s4_1051 = [s5_1204, s5_1306] := by decide
theorem s4_1051_safe : Safe 9 4 s4_1051 := by
  apply safe_succ 8 4 s4_1051 [s5_1204, s5_1306] (by decide) s4_1051_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1204_safe
  · subst z; exact s5_1306_safe
def s4_1052 : State := ⟨[35,12,64,161], 2923003275002088203328308128914387390864587559190, 3, 0, 1, 0⟩
theorem s4_1052_edges : next config 4 s4_1052 = [s5_1205, s5_1307] := by decide
theorem s4_1052_safe : Safe 9 4 s4_1052 := by
  apply safe_succ 8 4 s4_1052 [s5_1205, s5_1307] (by decide) s4_1052_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1205_safe
  · subst z; exact s5_1307_safe
def s4_1053 : State := ⟨[35,12,64,163], 11692013098987505712550417125212085508791592882462, 3, 0, 1, 0⟩
theorem s4_1053_edges : next config 4 s4_1053 = [s5_1206, s5_1308] := by decide
theorem s4_1053_safe : Safe 9 4 s4_1053 := by
  apply safe_succ 8 4 s4_1053 [s5_1206, s5_1308] (by decide) s4_1053_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1206_safe
  · subst z; exact s5_1308_safe
def s4_1054 : State := ⟨[35,12,64,163], 11692013098987505712550417125212085508800182817046, 3, 0, 1, 0⟩
theorem s4_1054_edges : next config 4 s4_1054 = [s5_1207, s5_1309] := by decide
theorem s4_1054_safe : Safe 9 4 s4_1054 := by
  apply safe_succ 8 4 s4_1054 [s5_1207, s5_1309] (by decide) s4_1054_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1207_safe
  · subst z; exact s5_1309_safe
def s4_1055 : State := ⟨[35,12,64,192], 6277101735386680764176071790128604879584176796008167051550, 3, 0, 1, 0⟩
theorem s4_1055_edges : next config 4 s4_1055 = [s5_1208, s5_1310] := by decide
theorem s4_1055_safe : Safe 9 4 s4_1055 := by
  apply safe_succ 8 4 s4_1055 [s5_1208, s5_1310] (by decide) s4_1055_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1208_safe
  · subst z; exact s5_1310_safe
def s4_1056 : State := ⟨[35,12,64,192], 6277101735386680764176071790128604879584176796016756986134, 3, 0, 1, 0⟩
theorem s4_1056_edges : next config 4 s4_1056 = [s5_1209, s5_1311] := by decide
theorem s4_1056_safe : Safe 9 4 s4_1056 := by
  apply safe_succ 8 4 s4_1056 [s5_1209, s5_1311] (by decide) s4_1056_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1209_safe
  · subst z; exact s5_1311_safe
def s4_1057 : State := ⟨[35,12,67,128], 340282366920938463629395304133808951582, 3, 0, 0, 0⟩
theorem s4_1057_edges : next config 4 s4_1057 = [s5_1497, s5_1210, s5_1289, s5_1286, s5_1291, s5_1282, s5_1285, s5_1287, s5_1288] := by decide
theorem s4_1057_safe : Safe 9 4 s4_1057 := by
  apply safe_succ 8 4 s4_1057 [s5_1497, s5_1210, s5_1289, s5_1286, s5_1291, s5_1282, s5_1285, s5_1287, s5_1288] (by decide) s4_1057_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1497_safe
  · subst z; exact s5_1210_safe
  · subst z; exact s5_1289_safe
  · subst z; exact s5_1286_safe
  · subst z; exact s5_1291_safe
  · subst z; exact s5_1282_safe
  · subst z; exact s5_1285_safe
  · subst z; exact s5_1287_safe
  · subst z; exact s5_1288_safe
def s4_1058 : State := ⟨[35,12,96,128], 340282367000166625996085689137676488990, 3, 0, 0, 0⟩
theorem s4_1058_edges : next config 4 s4_1058 = [s5_1239, s5_1279, s5_1314, s5_1308, s5_1301, s5_1312, s5_1294, s5_1299, s5_1303, s5_1305] := by decide
theorem s4_1058_safe : Safe 9 4 s4_1058 := by
  apply safe_succ 8 4 s4_1058 [s5_1239, s5_1279, s5_1314, s5_1308, s5_1301, s5_1312, s5_1294, s5_1299, s5_1303, s5_1305] (by decide) s4_1058_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1239_safe
  · subst z; exact s5_1279_safe
  · subst z; exact s5_1314_safe
  · subst z; exact s5_1308_safe
  · subst z; exact s5_1301_safe
  · subst z; exact s5_1312_safe
  · subst z; exact s5_1294_safe
  · subst z; exact s5_1299_safe
  · subst z; exact s5_1303_safe
  · subst z; exact s5_1305_safe
def s4_1059 : State := ⟨[35,12,96,128], 340282367000166625996085689146266423574, 3, 0, 0, 0⟩
theorem s4_1059_edges : next config 4 s4_1059 = [s5_1240, s5_1280, s5_1315, s5_1309, s5_1302, s5_1313, s5_1295, s5_1300, s5_1304, s5_1306] := by decide
theorem s4_1059_safe : Safe 9 4 s4_1059 := by
  apply safe_succ 8 4 s4_1059 [s5_1240, s5_1280, s5_1315, s5_1309, s5_1302, s5_1313, s5_1295, s5_1300, s5_1304, s5_1306] (by decide) s4_1059_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1240_safe
  · subst z; exact s5_1280_safe
  · subst z; exact s5_1315_safe
  · subst z; exact s5_1309_safe
  · subst z; exact s5_1302_safe
  · subst z; exact s5_1313_safe
  · subst z; exact s5_1295_safe
  · subst z; exact s5_1300_safe
  · subst z; exact s5_1304_safe
  · subst z; exact s5_1306_safe
def s4_1060 : State := ⟨[35,140,64,136], 1481249143206845131456088112894599388791070, 3, 0, 1, 0⟩
theorem s4_1060_edges : next config 4 s4_1060 = [s5_1195, s5_1317] := by decide
theorem s4_1060_safe : Safe 9 4 s4_1060 := by
  apply safe_succ 8 4 s4_1060 [s5_1195, s5_1317] (by decide) s4_1060_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1195_safe
  · subst z; exact s5_1317_safe
def s4_1061 : State := ⟨[35,140,64,136], 1481249143206845131456088112894607978725654, 3, 0, 1, 0⟩
theorem s4_1061_edges : next config 4 s4_1061 = [s5_1196, s5_1318] := by decide
theorem s4_1061_safe : Safe 9 4 s4_1061 := by
  apply safe_succ 8 4 s4_1061 [s5_1196, s5_1318] (by decide) s4_1061_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1196_safe
  · subst z; exact s5_1318_safe
def s4_1062 : State := ⟨[43,4,64,129], 1020847100762815390408570575203761979678, 1, 0, 1, 0⟩
theorem s4_1062_edges : next config 4 s4_1062 = [s5_1336, s5_1319] := by decide
theorem s4_1062_safe : Safe 9 4 s4_1062 := by
  apply safe_succ 8 4 s4_1062 [s5_1336, s5_1319] (by decide) s4_1062_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1336_safe
  · subst z; exact s5_1319_safe
def s4_1063 : State := ⟨[43,4,64,129], 1020847100762815390408570575212351914262, 1, 0, 1, 0⟩
theorem s4_1063_edges : next config 4 s4_1063 = [s5_1337, s5_1320] := by decide
theorem s4_1063_safe : Safe 9 4 s4_1063 := by
  apply safe_succ 8 4 s4_1063 [s5_1337, s5_1320] (by decide) s4_1063_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1337_safe
  · subst z; exact s5_1320_safe
def s4_1064 : State := ⟨[43,4,64,130], 1701411834604692317335319790067298402590, 1, 0, 1, 0⟩
theorem s4_1064_edges : next config 4 s4_1064 = [s5_1338] := by decide
theorem s4_1064_safe : Safe 9 4 s4_1064 := by
  apply safe_succ 8 4 s4_1064 [s5_1338] (by decide) s4_1064_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1338_safe
def s4_1065 : State := ⟨[43,4,64,130], 1701411834604692317335319790075888337174, 1, 0, 1, 0⟩
theorem s4_1065_edges : next config 4 s4_1065 = [s5_1339] := by decide
theorem s4_1065_safe : Safe 9 4 s4_1065 := by
  apply safe_succ 8 4 s4_1065 [s5_1339] (by decide) s4_1065_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1339_safe
def s4_1066 : State := ⟨[43,4,64,131], 3062541302288446171188818219794371248414, 1, 0, 1, 0⟩
theorem s4_1066_edges : next config 4 s4_1066 = [s5_1340] := by decide
theorem s4_1066_safe : Safe 9 4 s4_1066 := by
  apply safe_succ 8 4 s4_1066 [s5_1340] (by decide) s4_1066_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1340_safe
def s4_1067 : State := ⟨[43,4,64,132], 5784800237655953878895815079248516940062, 1, 0, 1, 0⟩
theorem s4_1067_edges : next config 4 s4_1067 = [s5_1341] := by decide
theorem s4_1067_safe : Safe 9 4 s4_1067 := by
  apply safe_succ 8 4 s4_1067 [s5_1341] (by decide) s4_1067_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1341_safe
def s4_1068 : State := ⟨[43,4,64,132], 5784800237655953878895815079257106874646, 1, 0, 1, 0⟩
theorem s4_1068_edges : next config 4 s4_1068 = [s5_1342] := by decide
theorem s4_1068_safe : Safe 9 4 s4_1068 := by
  apply safe_succ 8 4 s4_1068 [s5_1342] (by decide) s4_1068_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1342_safe
def s4_1069 : State := ⟨[43,4,64,136], 87452568298681185110105720862872887689502, 1, 0, 1, 0⟩
theorem s4_1069_edges : next config 4 s4_1069 = [s5_1343] := by decide
theorem s4_1069_safe : Safe 9 4 s4_1069 := by
  apply safe_succ 8 4 s4_1069 [s5_1343] (by decide) s4_1069_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1343_safe
def s4_1070 : State := ⟨[43,4,64,136], 87452568298681185110105720862881477624086, 1, 0, 1, 0⟩
theorem s4_1070_edges : next config 4 s4_1070 = [s5_1344] := by decide
theorem s4_1070_safe : Safe 9 4 s4_1070 := by
  apply safe_succ 8 4 s4_1070 [s5_1344] (by decide) s4_1070_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1344_safe
def s4_1071 : State := ⟨[43,4,64,144], 22301085480897544079999200094008701731537182, 1, 0, 1, 0⟩
theorem s4_1071_edges : next config 4 s4_1071 = [s5_1345] := by decide
theorem s4_1071_safe : Safe 9 4 s4_1071 := by
  apply safe_succ 8 4 s4_1071 [s5_1345] (by decide) s4_1071_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1345_safe
def s4_1072 : State := ⟨[43,4,64,144], 22301085480897544079999200094008710321471766, 1, 0, 1, 0⟩
theorem s4_1072_edges : next config 4 s4_1072 = [s5_1346] := by decide
theorem s4_1072_safe : Safe 9 4 s4_1072 := by
  apply safe_succ 8 4 s4_1072 [s5_1346] (by decide) s4_1072_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1346_safe
def s4_1073 : State := ⟨[43,4,64,160], 1461501637671185285124623296198104379996158099742, 1, 0, 1, 0⟩
theorem s4_1073_edges : next config 4 s4_1073 = [s5_1347] := by decide
theorem s4_1073_safe : Safe 9 4 s4_1073 := by
  apply safe_succ 8 4 s4_1073 [s5_1347] (by decide) s4_1073_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1347_safe
def s4_1074 : State := ⟨[43,4,64,160], 1461501637671185285124623296198104380004748034326, 1, 0, 1, 0⟩
theorem s4_1074_edges : next config 4 s4_1074 = [s5_1348] := by decide
theorem s4_1074_safe : Safe 9 4 s4_1074 := by
  apply safe_succ 8 4 s4_1074 [s5_1348] (by decide) s4_1074_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1348_safe
def s4_1075 : State := ⟨[43,4,64,161], 2923003275002088203328308128914387399660680577302, 1, 0, 1, 0⟩
theorem s4_1075_edges : next config 4 s4_1075 = [s5_1349] := by decide
theorem s4_1075_safe : Safe 9 4 s4_1075 := by
  apply safe_succ 8 4 s4_1075 [s5_1349] (by decide) s4_1075_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1349_safe
def s4_1076 : State := ⟨[43,4,64,163], 11692013098987505712550417125212085517587685900574, 1, 0, 1, 0⟩
theorem s4_1076_edges : next config 4 s4_1076 = [s5_1350] := by decide
theorem s4_1076_safe : Safe 9 4 s4_1076 := by
  apply safe_succ 8 4 s4_1076 [s5_1350] (by decide) s4_1076_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1350_safe
def s4_1077 : State := ⟨[43,4,64,163], 11692013098987505712550417125212085517596275835158, 1, 0, 1, 0⟩
theorem s4_1077_edges : next config 4 s4_1077 = [s5_1351] := by decide
theorem s4_1077_safe : Safe 9 4 s4_1077 := by
  apply safe_succ 8 4 s4_1077 [s5_1351] (by decide) s4_1077_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1351_safe
def s4_1078 : State := ⟨[43,4,64,171], 2993155353254029458848067475866429445615690073571614, 1, 0, 1, 0⟩
theorem s4_1078_edges : next config 4 s4_1078 = [s5_1352] := by decide
theorem s4_1078_safe : Safe 9 4 s4_1078 := by
  apply safe_succ 8 4 s4_1078 [s5_1352] (by decide) s4_1078_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1352_safe
def s4_1079 : State := ⟨[43,4,64,171], 2993155353254029458848067475866429445615698663506198, 1, 0, 1, 0⟩
theorem s4_1079_edges : next config 4 s4_1079 = [s5_1353] := by decide
theorem s4_1079_safe : Safe 9 4 s4_1079 := by
  apply safe_succ 8 4 s4_1079 [s5_1353] (by decide) s4_1079_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1353_safe
def s4_1080 : State := ⟨[43,4,64,192], 6277101735386680764176071790128604879584176804804260069662, 1, 0, 1, 0⟩
theorem s4_1080_edges : next config 4 s4_1080 = [s5_1354] := by decide
theorem s4_1080_safe : Safe 9 4 s4_1080 := by
  apply safe_succ 8 4 s4_1080 [s5_1354] (by decide) s4_1080_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1354_safe
def s4_1081 : State := ⟨[43,4,64,192], 6277101735386680764176071790128604879584176804812850004246, 1, 0, 1, 0⟩
theorem s4_1081_edges : next config 4 s4_1081 = [s5_1355] := by decide
theorem s4_1081_safe : Safe 9 4 s4_1081 := by
  apply safe_succ 8 4 s4_1081 [s5_1355] (by decide) s4_1081_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1355_safe
def s4_1082 : State := ⟨[43,4,67,128], 340282366920938463629395312929901969694, 1, 0, 0, 0⟩
theorem s4_1082_edges : next config 4 s4_1082 = [s5_1533, s5_1333, s5_1328, s5_1335, s5_1326, s5_1329, s5_1330, s5_1331] := by decide
theorem s4_1082_safe : Safe 9 4 s4_1082 := by
  apply safe_succ 8 4 s4_1082 [s5_1533, s5_1333, s5_1328, s5_1335, s5_1326, s5_1329, s5_1330, s5_1331] (by decide) s4_1082_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1533_safe
  · subst z; exact s5_1333_safe
  · subst z; exact s5_1328_safe
  · subst z; exact s5_1335_safe
  · subst z; exact s5_1326_safe
  · subst z; exact s5_1329_safe
  · subst z; exact s5_1330_safe
  · subst z; exact s5_1331_safe
def s4_1083 : State := ⟨[43,4,96,128], 340282367000166625996085697933769507102, 1, 0, 0, 0⟩
theorem s4_1083_edges : next config 4 s4_1083 = [s5_1358, s5_1352, s5_1341, s5_1356, s5_1338, s5_1343, s5_1345, s5_1347] := by decide
theorem s4_1083_safe : Safe 9 4 s4_1083 := by
  apply safe_succ 8 4 s4_1083 [s5_1358, s5_1352, s5_1341, s5_1356, s5_1338, s5_1343, s5_1345, s5_1347] (by decide) s4_1083_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1358_safe
  · subst z; exact s5_1352_safe
  · subst z; exact s5_1341_safe
  · subst z; exact s5_1356_safe
  · subst z; exact s5_1338_safe
  · subst z; exact s5_1343_safe
  · subst z; exact s5_1345_safe
  · subst z; exact s5_1347_safe
def s4_1084 : State := ⟨[43,4,96,128], 340282367000166625996085697942359441686, 1, 0, 0, 0⟩
theorem s4_1084_edges : next config 4 s4_1084 = [s5_1359, s5_1353, s5_1342, s5_1357, s5_1339, s5_1344, s5_1346, s5_1348] := by decide
theorem s4_1084_safe : Safe 9 4 s4_1084 := by
  apply safe_succ 8 4 s4_1084 [s5_1359, s5_1353, s5_1342, s5_1357, s5_1339, s5_1344, s5_1346, s5_1348] (by decide) s4_1084_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1359_safe
  · subst z; exact s5_1353_safe
  · subst z; exact s5_1342_safe
  · subst z; exact s5_1357_safe
  · subst z; exact s5_1339_safe
  · subst z; exact s5_1344_safe
  · subst z; exact s5_1346_safe
  · subst z; exact s5_1348_safe
def s4_1085 : State := ⟨[49,4,96,145], 44601830679428246449697432631548776282259734, 1, 0, 1, 0⟩
theorem s4_1085_edges : next config 4 s4_1085 = [s5_1364, s5_1363] := by decide
theorem s4_1085_safe : Safe 9 4 s4_1085 := by
  apply safe_succ 8 4 s4_1085 [s5_1364, s5_1363] (by decide) s4_1085_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1364_safe
  · subst z; exact s5_1363_safe
def s4_1086 : State := ⟨[49,12,64,145], 44601830679428167221534918367211182738313494, 3, 0, 1, 0⟩
theorem s4_1086_edges : next config 4 s4_1086 = [s5_1361, s5_1364] := by decide
theorem s4_1086_safe : Safe 9 4 s4_1086 := by
  apply safe_succ 8 4 s4_1086 [s5_1361, s5_1364] (by decide) s4_1086_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1361_safe
  · subst z; exact s5_1364_safe
def s4_1087 : State := ⟨[49,21,64,145], 44601830679428167221534918367211182740406550, 3, 0, 1, 0⟩
theorem s4_1087_edges : next config 4 s4_1087 = [s5_1365] := by decide
theorem s4_1087_safe : Safe 9 4 s4_1087 := by
  apply safe_succ 8 4 s4_1087 [s5_1365] (by decide) s4_1087_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1365_safe
def s4_1088 : State := ⟨[53,4,64,145], 44601830679428167221534918375655432041726230, 1, 0, 1, 0⟩
theorem s4_1088_edges : next config 4 s4_1088 = [s5_1366] := by decide
theorem s4_1088_safe : Safe 9 4 s4_1088 := by
  apply safe_succ 8 4 s4_1088 [s5_1366] (by decide) s4_1088_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1366_safe
def s4_1089 : State := ⟨[65,4,64,129], 1020847100762815390445464054520728326422, 3, 2, 1, 0⟩
theorem s4_1089_edges : next config 4 s4_1089 = [s5_2, s5_1375, s5_1367] := by decide
theorem s4_1089_safe : Safe 9 4 s4_1089 := by
  apply safe_succ 8 4 s4_1089 [s5_2, s5_1375, s5_1367] (by decide) s4_1089_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_2_safe
  · subst z; exact s5_1375_safe
  · subst z; exact s5_1367_safe
def s4_1090 : State := ⟨[65,4,64,130], 1701411834604692317372213269384264749334, 3, 2, 1, 0⟩
theorem s4_1090_edges : next config 4 s4_1090 = [s5_5, s5_1377, s5_1369, s5_1371] := by decide
theorem s4_1090_safe : Safe 9 4 s4_1090 := by
  apply safe_succ 8 4 s4_1090 [s5_5, s5_1377, s5_1369, s5_1371] (by decide) s4_1090_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_5_safe
  · subst z; exact s5_1377_safe
  · subst z; exact s5_1369_safe
  · subst z; exact s5_1371_safe
def s4_1091 : State := ⟨[65,4,64,132], 5784800237655953878932708558565483286806, 3, 2, 1, 0⟩
theorem s4_1091_edges : next config 4 s4_1091 = [s5_10, s5_1379] := by decide
theorem s4_1091_safe : Safe 9 4 s4_1091 := by
  apply safe_succ 8 4 s4_1091 [s5_10, s5_1379] (by decide) s4_1091_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_10_safe
  · subst z; exact s5_1379_safe
def s4_1092 : State := ⟨[65,4,64,136], 87452568298681185110142614342189854036246, 3, 2, 1, 0⟩
theorem s4_1092_edges : next config 4 s4_1092 = [s5_13, s5_1381] := by decide
theorem s4_1092_safe : Safe 9 4 s4_1092 := by
  apply safe_succ 8 4 s4_1092 [s5_13, s5_1381] (by decide) s4_1092_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_13_safe
  · subst z; exact s5_1381_safe
def s4_1093 : State := ⟨[65,4,64,136], 1481249143206845131456125006382712448155926, 3, 2, 1, 0⟩
theorem s4_1093_edges : next config 4 s4_1093 = [s5_16, s5_1383] := by decide
theorem s4_1093_safe : Safe 9 4 s4_1093 := by
  apply safe_succ 8 4 s4_1093 [s5_16, s5_1383] (by decide) s4_1093_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_16_safe
  · subst z; exact s5_1383_safe
def s4_1094 : State := ⟨[65,4,64,140], 1394136857275084884809501106880179786027286, 3, 2, 1, 0⟩
theorem s4_1094_edges : next config 4 s4_1094 = [s5_19, s5_1384] := by decide
theorem s4_1094_safe : Safe 9 4 s4_1094 := by
  apply safe_succ 8 4 s4_1094 [s5_19, s5_1384] (by decide) s4_1094_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_19_safe
  · subst z; exact s5_1384_safe
def s4_1095 : State := ⟨[65,4,64,144], 22301085480897544079999236987488018697883926, 3, 2, 1, 0⟩
theorem s4_1095_edges : next config 4 s4_1095 = [s5_22, s5_1385, s5_1370, s5_1373] := by decide
theorem s4_1095_safe : Safe 9 4 s4_1095 := by
  apply safe_succ 8 4 s4_1095 [s5_22, s5_1385, s5_1370, s5_1373] (by decide) s4_1095_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_22_safe
  · subst z; exact s5_1385_safe
  · subst z; exact s5_1370_safe
  · subst z; exact s5_1373_safe
def s4_1096 : State := ⟨[65,4,64,145], 44601830679428167221534955260136380203991318, 1, 1, 1, 0⟩
theorem s4_1096_edges : next config 4 s4_1096 = [s5_1431, s5_1387] := by decide
theorem s4_1096_safe : Safe 9 4 s4_1096 := by
  apply safe_succ 8 4 s4_1096 [s5_1431, s5_1387] (by decide) s4_1096_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1431_safe
  · subst z; exact s5_1387_safe
def s4_1097 : State := ⟨[65,4,64,160], 1461501637671185285124623296234997859313124446486, 3, 2, 1, 0⟩
theorem s4_1097_edges : next config 4 s4_1097 = [s5_30, s5_1388, s5_1372, s5_1374] := by decide
theorem s4_1097_safe : Safe 9 4 s4_1097 := by
  apply safe_succ 8 4 s4_1097 [s5_30, s5_1388, s5_1372, s5_1374] (by decide) s4_1097_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_30_safe
  · subst z; exact s5_1388_safe
  · subst z; exact s5_1372_safe
  · subst z; exact s5_1374_safe
def s4_1098 : State := ⟨[65,4,64,192], 6277101735386680764176071790128604879621070284121226416406, 3, 2, 1, 0⟩
theorem s4_1098_edges : next config 4 s4_1098 = [s5_49, s5_1390] := by decide
theorem s4_1098_safe : Safe 9 4 s4_1098 := by
  apply safe_succ 8 4 s4_1098 [s5_49, s5_1390] (by decide) s4_1098_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_49_safe
  · subst z; exact s5_1390_safe
def s4_1099 : State := ⟨[65,4,64,193], 12554203470773361528011861213336271295723425728585260929302, 3, 2, 1, 0⟩
theorem s4_1099_edges : next config 4 s4_1099 = [s5_51, s5_1392] := by decide
theorem s4_1099_safe : Safe 9 4 s4_1099 := by
  apply safe_succ 8 4 s4_1099 [s5_51, s5_1392] (by decide) s4_1099_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_51_safe
  · subst z; exact s5_1392_safe
def s4_1100 : State := ⟨[65,4,96,128], 340282367000166626032979177250735853846, 3, 2, 0, 0⟩
theorem s4_1100_edges : next config 4 s4_1100 = [s5_1400, s5_1392, s5_1379, s5_1394, s5_1377, s5_1381, s5_1385, s5_1388] := by decide
theorem s4_1100_safe : Safe 9 4 s4_1100 := by
  apply safe_succ 8 4 s4_1100 [s5_1400, s5_1392, s5_1379, s5_1394, s5_1377, s5_1381, s5_1385, s5_1388] (by decide) s4_1100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1400_safe
  · subst z; exact s5_1392_safe
  · subst z; exact s5_1379_safe
  · subst z; exact s5_1394_safe
  · subst z; exact s5_1377_safe
  · subst z; exact s5_1381_safe
  · subst z; exact s5_1385_safe
  · subst z; exact s5_1388_safe
def s4_1101 : State := ⟨[65,4,96,128], 340282368267817226261208578747439055126, 3, 2, 0, 0⟩
theorem s4_1101_edges : next config 4 s4_1101 = [s5_1401, s5_1393, s5_1380, s5_1395, s5_1378, s5_1382, s5_1386, s5_1389] := by decide
theorem s4_1101_safe : Safe 9 4 s4_1101 := by
  apply safe_succ 8 4 s4_1101 [s5_1401, s5_1393, s5_1380, s5_1395, s5_1378, s5_1382, s5_1386, s5_1389] (by decide) s4_1101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1401_safe
  · subst z; exact s5_1393_safe
  · subst z; exact s5_1380_safe
  · subst z; exact s5_1395_safe
  · subst z; exact s5_1378_safe
  · subst z; exact s5_1382_safe
  · subst z; exact s5_1386_safe
  · subst z; exact s5_1389_safe
def s4_1102 : State := ⟨[65,4,96,140], 1399581375145899128387429364936681621356822, 1, 0, 1, 0⟩
theorem s4_1102_edges : next config 4 s4_1102 = [s5_1403] := by decide
theorem s4_1102_safe : Safe 9 4 s4_1102 := by
  apply safe_succ 8 4 s4_1102 [s5_1403] (by decide) s4_1102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1403_safe
def s4_1103 : State := ⟨[65,4,96,140], 1481249143206924359618639270720305992106262, 1, 0, 1, 0⟩
theorem s4_1103_edges : next config 4 s4_1103 = [s5_1404] := by decide
theorem s4_1103_safe : Safe 9 4 s4_1103 := by
  apply safe_succ 8 4 s4_1103 [s5_1404] (by decide) s4_1103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1404_safe
def s4_1104 : State := ⟨[65,4,96,145], 44602511244162088326624396273688837284233494, 1, 0, 1, 0⟩
theorem s4_1104_edges : next config 4 s4_1104 = [s5_1452, s5_1432, s5_1398, s5_1429, s5_1405] := by decide
theorem s4_1104_safe : Safe 9 4 s4_1104 := by
  apply safe_succ 8 4 s4_1104 [s5_1452, s5_1432, s5_1398, s5_1429, s5_1405] (by decide) s4_1104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1452_safe
  · subst z; exact s5_1432_safe
  · subst z; exact s5_1398_safe
  · subst z; exact s5_1429_safe
  · subst z; exact s5_1405_safe
def s4_1105 : State := ⟨[65,4,96,145], 66902575877958869591233187797122335253790998, 1, 0, 1, 0⟩
theorem s4_1105_edges : next config 4 s4_1105 = [s5_1453, s5_1433, s5_1399, s5_1430, s5_1406] := by decide
theorem s4_1105_safe : Safe 9 4 s4_1105 := by
  apply safe_succ 8 4 s4_1105 [s5_1453, s5_1433, s5_1399, s5_1430, s5_1406] (by decide) s4_1105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1453_safe
  · subst z; exact s5_1433_safe
  · subst z; exact s5_1399_safe
  · subst z; exact s5_1430_safe
  · subst z; exact s5_1406_safe
def s4_1106 : State := ⟨[65,4,96,146], 89204682205957176486622759568200423832617238, 1, 0, 1, 0⟩
theorem s4_1106_edges : next config 4 s4_1106 = [s5_1434, s5_1407] := by decide
theorem s4_1106_safe : Safe 9 4 s4_1106 := by
  apply safe_succ 8 4 s4_1106 [s5_1434, s5_1407] (by decide) s4_1106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1434_safe
  · subst z; exact s5_1407_safe
def s4_1107 : State := ⟨[65,4,96,146], 111504066275020115874304624342419058265751830, 1, 0, 1, 0⟩
theorem s4_1107_edges : next config 4 s4_1107 = [s5_1435, s5_1408] := by decide
theorem s4_1107_safe : Safe 9 4 s4_1107 := by
  apply safe_succ 8 4 s4_1107 [s5_1435, s5_1408] (by decide) s4_1107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1435_safe
  · subst z; exact s5_1408_safe
def s4_1108 : State := ⟨[65,4,96,162], 5846006551025023507498659810751609685601538867478, 1, 0, 1, 0⟩
theorem s4_1108_edges : next config 4 s4_1108 = [s5_1436, s5_1409] := by decide
theorem s4_1108_safe : Safe 9 4 s4_1108 := by
  apply safe_succ 8 4 s4_1108 [s5_1436, s5_1409] (by decide) s4_1108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1436_safe
  · subst z; exact s5_1409_safe
def s4_1109 : State := ⟨[65,4,96,162], 7307508186994796958018590789614394275530398564630, 1, 0, 1, 0⟩
theorem s4_1109_edges : next config 4 s4_1109 = [s5_1437, s5_1410] := by decide
theorem s4_1109_safe : Safe 9 4 s4_1109 := by
  apply safe_succ 8 4 s4_1109 [s5_1437, s5_1410] (by decide) s4_1109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1437_safe
  · subst z; exact s5_1410_safe
def s4_1110 : State := ⟨[65,4,96,176], 95780971326419139128294312505056075227996807378305302, 1, 0, 1, 0⟩
theorem s4_1110_edges : next config 4 s4_1110 = [s5_1438, s5_1411] := by decide
theorem s4_1110_safe : Safe 9 4 s4_1110 := by
  apply safe_succ 8 4 s4_1110 [s5_1438, s5_1411] (by decide) s4_1110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1438_safe
  · subst z; exact s5_1411_safe
def s4_1111 : State := ⟨[65,4,96,176], 95782432805755724832681893048353073238368101804867862, 1, 0, 1, 0⟩
theorem s4_1111_edges : next config 4 s4_1111 = [s5_1439, s5_1412] := by decide
theorem s4_1111_safe : Safe 9 4 s4_1111 := by
  apply safe_succ 8 4 s4_1111 [s5_1439, s5_1412] (by decide) s4_1111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1439_safe
  · subst z; exact s5_1412_safe
def s4_1112 : State := ⟨[65,4,96,228], 431359146674410236714672241398098891015929492802096132593816791220502, 1, 0, 1, 0⟩
theorem s4_1112_edges : next config 4 s4_1112 = [s5_1413] := by decide
theorem s4_1112_safe : Safe 9 4 s4_1112 := by
  apply safe_succ 8 4 s4_1112 [s5_1413] (by decide) s4_1112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1413_safe
def s4_1113 : State := ⟨[65,4,96,228], 458319093341560876509339256479674003818831621809222711356012110086422, 1, 0, 1, 0⟩
theorem s4_1113_edges : next config 4 s4_1113 = [s5_1414] := by decide
theorem s4_1113_safe : Safe 9 4 s4_1113 := by
  apply safe_succ 8 4 s4_1113 [s5_1414] (by decide) s4_1113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1414_safe
def s4_1114 : State := ⟨[65,4,100,129], 1020847102109694153187957793610975478038, 1, 0, 1, 0⟩
theorem s4_1114_edges : next config 4 s4_1114 = [s5_1398] := by decide
theorem s4_1114_safe : Safe 9 4 s4_1114 := by
  apply safe_succ 8 4 s4_1114 [s5_1398] (by decide) s4_1114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1398_safe
def s4_1115 : State := ⟨[65,4,100,130], 1701411835951571080114707008474511900950, 1, 0, 1, 0⟩
theorem s4_1115_edges : next config 4 s4_1115 = [] := by decide
theorem s4_1115_safe : Safe 9 4 s4_1115 := by
  apply safe_succ 8 4 s4_1115 [] (by decide) s4_1115_edges
  simp
def s4_1116 : State := ⟨[65,4,100,132], 5784800239002832641675202297655730438422, 1, 0, 1, 0⟩
theorem s4_1116_edges : next config 4 s4_1116 = [] := by decide
theorem s4_1116_safe : Safe 9 4 s4_1116 := by
  apply safe_succ 8 4 s4_1116 [] (by decide) s4_1116_edges
  simp
def s4_1117 : State := ⟨[65,4,100,136], 87452568300028063872885108081280101187862, 1, 0, 1, 0⟩
theorem s4_1117_edges : next config 4 s4_1117 = [] := by decide
theorem s4_1117_safe : Safe 9 4 s4_1117 := by
  apply safe_succ 8 4 s4_1117 [] (by decide) s4_1117_edges
  simp
def s4_1118 : State := ⟨[65,4,100,144], 22301085480898890958761979481227108945035542, 1, 0, 1, 0⟩
theorem s4_1118_edges : next config 4 s4_1118 = [] := by decide
theorem s4_1118_safe : Safe 9 4 s4_1118 := by
  apply safe_succ 8 4 s4_1118 [] (by decide) s4_1118_edges
  simp
def s4_1119 : State := ⟨[65,4,100,160], 1461501637671185286471502058977491598403371598102, 1, 0, 1, 0⟩
theorem s4_1119_edges : next config 4 s4_1119 = [] := by decide
theorem s4_1119_safe : Safe 9 4 s4_1119 := by
  apply safe_succ 8 4 s4_1119 [] (by decide) s4_1119_edges
  simp
def s4_1120 : State := ⟨[65,4,100,192], 6277101735386680764176071791475483642363564023211473568022, 1, 0, 1, 0⟩
theorem s4_1120_edges : next config 4 s4_1120 = [] := by decide
theorem s4_1120_safe : Safe 9 4 s4_1120 := by
  apply safe_succ 8 4 s4_1120 [] (by decide) s4_1120_edges
  simp
def s4_1121 : State := ⟨[65,4,100,193], 12554203470773361528011861214683150058465919467675508080918, 1, 0, 1, 0⟩
theorem s4_1121_edges : next config 4 s4_1121 = [] := by decide
theorem s4_1121_safe : Safe 9 4 s4_1121 := by
  apply safe_succ 8 4 s4_1121 [] (by decide) s4_1121_edges
  simp
def s4_1122 : State := ⟨[65,4,100,224], 26959946667150639794667015087359913041904961648801781059851049304342, 1, 0, 1, 0⟩
theorem s4_1122_edges : next config 4 s4_1122 = [] := by decide
theorem s4_1122_safe : Safe 9 4 s4_1122 := by
  apply safe_succ 8 4 s4_1122 [] (by decide) s4_1122_edges
  simp
def s4_1123 : State := ⟨[65,4,100,228], 431359146674410236714672241392654373146462127986910368276405203042582, 1, 0, 1, 0⟩
theorem s4_1123_edges : next config 4 s4_1123 = [] := by decide
theorem s4_1123_safe : Safe 9 4 s4_1123 := by
  apply safe_succ 8 4 s4_1123 [] (by decide) s4_1123_edges
  simp
def s4_1124 : State := ⟨[65,4,104,129], 1020847121124453156611398816061523558678, 1, 0, 1, 0⟩
theorem s4_1124_edges : next config 4 s4_1124 = [s5_1465, s5_1440, s5_1417, s5_1405] := by decide
theorem s4_1124_safe : Safe 9 4 s4_1124 := by
  apply safe_succ 8 4 s4_1124 [s5_1465, s5_1440, s5_1417, s5_1405] (by decide) s4_1124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1465_safe
  · subst z; exact s5_1440_safe
  · subst z; exact s5_1417_safe
  · subst z; exact s5_1405_safe
def s4_1125 : State := ⟨[65,4,104,130], 1701411854966330083538148030925059981590, 1, 0, 1, 0⟩
theorem s4_1125_edges : next config 4 s4_1125 = [s5_1466, s5_1441, s5_1418, s5_1407, s5_1409] := by decide
theorem s4_1125_safe : Safe 9 4 s4_1125 := by
  apply safe_succ 8 4 s4_1125 [s5_1466, s5_1441, s5_1418, s5_1407, s5_1409] (by decide) s4_1125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1466_safe
  · subst z; exact s5_1441_safe
  · subst z; exact s5_1418_safe
  · subst z; exact s5_1407_safe
  · subst z; exact s5_1409_safe
def s4_1126 : State := ⟨[65,4,104,132], 5784800258017591645098643320106278519062, 1, 0, 1, 0⟩
theorem s4_1126_edges : next config 4 s4_1126 = [s5_1467, s5_1442, s5_1419, s5_1428, s5_1415, s5_1403] := by decide
theorem s4_1126_safe : Safe 9 4 s4_1126 := by
  apply safe_succ 8 4 s4_1126 [s5_1467, s5_1442, s5_1419, s5_1428, s5_1415, s5_1403] (by decide) s4_1126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_1467_safe
  · subst z; exact s5_1442_safe
  · subst z; exact s5_1419_safe
  · subst z; exact s5_1428_safe
  · subst z; exact s5_1415_safe
  · subst z; exact s5_1403_safe
def s4_1127 : State := ⟨[65,4,104,136], 87452568319042822876308549103730649268502, 1, 0, 1, 0⟩
theorem s4_1127_edges : next config 4 s4_1127 = [s5_1468, s5_1476, s5_1443, s5_1420, s5_1404] := by decide
theorem s4_1127_safe : Safe 9 4 s4_1127 := by
  apply safe_succ 8 4 s4_1127 [s5_1468, s5_1476, s5_1443, s5_1420, s5_1404] (by decide) s4_1127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1468_safe
  · subst z; exact s5_1476_safe
  · subst z; exact s5_1443_safe
  · subst z; exact s5_1420_safe
  · subst z; exact s5_1404_safe
def s4_1128 : State := ⟨[65,4,104,144], 22301085480917905717765402922249559493116182, 1, 0, 1, 0⟩
theorem s4_1128_edges : next config 4 s4_1128 = [s5_1469, s5_1445, s5_1421, s5_1408, s5_1411] := by decide
theorem s4_1128_safe : Safe 9 4 s4_1128 := by
  apply safe_succ 8 4 s4_1128 [s5_1469, s5_1445, s5_1421, s5_1408, s5_1411] (by decide) s4_1128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1469_safe
  · subst z; exact s5_1445_safe
  · subst z; exact s5_1421_safe
  · subst z; exact s5_1408_safe
  · subst z; exact s5_1411_safe
def s4_1129 : State := ⟨[65,4,104,160], 1461501637671185305486261062400932620853919678742, 1, 0, 1, 0⟩
theorem s4_1129_edges : next config 4 s4_1129 = [s5_1470, s5_1446, s5_1422, s5_1410, s5_1412] := by decide
theorem s4_1129_safe : Safe 9 4 s4_1129 := by
  apply safe_succ 8 4 s4_1129 [s5_1470, s5_1446, s5_1422, s5_1410, s5_1412] (by decide) s4_1129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1470_safe
  · subst z; exact s5_1446_safe
  · subst z; exact s5_1422_safe
  · subst z; exact s5_1410_safe
  · subst z; exact s5_1412_safe
def s4_1130 : State := ⟨[65,4,104,192], 6277101735386680764176071810490242645787005045662021648662, 1, 0, 1, 0⟩
theorem s4_1130_edges : next config 4 s4_1130 = [s5_1471, s5_1447, s5_1423] := by decide
theorem s4_1130_safe : Safe 9 4 s4_1130 := by
  apply safe_succ 8 4 s4_1130 [s5_1471, s5_1447, s5_1423] (by decide) s4_1130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1471_safe
  · subst z; exact s5_1447_safe
  · subst z; exact s5_1423_safe
def s4_1131 : State := ⟨[65,4,104,193], 12554203470773361528011861233697909061889360490126056161558, 1, 0, 1, 0⟩
theorem s4_1131_edges : next config 4 s4_1131 = [s5_1472, s5_1448, s5_1424] := by decide
theorem s4_1131_safe : Safe 9 4 s4_1131 := by
  apply safe_succ 8 4 s4_1131 [s5_1472, s5_1448, s5_1424] (by decide) s4_1131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1472_safe
  · subst z; exact s5_1448_safe
  · subst z; exact s5_1424_safe
def s4_1132 : State := ⟨[65,4,104,224], 26959946667150639794667015087359913060919720652225222082301597384982, 1, 0, 1, 0⟩
theorem s4_1132_edges : next config 4 s4_1132 = [s5_1473, s5_1477, s5_1449, s5_1425, s5_1414] := by decide
theorem s4_1132_safe : Safe 9 4 s4_1132 := by
  apply safe_succ 8 4 s4_1132 [s5_1473, s5_1477, s5_1449, s5_1425, s5_1414] (by decide) s4_1132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1473_safe
  · subst z; exact s5_1477_safe
  · subst z; exact s5_1449_safe
  · subst z; exact s5_1425_safe
  · subst z; exact s5_1414_safe
def s4_1133 : State := ⟨[65,4,104,232], 6901746346790563787434755862277365734838391548400071204763722210935062, 1, 0, 1, 0⟩
theorem s4_1133_edges : next config 4 s4_1133 = [s5_1474, s5_1478, s5_1450, s5_1426, s5_1416] := by decide
theorem s4_1133_safe : Safe 9 4 s4_1133 := by
  apply safe_succ 8 4 s4_1133 [s5_1474, s5_1478, s5_1450, s5_1426, s5_1416] (by decide) s4_1133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_1474_safe
  · subst z; exact s5_1478_safe
  · subst z; exact s5_1450_safe
  · subst z; exact s5_1426_safe
  · subst z; exact s5_1416_safe
def s4_1134 : State := ⟨[65,4,108,128], 340282711801129888111376384354007712022, 1, 0, 0, 0⟩
theorem s4_1134_edges : next config 4 s4_1134 = [s5_1424, s5_1419, s5_1427, s5_1418, s5_1420, s5_1421, s5_1422] := by decide
theorem s4_1134_safe : Safe 9 4 s4_1134 := by
  apply safe_succ 8 4 s4_1134 [s5_1424, s5_1419, s5_1427, s5_1418, s5_1420, s5_1421, s5_1422] (by decide) s4_1134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1424_safe
  · subst z; exact s5_1419_safe
  · subst z; exact s5_1427_safe
  · subst z; exact s5_1418_safe
  · subst z; exact s5_1420_safe
  · subst z; exact s5_1421_safe
  · subst z; exact s5_1422_safe
def s4_1135 : State := ⟨[65,4,228,132], 431359146674410236714672241398098891015929492802096132593816791220502, 1, 0, 1, 0⟩
theorem s4_1135_edges : next config 4 s4_1135 = [] := by decide
theorem s4_1135_safe : Safe 9 4 s4_1135 := by
  apply safe_succ 8 4 s4_1135 [] (by decide) s4_1135_edges
  simp
def s4_1136 : State := ⟨[65,12,64,145], 44602511244162009098461882009351243740287254, 3, 0, 1, 0⟩
theorem s4_1136_edges : next config 4 s4_1136 = [s5_521, s5_1367, s5_1432] := by decide
theorem s4_1136_safe : Safe 9 4 s4_1136 := by
  apply safe_succ 8 4 s4_1136 [s5_521, s5_1367, s5_1432] (by decide) s4_1136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_521_safe
  · subst z; exact s5_1367_safe
  · subst z; exact s5_1432_safe
def s4_1137 : State := ⟨[65,12,64,145], 66902575877958790363070673532784741709844758, 3, 0, 1, 0⟩
theorem s4_1137_edges : next config 4 s4_1137 = [s5_524, s5_1368, s5_1433] := by decide
theorem s4_1137_safe : Safe 9 4 s4_1137 := by
  apply safe_succ 8 4 s4_1137 [s5_524, s5_1368, s5_1433] (by decide) s4_1137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_524_safe
  · subst z; exact s5_1368_safe
  · subst z; exact s5_1433_safe
def s4_1138 : State := ⟨[65,12,64,146], 89204682205957097258460245303862830288670998, 3, 0, 1, 0⟩
theorem s4_1138_edges : next config 4 s4_1138 = [s5_526, s5_1369, s5_1434] := by decide
theorem s4_1138_safe : Safe 9 4 s4_1138 := by
  apply safe_succ 8 4 s4_1138 [s5_526, s5_1369, s5_1434] (by decide) s4_1138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_526_safe
  · subst z; exact s5_1369_safe
  · subst z; exact s5_1434_safe
def s4_1139 : State := ⟨[65,12,64,146], 111504066275020036646142110078081464721805590, 3, 0, 1, 0⟩
theorem s4_1139_edges : next config 4 s4_1139 = [s5_529, s5_1370, s5_1435] := by decide
theorem s4_1139_safe : Safe 9 4 s4_1139 := by
  apply safe_succ 8 4 s4_1139 [s5_529, s5_1370, s5_1435] (by decide) s4_1139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_529_safe
  · subst z; exact s5_1370_safe
  · subst z; exact s5_1435_safe
def s4_1140 : State := ⟨[65,12,64,162], 5846006551025023507419431648237345348007994921238, 3, 0, 1, 0⟩
theorem s4_1140_edges : next config 4 s4_1140 = [s5_531, s5_1371, s5_1436] := by decide
theorem s4_1140_safe : Safe 9 4 s4_1140 := by
  apply safe_succ 8 4 s4_1140 [s5_531, s5_1371, s5_1436] (by decide) s4_1140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_531_safe
  · subst z; exact s5_1371_safe
  · subst z; exact s5_1436_safe
def s4_1141 : State := ⟨[65,12,64,162], 7307508186994796957939362627100129937936854618390, 3, 0, 1, 0⟩
theorem s4_1141_edges : next config 4 s4_1141 = [s5_534, s5_1372, s5_1437] := by decide
theorem s4_1141_safe : Safe 9 4 s4_1141 := by
  apply safe_succ 8 4 s4_1141 [s5_534, s5_1372, s5_1437] (by decide) s4_1141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_534_safe
  · subst z; exact s5_1372_safe
  · subst z; exact s5_1437_safe
def s4_1142 : State := ⟨[65,12,64,176], 95780971326419139128294233276893560963659213834359062, 3, 0, 1, 0⟩
theorem s4_1142_edges : next config 4 s4_1142 = [s5_542, s5_1373, s5_1438] := by decide
theorem s4_1142_safe : Safe 9 4 s4_1142 := by
  apply safe_succ 8 4 s4_1142 [s5_542, s5_1373, s5_1438] (by decide) s4_1142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_542_safe
  · subst z; exact s5_1373_safe
  · subst z; exact s5_1438_safe
def s4_1143 : State := ⟨[65,12,64,176], 95782432805755724832681813820190558974030508260921622, 3, 0, 1, 0⟩
theorem s4_1143_edges : next config 4 s4_1143 = [s5_544, s5_1374, s5_1439] := by decide
theorem s4_1143_safe : Safe 9 4 s4_1143 := by
  apply safe_succ 8 4 s4_1143 [s5_544, s5_1374, s5_1439] (by decide) s4_1143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_544_safe
  · subst z; exact s5_1374_safe
  · subst z; exact s5_1439_safe
def s4_1144 : State := ⟨[65,12,96,129], 1020847100842043552959728392114272276758, 3, 0, 1, 0⟩
theorem s4_1144_edges : next config 4 s4_1144 = [s5_1375, s5_1440, s5_1432] := by decide
theorem s4_1144_safe : Safe 9 4 s4_1144 := by
  apply safe_succ 8 4 s4_1144 [s5_1375, s5_1440, s5_1432] (by decide) s4_1144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1375_safe
  · subst z; exact s5_1440_safe
  · subst z; exact s5_1432_safe
def s4_1145 : State := ⟨[65,12,96,130], 1701411834683920479886477606977808699670, 3, 0, 1, 0⟩
theorem s4_1145_edges : next config 4 s4_1145 = [s5_1377, s5_1441, s5_1434, s5_1436] := by decide
theorem s4_1145_safe : Safe 9 4 s4_1145 := by
  apply safe_succ 8 4 s4_1145 [s5_1377, s5_1441, s5_1434, s5_1436] (by decide) s4_1145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1377_safe
  · subst z; exact s5_1441_safe
  · subst z; exact s5_1434_safe
  · subst z; exact s5_1436_safe
def s4_1146 : State := ⟨[65,12,96,132], 5784800237735182041446972896159027237142, 3, 0, 1, 0⟩
theorem s4_1146_edges : next config 4 s4_1146 = [s5_1379, s5_1442] := by decide
theorem s4_1146_safe : Safe 9 4 s4_1146 := by
  apply safe_succ 8 4 s4_1146 [s5_1379, s5_1442] (by decide) s4_1146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1379_safe
  · subst z; exact s5_1442_safe
def s4_1147 : State := ⟨[65,12,96,136], 87452568298760413272656878679783397986582, 3, 0, 1, 0⟩
theorem s4_1147_edges : next config 4 s4_1147 = [s5_1381, s5_1443] := by decide
theorem s4_1147_safe : Safe 9 4 s4_1147 := by
  apply safe_succ 8 4 s4_1147 [s5_1381, s5_1443] (by decide) s4_1147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1381_safe
  · subst z; exact s5_1443_safe
def s4_1148 : State := ⟨[65,12,96,140], 1394136857275164112972015371217773329977622, 3, 0, 1, 0⟩
theorem s4_1148_edges : next config 4 s4_1148 = [s5_1384, s5_1444] := by decide
theorem s4_1148_safe : Safe 9 4 s4_1148 := by
  apply safe_succ 8 4 s4_1148 [s5_1384, s5_1444] (by decide) s4_1148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1384_safe
  · subst z; exact s5_1444_safe
def s4_1149 : State := ⟨[65,12,96,144], 22301085480897623308161751251825612241834262, 3, 0, 1, 0⟩
theorem s4_1149_edges : next config 4 s4_1149 = [s5_1385, s5_1445, s5_1435, s5_1438] := by decide
theorem s4_1149_safe : Safe 9 4 s4_1149 := by
  apply safe_succ 8 4 s4_1149 [s5_1385, s5_1445, s5_1435, s5_1438] (by decide) s4_1149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1385_safe
  · subst z; exact s5_1445_safe
  · subst z; exact s5_1435_safe
  · subst z; exact s5_1438_safe
def s4_1150 : State := ⟨[65,12,96,160], 1461501637671185285203851458749262196906668396822, 3, 0, 1, 0⟩
theorem s4_1150_edges : next config 4 s4_1150 = [s5_1388, s5_1446, s5_1437, s5_1439] := by decide
theorem s4_1150_safe : Safe 9 4 s4_1150 := by
  apply safe_succ 8 4 s4_1150 [s5_1388, s5_1446, s5_1437, s5_1439] (by decide) s4_1150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_1388_safe
  · subst z; exact s5_1446_safe
  · subst z; exact s5_1437_safe
  · subst z; exact s5_1439_safe
def s4_1151 : State := ⟨[65,12,96,192], 6277101735386680764176071790207833042135334621714770366742, 3, 0, 1, 0⟩
theorem s4_1151_edges : next config 4 s4_1151 = [s5_1390, s5_1447] := by decide
theorem s4_1151_safe : Safe 9 4 s4_1151 := by
  apply safe_succ 8 4 s4_1151 [s5_1390, s5_1447] (by decide) s4_1151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1390_safe
  · subst z; exact s5_1447_safe
def s4_1152 : State := ⟨[65,12,96,193], 12554203470773361528011861213415499458237690066178804879638, 3, 0, 1, 0⟩
theorem s4_1152_edges : next config 4 s4_1152 = [s5_1392, s5_1448] := by decide
theorem s4_1152_safe : Safe 9 4 s4_1152 := by
  apply safe_succ 8 4 s4_1152 [s5_1392, s5_1448] (by decide) s4_1152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1392_safe
  · subst z; exact s5_1448_safe
def s4_1153 : State := ⟨[65,12,96,224], 26959946667150639794667015087359913040637311048573551658354346103062, 3, 0, 1, 0⟩
theorem s4_1153_edges : next config 4 s4_1153 = [s5_1394, s5_1449] := by decide
theorem s4_1153_safe : Safe 9 4 s4_1153 := by
  apply safe_succ 8 4 s4_1153 [s5_1394, s5_1449] (by decide) s4_1153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1394_safe
  · subst z; exact s5_1449_safe
def s4_1154 : State := ⟨[65,12,104,128], 340282387282576229684649601197987139862, 3, 0, 0, 0⟩
theorem s4_1154_edges : next config 4 s4_1154 = [s5_1400, s5_1448, s5_1444, s5_1450, s5_1441, s5_1443, s5_1445, s5_1446] := by decide
theorem s4_1154_safe : Safe 9 4 s4_1154 := by
  apply safe_succ 8 4 s4_1154 [s5_1400, s5_1448, s5_1444, s5_1450, s5_1441, s5_1443, s5_1445, s5_1446] (by decide) s4_1154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1400_safe
  · subst z; exact s5_1448_safe
  · subst z; exact s5_1444_safe
  · subst z; exact s5_1450_safe
  · subst z; exact s5_1441_safe
  · subst z; exact s5_1443_safe
  · subst z; exact s5_1445_safe
  · subst z; exact s5_1446_safe
def s4_1155 : State := ⟨[65,100,96,129], 1020847102109694153187957793610975478038, 3, 0, 1, 0⟩
theorem s4_1155_edges : next config 4 s4_1155 = [s5_1376, s5_1454, s5_1452] := by decide
theorem s4_1155_safe : Safe 9 4 s4_1155 := by
  apply safe_succ 8 4 s4_1155 [s5_1376, s5_1454, s5_1452] (by decide) s4_1155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1376_safe
  · subst z; exact s5_1454_safe
  · subst z; exact s5_1452_safe
def s4_1156 : State := ⟨[65,100,96,130], 1701411835951571080114707008474511900950, 3, 0, 1, 0⟩
theorem s4_1156_edges : next config 4 s4_1156 = [s5_1378, s5_1455] := by decide
theorem s4_1156_safe : Safe 9 4 s4_1156 := by
  apply safe_succ 8 4 s4_1156 [s5_1378, s5_1455] (by decide) s4_1156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1378_safe
  · subst z; exact s5_1455_safe
def s4_1157 : State := ⟨[65,100,96,132], 5784800239002832641675202297655730438422, 3, 0, 1, 0⟩
theorem s4_1157_edges : next config 4 s4_1157 = [s5_1380, s5_1456] := by decide
theorem s4_1157_safe : Safe 9 4 s4_1157 := by
  apply safe_succ 8 4 s4_1157 [s5_1380, s5_1456] (by decide) s4_1157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1380_safe
  · subst z; exact s5_1456_safe
def s4_1158 : State := ⟨[65,100,96,136], 87452568300028063872885108081280101187862, 3, 0, 1, 0⟩
theorem s4_1158_edges : next config 4 s4_1158 = [s5_1382, s5_1457] := by decide
theorem s4_1158_safe : Safe 9 4 s4_1158 := by
  apply safe_succ 8 4 s4_1158 [s5_1382, s5_1457] (by decide) s4_1158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1382_safe
  · subst z; exact s5_1457_safe
def s4_1159 : State := ⟨[65,100,96,144], 22301085480898890958761979481227108945035542, 3, 0, 1, 0⟩
theorem s4_1159_edges : next config 4 s4_1159 = [s5_1386, s5_1458] := by decide
theorem s4_1159_safe : Safe 9 4 s4_1159 := by
  apply safe_succ 8 4 s4_1159 [s5_1386, s5_1458] (by decide) s4_1159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1386_safe
  · subst z; exact s5_1458_safe
def s4_1160 : State := ⟨[65,100,96,160], 1461501637671185286471502058977491598403371598102, 3, 0, 1, 0⟩
theorem s4_1160_edges : next config 4 s4_1160 = [s5_1389, s5_1459] := by decide
theorem s4_1160_safe : Safe 9 4 s4_1160 := by
  apply safe_succ 8 4 s4_1160 [s5_1389, s5_1459] (by decide) s4_1160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1389_safe
  · subst z; exact s5_1459_safe
def s4_1161 : State := ⟨[65,100,96,192], 6277101735386680764176071791475483642363564023211473568022, 3, 0, 1, 0⟩
theorem s4_1161_edges : next config 4 s4_1161 = [s5_1391, s5_1460] := by decide
theorem s4_1161_safe : Safe 9 4 s4_1161 := by
  apply safe_succ 8 4 s4_1161 [s5_1391, s5_1460] (by decide) s4_1161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1391_safe
  · subst z; exact s5_1460_safe
def s4_1162 : State := ⟨[65,100,96,193], 12554203470773361528011861214683150058465919467675508080918, 3, 0, 1, 0⟩
theorem s4_1162_edges : next config 4 s4_1162 = [s5_1393, s5_1461] := by decide
theorem s4_1162_safe : Safe 9 4 s4_1162 := by
  apply safe_succ 8 4 s4_1162 [s5_1393, s5_1461] (by decide) s4_1162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1393_safe
  · subst z; exact s5_1461_safe
def s4_1163 : State := ⟨[65,100,96,224], 26959946667150639794667015087359913041904961648801781059851049304342, 3, 0, 1, 0⟩
theorem s4_1163_edges : next config 4 s4_1163 = [s5_1395, s5_1462] := by decide
theorem s4_1163_safe : Safe 9 4 s4_1163 := by
  apply safe_succ 8 4 s4_1163 [s5_1395, s5_1462] (by decide) s4_1163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1395_safe
  · subst z; exact s5_1462_safe
def s4_1164 : State := ⟨[65,100,96,228], 431359146674410236714672241392654373146462127986910368276405203042582, 3, 0, 1, 0⟩
theorem s4_1164_edges : next config 4 s4_1164 = [s5_1397, s5_1463] := by decide
theorem s4_1164_safe : Safe 9 4 s4_1164 := by
  apply safe_succ 8 4 s4_1164 [s5_1397, s5_1463] (by decide) s4_1164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1397_safe
  · subst z; exact s5_1463_safe
def s4_1165 : State := ⟨[65,100,104,128], 340282388550226829912879002694690341142, 3, 0, 0, 0⟩
theorem s4_1165_edges : next config 4 s4_1165 = [s5_1461, s5_1463, s5_1464, s5_1455, s5_1457, s5_1458, s5_1459] := by decide
theorem s4_1165_safe : Safe 9 4 s4_1165 := by
  apply safe_succ 8 4 s4_1165 [s5_1461, s5_1463, s5_1464, s5_1455, s5_1457, s5_1458, s5_1459] (by decide) s4_1165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_1461_safe
  · subst z; exact s5_1463_safe
  · subst z; exact s5_1464_safe
  · subst z; exact s5_1455_safe
  · subst z; exact s5_1457_safe
  · subst z; exact s5_1458_safe
  · subst z; exact s5_1459_safe
def s4_1166 : State := ⟨[65,108,104,128], 340282711801129888111376384354007712022, 3, 0, 0, 0⟩
theorem s4_1166_edges : next config 4 s4_1166 = [s5_1402, s5_1472, s5_1475, s5_1474, s5_1466, s5_1468, s5_1469, s5_1470] := by decide
theorem s4_1166_safe : Safe 9 4 s4_1166 := by
  apply safe_succ 8 4 s4_1166 [s5_1402, s5_1472, s5_1475, s5_1474, s5_1466, s5_1468, s5_1469, s5_1470] (by decide) s4_1166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1402_safe
  · subst z; exact s5_1472_safe
  · subst z; exact s5_1475_safe
  · subst z; exact s5_1474_safe
  · subst z; exact s5_1466_safe
  · subst z; exact s5_1468_safe
  · subst z; exact s5_1469_safe
  · subst z; exact s5_1470_safe
def s4_1167 : State := ⟨[65,140,96,136], 1481249143206924359618639270720305992106262, 3, 0, 1, 0⟩
theorem s4_1167_edges : next config 4 s4_1167 = [s5_1383, s5_1476] := by decide
theorem s4_1167_safe : Safe 9 4 s4_1167 := by
  apply safe_succ 8 4 s4_1167 [s5_1383, s5_1476] (by decide) s4_1167_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1383_safe
  · subst z; exact s5_1476_safe
def s4_1168 : State := ⟨[65,228,96,224], 458319093341560876509339256479674003818831621809222711356012110086422, 3, 0, 1, 0⟩
theorem s4_1168_edges : next config 4 s4_1168 = [s5_1396, s5_1477] := by decide
theorem s4_1168_safe : Safe 9 4 s4_1168 := by
  apply safe_succ 8 4 s4_1168 [s5_1396, s5_1477] (by decide) s4_1168_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1396_safe
  · subst z; exact s5_1477_safe
def s4_1169 : State := ⟨[81,4,96,145], 44601830679428246452115284270215084678250774, 1, 0, 1, 0⟩
theorem s4_1169_edges : next config 4 s4_1169 = [s5_1482, s5_1481] := by decide
theorem s4_1169_safe : Safe 9 4 s4_1169 := by
  apply safe_succ 8 4 s4_1169 [s5_1482, s5_1481] (by decide) s4_1169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1482_safe
  · subst z; exact s5_1481_safe
def s4_1170 : State := ⟨[81,12,64,145], 44601830679428167223952770005877491134304534, 3, 0, 1, 0⟩
theorem s4_1170_edges : next config 4 s4_1170 = [s5_1479, s5_1482] := by decide
theorem s4_1170_safe : Safe 9 4 s4_1170 := by
  apply safe_succ 8 4 s4_1170 [s5_1479, s5_1482] (by decide) s4_1170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1479_safe
  · subst z; exact s5_1482_safe
def s4_1171 : State := ⟨[81,21,64,145], 44601830679428167223952770005877491136397590, 3, 0, 1, 0⟩
theorem s4_1171_edges : next config 4 s4_1171 = [s5_1483] := by decide
theorem s4_1171_safe : Safe 9 4 s4_1171 := by
  apply safe_succ 8 4 s4_1171 [s5_1483] (by decide) s4_1171_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1483_safe
def s4_1172 : State := ⟨[96,4,67,128], 340282367000166626143659641727352897822, 1, 0, 0, 0⟩
theorem s4_1172_edges : next config 4 s4_1172 = [s5_1534, s5_1497, s5_1496, s5_1489, s5_1495, s5_1487, s5_1490, s5_1491, s5_1492] := by decide
theorem s4_1172_safe : Safe 9 4 s4_1172 := by
  apply safe_succ 8 4 s4_1172 [s5_1534, s5_1497, s5_1496, s5_1489, s5_1495, s5_1487, s5_1490, s5_1491, s5_1492] (by decide) s4_1172_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_1534_safe
  · subst z; exact s5_1497_safe
  · subst z; exact s5_1496_safe
  · subst z; exact s5_1489_safe
  · subst z; exact s5_1495_safe
  · subst z; exact s5_1487_safe
  · subst z; exact s5_1490_safe
  · subst z; exact s5_1491_safe
  · subst z; exact s5_1492_safe
def s4_1173 : State := ⟨[97,4,96,128], 340282367158622951024614364290404651286, 3, 2, 0, 0⟩
theorem s4_1173_edges : next config 4 s4_1173 = [s5_187, s5_1510, s5_1509, s5_1500, s5_1508, s5_1499, s5_1501, s5_1504, s5_1506] := by decide
theorem s4_1173_safe : Safe 9 4 s4_1173 := by
  apply safe_succ 8 4 s4_1173 [s5_187, s5_1510, s5_1509, s5_1500, s5_1508, s5_1499, s5_1501, s5_1504, s5_1506] (by decide) s4_1173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s5_187_safe
  · subst z; exact s5_1510_safe
  · subst z; exact s5_1509_safe
  · subst z; exact s5_1500_safe
  · subst z; exact s5_1508_safe
  · subst z; exact s5_1499_safe
  · subst z; exact s5_1501_safe
  · subst z; exact s5_1504_safe
  · subst z; exact s5_1506_safe
def s4_1174 : State := ⟨[97,4,96,140], 1399581375146057584712421000123721290154262, 1, 0, 1, 0⟩
theorem s4_1174_edges : next config 4 s4_1174 = [s5_197, s5_1511] := by decide
theorem s4_1174_safe : Safe 9 4 s4_1174 := by
  apply safe_succ 8 4 s4_1174 [s5_197, s5_1511] (by decide) s4_1174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_197_safe
  · subst z; exact s5_1511_safe
def s4_1175 : State := ⟨[97,4,96,140], 1481249143207082815943630905907345660903702, 1, 0, 1, 0⟩
theorem s4_1175_edges : next config 4 s4_1175 = [s5_201, s5_1512] := by decide
theorem s4_1175_safe : Safe 9 4 s4_1175 := by
  apply safe_succ 8 4 s4_1175 [s5_201, s5_1512] (by decide) s4_1175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_201_safe
  · subst z; exact s5_1512_safe
def s4_1176 : State := ⟨[97,4,96,145], 44602511244162246782949387908875876953030934, 1, 0, 1, 0⟩
theorem s4_1176_edges : next config 4 s4_1176 = [s5_208, s5_1517, s5_1513] := by decide
theorem s4_1176_safe : Safe 9 4 s4_1176 := by
  apply safe_succ 8 4 s4_1176 [s5_208, s5_1517, s5_1513] (by decide) s4_1176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_208_safe
  · subst z; exact s5_1517_safe
  · subst z; exact s5_1513_safe
def s4_1177 : State := ⟨[97,4,96,145], 66902575877959028047558179432309374922588438, 1, 0, 1, 0⟩
theorem s4_1177_edges : next config 4 s4_1177 = [s5_216, s5_1518, s5_1514] := by decide
theorem s4_1177_safe : Safe 9 4 s4_1177 := by
  apply safe_succ 8 4 s4_1177 [s5_216, s5_1518, s5_1514] (by decide) s4_1177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_216_safe
  · subst z; exact s5_1518_safe
  · subst z; exact s5_1514_safe
def s4_1178 : State := ⟨[97,4,96,162], 5846006551025023507657116135743244872641207664918, 1, 0, 1, 0⟩
theorem s4_1178_edges : next config 4 s4_1178 = [s5_237, s5_1519, s5_1515] := by decide
theorem s4_1178_safe : Safe 9 4 s4_1178 := by
  apply safe_succ 8 4 s4_1178 [s5_237, s5_1519, s5_1515] (by decide) s4_1178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_237_safe
  · subst z; exact s5_1519_safe
  · subst z; exact s5_1515_safe
def s4_1179 : State := ⟨[97,4,96,162], 7307508186994796958177047114606029462570067362070, 1, 0, 1, 0⟩
theorem s4_1179_edges : next config 4 s4_1179 = [s5_244, s5_1520, s5_1516] := by decide
theorem s4_1179_safe : Safe 9 4 s4_1179 := by
  apply safe_succ 8 4 s4_1179 [s5_244, s5_1520, s5_1516] (by decide) s4_1179_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_244_safe
  · subst z; exact s5_1520_safe
  · subst z; exact s5_1516_safe
def s4_1180 : State := ⟨[97,4,104,129], 1020847121282909481603034003101192356118, 1, 0, 1, 0⟩
theorem s4_1180_edges : next config 4 s4_1180 = [s5_1521, s5_1513] := by decide
theorem s4_1180_safe : Safe 9 4 s4_1180 := by
  apply safe_succ 8 4 s4_1180 [s5_1521, s5_1513] (by decide) s4_1180_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1521_safe
  · subst z; exact s5_1513_safe
def s4_1181 : State := ⟨[97,4,104,130], 1701411855124786408529783217964728779030, 1, 0, 1, 0⟩
theorem s4_1181_edges : next config 4 s4_1181 = [s5_1522, s5_1515] := by decide
theorem s4_1181_safe : Safe 9 4 s4_1181 := by
  apply safe_succ 8 4 s4_1181 [s5_1522, s5_1515] (by decide) s4_1181_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1522_safe
  · subst z; exact s5_1515_safe
def s4_1182 : State := ⟨[97,4,104,132], 5784800258176047970090278507145947316502, 1, 0, 1, 0⟩
theorem s4_1182_edges : next config 4 s4_1182 = [s5_1523, s5_1511] := by decide
theorem s4_1182_safe : Safe 9 4 s4_1182 := by
  apply safe_succ 8 4 s4_1182 [s5_1523, s5_1511] (by decide) s4_1182_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1523_safe
  · subst z; exact s5_1511_safe
def s4_1183 : State := ⟨[97,4,104,136], 87452568319201279201300184290770318065942, 1, 0, 1, 0⟩
theorem s4_1183_edges : next config 4 s4_1183 = [s5_1532, s5_1524, s5_1512] := by decide
theorem s4_1183_safe : Safe 9 4 s4_1183 := by
  apply safe_succ 8 4 s4_1183 [s5_1532, s5_1524, s5_1512] (by decide) s4_1183_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1532_safe
  · subst z; exact s5_1524_safe
  · subst z; exact s5_1512_safe
def s4_1184 : State := ⟨[97,4,104,144], 22301085480918064174090394557436599161913622, 1, 0, 1, 0⟩
theorem s4_1184_edges : next config 4 s4_1184 = [s5_1526] := by decide
theorem s4_1184_safe : Safe 9 4 s4_1184 := by
  apply safe_succ 8 4 s4_1184 [s5_1526] (by decide) s4_1184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1526_safe
def s4_1185 : State := ⟨[97,4,104,160], 1461501637671185305644717387392567807893588476182, 1, 0, 1, 0⟩
theorem s4_1185_edges : next config 4 s4_1185 = [s5_1527, s5_1516] := by decide
theorem s4_1185_safe : Safe 9 4 s4_1185 := by
  apply safe_succ 8 4 s4_1185 [s5_1527, s5_1516] (by decide) s4_1185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1527_safe
  · subst z; exact s5_1516_safe
def s4_1186 : State := ⟨[97,4,104,192], 6277101735386680764176071810648698970778640232701690446102, 1, 0, 1, 0⟩
theorem s4_1186_edges : next config 4 s4_1186 = [s5_1528] := by decide
theorem s4_1186_safe : Safe 9 4 s4_1186 := by
  apply safe_succ 8 4 s4_1186 [s5_1528] (by decide) s4_1186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1528_safe
def s4_1187 : State := ⟨[97,4,104,224], 26959946667150639794667015087359913061078176977216857269341266182422, 1, 0, 1, 0⟩
theorem s4_1187_edges : next config 4 s4_1187 = [s5_1529] := by decide
theorem s4_1187_safe : Safe 9 4 s4_1187 := by
  apply safe_succ 8 4 s4_1187 [s5_1529] (by decide) s4_1187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1529_safe
def s4_1188 : State := ⟨[97,4,104,225], 53919893334301279589334030174379543734715321399757429750444876431638, 1, 0, 1, 0⟩
theorem s4_1188_edges : next config 4 s4_1188 = [s5_1530] := by decide
theorem s4_1188_safe : Safe 9 4 s4_1188 := by
  apply safe_succ 8 4 s4_1188 [s5_1530] (by decide) s4_1188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1530_safe
def s4_1189 : State := ⟨[97,4,104,232], 6901746346790563787434755862277365734838550004725062839950761879732502, 1, 0, 1, 0⟩
theorem s4_1189_edges : next config 4 s4_1189 = [s5_1531] := by decide
theorem s4_1189_safe : Safe 9 4 s4_1189 := by
  apply safe_succ 8 4 s4_1189 [s5_1531] (by decide) s4_1189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1531_safe
def s4_1190 : State := ⟨[97,12,96,129], 1020847101000499877951363579153941074198, 3, 0, 1, 0⟩
theorem s4_1190_edges : next config 4 s4_1190 = [s5_584, s5_1498, s5_1521, s5_1517] := by decide
theorem s4_1190_safe : Safe 9 4 s4_1190 := by
  apply safe_succ 8 4 s4_1190 [s5_584, s5_1498, s5_1521, s5_1517] (by decide) s4_1190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_584_safe
  · subst z; exact s5_1498_safe
  · subst z; exact s5_1521_safe
  · subst z; exact s5_1517_safe
def s4_1191 : State := ⟨[97,12,96,130], 1701411834842376804878112794017477497110, 3, 0, 1, 0⟩
theorem s4_1191_edges : next config 4 s4_1191 = [s5_588, s5_1499, s5_1522, s5_1519] := by decide
theorem s4_1191_safe : Safe 9 4 s4_1191 := by
  apply safe_succ 8 4 s4_1191 [s5_588, s5_1499, s5_1522, s5_1519] (by decide) s4_1191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_588_safe
  · subst z; exact s5_1499_safe
  · subst z; exact s5_1522_safe
  · subst z; exact s5_1519_safe
def s4_1192 : State := ⟨[97,12,96,132], 5784800237893638366438608083198696034582, 3, 0, 1, 0⟩
theorem s4_1192_edges : next config 4 s4_1192 = [s5_594, s5_1500, s5_1523] := by decide
theorem s4_1192_safe : Safe 9 4 s4_1192 := by
  apply safe_succ 8 4 s4_1192 [s5_594, s5_1500, s5_1523] (by decide) s4_1192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_594_safe
  · subst z; exact s5_1500_safe
  · subst z; exact s5_1523_safe
def s4_1193 : State := ⟨[97,12,96,136], 87452568298918869597648513866823066784022, 3, 0, 1, 0⟩
theorem s4_1193_edges : next config 4 s4_1193 = [s5_598, s5_1501, s5_1524] := by decide
theorem s4_1193_safe : Safe 9 4 s4_1193 := by
  apply safe_succ 8 4 s4_1193 [s5_598, s5_1501, s5_1524] (by decide) s4_1193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_598_safe
  · subst z; exact s5_1501_safe
  · subst z; exact s5_1524_safe
def s4_1194 : State := ⟨[97,12,96,140], 1394136857275322569297007006404812998775062, 3, 0, 1, 0⟩
theorem s4_1194_edges : next config 4 s4_1194 = [s5_602, s5_1503, s5_1525] := by decide
theorem s4_1194_safe : Safe 9 4 s4_1194 := by
  apply safe_succ 8 4 s4_1194 [s5_602, s5_1503, s5_1525] (by decide) s4_1194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_602_safe
  · subst z; exact s5_1503_safe
  · subst z; exact s5_1525_safe
def s4_1195 : State := ⟨[97,12,96,144], 22301085480897781764486742887012651910631702, 3, 0, 1, 0⟩
theorem s4_1195_edges : next config 4 s4_1195 = [s5_606, s5_1504, s5_1526] := by decide
theorem s4_1195_safe : Safe 9 4 s4_1195 := by
  apply safe_succ 8 4 s4_1195 [s5_606, s5_1504, s5_1526] (by decide) s4_1195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_606_safe
  · subst z; exact s5_1504_safe
  · subst z; exact s5_1526_safe
def s4_1196 : State := ⟨[97,12,96,160], 1461501637671185285362307783740897383946337194262, 3, 0, 1, 0⟩
theorem s4_1196_edges : next config 4 s4_1196 = [s5_611, s5_1506, s5_1527, s5_1520] := by decide
theorem s4_1196_safe : Safe 9 4 s4_1196 := by
  apply safe_succ 8 4 s4_1196 [s5_611, s5_1506, s5_1527, s5_1520] (by decide) s4_1196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_611_safe
  · subst z; exact s5_1506_safe
  · subst z; exact s5_1527_safe
  · subst z; exact s5_1520_safe
def s4_1197 : State := ⟨[97,12,96,192], 6277101735386680764176071790366289367126969808754439164182, 3, 0, 1, 0⟩
theorem s4_1197_edges : next config 4 s4_1197 = [s5_625, s5_1507, s5_1528] := by decide
theorem s4_1197_safe : Safe 9 4 s4_1197 := by
  apply safe_succ 8 4 s4_1197 [s5_625, s5_1507, s5_1528] (by decide) s4_1197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_625_safe
  · subst z; exact s5_1507_safe
  · subst z; exact s5_1528_safe
def s4_1198 : State := ⟨[97,12,96,224], 26959946667150639794667015087359913040795767373565186845394014900502, 3, 0, 1, 0⟩
theorem s4_1198_edges : next config 4 s4_1198 = [s5_639, s5_1508, s5_1529] := by decide
theorem s4_1198_safe : Safe 9 4 s4_1198 := by
  apply safe_succ 8 4 s4_1198 [s5_639, s5_1508, s5_1529] (by decide) s4_1198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_639_safe
  · subst z; exact s5_1508_safe
  · subst z; exact s5_1529_safe
def s4_1199 : State := ⟨[97,12,96,225], 53919893334301279589334030174379543714432911796105759326497625149718, 3, 0, 1, 0⟩
theorem s4_1199_edges : next config 4 s4_1199 = [s5_641, s5_1509, s5_1530] := by decide
theorem s4_1199_safe : Safe 9 4 s4_1199 := by
  apply safe_succ 8 4 s4_1199 [s5_641, s5_1509, s5_1530] (by decide) s4_1199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_641_safe
  · subst z; exact s5_1509_safe
  · subst z; exact s5_1530_safe
def s4_1200 : State := ⟨[97,12,104,128], 340282387441032554676284788237655937302, 3, 0, 0, 0⟩
theorem s4_1200_edges : next config 4 s4_1200 = [s5_1510, s5_1530, s5_1525, s5_1531, s5_1522, s5_1524, s5_1526, s5_1527] := by decide
theorem s4_1200_safe : Safe 9 4 s4_1200 := by
  apply safe_succ 8 4 s4_1200 [s5_1510, s5_1530, s5_1525, s5_1531, s5_1522, s5_1524, s5_1526, s5_1527] (by decide) s4_1200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_1510_safe
  · subst z; exact s5_1530_safe
  · subst z; exact s5_1525_safe
  · subst z; exact s5_1531_safe
  · subst z; exact s5_1522_safe
  · subst z; exact s5_1524_safe
  · subst z; exact s5_1526_safe
  · subst z; exact s5_1527_safe
def s4_1201 : State := ⟨[97,140,96,136], 1481249143207082815943630905907345660903702, 3, 0, 1, 0⟩
theorem s4_1201_edges : next config 4 s4_1201 = [s5_769, s5_1502, s5_1532] := by decide
theorem s4_1201_safe : Safe 9 4 s4_1201 := by
  apply safe_succ 8 4 s4_1201 [s5_769, s5_1502, s5_1532] (by decide) s4_1201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_769_safe
  · subst z; exact s5_1502_safe
  · subst z; exact s5_1532_safe
def s4_1202 : State := ⟨[113,4,96,145], 44601830689812840166767087888046818987278614, 1, 0, 1, 0⟩
theorem s4_1202_edges : next config 4 s4_1202 = [s5_1536, s5_1535] := by decide
theorem s4_1202_safe : Safe 9 4 s4_1202 := by
  apply safe_succ 8 4 s4_1202 [s5_1536, s5_1535] (by decide) s4_1202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1536_safe
  · subst z; exact s5_1535_safe
def s4_1203 : State := ⟨[131,4,64,130], 4423670769972200025042316640690991337750, 3, 2, 1, 0⟩
theorem s4_1203_edges : next config 4 s4_1203 = [s5_6, s5_1562, s5_1542, s5_1540, s5_1541] := by decide
theorem s4_1203_safe : Safe 9 4 s4_1203 := by
  apply safe_succ 8 4 s4_1203 [s5_6, s5_1562, s5_1542, s5_1540, s5_1541] (by decide) s4_1203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s5_6_safe
  · subst z; exact s5_1562_safe
  · subst z; exact s5_1542_safe
  · subst z; exact s5_1540_safe
  · subst z; exact s5_1541_safe
def s4_1204 : State := ⟨[131,4,96,146], 89207404464892543994330429671571730559205654, 1, 0, 1, 0⟩
theorem s4_1204_edges : next config 4 s4_1204 = [s5_1547, s5_1544] := by decide
theorem s4_1204_safe : Safe 9 4 s4_1204 := by
  apply safe_succ 8 4 s4_1204 [s5_1547, s5_1544] (by decide) s4_1204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1547_safe
  · subst z; exact s5_1544_safe
def s4_1205 : State := ⟨[131,4,96,162], 5846006553747282442866167518421713056908265455894, 1, 0, 1, 0⟩
theorem s4_1205_edges : next config 4 s4_1205 = [s5_1548, s5_1545] := by decide
theorem s4_1205_safe : Safe 9 4 s4_1205 := by
  apply safe_succ 8 4 s4_1205 [s5_1548, s5_1545] (by decide) s4_1205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1548_safe
  · subst z; exact s5_1545_safe
def s4_1206 : State := ⟨[131,4,100,130], 4423670771319078787784810379781238489366, 1, 0, 1, 0⟩
theorem s4_1206_edges : next config 4 s4_1206 = [s5_310] := by decide
theorem s4_1206_safe : Safe 9 4 s4_1206 := by
  apply safe_succ 8 4 s4_1206 [s5_310] (by decide) s4_1206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_310_safe
def s4_1207 : State := ⟨[131,4,104,130], 4423670790333837791208251402231786570006, 1, 0, 1, 0⟩
theorem s4_1207_edges : next config 4 s4_1207 = [s5_347, s5_1568, s5_1551, s5_1549, s5_1546, s5_1544, s5_1545] := by decide
theorem s4_1207_safe : Safe 9 4 s4_1207 := by
  apply safe_succ 8 4 s4_1207 [s5_347, s5_1568, s5_1551, s5_1549, s5_1546, s5_1544, s5_1545] (by decide) s4_1207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_347_safe
  · subst z; exact s5_1568_safe
  · subst z; exact s5_1551_safe
  · subst z; exact s5_1549_safe
  · subst z; exact s5_1546_safe
  · subst z; exact s5_1544_safe
  · subst z; exact s5_1545_safe
def s4_1208 : State := ⟨[131,12,64,146], 89207404464892464766167915407234137015259414, 3, 0, 1, 0⟩
theorem s4_1208_edges : next config 4 s4_1208 = [s5_1540, s5_1547] := by decide
theorem s4_1208_safe : Safe 9 4 s4_1208 := by
  apply safe_succ 8 4 s4_1208 [s5_1540, s5_1547] (by decide) s4_1208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1540_safe
  · subst z; exact s5_1547_safe
def s4_1209 : State := ⟨[131,12,64,162], 5846006553747282442786939355907448719314721509654, 3, 0, 1, 0⟩
theorem s4_1209_edges : next config 4 s4_1209 = [s5_1541, s5_1548] := by decide
theorem s4_1209_safe : Safe 9 4 s4_1209 := by
  apply safe_succ 8 4 s4_1209 [s5_1541, s5_1548] (by decide) s4_1209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1541_safe
  · subst z; exact s5_1548_safe
def s4_1210 : State := ⟨[131,12,96,130], 4423670770051428187556580978284535288086, 3, 0, 1, 0⟩
theorem s4_1210_edges : next config 4 s4_1210 = [s5_589, s5_1575, s5_1542, s5_1549, s5_1547, s5_1548] := by decide
theorem s4_1210_safe : Safe 9 4 s4_1210 := by
  apply safe_succ 8 4 s4_1210 [s5_589, s5_1575, s5_1542, s5_1549, s5_1547, s5_1548] (by decide) s4_1210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_589_safe
  · subst z; exact s5_1575_safe
  · subst z; exact s5_1542_safe
  · subst z; exact s5_1549_safe
  · subst z; exact s5_1547_safe
  · subst z; exact s5_1548_safe
def s4_1211 : State := ⟨[131,100,96,130], 4423670771319078787784810379781238489366, 3, 0, 1, 0⟩
theorem s4_1211_edges : next config 4 s4_1211 = [s5_712, s5_1543, s5_1550] := by decide
theorem s4_1211_safe : Safe 9 4 s4_1211 := by
  apply safe_succ 8 4 s4_1211 [s5_712, s5_1543, s5_1550] (by decide) s4_1211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_712_safe
  · subst z; exact s5_1543_safe
  · subst z; exact s5_1550_safe
def s4_1212 : State := ⟨[137,4,104,136], 261677140182563316169519454620648554430742, 1, 0, 1, 0⟩
theorem s4_1212_edges : next config 4 s4_1212 = [s5_367] := by decide
theorem s4_1212_safe : Safe 9 4 s4_1212 := by
  apply safe_succ 8 4 s4_1212 [s5_367] (by decide) s4_1212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_367_safe
def s4_1213 : State := ⟨[146,4,64,145], 133805492038284501664604718206456542345101598, 1, 0, 1, 0⟩
theorem s4_1213_edges : next config 4 s4_1213 = [s5_1557, s5_1555] := by decide
theorem s4_1213_safe : Safe 9 4 s4_1213 := by
  apply safe_succ 8 4 s4_1213 [s5_1557, s5_1555] (by decide) s4_1213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1557_safe
  · subst z; exact s5_1555_safe
def s4_1214 : State := ⟨[146,4,64,145], 156105556672081282929213509729890040314659102, 1, 0, 1, 0⟩
theorem s4_1214_edges : next config 4 s4_1214 = [s5_1558, s5_1556] := by decide
theorem s4_1214_safe : Safe 9 4 s4_1214 := by
  apply safe_succ 8 4 s4_1214 [s5_1558, s5_1556] (by decide) s4_1214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1558_safe
  · subst z; exact s5_1556_safe
def s4_1215 : State := ⟨[161,4,64,160], 4384504912332991121531992961630670410477570429206, 3, 2, 1, 0⟩
theorem s4_1215_edges : next config 4 s4_1215 = [s5_31, s5_1564, s5_1559] := by decide
theorem s4_1215_safe : Safe 9 4 s4_1215 := by
  apply safe_succ 8 4 s4_1215 [s5_31, s5_1564, s5_1559] (by decide) s4_1215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_31_safe
  · subst z; exact s5_1564_safe
  · subst z; exact s5_1559_safe
def s4_1216 : State := ⟨[161,4,104,160], 4384504912332991141893630727796605172018365661462, 1, 0, 1, 0⟩
theorem s4_1216_edges : next config 4 s4_1216 = [s5_392, s5_1570, s5_1560] := by decide
theorem s4_1216_safe : Safe 9 4 s4_1216 := by
  apply safe_succ 8 4 s4_1216 [s5_392, s5_1570, s5_1560] (by decide) s4_1216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_392_safe
  · subst z; exact s5_1570_safe
  · subst z; exact s5_1560_safe
def s4_1217 : State := ⟨[161,12,96,160], 4384504912332991121611221124144934748071114379542, 3, 0, 1, 0⟩
theorem s4_1217_edges : next config 4 s4_1217 = [s5_612, s5_1577, s5_1559, s5_1560] := by decide
theorem s4_1217_safe : Safe 9 4 s4_1217 := by
  apply safe_succ 8 4 s4_1217 [s5_612, s5_1577, s5_1559, s5_1560] (by decide) s4_1217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_612_safe
  · subst z; exact s5_1577_safe
  · subst z; exact s5_1559_safe
  · subst z; exact s5_1560_safe
def s4_1218 : State := ⟨[163,4,67,160], 13153514736318408630754101958075942481002842095902, 1, 0, 1, 0⟩
theorem s4_1218_edges : next config 4 s4_1218 = [s5_1581, s5_1573] := by decide
theorem s4_1218_safe : Safe 9 4 s4_1218 := by
  apply safe_succ 8 4 s4_1218 [s5_1581, s5_1573] (by decide) s4_1218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1581_safe
  · subst z; exact s5_1573_safe
def s4_1219 : State := ⟨[163,4,96,130], 11692013100348635180313399141579848276086439870742, 1, 0, 1, 0⟩
theorem s4_1219_edges : next config 4 s4_1219 = [s5_1582, s5_1574, s5_1567] := by decide
theorem s4_1219_safe : Safe 9 4 s4_1219 := by
  apply safe_succ 8 4 s4_1219 [s5_1582, s5_1574, s5_1567] (by decide) s4_1219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1582_safe
  · subst z; exact s5_1574_safe
  · subst z; exact s5_1567_safe
def s4_1220 : State := ⟨[163,4,96,130], 11692013103070894115680906849286845135531995627798, 1, 0, 1, 0⟩
theorem s4_1220_edges : next config 4 s4_1220 = [s5_1583, s5_1575, s5_1568] := by decide
theorem s4_1220_safe : Safe 9 4 s4_1220 := by
  apply safe_succ 8 4 s4_1220 [s5_1583, s5_1575, s5_1568] (by decide) s4_1220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1583_safe
  · subst z; exact s5_1575_safe
  · subst z; exact s5_1568_safe
def s4_1221 : State := ⟨[163,4,96,160], 13153514736318408630833330120442632866006709633310, 1, 0, 1, 0⟩
theorem s4_1221_edges : next config 4 s4_1221 = [s5_1586, s5_1576, s5_1569] := by decide
theorem s4_1221_safe : Safe 9 4 s4_1221 := by
  apply safe_succ 8 4 s4_1221 [s5_1586, s5_1576, s5_1569] (by decide) s4_1221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1586_safe
  · subst z; exact s5_1576_safe
  · subst z; exact s5_1569_safe
def s4_1222 : State := ⟨[163,4,96,160], 16076518010980214467240699785875198905318574719254, 1, 0, 1, 0⟩
theorem s4_1222_edges : next config 4 s4_1222 = [s5_1587, s5_1577, s5_1570] := by decide
theorem s4_1222_safe : Safe 9 4 s4_1222 := by
  apply safe_succ 8 4 s4_1222 [s5_1587, s5_1577, s5_1570] (by decide) s4_1222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_1587_safe
  · subst z; exact s5_1577_safe
  · subst z; exact s5_1570_safe
def s4_1223 : State := ⟨[163,4,96,162], 17538019649672246853128138472444980354701580108054, 1, 0, 1, 0⟩
theorem s4_1223_edges : next config 4 s4_1223 = [s5_246, s5_1590, s5_1578, s5_1571] := by decide
theorem s4_1223_safe : Safe 9 4 s4_1223 := by
  apply safe_succ 8 4 s4_1223 [s5_246, s5_1590, s5_1578, s5_1571] (by decide) s4_1223_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_246_safe
  · subst z; exact s5_1590_safe
  · subst z; exact s5_1578_safe
  · subst z; exact s5_1571_safe
def s4_1224 : State := ⟨[163,4,96,162], 18999521285642020303648069451307764944630439805206, 1, 0, 1, 0⟩
theorem s4_1224_edges : next config 4 s4_1224 = [s5_247, s5_1591, s5_1579, s5_1572] := by decide
theorem s4_1224_safe : Safe 9 4 s4_1224 := by
  apply safe_succ 8 4 s4_1224 [s5_247, s5_1591, s5_1579, s5_1572] (by decide) s4_1224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_247_safe
  · subst z; exact s5_1591_safe
  · subst z; exact s5_1579_safe
  · subst z; exact s5_1572_safe
def s4_1225 : State := ⟨[163,12,64,130], 11692013100348635180234170979065583938492895924502, 3, 0, 1, 0⟩
theorem s4_1225_edges : next config 4 s4_1225 = [s5_1561, s5_1574] := by decide
theorem s4_1225_safe : Safe 9 4 s4_1225 := by
  apply safe_succ 8 4 s4_1225 [s5_1561, s5_1574] (by decide) s4_1225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1561_safe
  · subst z; exact s5_1574_safe
def s4_1226 : State := ⟨[163,12,64,130], 11692013103070894115601678686772580797938451681558, 3, 0, 1, 0⟩
theorem s4_1226_edges : next config 4 s4_1226 = [s5_1562, s5_1575] := by decide
theorem s4_1226_safe : Safe 9 4 s4_1226 := by
  apply safe_succ 8 4 s4_1226 [s5_1562, s5_1575] (by decide) s4_1226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1562_safe
  · subst z; exact s5_1575_safe
def s4_1227 : State := ⟨[163,12,64,160], 13153514736318408630754101957928368528413165687070, 3, 0, 1, 0⟩
theorem s4_1227_edges : next config 4 s4_1227 = [s5_1563, s5_1576] := by decide
theorem s4_1227_safe : Safe 9 4 s4_1227 := by
  apply safe_succ 8 4 s4_1227 [s5_1563, s5_1576] (by decide) s4_1227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1563_safe
  · subst z; exact s5_1576_safe
def s4_1228 : State := ⟨[163,12,64,160], 16076518010980214467161471623360934567725030773014, 3, 0, 1, 0⟩
theorem s4_1228_edges : next config 4 s4_1228 = [s5_1564, s5_1577] := by decide
theorem s4_1228_safe : Safe 9 4 s4_1228 := by
  apply safe_succ 8 4 s4_1228 [s5_1564, s5_1577] (by decide) s4_1228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_1564_safe
  · subst z; exact s5_1577_safe
def s4_1229 : State := ⟨[163,12,64,162], 17538019649672246853048910309930716017108036161814, 3, 0, 1, 0⟩
theorem s4_1229_edges : next config 4 s4_1229 = [s5_535, s5_1565, s5_1578] := by decide
theorem s4_1229_safe : Safe 9 4 s4_1229 := by
  apply safe_succ 8 4 s4_1229 [s5_535, s5_1565, s5_1578] (by decide) s4_1229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_535_safe
  · subst z; exact s5_1565_safe
  · subst z; exact s5_1578_safe
def s4_1230 : State := ⟨[163,12,64,162], 18999521285642020303568841288793500607036895858966, 3, 0, 1, 0⟩
theorem s4_1230_edges : next config 4 s4_1230 = [s5_536, s5_1566, s5_1579] := by decide
theorem s4_1230_safe : Safe 9 4 s4_1230 := by
  apply safe_succ 8 4 s4_1230 [s5_536, s5_1566, s5_1579] (by decide) s4_1230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_536_safe
  · subst z; exact s5_1566_safe
  · subst z; exact s5_1579_safe
def s4_1231 : State := ⟨[171,4,64,130], 3004847366354037811661380708382013208193842743935254, 1, 0, 1, 0⟩
theorem s4_1231_edges : next config 4 s4_1231 = [s5_1582] := by decide
theorem s4_1231_safe : Safe 9 4 s4_1231 := by
  apply safe_succ 8 4 s4_1231 [s5_1582] (by decide) s4_1231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1582_safe
def s4_1232 : State := ⟨[171,4,64,130], 3004847366356760070596748216089720205053288299692310, 1, 0, 1, 0⟩
theorem s4_1232_edges : next config 4 s4_1232 = [s5_1583] := by decide
theorem s4_1232_safe : Safe 9 4 s4_1232 := by
  apply safe_succ 8 4 s4_1232 [s5_1583] (by decide) s4_1232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1583_safe
def s4_1233 : State := ⟨[171,4,64,136], 2993155353341141744779827722513053345109426642682142, 1, 0, 1, 0⟩
theorem s4_1233_edges : next config 4 s4_1233 = [s5_1584] := by decide
theorem s4_1233_safe : Safe 9 4 s4_1233 := by
  apply safe_succ 8 4 s4_1233 [s5_1584] (by decide) s4_1233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1584_safe
def s4_1234 : State := ⟨[171,4,64,136], 2993155353341141744779827722513053345109435232616726, 1, 0, 1, 0⟩
theorem s4_1234_edges : next config 4 s4_1234 = [s5_1585] := by decide
theorem s4_1234_safe : Safe 9 4 s4_1234 := by
  apply safe_succ 8 4 s4_1234 [s5_1585] (by decide) s4_1234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1585_safe
def s4_1235 : State := ⟨[171,4,64,160], 3006308867990007585111900639360875992783763013697822, 1, 0, 1, 0⟩
theorem s4_1235_edges : next config 4 s4_1235 = [s5_1586] := by decide
theorem s4_1235_safe : Safe 9 4 s4_1235 := by
  apply safe_succ 8 4 s4_1235 [s5_1586] (by decide) s4_1235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1586_safe
def s4_1236 : State := ⟨[171,4,64,160], 3009231871264669390948308009026308558823074878783766, 1, 0, 1, 0⟩
theorem s4_1236_edges : next config 4 s4_1236 = [s5_1587] := by decide
theorem s4_1236_safe : Safe 9 4 s4_1236 := by
  apply safe_succ 8 4 s4_1236 [s5_1587] (by decide) s4_1236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1587_safe
def s4_1237 : State := ⟨[171,4,64,162], 2999001359804714199988565969051148076115210423829270, 1, 0, 1, 0⟩
theorem s4_1237_edges : next config 4 s4_1237 = [s5_1588] := by decide
theorem s4_1237_safe : Safe 9 4 s4_1237 := by
  apply safe_succ 8 4 s4_1237 [s5_1588] (by decide) s4_1237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1588_safe
def s4_1238 : State := ⟨[171,4,64,162], 3000462861440683973439085900030010860705139283526422, 1, 0, 1, 0⟩
theorem s4_1238_edges : next config 4 s4_1238 = [s5_1589] := by decide
theorem s4_1238_safe : Safe 9 4 s4_1238 := by
  apply safe_succ 8 4 s4_1238 [s5_1589] (by decide) s4_1238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1589_safe
def s4_1239 : State := ⟨[171,4,64,162], 3010693372903361423334195447712878340272457884172566, 1, 0, 1, 0⟩
theorem s4_1239_edges : next config 4 s4_1239 = [s5_1590] := by decide
theorem s4_1239_safe : Safe 9 4 s4_1239 := by
  apply safe_succ 8 4 s4_1239 [s5_1590] (by decide) s4_1239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1590_safe
def s4_1240 : State := ⟨[171,4,64,162], 3012154874539331196784715378691741124862386743869718, 1, 0, 1, 0⟩
theorem s4_1240_edges : next config 4 s4_1240 = [s5_1591] := by decide
theorem s4_1240_safe : Safe 9 4 s4_1240 := by
  apply safe_succ 8 4 s4_1240 [s5_1591] (by decide) s4_1240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1591_safe
def s4_1241 : State := ⟨[171,4,64,170], 4495579036431558788229139237752621888242885347836182, 1, 0, 1, 0⟩
theorem s4_1241_edges : next config 4 s4_1241 = [s5_39, s5_1592] := by decide
theorem s4_1241_safe : Safe 9 4 s4_1241 := by
  apply safe_succ 8 4 s4_1241 [s5_39, s5_1592] (by decide) s4_1241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_39_safe
  · subst z; exact s5_1592_safe
def s4_1242 : State := ⟨[171,4,64,170], 4497040538067528561679659168731484672832814207533334, 1, 0, 1, 0⟩
theorem s4_1242_edges : next config 4 s4_1242 = [s5_40, s5_1593] := by decide
theorem s4_1242_safe : Safe 9 4 s4_1242 := by
  apply safe_succ 8 4 s4_1242 [s5_40, s5_1593] (by decide) s4_1242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_40_safe
  · subst z; exact s5_1593_safe
def s4_1243 : State := ⟨[193,4,64,192], 18831305206160042291847650636543937711788887684901876338966, 3, 2, 1, 0⟩
theorem s4_1243_edges : next config 4 s4_1243 = [s5_50, s5_1594] := by decide
theorem s4_1243_safe : Safe 9 4 s4_1243 := by
  apply safe_succ 8 4 s4_1243 [s5_50, s5_1594] (by decide) s4_1243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_50_safe
  · subst z; exact s5_1594_safe
def s4_1244 : State := ⟨[193,4,100,192], 18831305206160042291847650637890816474531381423992123490582, 1, 0, 1, 0⟩
theorem s4_1244_edges : next config 4 s4_1244 = [s5_323] := by decide
theorem s4_1244_safe : Safe 9 4 s4_1244 := by
  apply safe_succ 8 4 s4_1244 [s5_323] (by decide) s4_1244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_323_safe
def s4_1245 : State := ⟨[193,4,104,192], 18831305206160042291847650656905575477954822446442671571222, 1, 0, 1, 0⟩
theorem s4_1245_edges : next config 4 s4_1245 = [s5_415, s5_1599, s5_1597, s5_1596] := by decide
theorem s4_1245_safe : Safe 9 4 s4_1245 := by
  apply safe_succ 8 4 s4_1245 [s5_415, s5_1599, s5_1597, s5_1596] (by decide) s4_1245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_415_safe
  · subst z; exact s5_1599_safe
  · subst z; exact s5_1597_safe
  · subst z; exact s5_1596_safe
def s4_1246 : State := ⟨[193,12,96,192], 18831305206160042291847650636623165874303152022495420289302, 3, 0, 1, 0⟩
theorem s4_1246_edges : next config 4 s4_1246 = [s5_626, s5_1594, s5_1597] := by decide
theorem s4_1246_safe : Safe 9 4 s4_1246 := by
  apply safe_succ 8 4 s4_1246 [s5_626, s5_1594, s5_1597] (by decide) s4_1246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_626_safe
  · subst z; exact s5_1594_safe
  · subst z; exact s5_1597_safe
def s4_1247 : State := ⟨[193,100,96,192], 18831305206160042291847650637890816474531381423992123490582, 3, 0, 1, 0⟩
theorem s4_1247_edges : next config 4 s4_1247 = [s5_725, s5_1595, s5_1598] := by decide
theorem s4_1247_safe : Safe 9 4 s4_1247 := by
  apply safe_succ 8 4 s4_1247 [s5_725, s5_1595, s5_1598] (by decide) s4_1247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_725_safe
  · subst z; exact s5_1595_safe
  · subst z; exact s5_1598_safe
def s4_1248 : State := ⟨[225,4,104,224], 80879840001451919384001045261399174408194009497269473556361398780182, 1, 0, 1, 0⟩
theorem s4_1248_edges : next config 4 s4_1248 = [s5_436, s5_1601] := by decide
theorem s4_1248_safe : Safe 9 4 s4_1248 := by
  apply safe_succ 8 4 s4_1248 [s5_436, s5_1601] (by decide) s4_1248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_436_safe
  · subst z; exact s5_1601_safe
def s4_1249 : State := ⟨[225,12,96,224], 80879840001451919384001045261399174387911599893617803132414147498262, 3, 0, 1, 0⟩
theorem s4_1249_edges : next config 4 s4_1249 = [s5_640, s5_1600, s5_1601] := by decide
theorem s4_1249_safe : Safe 9 4 s4_1249 := by
  apply safe_succ 8 4 s4_1249 [s5_640, s5_1600, s5_1601] (by decide) s4_1249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_640_safe
  · subst z; exact s5_1600_safe
  · subst z; exact s5_1601_safe
end HGP13.SectorGraph234
