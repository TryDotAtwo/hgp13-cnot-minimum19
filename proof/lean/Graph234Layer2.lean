import Graph234Layer3
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s2_0 : State := ⟨[1,4,64,128], 340282366920938463481821351509772796190, 1, 1, 0, 0⟩
theorem s2_0_edges : next config 2 s2_0 = [s3_398, s3_236, s3_145, s3_0, s3_14, s3_55, s3_6, s3_20, s3_30, s3_39] := by decide
theorem s2_0_safe : Safe 11 2 s2_0 := by
  apply safe_succ 10 2 s2_0 [s3_398, s3_236, s3_145, s3_0, s3_14, s3_55, s3_6, s3_20, s3_30, s3_39] (by decide) s2_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_398_safe
  · subst z; exact s3_236_safe
  · subst z; exact s3_145_safe
  · subst z; exact s3_0_safe
  · subst z; exact s3_14_safe
  · subst z; exact s3_55_safe
  · subst z; exact s3_6_safe
  · subst z; exact s3_20_safe
  · subst z; exact s3_30_safe
  · subst z; exact s3_39_safe
def s2_1 : State := ⟨[1,4,64,128], 340282366920938463481821351509772796694, 1, 1, 0, 0⟩
theorem s2_1_edges : next config 2 s2_1 = [s3_399, s3_146, s3_1, s3_15, s3_56, s3_7, s3_21, s3_31, s3_40] := by decide
theorem s2_1_safe : Safe 11 2 s2_1 := by
  apply safe_succ 10 2 s2_1 [s3_399, s3_146, s3_1, s3_15, s3_56, s3_7, s3_21, s3_31, s3_40] (by decide) s2_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_399_safe
  · subst z; exact s3_146_safe
  · subst z; exact s3_1_safe
  · subst z; exact s3_15_safe
  · subst z; exact s3_56_safe
  · subst z; exact s3_7_safe
  · subst z; exact s3_21_safe
  · subst z; exact s3_31_safe
  · subst z; exact s3_40_safe
def s2_2 : State := ⟨[1,4,64,128], 340282366920938463481821351509772800278, 2, 2, 0, 0⟩
theorem s2_2_edges : next config 2 s2_2 = [s3_495, s3_338, s3_400, s3_441, s3_71, s3_82, s3_118, s3_147, s3_2, s3_16, s3_57, s3_8, s3_22, s3_32, s3_41] := by decide
theorem s2_2_safe : Safe 11 2 s2_2 := by
  apply safe_succ 10 2 s2_2 [s3_495, s3_338, s3_400, s3_441, s3_71, s3_82, s3_118, s3_147, s3_2, s3_16, s3_57, s3_8, s3_22, s3_32, s3_41] (by decide) s2_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_495_safe
  · subst z; exact s3_338_safe
  · subst z; exact s3_400_safe
  · subst z; exact s3_441_safe
  · subst z; exact s3_71_safe
  · subst z; exact s3_82_safe
  · subst z; exact s3_118_safe
  · subst z; exact s3_147_safe
  · subst z; exact s3_2_safe
  · subst z; exact s3_16_safe
  · subst z; exact s3_57_safe
  · subst z; exact s3_8_safe
  · subst z; exact s3_22_safe
  · subst z; exact s3_32_safe
  · subst z; exact s3_41_safe
def s2_3 : State := ⟨[1,4,64,128], 340282366920938463481821351518362730774, 1, 1, 0, 0⟩
theorem s2_3_edges : next config 2 s2_3 = [s3_402, s3_237, s3_148, s3_3, s3_17, s3_58, s3_9, s3_23, s3_33, s3_42] := by decide
theorem s2_3_safe : Safe 11 2 s2_3 := by
  apply safe_succ 10 2 s2_3 [s3_402, s3_237, s3_148, s3_3, s3_17, s3_58, s3_9, s3_23, s3_33, s3_42] (by decide) s2_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_402_safe
  · subst z; exact s3_237_safe
  · subst z; exact s3_148_safe
  · subst z; exact s3_3_safe
  · subst z; exact s3_17_safe
  · subst z; exact s3_58_safe
  · subst z; exact s3_9_safe
  · subst z; exact s3_23_safe
  · subst z; exact s3_33_safe
  · subst z; exact s3_42_safe
def s2_4 : State := ⟨[1,4,64,128], 340282366920938463518714839657191899414, 1, 1, 0, 0⟩
theorem s2_4_edges : next config 2 s2_4 = [s3_403, s3_238, s3_149, s3_4, s3_18, s3_59, s3_10, s3_24, s3_34, s3_43] := by decide
theorem s2_4_safe : Safe 11 2 s2_4 := by
  apply safe_succ 10 2 s2_4 [s3_403, s3_238, s3_149, s3_4, s3_18, s3_59, s3_10, s3_24, s3_34, s3_43] (by decide) s2_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_403_safe
  · subst z; exact s3_238_safe
  · subst z; exact s3_149_safe
  · subst z; exact s3_4_safe
  · subst z; exact s3_18_safe
  · subst z; exact s3_59_safe
  · subst z; exact s3_10_safe
  · subst z; exact s3_24_safe
  · subst z; exact s3_34_safe
  · subst z; exact s3_43_safe
def s2_5 : State := ⟨[1,4,64,128], 340282366920938463776969256689125622038, 2, 2, 0, 0⟩
theorem s2_5_edges : next config 2 s2_5 = [s3_404, s3_150, s3_5, s3_19, s3_60, s3_11, s3_25, s3_35, s3_44] := by decide
theorem s2_5_safe : Safe 11 2 s2_5 := by
  apply safe_succ 10 2 s2_5 [s3_404, s3_150, s3_5, s3_19, s3_60, s3_11, s3_25, s3_35, s3_44] (by decide) s2_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_404_safe
  · subst z; exact s3_150_safe
  · subst z; exact s3_5_safe
  · subst z; exact s3_19_safe
  · subst z; exact s3_60_safe
  · subst z; exact s3_11_safe
  · subst z; exact s3_25_safe
  · subst z; exact s3_35_safe
  · subst z; exact s3_44_safe
def s2_6 : State := ⟨[1,4,64,131], 3743106036130323098115567425827454910742, 0, 0, 1, 0⟩
theorem s2_6_edges : next config 2 s2_6 = [s3_239, s3_153, s3_47] := by decide
theorem s2_6_safe : Safe 11 2 s2_6 := by
  apply safe_succ 10 2 s2_6 [s3_239, s3_153, s3_47] (by decide) s2_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_239_safe
  · subst z; exact s3_153_safe
  · subst z; exact s3_47_safe
def s2_7 : State := ⟨[1,4,64,131], 4423670769972200025042316640690991333654, 0, 0, 1, 0⟩
theorem s2_7_edges : next config 2 s2_7 = [s3_240, s3_154, s3_48] := by decide
theorem s2_7_safe : Safe 11 2 s2_7 := by
  apply safe_succ 10 2 s2_7 [s3_240, s3_154, s3_48] (by decide) s2_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_240_safe
  · subst z; exact s3_154_safe
  · subst z; exact s3_48_safe
def s2_8 : State := ⟨[1,4,64,137], 175245418964283308683656369571438633484566, 0, 0, 1, 0⟩
theorem s2_8_edges : next config 2 s2_8 = [s3_155] := by decide
theorem s2_8_safe : Safe 11 2 s2_8 := by
  apply safe_succ 10 2 s2_8 [s3_155] (by decide) s2_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_155_safe
def s2_9 : State := ⟨[1,4,64,137], 261677140162201678403353519859107759194390, 0, 0, 1, 0⟩
theorem s2_9_edges : next config 2 s2_9 = [s3_156] := by decide
theorem s2_9_safe : Safe 11 2 s2_9 := by
  apply safe_succ 10 2 s2_9 [s3_156] (by decide) s2_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_156_safe
def s2_10 : State := ⟨[1,4,64,140], 1399581375145819900224878207110940658303254, 0, 0, 1, 0⟩
theorem s2_10_edges : next config 2 s2_10 = [s3_496, s3_339, s3_442, s3_72, s3_83, s3_119, s3_157] := by decide
theorem s2_10_safe : Safe 11 2 s2_10 := by
  apply safe_succ 10 2 s2_10 [s3_496, s3_339, s3_442, s3_72, s3_83, s3_119, s3_157] (by decide) s2_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s3_496_safe
  · subst z; exact s3_339_safe
  · subst z; exact s3_442_safe
  · subst z; exact s3_72_safe
  · subst z; exact s3_83_safe
  · subst z; exact s3_119_safe
  · subst z; exact s3_157_safe
def s2_11 : State := ⟨[1,4,64,140], 1481249143206845131456088112894565029052694, 0, 0, 1, 0⟩
theorem s2_11_edges : next config 2 s2_11 = [s3_497, s3_340, s3_443, s3_73, s3_84, s3_120, s3_158] := by decide
theorem s2_11_safe : Safe 11 2 s2_11 := by
  apply safe_succ 10 2 s2_11 [s3_497, s3_340, s3_443, s3_73, s3_84, s3_120, s3_158] (by decide) s2_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s3_497_safe
  · subst z; exact s3_340_safe
  · subst z; exact s3_443_safe
  · subst z; exact s3_73_safe
  · subst z; exact s3_84_safe
  · subst z; exact s3_120_safe
  · subst z; exact s3_158_safe
def s2_12 : State := ⟨[1,4,64,145], 44602511244162009098461845115863096321179926, 0, 0, 1, 0⟩
theorem s2_12_edges : next config 2 s2_12 = [s3_498, s3_341, s3_384, s3_444, s3_303, s3_241, s3_74, s3_114, s3_225, s3_85, s3_121, s3_159] := by decide
theorem s2_12_safe : Safe 11 2 s2_12 := by
  apply safe_succ 10 2 s2_12 [s3_498, s3_341, s3_384, s3_444, s3_303, s3_241, s3_74, s3_114, s3_225, s3_85, s3_121, s3_159] (by decide) s2_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_498_safe
  · subst z; exact s3_341_safe
  · subst z; exact s3_384_safe
  · subst z; exact s3_444_safe
  · subst z; exact s3_303_safe
  · subst z; exact s3_241_safe
  · subst z; exact s3_74_safe
  · subst z; exact s3_114_safe
  · subst z; exact s3_225_safe
  · subst z; exact s3_85_safe
  · subst z; exact s3_121_safe
  · subst z; exact s3_159_safe
def s2_13 : State := ⟨[1,4,64,145], 66902575877958790363070636639296594290737430, 0, 0, 1, 0⟩
theorem s2_13_edges : next config 2 s2_13 = [s3_499, s3_342, s3_385, s3_445, s3_304, s3_242, s3_75, s3_115, s3_226, s3_86, s3_122, s3_160] := by decide
theorem s2_13_safe : Safe 11 2 s2_13 := by
  apply safe_succ 10 2 s2_13 [s3_499, s3_342, s3_385, s3_445, s3_304, s3_242, s3_75, s3_115, s3_226, s3_86, s3_122, s3_160] (by decide) s2_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_499_safe
  · subst z; exact s3_342_safe
  · subst z; exact s3_385_safe
  · subst z; exact s3_445_safe
  · subst z; exact s3_304_safe
  · subst z; exact s3_242_safe
  · subst z; exact s3_75_safe
  · subst z; exact s3_115_safe
  · subst z; exact s3_226_safe
  · subst z; exact s3_86_safe
  · subst z; exact s3_122_safe
  · subst z; exact s3_160_safe
def s2_14 : State := ⟨[1,4,64,146], 89204682205957097258460208410374682869563670, 0, 0, 1, 0⟩
theorem s2_14_edges : next config 2 s2_14 = [s3_500, s3_343, s3_305, s3_334, s3_243, s3_76, s3_116, s3_231, s3_87, s3_161, s3_37, s3_65] := by decide
theorem s2_14_safe : Safe 11 2 s2_14 := by
  apply safe_succ 10 2 s2_14 [s3_500, s3_343, s3_305, s3_334, s3_243, s3_76, s3_116, s3_231, s3_87, s3_161, s3_37, s3_65] (by decide) s2_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_500_safe
  · subst z; exact s3_343_safe
  · subst z; exact s3_305_safe
  · subst z; exact s3_334_safe
  · subst z; exact s3_243_safe
  · subst z; exact s3_76_safe
  · subst z; exact s3_116_safe
  · subst z; exact s3_231_safe
  · subst z; exact s3_87_safe
  · subst z; exact s3_161_safe
  · subst z; exact s3_37_safe
  · subst z; exact s3_65_safe
def s2_15 : State := ⟨[1,4,64,146], 111504066275020036646142073184593317302698262, 0, 0, 1, 0⟩
theorem s2_15_edges : next config 2 s2_15 = [s3_501, s3_344, s3_306, s3_335, s3_244, s3_77, s3_117, s3_232, s3_88, s3_162, s3_38, s3_66] := by decide
theorem s2_15_safe : Safe 11 2 s2_15 := by
  apply safe_succ 10 2 s2_15 [s3_501, s3_344, s3_306, s3_335, s3_244, s3_77, s3_117, s3_232, s3_88, s3_162, s3_38, s3_66] (by decide) s2_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_501_safe
  · subst z; exact s3_344_safe
  · subst z; exact s3_306_safe
  · subst z; exact s3_335_safe
  · subst z; exact s3_244_safe
  · subst z; exact s3_77_safe
  · subst z; exact s3_117_safe
  · subst z; exact s3_232_safe
  · subst z; exact s3_88_safe
  · subst z; exact s3_162_safe
  · subst z; exact s3_38_safe
  · subst z; exact s3_66_safe
def s2_16 : State := ⟨[1,4,64,161], 2923003275682652937170185055841136605685174305046, 0, 0, 1, 0⟩
theorem s2_16_edges : next config 2 s2_16 = [s3_245, s3_163, s3_49] := by decide
theorem s2_16_safe : Safe 11 2 s2_16 := by
  apply safe_succ 10 2 s2_16 [s3_245, s3_163, s3_49] (by decide) s2_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_245_safe
  · subst z; exact s3_163_safe
  · subst z; exact s3_49_safe
def s2_17 : State := ⟨[1,4,64,161], 4384504912332991121531992961630670410477570425110, 0, 0, 1, 0⟩
theorem s2_17_edges : next config 2 s2_17 = [s3_246, s3_164, s3_50] := by decide
theorem s2_17_safe : Safe 11 2 s2_17 := by
  apply safe_succ 10 2 s2_17 [s3_246, s3_164, s3_50] (by decide) s2_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_246_safe
  · subst z; exact s3_164_safe
  · subst z; exact s3_50_safe
def s2_18 : State := ⟨[1,4,64,162], 5846006551025023507419431648200451859860575813910, 0, 0, 1, 0⟩
theorem s2_18_edges : next config 2 s2_18 = [s3_502, s3_552, s3_345, s3_386, s3_247, s3_78, s3_89, s3_165, s3_51, s3_53] := by decide
theorem s2_18_safe : Safe 11 2 s2_18 := by
  apply safe_succ 10 2 s2_18 [s3_502, s3_552, s3_345, s3_386, s3_247, s3_78, s3_89, s3_165, s3_51, s3_53] (by decide) s2_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_502_safe
  · subst z; exact s3_552_safe
  · subst z; exact s3_345_safe
  · subst z; exact s3_386_safe
  · subst z; exact s3_247_safe
  · subst z; exact s3_78_safe
  · subst z; exact s3_89_safe
  · subst z; exact s3_165_safe
  · subst z; exact s3_51_safe
  · subst z; exact s3_53_safe
def s2_19 : State := ⟨[1,4,64,162], 7307508186994796957939362627063236449789435511062, 0, 0, 1, 0⟩
theorem s2_19_edges : next config 2 s2_19 = [s3_503, s3_553, s3_346, s3_387, s3_248, s3_79, s3_90, s3_166, s3_52, s3_54] := by decide
theorem s2_19_safe : Safe 11 2 s2_19 := by
  apply safe_succ 10 2 s2_19 [s3_503, s3_553, s3_346, s3_387, s3_248, s3_79, s3_90, s3_166, s3_52, s3_54] (by decide) s2_19_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_503_safe
  · subst z; exact s3_553_safe
  · subst z; exact s3_346_safe
  · subst z; exact s3_387_safe
  · subst z; exact s3_248_safe
  · subst z; exact s3_79_safe
  · subst z; exact s3_90_safe
  · subst z; exact s3_166_safe
  · subst z; exact s3_52_safe
  · subst z; exact s3_54_safe
def s2_20 : State := ⟨[1,4,64,176], 95780971326419139128294233276893524070171066415251734, 0, 0, 1, 0⟩
theorem s2_20_edges : next config 2 s2_20 = [s3_504, s3_349, s3_249, s3_80, s3_91, s3_167] := by decide
theorem s2_20_safe : Safe 11 2 s2_20 := by
  apply safe_succ 10 2 s2_20 [s3_504, s3_349, s3_249, s3_80, s3_91, s3_167] (by decide) s2_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_504_safe
  · subst z; exact s3_349_safe
  · subst z; exact s3_249_safe
  · subst z; exact s3_80_safe
  · subst z; exact s3_91_safe
  · subst z; exact s3_167_safe
def s2_21 : State := ⟨[1,4,64,176], 95782432805755724832681813820190522080542360841814294, 0, 0, 1, 0⟩
theorem s2_21_edges : next config 2 s2_21 = [s3_505, s3_350, s3_250, s3_81, s3_92, s3_168] := by decide
theorem s2_21_safe : Safe 11 2 s2_21 := by
  apply safe_succ 10 2 s2_21 [s3_505, s3_350, s3_250, s3_81, s3_92, s3_168] (by decide) s2_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_505_safe
  · subst z; exact s3_350_safe
  · subst z; exact s3_250_safe
  · subst z; exact s3_81_safe
  · subst z; exact s3_92_safe
  · subst z; exact s3_168_safe
def s2_22 : State := ⟨[1,4,64,193], 12554203470773361528692425947178148222613281455301378244886, 0, 0, 1, 0⟩
theorem s2_22_edges : next config 2 s2_22 = [s3_251, s3_169] := by decide
theorem s2_22_safe : Safe 11 2 s2_22 := by
  apply safe_succ 10 2 s2_22 [s3_251, s3_169] (by decide) s2_22_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_251_safe
  · subst z; exact s3_169_safe
def s2_23 : State := ⟨[1,4,64,193], 18831305206160042291847650636543937711788887684901876334870, 0, 0, 1, 0⟩
theorem s2_23_edges : next config 2 s2_23 = [s3_252, s3_170] := by decide
theorem s2_23_safe : Safe 11 2 s2_23 := by
  apply safe_succ 10 2 s2_23 [s3_252, s3_170] (by decide) s2_23_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_252_safe
  · subst z; exact s3_170_safe
def s2_24 : State := ⟨[1,4,64,194], 25108406941546723057044569527435357981744741559092983693590, 0, 0, 1, 0⟩
theorem s2_24_edges : next config 2 s2_24 = [s3_253, s3_171, s3_67] := by decide
theorem s2_24_safe : Safe 11 2 s2_24 := by
  apply safe_succ 10 2 s2_24 [s3_253, s3_171, s3_67] (by decide) s2_24_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_253_safe
  · subst z; exact s3_171_safe
  · subst z; exact s3_67_safe
def s2_25 : State := ⟨[1,4,64,194], 31385508676933403819519229482959270543993598573829945360662, 0, 0, 1, 0⟩
theorem s2_25_edges : next config 2 s2_25 = [s3_254, s3_172, s3_68] := by decide
theorem s2_25_safe : Safe 11 2 s2_25 := by
  apply safe_succ 10 2 s2_25 [s3_254, s3_172, s3_68] (by decide) s2_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_254_safe
  · subst z; exact s3_172_safe
  · subst z; exact s3_68_safe
def s2_26 : State := ⟨[1,4,64,196], 100433627766186892227157431008978616536533502181842616385814, 0, 0, 1, 0⟩
theorem s2_26_edges : next config 2 s2_26 = [s3_173] := by decide
theorem s2_26_safe : Safe 11 2 s2_26 := by
  apply safe_succ 10 2 s2_26 [s3_173] (by decide) s2_26_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_173_safe
def s2_27 : State := ⟨[1,4,64,196], 106710729501573572985548702561451267537221863907398359515414, 0, 0, 1, 0⟩
theorem s2_27_edges : next config 2 s2_27 = [s3_174] := by decide
theorem s2_27_safe : Safe 11 2 s2_27 := by
  apply safe_succ 10 2 s2_27 [s3_174] (by decide) s2_27_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_174_safe
def s2_28 : State := ⟨[1,4,64,208], 411376139330301510561043381120235170325683166502394837115928854, 0, 0, 1, 0⟩
theorem s2_28_edges : next config 2 s2_28 = [s3_255, s3_175, s3_69] := by decide
theorem s2_28_safe : Safe 11 2 s2_28 := by
  apply safe_succ 10 2 s2_28 [s3_255, s3_175, s3_69] (by decide) s2_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_255_safe
  · subst z; exact s3_175_safe
  · subst z; exact s3_69_safe
def s2_29 : State := ⟨[1,4,64,208], 411382416432036897219506471711127754850563550585190939644461334, 0, 0, 1, 0⟩
theorem s2_29_edges : next config 2 s2_29 = [s3_256, s3_176, s3_70] := by decide
theorem s2_29_safe : Safe 11 2 s2_29 := by
  apply safe_succ 10 2 s2_29 [s3_256, s3_176, s3_70] (by decide) s2_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_256_safe
  · subst z; exact s3_176_safe
  · subst z; exact s3_70_safe
def s2_30 : State := ⟨[1,4,65,129], 1020847100762815390445464054520728322326, 0, 0, 1, 0⟩
theorem s2_30_edges : next config 2 s2_30 = [s3_257, s3_96, s3_74] := by decide
theorem s2_30_safe : Safe 11 2 s2_30 := by
  apply safe_succ 10 2 s2_30 [s3_257, s3_96, s3_74] (by decide) s2_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_257_safe
  · subst z; exact s3_96_safe
  · subst z; exact s3_74_safe
def s2_31 : State := ⟨[1,4,65,130], 1701411834604692317372213269384264745238, 0, 0, 1, 0⟩
theorem s2_31_edges : next config 2 s2_31 = [s3_258, s3_98, s3_76, s3_78] := by decide
theorem s2_31_safe : Safe 11 2 s2_31 := by
  apply safe_succ 10 2 s2_31 [s3_258, s3_98, s3_76, s3_78] (by decide) s2_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_258_safe
  · subst z; exact s3_98_safe
  · subst z; exact s3_76_safe
  · subst z; exact s3_78_safe
def s2_32 : State := ⟨[1,4,65,132], 5784800237655953878932708558565483282710, 0, 0, 1, 0⟩
theorem s2_32_edges : next config 2 s2_32 = [s3_259, s3_100, s3_72] := by decide
theorem s2_32_safe : Safe 11 2 s2_32 := by
  apply safe_succ 10 2 s2_32 [s3_259, s3_100, s3_72] (by decide) s2_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_259_safe
  · subst z; exact s3_100_safe
  · subst z; exact s3_72_safe
def s2_33 : State := ⟨[1,4,65,136], 87452568298681185110142614342189854032150, 0, 0, 1, 0⟩
theorem s2_33_edges : next config 2 s2_33 = [s3_330, s3_260, s3_102, s3_73] := by decide
theorem s2_33_safe : Safe 11 2 s2_33 := by
  apply safe_succ 10 2 s2_33 [s3_330, s3_260, s3_102, s3_73] (by decide) s2_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_330_safe
  · subst z; exact s3_260_safe
  · subst z; exact s3_102_safe
  · subst z; exact s3_73_safe
def s2_34 : State := ⟨[1,4,65,144], 22301085480897544079999236987488018697879830, 0, 0, 1, 0⟩
theorem s2_34_edges : next config 2 s2_34 = [s3_262, s3_104, s3_75, s3_77, s3_80] := by decide
theorem s2_34_safe : Safe 11 2 s2_34 := by
  apply safe_succ 10 2 s2_34 [s3_262, s3_104, s3_75, s3_77, s3_80] (by decide) s2_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_262_safe
  · subst z; exact s3_104_safe
  · subst z; exact s3_75_safe
  · subst z; exact s3_77_safe
  · subst z; exact s3_80_safe
def s2_35 : State := ⟨[1,4,65,160], 1461501637671185285124623296234997859313124442390, 0, 0, 1, 0⟩
theorem s2_35_edges : next config 2 s2_35 = [s3_263, s3_106, s3_79, s3_81] := by decide
theorem s2_35_safe : Safe 11 2 s2_35 := by
  apply safe_succ 10 2 s2_35 [s3_263, s3_106, s3_79, s3_81] (by decide) s2_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_263_safe
  · subst z; exact s3_106_safe
  · subst z; exact s3_79_safe
  · subst z; exact s3_81_safe
def s2_36 : State := ⟨[1,4,65,192], 6277101735386680764176071790128604879621070284121226412310, 0, 0, 1, 0⟩
theorem s2_36_edges : next config 2 s2_36 = [s3_264, s3_108] := by decide
theorem s2_36_safe : Safe 11 2 s2_36 := by
  apply safe_succ 10 2 s2_36 [s3_264, s3_108] (by decide) s2_36_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_264_safe
  · subst z; exact s3_108_safe
def s2_37 : State := ⟨[1,4,65,193], 12554203470773361528011861213336271295723425728585260925206, 0, 0, 1, 0⟩
theorem s2_37_edges : next config 2 s2_37 = [s3_265, s3_110] := by decide
theorem s2_37_safe : Safe 11 2 s2_37 := by
  apply safe_succ 10 2 s2_37 [s3_265, s3_110] (by decide) s2_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_265_safe
  · subst z; exact s3_110_safe
def s2_38 : State := ⟨[1,4,66,129], 1020847100762815390482357542668147425558, 0, 0, 1, 0⟩
theorem s2_38_edges : next config 2 s2_38 = [s3_266, s3_97, s3_125, s3_85] := by decide
theorem s2_38_safe : Safe 11 2 s2_38 := by
  apply safe_succ 10 2 s2_38 [s3_266, s3_97, s3_125, s3_85] (by decide) s2_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_266_safe
  · subst z; exact s3_97_safe
  · subst z; exact s3_125_safe
  · subst z; exact s3_85_safe
def s2_39 : State := ⟨[1,4,66,130], 1701411834604692317409106757531683848470, 0, 0, 1, 0⟩
theorem s2_39_edges : next config 2 s2_39 = [s3_267, s3_99, s3_127, s3_87, s3_89] := by decide
theorem s2_39_safe : Safe 11 2 s2_39 := by
  apply safe_succ 10 2 s2_39 [s3_267, s3_99, s3_127, s3_87, s3_89] (by decide) s2_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_267_safe
  · subst z; exact s3_99_safe
  · subst z; exact s3_127_safe
  · subst z; exact s3_87_safe
  · subst z; exact s3_89_safe
def s2_40 : State := ⟨[1,4,66,132], 5784800237655953878969602046712902385942, 0, 0, 1, 0⟩
theorem s2_40_edges : next config 2 s2_40 = [s3_268, s3_101, s3_129, s3_83] := by decide
theorem s2_40_safe : Safe 11 2 s2_40 := by
  apply safe_succ 10 2 s2_40 [s3_268, s3_101, s3_129, s3_83] (by decide) s2_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_268_safe
  · subst z; exact s3_101_safe
  · subst z; exact s3_129_safe
  · subst z; exact s3_83_safe
def s2_41 : State := ⟨[1,4,66,136], 87452568298681185110179507830337273135382, 0, 0, 1, 0⟩
theorem s2_41_edges : next config 2 s2_41 = [s3_331, s3_269, s3_103, s3_131, s3_84] := by decide
theorem s2_41_safe : Safe 11 2 s2_41 := by
  apply safe_succ 10 2 s2_41 [s3_331, s3_269, s3_103, s3_131, s3_84] (by decide) s2_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_331_safe
  · subst z; exact s3_269_safe
  · subst z; exact s3_103_safe
  · subst z; exact s3_131_safe
  · subst z; exact s3_84_safe
def s2_42 : State := ⟨[1,4,66,144], 22301085480897544079999273880976166116983062, 0, 0, 1, 0⟩
theorem s2_42_edges : next config 2 s2_42 = [s3_271, s3_105, s3_229, s3_133, s3_86, s3_93, s3_88, s3_91] := by decide
theorem s2_42_safe : Safe 11 2 s2_42 := by
  apply safe_succ 10 2 s2_42 [s3_271, s3_105, s3_229, s3_133, s3_86, s3_93, s3_88, s3_91] (by decide) s2_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_271_safe
  · subst z; exact s3_105_safe
  · subst z; exact s3_229_safe
  · subst z; exact s3_133_safe
  · subst z; exact s3_86_safe
  · subst z; exact s3_93_safe
  · subst z; exact s3_88_safe
  · subst z; exact s3_91_safe
def s2_43 : State := ⟨[1,4,66,160], 1461501637671185285124623296271891347460543545622, 0, 0, 1, 0⟩
theorem s2_43_edges : next config 2 s2_43 = [s3_272, s3_107, s3_135, s3_90, s3_92] := by decide
theorem s2_43_safe : Safe 11 2 s2_43 := by
  apply safe_succ 10 2 s2_43 [s3_272, s3_107, s3_135, s3_90, s3_92] (by decide) s2_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_272_safe
  · subst z; exact s3_107_safe
  · subst z; exact s3_135_safe
  · subst z; exact s3_90_safe
  · subst z; exact s3_92_safe
def s2_44 : State := ⟨[1,4,66,192], 6277101735386680764176071790128604879657963772268645515542, 0, 0, 1, 0⟩
theorem s2_44_edges : next config 2 s2_44 = [s3_273, s3_109, s3_137] := by decide
theorem s2_44_safe : Safe 11 2 s2_44 := by
  apply safe_succ 10 2 s2_44 [s3_273, s3_109, s3_137] (by decide) s2_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_273_safe
  · subst z; exact s3_109_safe
  · subst z; exact s3_137_safe
def s2_45 : State := ⟨[1,4,66,194], 25108406941546723055683440059751604127965030105660749054230, 0, 0, 1, 0⟩
theorem s2_45_edges : next config 2 s2_45 = [s3_274, s3_111, s3_139, s3_94] := by decide
theorem s2_45_safe : Safe 11 2 s2_45 := by
  apply safe_succ 10 2 s2_45 [s3_274, s3_111, s3_139, s3_94] (by decide) s2_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_274_safe
  · subst z; exact s3_111_safe
  · subst z; exact s3_139_safe
  · subst z; exact s3_94_safe
def s2_46 : State := ⟨[1,4,67,128], 340282366920938463666288792246868312342, 0, 0, 0, 0⟩
theorem s2_46_edges : next config 2 s2_46 = [s3_407, s3_275, s3_96, s3_100, s3_112, s3_98, s3_102, s3_104, s3_106] := by decide
theorem s2_46_safe : Safe 11 2 s2_46 := by
  apply safe_succ 10 2 s2_46 [s3_407, s3_275, s3_96, s3_100, s3_112, s3_98, s3_102, s3_104, s3_106] (by decide) s2_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_407_safe
  · subst z; exact s3_275_safe
  · subst z; exact s3_96_safe
  · subst z; exact s3_100_safe
  · subst z; exact s3_112_safe
  · subst z; exact s3_98_safe
  · subst z; exact s3_102_safe
  · subst z; exact s3_104_safe
  · subst z; exact s3_106_safe
def s2_47 : State := ⟨[1,4,67,128], 340282366920938463703182280394287415574, 0, 0, 0, 0⟩
theorem s2_47_edges : next config 2 s2_47 = [s3_408, s3_276, s3_97, s3_101, s3_113, s3_99, s3_103, s3_105, s3_107] := by decide
theorem s2_47_safe : Safe 11 2 s2_47 := by
  apply safe_succ 10 2 s2_47 [s3_408, s3_276, s3_97, s3_101, s3_113, s3_99, s3_103, s3_105, s3_107] (by decide) s2_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_408_safe
  · subst z; exact s3_276_safe
  · subst z; exact s3_97_safe
  · subst z; exact s3_101_safe
  · subst z; exact s3_113_safe
  · subst z; exact s3_99_safe
  · subst z; exact s3_103_safe
  · subst z; exact s3_105_safe
  · subst z; exact s3_107_safe
def s2_48 : State := ⟨[1,4,68,129], 1020847100762815390703718471552662044950, 0, 0, 1, 0⟩
theorem s2_48_edges : next config 2 s2_48 = [s3_114] := by decide
theorem s2_48_safe : Safe 11 2 s2_48 := by
  apply safe_succ 10 2 s2_48 [s3_114] (by decide) s2_48_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_114_safe
def s2_49 : State := ⟨[1,4,68,130], 1701411834604692317630467686416198467862, 0, 0, 1, 0⟩
theorem s2_49_edges : next config 2 s2_49 = [s3_116] := by decide
theorem s2_49_safe : Safe 11 2 s2_49 := by
  apply safe_succ 10 2 s2_49 [s3_116] (by decide) s2_49_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_116_safe
def s2_50 : State := ⟨[1,4,68,132], 5784800237655953879190962975597417005334, 0, 0, 1, 0⟩
theorem s2_50_edges : next config 2 s2_50 = [] := by decide
theorem s2_50_safe : Safe 11 2 s2_50 := by
  apply safe_succ 10 2 s2_50 [] (by decide) s2_50_edges
  simp
def s2_51 : State := ⟨[1,4,68,136], 87452568298681185110400868759221787754774, 0, 0, 1, 0⟩
theorem s2_51_edges : next config 2 s2_51 = [] := by decide
theorem s2_51_safe : Safe 11 2 s2_51 := by
  apply safe_succ 10 2 s2_51 [] (by decide) s2_51_edges
  simp
def s2_52 : State := ⟨[1,4,68,144], 22301085480897544079999495241905050631602454, 0, 0, 1, 0⟩
theorem s2_52_edges : next config 2 s2_52 = [s3_115, s3_117] := by decide
theorem s2_52_safe : Safe 11 2 s2_52 := by
  apply safe_succ 10 2 s2_52 [s3_115, s3_117] (by decide) s2_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_115_safe
  · subst z; exact s3_117_safe
def s2_53 : State := ⟨[1,4,68,160], 1461501637671185285124623296493252276345058165014, 0, 0, 1, 0⟩
theorem s2_53_edges : next config 2 s2_53 = [] := by decide
theorem s2_53_safe : Safe 11 2 s2_53 := by
  apply safe_succ 10 2 s2_53 [] (by decide) s2_53_edges
  simp
def s2_54 : State := ⟨[1,4,68,192], 6277101735386680764176071790128604879879324701153160134934, 0, 0, 1, 0⟩
theorem s2_54_edges : next config 2 s2_54 = [] := by decide
theorem s2_54_safe : Safe 11 2 s2_54 := by
  apply safe_succ 10 2 s2_54 [] (by decide) s2_54_edges
  simp
def s2_55 : State := ⟨[1,4,68,196], 100433627766186892221712913138243601121414656368113677828374, 0, 0, 1, 0⟩
theorem s2_55_edges : next config 2 s2_55 = [] := by decide
theorem s2_55_safe : Safe 11 2 s2_55 := by
  apply safe_succ 10 2 s2_55 [] (by decide) s2_55_edges
  simp
def s2_56 : State := ⟨[1,4,80,129], 1020847100762816599334390181002483925270, 0, 0, 1, 0⟩
theorem s2_56_edges : next config 2 s2_56 = [s3_277, s3_126, s3_121] := by decide
theorem s2_56_safe : Safe 11 2 s2_56 := by
  apply safe_succ 10 2 s2_56 [s3_277, s3_126, s3_121] (by decide) s2_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_277_safe
  · subst z; exact s3_126_safe
  · subst z; exact s3_121_safe
def s2_57 : State := ⟨[1,4,80,130], 1701411834604693526261139395866020348182, 0, 0, 1, 0⟩
theorem s2_57_edges : next config 2 s2_57 = [s3_278, s3_227, s3_128, s3_123] := by decide
theorem s2_57_safe : Safe 11 2 s2_57 := by
  apply safe_succ 10 2 s2_57 [s3_278, s3_227, s3_128, s3_123] (by decide) s2_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_278_safe
  · subst z; exact s3_227_safe
  · subst z; exact s3_128_safe
  · subst z; exact s3_123_safe
def s2_58 : State := ⟨[1,4,80,132], 5784800237655955087821634685047238885654, 0, 0, 1, 0⟩
theorem s2_58_edges : next config 2 s2_58 = [s3_279, s3_130, s3_119] := by decide
theorem s2_58_safe : Safe 11 2 s2_58 := by
  apply safe_succ 10 2 s2_58 [s3_279, s3_130, s3_119] (by decide) s2_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_279_safe
  · subst z; exact s3_130_safe
  · subst z; exact s3_119_safe
def s2_59 : State := ⟨[1,4,80,136], 87452568298681186319031540468671609635094, 0, 0, 1, 0⟩
theorem s2_59_edges : next config 2 s2_59 = [s3_332, s3_280, s3_132, s3_120] := by decide
theorem s2_59_safe : Safe 11 2 s2_59 := by
  apply safe_succ 10 2 s2_59 [s3_332, s3_280, s3_132, s3_120] (by decide) s2_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_332_safe
  · subst z; exact s3_280_safe
  · subst z; exact s3_132_safe
  · subst z; exact s3_120_safe
def s2_60 : State := ⟨[1,4,80,144], 22301085480897544081208125913614500453482774, 0, 0, 1, 0⟩
theorem s2_60_edges : next config 2 s2_60 = [s3_282, s3_134, s3_122] := by decide
theorem s2_60_safe : Safe 11 2 s2_60 := by
  apply safe_succ 10 2 s2_60 [s3_282, s3_134, s3_122] (by decide) s2_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_282_safe
  · subst z; exact s3_134_safe
  · subst z; exact s3_122_safe
def s2_61 : State := ⟨[1,4,80,160], 1461501637671185285124624505123923985794880045334, 0, 0, 1, 0⟩
theorem s2_61_edges : next config 2 s2_61 = [s3_283, s3_136] := by decide
theorem s2_61_safe : Safe 11 2 s2_61 := by
  apply safe_succ 10 2 s2_61 [s3_283, s3_136] (by decide) s2_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_283_safe
  · subst z; exact s3_136_safe
def s2_62 : State := ⟨[1,4,80,192], 6277101735386680764176071790128606088509996410602982015254, 0, 0, 1, 0⟩
theorem s2_62_edges : next config 2 s2_62 = [s3_284, s3_138] := by decide
theorem s2_62_safe : Safe 11 2 s2_62 := by
  apply safe_succ 10 2 s2_62 [s3_284, s3_138] (by decide) s2_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_284_safe
  · subst z; exact s3_138_safe
def s2_63 : State := ⟨[1,4,80,208], 411376139330301510538742635921704547185356374049361104784654614, 0, 0, 1, 0⟩
theorem s2_63_edges : next config 2 s2_63 = [s3_285, s3_140, s3_124] := by decide
theorem s2_63_safe : Safe 11 2 s2_63 := by
  apply safe_succ 10 2 s2_63 [s3_285, s3_140, s3_124] (by decide) s2_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_285_safe
  · subst z; exact s3_140_safe
  · subst z; exact s3_124_safe
def s2_64 : State := ⟨[1,4,82,128], 340282366920943299258886786321309827350, 0, 0, 0, 0⟩
theorem s2_64_edges : next config 2 s2_64 = [s3_412, s3_317, s3_286, s3_143, s3_125, s3_129, s3_141, s3_127, s3_131, s3_133, s3_135] := by decide
theorem s2_64_safe : Safe 11 2 s2_64 := by
  apply safe_succ 10 2 s2_64 [s3_412, s3_317, s3_286, s3_143, s3_125, s3_129, s3_141, s3_127, s3_131, s3_133, s3_135] (by decide) s2_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_412_safe
  · subst z; exact s3_317_safe
  · subst z; exact s3_286_safe
  · subst z; exact s3_143_safe
  · subst z; exact s3_125_safe
  · subst z; exact s3_129_safe
  · subst z; exact s3_141_safe
  · subst z; exact s3_127_safe
  · subst z; exact s3_131_safe
  · subst z; exact s3_133_safe
  · subst z; exact s3_135_safe
def s2_65 : State := ⟨[1,4,82,128], 340282366920944508110919424655646327062, 0, 0, 0, 0⟩
theorem s2_65_edges : next config 2 s2_65 = [s3_413, s3_318, s3_287, s3_144, s3_126, s3_130, s3_142, s3_128, s3_132, s3_134, s3_136] := by decide
theorem s2_65_safe : Safe 11 2 s2_65 := by
  apply safe_succ 10 2 s2_65 [s3_413, s3_318, s3_287, s3_144, s3_126, s3_130, s3_142, s3_128, s3_132, s3_134, s3_136] (by decide) s2_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_413_safe
  · subst z; exact s3_318_safe
  · subst z; exact s3_287_safe
  · subst z; exact s3_144_safe
  · subst z; exact s3_126_safe
  · subst z; exact s3_130_safe
  · subst z; exact s3_142_safe
  · subst z; exact s3_128_safe
  · subst z; exact s3_132_safe
  · subst z; exact s3_134_safe
  · subst z; exact s3_136_safe
def s2_66 : State := ⟨[1,4,96,129], 1020847100842043552922834903966853169430, 0, 0, 1, 0⟩
theorem s2_66_edges : next config 2 s2_66 = [s3_530, s3_360, s3_388, s3_448, s3_319, s3_288, s3_183, s3_192, s3_233, s3_201, s3_211, s3_177, s3_153, s3_155, s3_159, s3_163] := by decide
theorem s2_66_safe : Safe 11 2 s2_66 := by
  apply safe_succ 10 2 s2_66 [s3_530, s3_360, s3_388, s3_448, s3_319, s3_288, s3_183, s3_192, s3_233, s3_201, s3_211, s3_177, s3_153, s3_155, s3_159, s3_163] (by decide) s2_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_530_safe
  · subst z; exact s3_360_safe
  · subst z; exact s3_388_safe
  · subst z; exact s3_448_safe
  · subst z; exact s3_319_safe
  · subst z; exact s3_288_safe
  · subst z; exact s3_183_safe
  · subst z; exact s3_192_safe
  · subst z; exact s3_233_safe
  · subst z; exact s3_201_safe
  · subst z; exact s3_211_safe
  · subst z; exact s3_177_safe
  · subst z; exact s3_153_safe
  · subst z; exact s3_155_safe
  · subst z; exact s3_159_safe
  · subst z; exact s3_163_safe
def s2_67 : State := ⟨[1,4,96,130], 1701411834683920479849584118830389592342, 0, 0, 1, 0⟩
theorem s2_67_edges : next config 2 s2_67 = [s3_531, s3_543, s3_361, s3_389, s3_449, s3_320, s3_289, s3_184, s3_193, s3_202, s3_212, s3_154, s3_161, s3_165] := by decide
theorem s2_67_safe : Safe 11 2 s2_67 := by
  apply safe_succ 10 2 s2_67 [s3_531, s3_543, s3_361, s3_389, s3_449, s3_320, s3_289, s3_184, s3_193, s3_202, s3_212, s3_154, s3_161, s3_165] (by decide) s2_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_531_safe
  · subst z; exact s3_543_safe
  · subst z; exact s3_361_safe
  · subst z; exact s3_389_safe
  · subst z; exact s3_449_safe
  · subst z; exact s3_320_safe
  · subst z; exact s3_289_safe
  · subst z; exact s3_184_safe
  · subst z; exact s3_193_safe
  · subst z; exact s3_202_safe
  · subst z; exact s3_212_safe
  · subst z; exact s3_154_safe
  · subst z; exact s3_161_safe
  · subst z; exact s3_165_safe
def s2_68 : State := ⟨[1,4,96,132], 5784800237735182041410079408011608129814, 0, 0, 1, 0⟩
theorem s2_68_edges : next config 2 s2_68 = [s3_532, s3_363, s3_390, s3_450, s3_321, s3_290, s3_185, s3_194, s3_234, s3_203, s3_213, s3_179, s3_157] := by decide
theorem s2_68_safe : Safe 11 2 s2_68 := by
  apply safe_succ 10 2 s2_68 [s3_532, s3_363, s3_390, s3_450, s3_321, s3_290, s3_185, s3_194, s3_234, s3_203, s3_213, s3_179, s3_157] (by decide) s2_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_532_safe
  · subst z; exact s3_363_safe
  · subst z; exact s3_390_safe
  · subst z; exact s3_450_safe
  · subst z; exact s3_321_safe
  · subst z; exact s3_290_safe
  · subst z; exact s3_185_safe
  · subst z; exact s3_194_safe
  · subst z; exact s3_234_safe
  · subst z; exact s3_203_safe
  · subst z; exact s3_213_safe
  · subst z; exact s3_179_safe
  · subst z; exact s3_157_safe
def s2_69 : State := ⟨[1,4,96,136], 87452568298760413272619985191635978879254, 0, 0, 1, 0⟩
theorem s2_69_edges : next config 2 s2_69 = [s3_533, s3_545, s3_364, s3_391, s3_451, s3_322, s3_333, s3_291, s3_186, s3_195, s3_204, s3_214, s3_156, s3_158] := by decide
theorem s2_69_safe : Safe 11 2 s2_69 := by
  apply safe_succ 10 2 s2_69 [s3_533, s3_545, s3_364, s3_391, s3_451, s3_322, s3_333, s3_291, s3_186, s3_195, s3_204, s3_214, s3_156, s3_158] (by decide) s2_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_533_safe
  · subst z; exact s3_545_safe
  · subst z; exact s3_364_safe
  · subst z; exact s3_391_safe
  · subst z; exact s3_451_safe
  · subst z; exact s3_322_safe
  · subst z; exact s3_333_safe
  · subst z; exact s3_291_safe
  · subst z; exact s3_186_safe
  · subst z; exact s3_195_safe
  · subst z; exact s3_204_safe
  · subst z; exact s3_214_safe
  · subst z; exact s3_156_safe
  · subst z; exact s3_158_safe
def s2_70 : State := ⟨[1,4,96,144], 22301085480897623308161714358337464822726934, 0, 0, 1, 0⟩
theorem s2_70_edges : next config 2 s2_70 = [s3_534, s3_365, s3_393, s3_452, s3_323, s3_293, s3_187, s3_196, s3_235, s3_205, s3_215, s3_160, s3_181, s3_162, s3_167] := by decide
theorem s2_70_safe : Safe 11 2 s2_70 := by
  apply safe_succ 10 2 s2_70 [s3_534, s3_365, s3_393, s3_452, s3_323, s3_293, s3_187, s3_196, s3_235, s3_205, s3_215, s3_160, s3_181, s3_162, s3_167] (by decide) s2_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_534_safe
  · subst z; exact s3_365_safe
  · subst z; exact s3_393_safe
  · subst z; exact s3_452_safe
  · subst z; exact s3_323_safe
  · subst z; exact s3_293_safe
  · subst z; exact s3_187_safe
  · subst z; exact s3_196_safe
  · subst z; exact s3_235_safe
  · subst z; exact s3_205_safe
  · subst z; exact s3_215_safe
  · subst z; exact s3_160_safe
  · subst z; exact s3_181_safe
  · subst z; exact s3_162_safe
  · subst z; exact s3_167_safe
def s2_71 : State := ⟨[1,4,96,160], 1461501637671185285203851458712368708759249289494, 0, 0, 1, 0⟩
theorem s2_71_edges : next config 2 s2_71 = [s3_535, s3_546, s3_366, s3_394, s3_453, s3_324, s3_294, s3_188, s3_197, s3_206, s3_216, s3_164, s3_166, s3_168] := by decide
theorem s2_71_safe : Safe 11 2 s2_71 := by
  apply safe_succ 10 2 s2_71 [s3_535, s3_546, s3_366, s3_394, s3_453, s3_324, s3_294, s3_188, s3_197, s3_206, s3_216, s3_164, s3_166, s3_168] (by decide) s2_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_535_safe
  · subst z; exact s3_546_safe
  · subst z; exact s3_366_safe
  · subst z; exact s3_394_safe
  · subst z; exact s3_453_safe
  · subst z; exact s3_324_safe
  · subst z; exact s3_294_safe
  · subst z; exact s3_188_safe
  · subst z; exact s3_197_safe
  · subst z; exact s3_206_safe
  · subst z; exact s3_216_safe
  · subst z; exact s3_164_safe
  · subst z; exact s3_166_safe
  · subst z; exact s3_168_safe
def s2_72 : State := ⟨[1,4,96,192], 6277101735386680764176071790207833042098441133567351259414, 0, 0, 1, 0⟩
theorem s2_72_edges : next config 2 s2_72 = [s3_536, s3_554, s3_367, s3_395, s3_455, s3_325, s3_336, s3_295, s3_189, s3_198, s3_207, s3_217, s3_170, s3_174, s3_172, s3_176] := by decide
theorem s2_72_safe : Safe 11 2 s2_72 := by
  apply safe_succ 10 2 s2_72 [s3_536, s3_554, s3_367, s3_395, s3_455, s3_325, s3_336, s3_295, s3_189, s3_198, s3_207, s3_217, s3_170, s3_174, s3_172, s3_176] (by decide) s2_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_536_safe
  · subst z; exact s3_554_safe
  · subst z; exact s3_367_safe
  · subst z; exact s3_395_safe
  · subst z; exact s3_455_safe
  · subst z; exact s3_325_safe
  · subst z; exact s3_336_safe
  · subst z; exact s3_295_safe
  · subst z; exact s3_189_safe
  · subst z; exact s3_198_safe
  · subst z; exact s3_207_safe
  · subst z; exact s3_217_safe
  · subst z; exact s3_170_safe
  · subst z; exact s3_174_safe
  · subst z; exact s3_172_safe
  · subst z; exact s3_176_safe
def s2_73 : State := ⟨[1,4,96,224], 26959946667150639794667015087359913040637311048536658170206926995734, 0, 0, 1, 0⟩
theorem s2_73_edges : next config 2 s2_73 = [s3_537, s3_556, s3_368, s3_396, s3_456, s3_326, s3_337, s3_296, s3_190, s3_199, s3_208, s3_218, s3_178, s3_180, s3_182] := by decide
theorem s2_73_safe : Safe 11 2 s2_73 := by
  apply safe_succ 10 2 s2_73 [s3_537, s3_556, s3_368, s3_396, s3_456, s3_326, s3_337, s3_296, s3_190, s3_199, s3_208, s3_218, s3_178, s3_180, s3_182] (by decide) s2_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_537_safe
  · subst z; exact s3_556_safe
  · subst z; exact s3_368_safe
  · subst z; exact s3_396_safe
  · subst z; exact s3_456_safe
  · subst z; exact s3_326_safe
  · subst z; exact s3_337_safe
  · subst z; exact s3_296_safe
  · subst z; exact s3_190_safe
  · subst z; exact s3_199_safe
  · subst z; exact s3_208_safe
  · subst z; exact s3_218_safe
  · subst z; exact s3_178_safe
  · subst z; exact s3_180_safe
  · subst z; exact s3_182_safe
def s2_74 : State := ⟨[1,4,97,128], 340282367158622951024614364290404647190, 0, 0, 0, 0⟩
theorem s2_74_edges : next config 2 s2_74 = [s3_415, s3_297, s3_183, s3_185, s3_191, s3_184, s3_186, s3_187, s3_188] := by decide
theorem s2_74_safe : Safe 11 2 s2_74 := by
  apply safe_succ 10 2 s2_74 [s3_415, s3_297, s3_183, s3_185, s3_191, s3_184, s3_186, s3_187, s3_188] (by decide) s2_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_415_safe
  · subst z; exact s3_297_safe
  · subst z; exact s3_183_safe
  · subst z; exact s3_185_safe
  · subst z; exact s3_191_safe
  · subst z; exact s3_184_safe
  · subst z; exact s3_186_safe
  · subst z; exact s3_187_safe
  · subst z; exact s3_188_safe
def s2_75 : State := ⟨[1,4,100,128], 340282368267817226224315090600019951894, 0, 0, 0, 0⟩
theorem s2_75_edges : next config 2 s2_75 = [s3_369, s3_416, s3_192, s3_194, s3_200, s3_193, s3_195, s3_196, s3_197] := by decide
theorem s2_75_safe : Safe 11 2 s2_75 := by
  apply safe_succ 10 2 s2_75 [s3_369, s3_416, s3_192, s3_194, s3_200, s3_193, s3_195, s3_196, s3_197] (by decide) s2_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_369_safe
  · subst z; exact s3_416_safe
  · subst z; exact s3_192_safe
  · subst z; exact s3_194_safe
  · subst z; exact s3_200_safe
  · subst z; exact s3_193_safe
  · subst z; exact s3_195_safe
  · subst z; exact s3_196_safe
  · subst z; exact s3_197_safe
def s2_76 : State := ⟨[1,4,104,128], 340282387282576229647756113050568032534, 0, 0, 0, 0⟩
theorem s2_76_edges : next config 2 s2_76 = [s3_370, s3_397, s3_417, s3_457, s3_329, s3_298, s3_210, s3_220, s3_201, s3_203, s3_209, s3_202, s3_204, s3_205, s3_206] := by decide
theorem s2_76_safe : Safe 11 2 s2_76 := by
  apply safe_succ 10 2 s2_76 [s3_370, s3_397, s3_417, s3_457, s3_329, s3_298, s3_210, s3_220, s3_201, s3_203, s3_209, s3_202, s3_204, s3_205, s3_206] (by decide) s2_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_370_safe
  · subst z; exact s3_397_safe
  · subst z; exact s3_417_safe
  · subst z; exact s3_457_safe
  · subst z; exact s3_329_safe
  · subst z; exact s3_298_safe
  · subst z; exact s3_210_safe
  · subst z; exact s3_220_safe
  · subst z; exact s3_201_safe
  · subst z; exact s3_203_safe
  · subst z; exact s3_209_safe
  · subst z; exact s3_202_safe
  · subst z; exact s3_204_safe
  · subst z; exact s3_205_safe
  · subst z; exact s3_206_safe
def s2_77 : State := ⟨[1,4,112,128], 340287559297025160823714219599645966614, 0, 0, 0, 0⟩
theorem s2_77_edges : next config 2 s2_77 = [s3_418, s3_299, s3_211, s3_213, s3_219, s3_212, s3_214, s3_215, s3_216] := by decide
theorem s2_77_safe : Safe 11 2 s2_77 := by
  apply safe_succ 10 2 s2_77 [s3_418, s3_299, s3_211, s3_213, s3_219, s3_212, s3_214, s3_215, s3_216] (by decide) s2_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_418_safe
  · subst z; exact s3_299_safe
  · subst z; exact s3_211_safe
  · subst z; exact s3_213_safe
  · subst z; exact s3_219_safe
  · subst z; exact s3_212_safe
  · subst z; exact s3_214_safe
  · subst z; exact s3_215_safe
  · subst z; exact s3_216_safe
def s2_78 : State := ⟨[1,4,193,129], 12554203470773361528692425947178148222613281455301378244886, 0, 0, 1, 0⟩
theorem s2_78_edges : next config 2 s2_78 = [s3_300, s3_221] := by decide
theorem s2_78_safe : Safe 11 2 s2_78 := by
  apply safe_succ 10 2 s2_78 [s3_300, s3_221] (by decide) s2_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_300_safe
  · subst z; exact s3_221_safe
def s2_79 : State := ⟨[1,4,194,130], 25108406941546723057044569527435357981744741559092983693590, 0, 0, 1, 0⟩
theorem s2_79_edges : next config 2 s2_79 = [s3_301, s3_228, s3_222, s3_223] := by decide
theorem s2_79_safe : Safe 11 2 s2_79 := by
  apply safe_succ 10 2 s2_79 [s3_301, s3_228, s3_222, s3_223] (by decide) s2_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_301_safe
  · subst z; exact s3_228_safe
  · subst z; exact s3_222_safe
  · subst z; exact s3_223_safe
def s2_80 : State := ⟨[1,4,196,132], 100433627766186892227157431008978616536533502181842616385814, 0, 0, 1, 0⟩
theorem s2_80_edges : next config 2 s2_80 = [] := by decide
theorem s2_80_safe : Safe 11 2 s2_80 := by
  apply safe_succ 10 2 s2_80 [] (by decide) s2_80_edges
  simp
def s2_81 : State := ⟨[1,4,208,144], 411376139330301510561043381120235170325683166502394837115928854, 0, 0, 1, 0⟩
theorem s2_81_edges : next config 2 s2_81 = [s3_302, s3_230, s3_224] := by decide
theorem s2_81_safe : Safe 11 2 s2_81 := by
  apply safe_succ 10 2 s2_81 [s3_302, s3_230, s3_224] (by decide) s2_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_302_safe
  · subst z; exact s3_230_safe
  · subst z; exact s3_224_safe
def s2_82 : State := ⟨[1,12,64,129], 1020847100762815390408570566373309223190, 2, 0, 1, 0⟩
theorem s2_82_edges : next config 2 s2_82 = [s3_517, s3_371, s3_458, s3_2, s3_257, s3_300, s3_266, s3_277, s3_288, s3_251, s3_239, s3_241, s3_245] := by decide
theorem s2_82_safe : Safe 11 2 s2_82 := by
  apply safe_succ 10 2 s2_82 [s3_517, s3_371, s3_458, s3_2, s3_257, s3_300, s3_266, s3_277, s3_288, s3_251, s3_239, s3_241, s3_245] (by decide) s2_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_517_safe
  · subst z; exact s3_371_safe
  · subst z; exact s3_458_safe
  · subst z; exact s3_2_safe
  · subst z; exact s3_257_safe
  · subst z; exact s3_300_safe
  · subst z; exact s3_266_safe
  · subst z; exact s3_277_safe
  · subst z; exact s3_288_safe
  · subst z; exact s3_251_safe
  · subst z; exact s3_239_safe
  · subst z; exact s3_241_safe
  · subst z; exact s3_245_safe
def s2_83 : State := ⟨[1,12,64,130], 1701411834604692317335319781236845646102, 2, 0, 1, 0⟩
theorem s2_83_edges : next config 2 s2_83 = [s3_518, s3_544, s3_372, s3_459, s3_8, s3_258, s3_301, s3_267, s3_278, s3_289, s3_240, s3_253, s3_243, s3_247] := by decide
theorem s2_83_safe : Safe 11 2 s2_83 := by
  apply safe_succ 10 2 s2_83 [s3_518, s3_544, s3_372, s3_459, s3_8, s3_258, s3_301, s3_267, s3_278, s3_289, s3_240, s3_253, s3_243, s3_247] (by decide) s2_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_518_safe
  · subst z; exact s3_544_safe
  · subst z; exact s3_372_safe
  · subst z; exact s3_459_safe
  · subst z; exact s3_8_safe
  · subst z; exact s3_258_safe
  · subst z; exact s3_301_safe
  · subst z; exact s3_267_safe
  · subst z; exact s3_278_safe
  · subst z; exact s3_289_safe
  · subst z; exact s3_240_safe
  · subst z; exact s3_253_safe
  · subst z; exact s3_243_safe
  · subst z; exact s3_247_safe
def s2_84 : State := ⟨[1,12,64,132], 5784800237655953878895815070418064183574, 2, 0, 1, 0⟩
theorem s2_84_edges : next config 2 s2_84 = [s3_519, s3_374, s3_460, s3_16, s3_259, s3_268, s3_279, s3_290] := by decide
theorem s2_84_safe : Safe 11 2 s2_84 := by
  apply safe_succ 10 2 s2_84 [s3_519, s3_374, s3_460, s3_16, s3_259, s3_268, s3_279, s3_290] (by decide) s2_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_519_safe
  · subst z; exact s3_374_safe
  · subst z; exact s3_460_safe
  · subst z; exact s3_16_safe
  · subst z; exact s3_259_safe
  · subst z; exact s3_268_safe
  · subst z; exact s3_279_safe
  · subst z; exact s3_290_safe
def s2_85 : State := ⟨[1,12,64,136], 87452568298681185110105720854042434933014, 2, 0, 1, 0⟩
theorem s2_85_edges : next config 2 s2_85 = [s3_520, s3_375, s3_461, s3_22, s3_260, s3_269, s3_280, s3_291] := by decide
theorem s2_85_safe : Safe 11 2 s2_85 := by
  apply safe_succ 10 2 s2_85 [s3_520, s3_375, s3_461, s3_22, s3_260, s3_269, s3_280, s3_291] (by decide) s2_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_520_safe
  · subst z; exact s3_375_safe
  · subst z; exact s3_461_safe
  · subst z; exact s3_22_safe
  · subst z; exact s3_260_safe
  · subst z; exact s3_269_safe
  · subst z; exact s3_280_safe
  · subst z; exact s3_291_safe
def s2_86 : State := ⟨[1,12,64,140], 1394136857275084884809464213392032366924054, 2, 0, 1, 0⟩
theorem s2_86_edges : next config 2 s2_86 = [s3_521, s3_376, s3_462, s3_29, s3_261, s3_270, s3_281, s3_292] := by decide
theorem s2_86_safe : Safe 11 2 s2_86 := by
  apply safe_succ 10 2 s2_86 [s3_521, s3_376, s3_462, s3_29, s3_261, s3_270, s3_281, s3_292] (by decide) s2_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_521_safe
  · subst z; exact s3_376_safe
  · subst z; exact s3_462_safe
  · subst z; exact s3_29_safe
  · subst z; exact s3_261_safe
  · subst z; exact s3_270_safe
  · subst z; exact s3_281_safe
  · subst z; exact s3_292_safe
def s2_87 : State := ⟨[1,12,64,144], 22301085480897544079999200093999871278780694, 2, 0, 1, 0⟩
theorem s2_87_edges : next config 2 s2_87 = [s3_522, s3_377, s3_463, s3_32, s3_262, s3_302, s3_271, s3_282, s3_293, s3_242, s3_255, s3_244, s3_249] := by decide
theorem s2_87_safe : Safe 11 2 s2_87 := by
  apply safe_succ 10 2 s2_87 [s3_522, s3_377, s3_463, s3_32, s3_262, s3_302, s3_271, s3_282, s3_293, s3_242, s3_255, s3_244, s3_249] (by decide) s2_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_522_safe
  · subst z; exact s3_377_safe
  · subst z; exact s3_463_safe
  · subst z; exact s3_32_safe
  · subst z; exact s3_262_safe
  · subst z; exact s3_302_safe
  · subst z; exact s3_271_safe
  · subst z; exact s3_282_safe
  · subst z; exact s3_293_safe
  · subst z; exact s3_242_safe
  · subst z; exact s3_255_safe
  · subst z; exact s3_244_safe
  · subst z; exact s3_249_safe
def s2_88 : State := ⟨[1,12,64,160], 1461501637671185285124623296198104371165705343254, 2, 0, 1, 0⟩
theorem s2_88_edges : next config 2 s2_88 = [s3_523, s3_547, s3_378, s3_464, s3_41, s3_263, s3_272, s3_283, s3_294, s3_246, s3_248, s3_250] := by decide
theorem s2_88_safe : Safe 11 2 s2_88 := by
  apply safe_succ 10 2 s2_88 [s3_523, s3_547, s3_378, s3_464, s3_41, s3_263, s3_272, s3_283, s3_294, s3_246, s3_248, s3_250] (by decide) s2_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_523_safe
  · subst z; exact s3_547_safe
  · subst z; exact s3_378_safe
  · subst z; exact s3_464_safe
  · subst z; exact s3_41_safe
  · subst z; exact s3_263_safe
  · subst z; exact s3_272_safe
  · subst z; exact s3_283_safe
  · subst z; exact s3_294_safe
  · subst z; exact s3_246_safe
  · subst z; exact s3_248_safe
  · subst z; exact s3_250_safe
def s2_89 : State := ⟨[1,12,64,192], 6277101735386680764176071790128604879584176795973807313174, 2, 0, 1, 0⟩
theorem s2_89_edges : next config 2 s2_89 = [s3_524, s3_555, s3_379, s3_466, s3_57, s3_264, s3_273, s3_284, s3_295, s3_252, s3_254, s3_256] := by decide
theorem s2_89_safe : Safe 11 2 s2_89 := by
  apply safe_succ 10 2 s2_89 [s3_524, s3_555, s3_379, s3_466, s3_57, s3_264, s3_273, s3_284, s3_295, s3_252, s3_254, s3_256] (by decide) s2_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_524_safe
  · subst z; exact s3_555_safe
  · subst z; exact s3_379_safe
  · subst z; exact s3_466_safe
  · subst z; exact s3_57_safe
  · subst z; exact s3_264_safe
  · subst z; exact s3_273_safe
  · subst z; exact s3_284_safe
  · subst z; exact s3_295_safe
  · subst z; exact s3_252_safe
  · subst z; exact s3_254_safe
  · subst z; exact s3_256_safe
def s2_90 : State := ⟨[1,12,65,128], 340282366920938463518714839657191903510, 2, 0, 0, 0⟩
theorem s2_90_edges : next config 2 s2_90 = [s3_422, s3_71, s3_275, s3_257, s3_261, s3_265, s3_258, s3_260, s3_262, s3_263] := by decide
theorem s2_90_safe : Safe 11 2 s2_90 := by
  apply safe_succ 10 2 s2_90 [s3_422, s3_71, s3_275, s3_257, s3_261, s3_265, s3_258, s3_260, s3_262, s3_263] (by decide) s2_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_422_safe
  · subst z; exact s3_71_safe
  · subst z; exact s3_275_safe
  · subst z; exact s3_257_safe
  · subst z; exact s3_261_safe
  · subst z; exact s3_265_safe
  · subst z; exact s3_258_safe
  · subst z; exact s3_260_safe
  · subst z; exact s3_262_safe
  · subst z; exact s3_263_safe
def s2_91 : State := ⟨[1,12,66,128], 340282366920938463555608327804611006742, 2, 0, 0, 0⟩
theorem s2_91_edges : next config 2 s2_91 = [s3_423, s3_82, s3_276, s3_286, s3_266, s3_270, s3_274, s3_267, s3_269, s3_271, s3_272] := by decide
theorem s2_91_safe : Safe 11 2 s2_91 := by
  apply safe_succ 10 2 s2_91 [s3_423, s3_82, s3_276, s3_286, s3_266, s3_270, s3_274, s3_267, s3_269, s3_271, s3_272] (by decide) s2_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_423_safe
  · subst z; exact s3_82_safe
  · subst z; exact s3_276_safe
  · subst z; exact s3_286_safe
  · subst z; exact s3_266_safe
  · subst z; exact s3_270_safe
  · subst z; exact s3_274_safe
  · subst z; exact s3_267_safe
  · subst z; exact s3_269_safe
  · subst z; exact s3_271_safe
  · subst z; exact s3_272_safe
def s2_92 : State := ⟨[1,12,80,128], 340282366920939672407640966138947506454, 2, 0, 0, 0⟩
theorem s2_92_edges : next config 2 s2_92 = [s3_424, s3_118, s3_287, s3_277, s3_281, s3_285, s3_278, s3_280, s3_282, s3_283] := by decide
theorem s2_92_safe : Safe 11 2 s2_92 := by
  apply safe_succ 10 2 s2_92 [s3_424, s3_118, s3_287, s3_277, s3_281, s3_285, s3_278, s3_280, s3_282, s3_283] (by decide) s2_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_424_safe
  · subst z; exact s3_118_safe
  · subst z; exact s3_287_safe
  · subst z; exact s3_277_safe
  · subst z; exact s3_281_safe
  · subst z; exact s3_285_safe
  · subst z; exact s3_278_safe
  · subst z; exact s3_280_safe
  · subst z; exact s3_282_safe
  · subst z; exact s3_283_safe
def s2_93 : State := ⟨[1,12,96,128], 340282367000166625996085689103316750614, 2, 0, 0, 0⟩
theorem s2_93_edges : next config 2 s2_93 = [s3_540, s3_381, s3_426, s3_467, s3_147, s3_297, s3_298, s3_299, s3_288, s3_292, s3_296, s3_289, s3_291, s3_293, s3_294] := by decide
theorem s2_93_safe : Safe 11 2 s2_93 := by
  apply safe_succ 10 2 s2_93 [s3_540, s3_381, s3_426, s3_467, s3_147, s3_297, s3_298, s3_299, s3_288, s3_292, s3_296, s3_289, s3_291, s3_293, s3_294] (by decide) s2_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_540_safe
  · subst z; exact s3_381_safe
  · subst z; exact s3_426_safe
  · subst z; exact s3_467_safe
  · subst z; exact s3_147_safe
  · subst z; exact s3_297_safe
  · subst z; exact s3_298_safe
  · subst z; exact s3_299_safe
  · subst z; exact s3_288_safe
  · subst z; exact s3_292_safe
  · subst z; exact s3_296_safe
  · subst z; exact s3_289_safe
  · subst z; exact s3_291_safe
  · subst z; exact s3_293_safe
  · subst z; exact s3_294_safe
def s2_94 : State := ⟨[1,68,64,129], 1020847100762815390703718471552662044950, 2, 0, 1, 0⟩
theorem s2_94_edges : next config 2 s2_94 = [s3_5, s3_307, s3_303] := by decide
theorem s2_94_safe : Safe 11 2 s2_94 := by
  apply safe_succ 10 2 s2_94 [s3_5, s3_307, s3_303] (by decide) s2_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_5_safe
  · subst z; exact s3_307_safe
  · subst z; exact s3_303_safe
def s2_95 : State := ⟨[1,68,64,130], 1701411834604692317630467686416198467862, 2, 0, 1, 0⟩
theorem s2_95_edges : next config 2 s2_95 = [s3_11, s3_308, s3_305] := by decide
theorem s2_95_safe : Safe 11 2 s2_95 := by
  apply safe_succ 10 2 s2_95 [s3_11, s3_308, s3_305] (by decide) s2_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_11_safe
  · subst z; exact s3_308_safe
  · subst z; exact s3_305_safe
def s2_96 : State := ⟨[1,68,64,132], 5784800237655953879190962975597417005334, 2, 0, 1, 0⟩
theorem s2_96_edges : next config 2 s2_96 = [s3_19, s3_309] := by decide
theorem s2_96_safe : Safe 11 2 s2_96 := by
  apply safe_succ 10 2 s2_96 [s3_19, s3_309] (by decide) s2_96_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_19_safe
  · subst z; exact s3_309_safe
def s2_97 : State := ⟨[1,68,64,136], 87452568298681185110400868759221787754774, 2, 0, 1, 0⟩
theorem s2_97_edges : next config 2 s2_97 = [s3_25, s3_310] := by decide
theorem s2_97_safe : Safe 11 2 s2_97 := by
  apply safe_succ 10 2 s2_97 [s3_25, s3_310] (by decide) s2_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_25_safe
  · subst z; exact s3_310_safe
def s2_98 : State := ⟨[1,68,64,144], 22301085480897544079999495241905050631602454, 2, 0, 1, 0⟩
theorem s2_98_edges : next config 2 s2_98 = [s3_35, s3_311, s3_304, s3_306] := by decide
theorem s2_98_safe : Safe 11 2 s2_98 := by
  apply safe_succ 10 2 s2_98 [s3_35, s3_311, s3_304, s3_306] (by decide) s2_98_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_35_safe
  · subst z; exact s3_311_safe
  · subst z; exact s3_304_safe
  · subst z; exact s3_306_safe
def s2_99 : State := ⟨[1,68,64,160], 1461501637671185285124623296493252276345058165014, 2, 0, 1, 0⟩
theorem s2_99_edges : next config 2 s2_99 = [s3_44, s3_312] := by decide
theorem s2_99_safe : Safe 11 2 s2_99 := by
  apply safe_succ 10 2 s2_99 [s3_44, s3_312] (by decide) s2_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_44_safe
  · subst z; exact s3_312_safe
def s2_100 : State := ⟨[1,68,64,192], 6277101735386680764176071790128604879879324701153160134934, 2, 0, 1, 0⟩
theorem s2_100_edges : next config 2 s2_100 = [s3_60, s3_313] := by decide
theorem s2_100_safe : Safe 11 2 s2_100 := by
  apply safe_succ 10 2 s2_100 [s3_60, s3_313] (by decide) s2_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_60_safe
  · subst z; exact s3_313_safe
def s2_101 : State := ⟨[1,68,64,196], 100433627766186892221712913138243601121414656368113677828374, 2, 0, 1, 0⟩
theorem s2_101_edges : next config 2 s2_101 = [s3_64, s3_314] := by decide
theorem s2_101_safe : Safe 11 2 s2_101 := by
  apply safe_succ 10 2 s2_101 [s3_64, s3_314] (by decide) s2_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_64_safe
  · subst z; exact s3_314_safe
def s2_102 : State := ⟨[1,68,96,128], 340282367000166626291233594282669572374, 2, 0, 0, 0⟩
theorem s2_102_edges : next config 2 s2_102 = [s3_437, s3_316, s3_307, s3_314, s3_315, s3_308, s3_310, s3_311, s3_312] := by decide
theorem s2_102_safe : Safe 11 2 s2_102 := by
  apply safe_succ 10 2 s2_102 [s3_437, s3_316, s3_307, s3_314, s3_315, s3_308, s3_310, s3_311, s3_312] (by decide) s2_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_437_safe
  · subst z; exact s3_316_safe
  · subst z; exact s3_307_safe
  · subst z; exact s3_314_safe
  · subst z; exact s3_315_safe
  · subst z; exact s3_308_safe
  · subst z; exact s3_310_safe
  · subst z; exact s3_311_safe
  · subst z; exact s3_312_safe
def s2_103 : State := ⟨[1,100,96,128], 340282368267817226224315090600019951894, 2, 0, 0, 0⟩
theorem s2_103_edges : next config 2 s2_103 = [s3_382, s3_438, s3_152, s3_328, s3_319, s3_327, s3_326, s3_320, s3_322, s3_323, s3_324] := by decide
theorem s2_103_safe : Safe 11 2 s2_103 := by
  apply safe_succ 10 2 s2_103 [s3_382, s3_438, s3_152, s3_328, s3_319, s3_327, s3_326, s3_320, s3_322, s3_323, s3_324] (by decide) s2_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_382_safe
  · subst z; exact s3_438_safe
  · subst z; exact s3_152_safe
  · subst z; exact s3_328_safe
  · subst z; exact s3_319_safe
  · subst z; exact s3_327_safe
  · subst z; exact s3_326_safe
  · subst z; exact s3_320_safe
  · subst z; exact s3_322_safe
  · subst z; exact s3_323_safe
  · subst z; exact s3_324_safe
def s2_104 : State := ⟨[1,140,64,136], 1481249143206845131456088112894565029052694, 2, 0, 1, 0⟩
theorem s2_104_edges : next config 2 s2_104 = [s3_528, s3_383, s3_468, s3_27, s3_330, s3_331, s3_332, s3_333] := by decide
theorem s2_104_safe : Safe 11 2 s2_104 := by
  apply safe_succ 10 2 s2_104 [s3_528, s3_383, s3_468, s3_27, s3_330, s3_331, s3_332, s3_333] (by decide) s2_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_528_safe
  · subst z; exact s3_383_safe
  · subst z; exact s3_468_safe
  · subst z; exact s3_27_safe
  · subst z; exact s3_330_safe
  · subst z; exact s3_331_safe
  · subst z; exact s3_332_safe
  · subst z; exact s3_333_safe
def s2_105 : State := ⟨[1,196,64,192], 106710729501573572985548702561451267537221863907398359515414, 2, 0, 1, 0⟩
theorem s2_105_edges : next config 2 s2_105 = [s3_62, s3_336] := by decide
theorem s2_105_safe : Safe 11 2 s2_105 := by
  apply safe_succ 10 2 s2_105 [s3_62, s3_336] (by decide) s2_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_62_safe
  · subst z; exact s3_336_safe
def s2_106 : State := ⟨[3,4,64,129], 1020847100762815390408570566373309219102, 1, 0, 1, 0⟩
theorem s2_106_edges : next config 2 s2_106 = [s3_0, s3_469, s3_371, s3_351, s3_360, s3_341] := by decide
theorem s2_106_safe : Safe 11 2 s2_106 := by
  apply safe_succ 10 2 s2_106 [s3_0, s3_469, s3_371, s3_351, s3_360, s3_341] (by decide) s2_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_0_safe
  · subst z; exact s3_469_safe
  · subst z; exact s3_371_safe
  · subst z; exact s3_351_safe
  · subst z; exact s3_360_safe
  · subst z; exact s3_341_safe
def s2_107 : State := ⟨[3,4,64,130], 1701411834604692317335319781236845642014, 1, 0, 1, 0⟩
theorem s2_107_edges : next config 2 s2_107 = [s3_6, s3_471, s3_372, s3_352, s3_361, s3_343, s3_345] := by decide
theorem s2_107_safe : Safe 11 2 s2_107 := by
  apply safe_succ 10 2 s2_107 [s3_6, s3_471, s3_372, s3_352, s3_361, s3_343, s3_345] (by decide) s2_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s3_6_safe
  · subst z; exact s3_471_safe
  · subst z; exact s3_372_safe
  · subst z; exact s3_352_safe
  · subst z; exact s3_361_safe
  · subst z; exact s3_343_safe
  · subst z; exact s3_345_safe
def s2_108 : State := ⟨[3,4,64,131], 3062541302288446171188818210963918487838, 1, 0, 1, 0⟩
theorem s2_108_edges : next config 2 s2_108 = [s3_13, s3_473, s3_373, s3_353, s3_362, s3_347] := by decide
theorem s2_108_safe : Safe 11 2 s2_108 := by
  apply safe_succ 10 2 s2_108 [s3_13, s3_473, s3_373, s3_353, s3_362, s3_347] (by decide) s2_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_13_safe
  · subst z; exact s3_473_safe
  · subst z; exact s3_373_safe
  · subst z; exact s3_353_safe
  · subst z; exact s3_362_safe
  · subst z; exact s3_347_safe
def s2_109 : State := ⟨[3,4,64,132], 5784800237655953878895815070418064179486, 1, 0, 1, 0⟩
theorem s2_109_edges : next config 2 s2_109 = [s3_14, s3_474, s3_374, s3_354, s3_363, s3_339] := by decide
theorem s2_109_safe : Safe 11 2 s2_109 := by
  apply safe_succ 10 2 s2_109 [s3_14, s3_474, s3_374, s3_354, s3_363, s3_339] (by decide) s2_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_14_safe
  · subst z; exact s3_474_safe
  · subst z; exact s3_374_safe
  · subst z; exact s3_354_safe
  · subst z; exact s3_363_safe
  · subst z; exact s3_339_safe
def s2_110 : State := ⟨[3,4,64,136], 87452568298681185110105720854042434928926, 1, 0, 1, 0⟩
theorem s2_110_edges : next config 2 s2_110 = [s3_20, s3_476, s3_383, s3_375, s3_355, s3_364, s3_340] := by decide
theorem s2_110_safe : Safe 11 2 s2_110 := by
  apply safe_succ 10 2 s2_110 [s3_20, s3_476, s3_383, s3_375, s3_355, s3_364, s3_340] (by decide) s2_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s3_20_safe
  · subst z; exact s3_476_safe
  · subst z; exact s3_383_safe
  · subst z; exact s3_375_safe
  · subst z; exact s3_355_safe
  · subst z; exact s3_364_safe
  · subst z; exact s3_340_safe
def s2_111 : State := ⟨[3,4,64,144], 22301085480897544079999200093999871278776606, 1, 0, 1, 0⟩
theorem s2_111_edges : next config 2 s2_111 = [s3_30, s3_478, s3_377, s3_356, s3_365, s3_344, s3_349] := by decide
theorem s2_111_safe : Safe 11 2 s2_111 := by
  apply safe_succ 10 2 s2_111 [s3_30, s3_478, s3_377, s3_356, s3_365, s3_344, s3_349] (by decide) s2_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s3_30_safe
  · subst z; exact s3_478_safe
  · subst z; exact s3_377_safe
  · subst z; exact s3_356_safe
  · subst z; exact s3_365_safe
  · subst z; exact s3_344_safe
  · subst z; exact s3_349_safe
def s2_112 : State := ⟨[3,4,64,160], 1461501637671185285124623296198104371165705339166, 1, 0, 1, 0⟩
theorem s2_112_edges : next config 2 s2_112 = [s3_550, s3_39, s3_480, s3_378, s3_357, s3_366, s3_348, s3_346, s3_350] := by decide
theorem s2_112_safe : Safe 11 2 s2_112 := by
  apply safe_succ 10 2 s2_112 [s3_550, s3_39, s3_480, s3_378, s3_357, s3_366, s3_348, s3_346, s3_350] (by decide) s2_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_550_safe
  · subst z; exact s3_39_safe
  · subst z; exact s3_480_safe
  · subst z; exact s3_378_safe
  · subst z; exact s3_357_safe
  · subst z; exact s3_366_safe
  · subst z; exact s3_348_safe
  · subst z; exact s3_346_safe
  · subst z; exact s3_350_safe
def s2_113 : State := ⟨[3,4,64,192], 6277101735386680764176071790128604879584176795973807309086, 1, 0, 1, 0⟩
theorem s2_113_edges : next config 2 s2_113 = [s3_55, s3_485, s3_379, s3_358, s3_367] := by decide
theorem s2_113_safe : Safe 11 2 s2_113 := by
  apply safe_succ 10 2 s2_113 [s3_55, s3_485, s3_379, s3_358, s3_367] (by decide) s2_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_55_safe
  · subst z; exact s3_485_safe
  · subst z; exact s3_379_safe
  · subst z; exact s3_358_safe
  · subst z; exact s3_367_safe
def s2_114 : State := ⟨[3,4,67,128], 340282366920938463629395304099449209118, 1, 0, 0, 0⟩
theorem s2_114_edges : next config 2 s2_114 = [s3_95, s3_487, s3_380, s3_353, s3_354, s3_359, s3_352, s3_355, s3_356, s3_357] := by decide
theorem s2_114_safe : Safe 11 2 s2_114 := by
  apply safe_succ 10 2 s2_114 [s3_95, s3_487, s3_380, s3_353, s3_354, s3_359, s3_352, s3_355, s3_356, s3_357] (by decide) s2_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_95_safe
  · subst z; exact s3_487_safe
  · subst z; exact s3_380_safe
  · subst z; exact s3_353_safe
  · subst z; exact s3_354_safe
  · subst z; exact s3_359_safe
  · subst z; exact s3_352_safe
  · subst z; exact s3_355_safe
  · subst z; exact s3_356_safe
  · subst z; exact s3_357_safe
def s2_115 : State := ⟨[3,4,96,128], 340282367000166625996085689103316746526, 1, 0, 0, 0⟩
theorem s2_115_edges : next config 2 s2_115 = [s3_145, s3_488, s3_382, s3_381, s3_369, s3_370, s3_362, s3_363, s3_368, s3_361, s3_364, s3_365, s3_366] := by decide
theorem s2_115_safe : Safe 11 2 s2_115 := by
  apply safe_succ 10 2 s2_115 [s3_145, s3_488, s3_382, s3_381, s3_369, s3_370, s3_362, s3_363, s3_368, s3_361, s3_364, s3_365, s3_366] (by decide) s2_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_145_safe
  · subst z; exact s3_488_safe
  · subst z; exact s3_382_safe
  · subst z; exact s3_381_safe
  · subst z; exact s3_369_safe
  · subst z; exact s3_370_safe
  · subst z; exact s3_362_safe
  · subst z; exact s3_363_safe
  · subst z; exact s3_368_safe
  · subst z; exact s3_361_safe
  · subst z; exact s3_364_safe
  · subst z; exact s3_365_safe
  · subst z; exact s3_366_safe
def s2_116 : State := ⟨[3,12,64,128], 340282366920938463481821351509772800286, 3, 0, 0, 0⟩
theorem s2_116_edges : next config 2 s2_116 = [s3_236, s3_490, s3_338, s3_380, s3_381, s3_373, s3_376, s3_379, s3_372, s3_375, s3_377, s3_378] := by decide
theorem s2_116_safe : Safe 11 2 s2_116 := by
  apply safe_succ 10 2 s2_116 [s3_236, s3_490, s3_338, s3_380, s3_381, s3_373, s3_376, s3_379, s3_372, s3_375, s3_377, s3_378] (by decide) s2_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_236_safe
  · subst z; exact s3_490_safe
  · subst z; exact s3_338_safe
  · subst z; exact s3_380_safe
  · subst z; exact s3_381_safe
  · subst z; exact s3_373_safe
  · subst z; exact s3_376_safe
  · subst z; exact s3_379_safe
  · subst z; exact s3_372_safe
  · subst z; exact s3_375_safe
  · subst z; exact s3_377_safe
  · subst z; exact s3_378_safe
def s2_117 : State := ⟨[9,4,64,129], 1020847100762815390408570566373309219606, 1, 0, 1, 0⟩
theorem s2_117_edges : next config 2 s2_117 = [s3_1, s3_388, s3_384] := by decide
theorem s2_117_safe : Safe 11 2 s2_117 := by
  apply safe_succ 10 2 s2_117 [s3_1, s3_388, s3_384] (by decide) s2_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_1_safe
  · subst z; exact s3_388_safe
  · subst z; exact s3_384_safe
def s2_118 : State := ⟨[9,4,64,130], 1701411834604692317335319781236845642518, 1, 0, 1, 0⟩
theorem s2_118_edges : next config 2 s2_118 = [s3_7, s3_389, s3_386] := by decide
theorem s2_118_safe : Safe 11 2 s2_118 := by
  apply safe_succ 10 2 s2_118 [s3_7, s3_389, s3_386] (by decide) s2_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_7_safe
  · subst z; exact s3_389_safe
  · subst z; exact s3_386_safe
def s2_119 : State := ⟨[9,4,64,132], 5784800237655953878895815070418064179990, 1, 0, 1, 0⟩
theorem s2_119_edges : next config 2 s2_119 = [s3_15, s3_390] := by decide
theorem s2_119_safe : Safe 11 2 s2_119 := by
  apply safe_succ 10 2 s2_119 [s3_15, s3_390] (by decide) s2_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_15_safe
  · subst z; exact s3_390_safe
def s2_120 : State := ⟨[9,4,64,136], 87452568298681185110105720854042434929430, 1, 0, 1, 0⟩
theorem s2_120_edges : next config 2 s2_120 = [s3_21, s3_391] := by decide
theorem s2_120_safe : Safe 11 2 s2_120 := by
  apply safe_succ 10 2 s2_120 [s3_21, s3_391] (by decide) s2_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_21_safe
  · subst z; exact s3_391_safe
def s2_121 : State := ⟨[9,4,64,137], 174564854230441431756729620356575097062166, 1, 0, 1, 0⟩
theorem s2_121_edges : next config 2 s2_121 = [s3_28, s3_392] := by decide
theorem s2_121_safe : Safe 11 2 s2_121 := by
  apply safe_succ 10 2 s2_121 [s3_28, s3_392] (by decide) s2_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_28_safe
  · subst z; exact s3_392_safe
def s2_122 : State := ⟨[9,4,64,144], 22301085480897544079999200093999871278777110, 1, 0, 1, 0⟩
theorem s2_122_edges : next config 2 s2_122 = [s3_31, s3_393] := by decide
theorem s2_122_safe : Safe 11 2 s2_122 := by
  apply safe_succ 10 2 s2_122 [s3_31, s3_393] (by decide) s2_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_31_safe
  · subst z; exact s3_393_safe
def s2_123 : State := ⟨[9,4,64,160], 1461501637671185285124623296198104371165705339670, 1, 0, 1, 0⟩
theorem s2_123_edges : next config 2 s2_123 = [s3_40, s3_394, s3_387] := by decide
theorem s2_123_safe : Safe 11 2 s2_123 := by
  apply safe_succ 10 2 s2_123 [s3_40, s3_394, s3_387] (by decide) s2_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_40_safe
  · subst z; exact s3_394_safe
  · subst z; exact s3_387_safe
def s2_124 : State := ⟨[9,4,64,192], 6277101735386680764176071790128604879584176795973807309590, 1, 0, 1, 0⟩
theorem s2_124_edges : next config 2 s2_124 = [s3_56, s3_395] := by decide
theorem s2_124_safe : Safe 11 2 s2_124 := by
  apply safe_succ 10 2 s2_124 [s3_56, s3_395] (by decide) s2_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_56_safe
  · subst z; exact s3_395_safe
def s2_125 : State := ⟨[9,4,96,128], 340282367000166625996085689103316747030, 1, 0, 0, 0⟩
theorem s2_125_edges : next config 2 s2_125 = [s3_146, s3_397, s3_392, s3_390, s3_396, s3_389, s3_391, s3_393, s3_394] := by decide
theorem s2_125_safe : Safe 11 2 s2_125 := by
  apply safe_succ 10 2 s2_125 [s3_146, s3_397, s3_392, s3_390, s3_396, s3_389, s3_391, s3_393, s3_394] (by decide) s2_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_146_safe
  · subst z; exact s3_397_safe
  · subst z; exact s3_392_safe
  · subst z; exact s3_390_safe
  · subst z; exact s3_396_safe
  · subst z; exact s3_389_safe
  · subst z; exact s3_391_safe
  · subst z; exact s3_393_safe
  · subst z; exact s3_394_safe
def s2_126 : State := ⟨[17,4,64,145], 44601830679428167221534918366648232784888086, 1, 0, 1, 0⟩
theorem s2_126_edges : next config 2 s2_126 = [s3_439, s3_529, s3_440, s3_36, s3_494, s3_427, s3_436, s3_421, s3_411, s3_409, s3_420, s3_406, s3_410, s3_414] := by decide
theorem s2_126_safe : Safe 11 2 s2_126 := by
  apply safe_succ 10 2 s2_126 [s3_439, s3_529, s3_440, s3_36, s3_494, s3_427, s3_436, s3_421, s3_411, s3_409, s3_420, s3_406, s3_410, s3_414] (by decide) s2_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_439_safe
  · subst z; exact s3_529_safe
  · subst z; exact s3_440_safe
  · subst z; exact s3_36_safe
  · subst z; exact s3_494_safe
  · subst z; exact s3_427_safe
  · subst z; exact s3_436_safe
  · subst z; exact s3_421_safe
  · subst z; exact s3_411_safe
  · subst z; exact s3_409_safe
  · subst z; exact s3_420_safe
  · subst z; exact s3_406_safe
  · subst z; exact s3_410_safe
  · subst z; exact s3_414_safe
def s2_127 : State := ⟨[17,4,65,128], 340282366920938463518714839657192030486, 1, 0, 0, 0⟩
theorem s2_127_edges : next config 2 s2_127 = [s3_428, s3_422, s3_407, s3_405] := by decide
theorem s2_127_safe : Safe 11 2 s2_127 := by
  apply safe_succ 10 2 s2_127 [s3_428, s3_422, s3_407, s3_405] (by decide) s2_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_428_safe
  · subst z; exact s3_422_safe
  · subst z; exact s3_407_safe
  · subst z; exact s3_405_safe
def s2_128 : State := ⟨[17,4,66,128], 340282366920938463555608327804611133718, 1, 0, 0, 0⟩
theorem s2_128_edges : next config 2 s2_128 = [s3_429, s3_423, s3_412, s3_406] := by decide
theorem s2_128_safe : Safe 11 2 s2_128 := by
  apply safe_succ 10 2 s2_128 [s3_429, s3_423, s3_412, s3_406] (by decide) s2_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_429_safe
  · subst z; exact s3_423_safe
  · subst z; exact s3_412_safe
  · subst z; exact s3_406_safe
def s2_129 : State := ⟨[17,4,68,128], 340282366920938463776969256689125753110, 1, 0, 0, 0⟩
theorem s2_129_edges : next config 2 s2_129 = [s3_430, s3_409] := by decide
theorem s2_129_safe : Safe 11 2 s2_129 := by
  apply safe_succ 10 2 s2_129 [s3_430, s3_409] (by decide) s2_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_430_safe
  · subst z; exact s3_409_safe
def s2_130 : State := ⟨[17,4,80,128], 340282366920939672407640966138947633430, 1, 0, 0, 0⟩
theorem s2_130_edges : next config 2 s2_130 = [s3_431, s3_424, s3_413, s3_410] := by decide
theorem s2_130_safe : Safe 11 2 s2_130 := by
  apply safe_succ 10 2 s2_130 [s3_431, s3_424, s3_413, s3_410] (by decide) s2_130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_431_safe
  · subst z; exact s3_424_safe
  · subst z; exact s3_413_safe
  · subst z; exact s3_410_safe
def s2_131 : State := ⟨[17,4,81,128], 340282366920940881333460580768122339606, 1, 0, 0, 0⟩
theorem s2_131_edges : next config 2 s2_131 = [s3_432, s3_425, s3_411] := by decide
theorem s2_131_safe : Safe 11 2 s2_131 := by
  apply safe_succ 10 2 s2_131 [s3_432, s3_425, s3_411] (by decide) s2_131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_432_safe
  · subst z; exact s3_425_safe
  · subst z; exact s3_411_safe
def s2_132 : State := ⟨[17,4,96,128], 340282367000166625996085689103316877590, 1, 0, 0, 0⟩
theorem s2_132_edges : next config 2 s2_132 = [s3_433, s3_438, s3_426, s3_419, s3_416, s3_417, s3_418, s3_414] := by decide
theorem s2_132_safe : Safe 11 2 s2_132 := by
  apply safe_succ 10 2 s2_132 [s3_433, s3_438, s3_426, s3_419, s3_416, s3_417, s3_418, s3_414] (by decide) s2_132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_433_safe
  · subst z; exact s3_438_safe
  · subst z; exact s3_426_safe
  · subst z; exact s3_419_safe
  · subst z; exact s3_416_safe
  · subst z; exact s3_417_safe
  · subst z; exact s3_418_safe
  · subst z; exact s3_414_safe
def s2_133 : State := ⟨[17,12,64,128], 340282366920938463481821351509772931350, 3, 0, 0, 0⟩
theorem s2_133_edges : next config 2 s2_133 = [s3_400, s3_425, s3_423, s3_424, s3_426, s3_421] := by decide
theorem s2_133_safe : Safe 11 2 s2_133 := by
  apply safe_succ 10 2 s2_133 [s3_400, s3_425, s3_423, s3_424, s3_426, s3_421] (by decide) s2_133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_400_safe
  · subst z; exact s3_425_safe
  · subst z; exact s3_423_safe
  · subst z; exact s3_424_safe
  · subst z; exact s3_426_safe
  · subst z; exact s3_421_safe
def s2_134 : State := ⟨[17,21,64,128], 340282366920938463481821351509775024406, 3, 0, 0, 0⟩
theorem s2_134_edges : next config 2 s2_134 = [s3_401, s3_434, s3_435, s3_432, s3_429, s3_431, s3_433, s3_427] := by decide
theorem s2_134_safe : Safe 11 2 s2_134 := by
  apply safe_succ 10 2 s2_134 [s3_401, s3_434, s3_435, s3_432, s3_429, s3_431, s3_433, s3_427] (by decide) s2_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_401_safe
  · subst z; exact s3_434_safe
  · subst z; exact s3_435_safe
  · subst z; exact s3_432_safe
  · subst z; exact s3_429_safe
  · subst z; exact s3_431_safe
  · subst z; exact s3_433_safe
  · subst z; exact s3_427_safe
def s2_135 : State := ⟨[17,68,64,128], 340282366920938463776969256689125753110, 3, 0, 0, 0⟩
theorem s2_135_edges : next config 2 s2_135 = [s3_404, s3_437, s3_436] := by decide
theorem s2_135_safe : Safe 11 2 s2_135 := by
  apply safe_succ 10 2 s2_135 [s3_404, s3_437, s3_436] (by decide) s2_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_404_safe
  · subst z; exact s3_437_safe
  · subst z; exact s3_436_safe
def s2_136 : State := ⟨[33,4,64,129], 1020847100762815390408570566381899153686, 1, 0, 1, 0⟩
theorem s2_136_edges : next config 2 s2_136 = [s3_470, s3_3, s3_458, s3_448, s3_444] := by decide
theorem s2_136_safe : Safe 11 2 s2_136 := by
  apply safe_succ 10 2 s2_136 [s3_470, s3_3, s3_458, s3_448, s3_444] (by decide) s2_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_470_safe
  · subst z; exact s3_3_safe
  · subst z; exact s3_458_safe
  · subst z; exact s3_448_safe
  · subst z; exact s3_444_safe
def s2_137 : State := ⟨[33,4,64,130], 1701411834604692317335319781245435576598, 1, 0, 1, 0⟩
theorem s2_137_edges : next config 2 s2_137 = [s3_548, s3_472, s3_9, s3_459, s3_449, s3_446] := by decide
theorem s2_137_safe : Safe 11 2 s2_137 := by
  apply safe_succ 10 2 s2_137 [s3_548, s3_472, s3_9, s3_459, s3_449, s3_446] (by decide) s2_137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_548_safe
  · subst z; exact s3_472_safe
  · subst z; exact s3_9_safe
  · subst z; exact s3_459_safe
  · subst z; exact s3_449_safe
  · subst z; exact s3_446_safe
def s2_138 : State := ⟨[33,4,64,132], 5784800237655953878895815070426654114070, 1, 0, 1, 0⟩
theorem s2_138_edges : next config 2 s2_138 = [s3_475, s3_17, s3_460, s3_450, s3_442] := by decide
theorem s2_138_safe : Safe 11 2 s2_138 := by
  apply safe_succ 10 2 s2_138 [s3_475, s3_17, s3_460, s3_450, s3_442] (by decide) s2_138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_475_safe
  · subst z; exact s3_17_safe
  · subst z; exact s3_460_safe
  · subst z; exact s3_450_safe
  · subst z; exact s3_442_safe
def s2_139 : State := ⟨[33,4,64,136], 87452568298681185110105720854051024863510, 1, 0, 1, 0⟩
theorem s2_139_edges : next config 2 s2_139 = [s3_477, s3_23, s3_468, s3_461, s3_451, s3_443] := by decide
theorem s2_139_safe : Safe 11 2 s2_139 := by
  apply safe_succ 10 2 s2_139 [s3_477, s3_23, s3_468, s3_461, s3_451, s3_443] (by decide) s2_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_477_safe
  · subst z; exact s3_23_safe
  · subst z; exact s3_468_safe
  · subst z; exact s3_461_safe
  · subst z; exact s3_451_safe
  · subst z; exact s3_443_safe
def s2_140 : State := ⟨[33,4,64,144], 22301085480897544079999200093999879868711190, 1, 0, 1, 0⟩
theorem s2_140_edges : next config 2 s2_140 = [s3_479, s3_33, s3_463, s3_452] := by decide
theorem s2_140_safe : Safe 11 2 s2_140 := by
  apply safe_succ 10 2 s2_140 [s3_479, s3_33, s3_463, s3_452] (by decide) s2_140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_479_safe
  · subst z; exact s3_33_safe
  · subst z; exact s3_463_safe
  · subst z; exact s3_452_safe
def s2_141 : State := ⟨[33,4,64,160], 1461501637671185285124623296198104371174295273750, 1, 0, 1, 0⟩
theorem s2_141_edges : next config 2 s2_141 = [s3_481, s3_42, s3_464, s3_453] := by decide
theorem s2_141_safe : Safe 11 2 s2_141 := by
  apply safe_succ 10 2 s2_141 [s3_481, s3_42, s3_464, s3_453] (by decide) s2_141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_481_safe
  · subst z; exact s3_42_safe
  · subst z; exact s3_464_safe
  · subst z; exact s3_453_safe
def s2_142 : State := ⟨[33,4,64,161], 2923003275002088203328308128914387390830227816726, 1, 0, 1, 0⟩
theorem s2_142_edges : next config 2 s2_142 = [s3_482, s3_46, s3_465, s3_454, s3_447] := by decide
theorem s2_142_safe : Safe 11 2 s2_142 := by
  apply safe_succ 10 2 s2_142 [s3_482, s3_46, s3_465, s3_454, s3_447] (by decide) s2_142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_482_safe
  · subst z; exact s3_46_safe
  · subst z; exact s3_465_safe
  · subst z; exact s3_454_safe
  · subst z; exact s3_447_safe
def s2_143 : State := ⟨[33,4,64,192], 6277101735386680764176071790128604879584176795982397243670, 1, 0, 1, 0⟩
theorem s2_143_edges : next config 2 s2_143 = [s3_486, s3_58, s3_466, s3_455] := by decide
theorem s2_143_safe : Safe 11 2 s2_143 := by
  apply safe_succ 10 2 s2_143 [s3_486, s3_58, s3_466, s3_455] (by decide) s2_143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_486_safe
  · subst z; exact s3_58_safe
  · subst z; exact s3_466_safe
  · subst z; exact s3_455_safe
def s2_144 : State := ⟨[33,4,96,128], 340282367000166625996085689111906681110, 1, 0, 0, 0⟩
theorem s2_144_edges : next config 2 s2_144 = [s3_489, s3_148, s3_467, s3_457, s3_454, s3_450, s3_456, s3_449, s3_451, s3_452, s3_453] := by decide
theorem s2_144_safe : Safe 11 2 s2_144 := by
  apply safe_succ 10 2 s2_144 [s3_489, s3_148, s3_467, s3_457, s3_454, s3_450, s3_456, s3_449, s3_451, s3_452, s3_453] (by decide) s2_144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_489_safe
  · subst z; exact s3_148_safe
  · subst z; exact s3_467_safe
  · subst z; exact s3_457_safe
  · subst z; exact s3_454_safe
  · subst z; exact s3_450_safe
  · subst z; exact s3_456_safe
  · subst z; exact s3_449_safe
  · subst z; exact s3_451_safe
  · subst z; exact s3_452_safe
  · subst z; exact s3_453_safe
def s2_145 : State := ⟨[33,12,64,128], 340282366920938463481821351518362734870, 3, 0, 0, 0⟩
theorem s2_145_edges : next config 2 s2_145 = [s3_491, s3_237, s3_441, s3_467, s3_465, s3_462, s3_466, s3_459, s3_461, s3_463, s3_464] := by decide
theorem s2_145_safe : Safe 11 2 s2_145 := by
  apply safe_succ 10 2 s2_145 [s3_491, s3_237, s3_441, s3_467, s3_465, s3_462, s3_466, s3_459, s3_461, s3_463, s3_464] (by decide) s2_145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_491_safe
  · subst z; exact s3_237_safe
  · subst z; exact s3_441_safe
  · subst z; exact s3_467_safe
  · subst z; exact s3_465_safe
  · subst z; exact s3_462_safe
  · subst z; exact s3_466_safe
  · subst z; exact s3_459_safe
  · subst z; exact s3_461_safe
  · subst z; exact s3_463_safe
  · subst z; exact s3_464_safe
def s2_146 : State := ⟨[35,4,64,128], 340282366920938463481821351544132534558, 1, 0, 0, 0⟩
theorem s2_146_edges : next config 2 s2_146 = [s3_492, s3_490, s3_488, s3_483, s3_474, s3_485, s3_471, s3_476, s3_478, s3_480] := by decide
theorem s2_146_safe : Safe 11 2 s2_146 := by
  apply safe_succ 10 2 s2_146 [s3_492, s3_490, s3_488, s3_483, s3_474, s3_485, s3_471, s3_476, s3_478, s3_480] (by decide) s2_146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_492_safe
  · subst z; exact s3_490_safe
  · subst z; exact s3_488_safe
  · subst z; exact s3_483_safe
  · subst z; exact s3_474_safe
  · subst z; exact s3_485_safe
  · subst z; exact s3_471_safe
  · subst z; exact s3_476_safe
  · subst z; exact s3_478_safe
  · subst z; exact s3_480_safe
def s2_147 : State := ⟨[35,4,64,128], 340282366920938463481821351552722469142, 1, 0, 0, 0⟩
theorem s2_147_edges : next config 2 s2_147 = [s3_493, s3_491, s3_489, s3_484, s3_475, s3_486, s3_472, s3_477, s3_479, s3_481] := by decide
theorem s2_147_safe : Safe 11 2 s2_147 := by
  apply safe_succ 10 2 s2_147 [s3_493, s3_491, s3_489, s3_484, s3_475, s3_486, s3_472, s3_477, s3_479, s3_481] (by decide) s2_147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_493_safe
  · subst z; exact s3_491_safe
  · subst z; exact s3_489_safe
  · subst z; exact s3_484_safe
  · subst z; exact s3_475_safe
  · subst z; exact s3_486_safe
  · subst z; exact s3_472_safe
  · subst z; exact s3_477_safe
  · subst z; exact s3_479_safe
  · subst z; exact s3_481_safe
def s2_148 : State := ⟨[65,4,64,129], 1020847100762815390445464054520728322326, 1, 0, 1, 0⟩
theorem s2_148_edges : next config 2 s2_148 = [s3_4, s3_517, s3_506, s3_498] := by decide
theorem s2_148_safe : Safe 11 2 s2_148 := by
  apply safe_succ 10 2 s2_148 [s3_4, s3_517, s3_506, s3_498] (by decide) s2_148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_4_safe
  · subst z; exact s3_517_safe
  · subst z; exact s3_506_safe
  · subst z; exact s3_498_safe
def s2_149 : State := ⟨[65,4,64,130], 1701411834604692317372213269384264745238, 1, 0, 1, 0⟩
theorem s2_149_edges : next config 2 s2_149 = [s3_10, s3_518, s3_507, s3_500, s3_502] := by decide
theorem s2_149_safe : Safe 11 2 s2_149 := by
  apply safe_succ 10 2 s2_149 [s3_10, s3_518, s3_507, s3_500, s3_502] (by decide) s2_149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_10_safe
  · subst z; exact s3_518_safe
  · subst z; exact s3_507_safe
  · subst z; exact s3_500_safe
  · subst z; exact s3_502_safe
def s2_150 : State := ⟨[65,4,64,132], 5784800237655953878932708558565483282710, 1, 0, 1, 0⟩
theorem s2_150_edges : next config 2 s2_150 = [s3_18, s3_519, s3_508, s3_496] := by decide
theorem s2_150_safe : Safe 11 2 s2_150 := by
  apply safe_succ 10 2 s2_150 [s3_18, s3_519, s3_508, s3_496] (by decide) s2_150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_18_safe
  · subst z; exact s3_519_safe
  · subst z; exact s3_508_safe
  · subst z; exact s3_496_safe
def s2_151 : State := ⟨[65,4,64,136], 87452568298681185110142614342189854032150, 1, 0, 1, 0⟩
theorem s2_151_edges : next config 2 s2_151 = [s3_24, s3_528, s3_520, s3_509, s3_497] := by decide
theorem s2_151_safe : Safe 11 2 s2_151 := by
  apply safe_succ 10 2 s2_151 [s3_24, s3_528, s3_520, s3_509, s3_497] (by decide) s2_151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_24_safe
  · subst z; exact s3_528_safe
  · subst z; exact s3_520_safe
  · subst z; exact s3_509_safe
  · subst z; exact s3_497_safe
def s2_152 : State := ⟨[65,4,64,144], 22301085480897544079999236987488018697879830, 1, 0, 1, 0⟩
theorem s2_152_edges : next config 2 s2_152 = [s3_34, s3_522, s3_510, s3_501, s3_504] := by decide
theorem s2_152_safe : Safe 11 2 s2_152 := by
  apply safe_succ 10 2 s2_152 [s3_34, s3_522, s3_510, s3_501, s3_504] (by decide) s2_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_34_safe
  · subst z; exact s3_522_safe
  · subst z; exact s3_510_safe
  · subst z; exact s3_501_safe
  · subst z; exact s3_504_safe
def s2_153 : State := ⟨[65,4,64,160], 1461501637671185285124623296234997859313124442390, 1, 0, 1, 0⟩
theorem s2_153_edges : next config 2 s2_153 = [s3_43, s3_523, s3_511, s3_503, s3_505] := by decide
theorem s2_153_safe : Safe 11 2 s2_153 := by
  apply safe_succ 10 2 s2_153 [s3_43, s3_523, s3_511, s3_503, s3_505] (by decide) s2_153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_43_safe
  · subst z; exact s3_523_safe
  · subst z; exact s3_511_safe
  · subst z; exact s3_503_safe
  · subst z; exact s3_505_safe
def s2_154 : State := ⟨[65,4,64,192], 6277101735386680764176071790128604879621070284121226412310, 1, 0, 1, 0⟩
theorem s2_154_edges : next config 2 s2_154 = [s3_59, s3_524, s3_512] := by decide
theorem s2_154_safe : Safe 11 2 s2_154 := by
  apply safe_succ 10 2 s2_154 [s3_59, s3_524, s3_512] (by decide) s2_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_59_safe
  · subst z; exact s3_524_safe
  · subst z; exact s3_512_safe
def s2_155 : State := ⟨[65,4,64,193], 12554203470773361528011861213336271295723425728585260925206, 1, 0, 1, 0⟩
theorem s2_155_edges : next config 2 s2_155 = [s3_63, s3_525, s3_513] := by decide
theorem s2_155_safe : Safe 11 2 s2_155 := by
  apply safe_succ 10 2 s2_155 [s3_63, s3_525, s3_513] (by decide) s2_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_63_safe
  · subst z; exact s3_525_safe
  · subst z; exact s3_513_safe
def s2_156 : State := ⟨[65,4,96,128], 340282367000166626032979177250735849750, 1, 0, 0, 0⟩
theorem s2_156_edges : next config 2 s2_156 = [s3_527, s3_526, s3_515, s3_516, s3_513, s3_508, s3_514, s3_507, s3_509, s3_510, s3_511] := by decide
theorem s2_156_safe : Safe 11 2 s2_156 := by
  apply safe_succ 10 2 s2_156 [s3_527, s3_526, s3_515, s3_516, s3_513, s3_508, s3_514, s3_507, s3_509, s3_510, s3_511] (by decide) s2_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_527_safe
  · subst z; exact s3_526_safe
  · subst z; exact s3_515_safe
  · subst z; exact s3_516_safe
  · subst z; exact s3_513_safe
  · subst z; exact s3_508_safe
  · subst z; exact s3_514_safe
  · subst z; exact s3_507_safe
  · subst z; exact s3_509_safe
  · subst z; exact s3_510_safe
  · subst z; exact s3_511_safe
def s2_157 : State := ⟨[65,12,64,128], 340282366920938463518714839657191903510, 3, 0, 0, 0⟩
theorem s2_157_edges : next config 2 s2_157 = [s3_238, s3_495, s3_526, s3_525, s3_521, s3_524, s3_518, s3_520, s3_522, s3_523] := by decide
theorem s2_157_safe : Safe 11 2 s2_157 := by
  apply safe_succ 10 2 s2_157 [s3_238, s3_495, s3_526, s3_525, s3_521, s3_524, s3_518, s3_520, s3_522, s3_523] (by decide) s2_157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_238_safe
  · subst z; exact s3_495_safe
  · subst z; exact s3_526_safe
  · subst z; exact s3_525_safe
  · subst z; exact s3_521_safe
  · subst z; exact s3_524_safe
  · subst z; exact s3_518_safe
  · subst z; exact s3_520_safe
  · subst z; exact s3_522_safe
  · subst z; exact s3_523_safe
def s2_158 : State := ⟨[97,4,96,128], 340282367158622951024614364290404647190, 1, 0, 0, 0⟩
theorem s2_158_edges : next config 2 s2_158 = [s3_151, s3_540, s3_539, s3_538, s3_532, s3_537, s3_531, s3_533, s3_534, s3_535] := by decide
theorem s2_158_safe : Safe 11 2 s2_158 := by
  apply safe_succ 10 2 s2_158 [s3_151, s3_540, s3_539, s3_538, s3_532, s3_537, s3_531, s3_533, s3_534, s3_535] (by decide) s2_158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_151_safe
  · subst z; exact s3_540_safe
  · subst z; exact s3_539_safe
  · subst z; exact s3_538_safe
  · subst z; exact s3_532_safe
  · subst z; exact s3_537_safe
  · subst z; exact s3_531_safe
  · subst z; exact s3_533_safe
  · subst z; exact s3_534_safe
  · subst z; exact s3_535_safe
def s2_159 : State := ⟨[131,4,64,130], 4423670769972200025042316640690991333654, 1, 0, 1, 0⟩
theorem s2_159_edges : next config 2 s2_159 = [s3_12, s3_549, s3_544, s3_543, s3_541, s3_542] := by decide
theorem s2_159_safe : Safe 11 2 s2_159 := by
  apply safe_succ 10 2 s2_159 [s3_12, s3_549, s3_544, s3_543, s3_541, s3_542] (by decide) s2_159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_12_safe
  · subst z; exact s3_549_safe
  · subst z; exact s3_544_safe
  · subst z; exact s3_543_safe
  · subst z; exact s3_541_safe
  · subst z; exact s3_542_safe
def s2_160 : State := ⟨[137,4,64,136], 261677140162201678403353519859107759194390, 1, 0, 1, 0⟩
theorem s2_160_edges : next config 2 s2_160 = [s3_26, s3_545] := by decide
theorem s2_160_safe : Safe 11 2 s2_160 := by
  apply safe_succ 10 2 s2_160 [s3_26, s3_545] (by decide) s2_160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_26_safe
  · subst z; exact s3_545_safe
def s2_161 : State := ⟨[161,4,64,160], 4384504912332991121531992961630670410477570425110, 1, 0, 1, 0⟩
theorem s2_161_edges : next config 2 s2_161 = [s3_45, s3_551, s3_547, s3_546] := by decide
theorem s2_161_safe : Safe 11 2 s2_161 := by
  apply safe_succ 10 2 s2_161 [s3_45, s3_551, s3_547, s3_546] (by decide) s2_161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_45_safe
  · subst z; exact s3_551_safe
  · subst z; exact s3_547_safe
  · subst z; exact s3_546_safe
def s2_162 : State := ⟨[193,4,64,192], 18831305206160042291847650636543937711788887684901876334870, 1, 0, 1, 0⟩
theorem s2_162_edges : next config 2 s2_162 = [s3_61, s3_555, s3_554] := by decide
theorem s2_162_safe : Safe 11 2 s2_162 := by
  apply safe_succ 10 2 s2_162 [s3_61, s3_555, s3_554] (by decide) s2_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_61_safe
  · subst z; exact s3_555_safe
  · subst z; exact s3_554_safe
end HGP13.SectorGraph234
