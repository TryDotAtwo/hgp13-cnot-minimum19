import Graph234Layer2
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s1_0 : State := ⟨[1,4,64,129], 1020847100762815390408570566373309219094, 0, 0, 1, 0⟩
theorem s1_0_edges : next config 1 s1_0 = [s2_148, s2_106, s2_117, s2_136, s2_94, s2_82, s2_30, s2_48, s2_78, s2_38, s2_56, s2_66, s2_22, s2_6, s2_8, s2_12, s2_16] := by decide
theorem s1_0_safe : Safe 12 1 s1_0 := by
  apply safe_succ 11 1 s1_0 [s2_148, s2_106, s2_117, s2_136, s2_94, s2_82, s2_30, s2_48, s2_78, s2_38, s2_56, s2_66, s2_22, s2_6, s2_8, s2_12, s2_16] (by decide) s1_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_148_safe
  · subst z; exact s2_106_safe
  · subst z; exact s2_117_safe
  · subst z; exact s2_136_safe
  · subst z; exact s2_94_safe
  · subst z; exact s2_82_safe
  · subst z; exact s2_30_safe
  · subst z; exact s2_48_safe
  · subst z; exact s2_78_safe
  · subst z; exact s2_38_safe
  · subst z; exact s2_56_safe
  · subst z; exact s2_66_safe
  · subst z; exact s2_22_safe
  · subst z; exact s2_6_safe
  · subst z; exact s2_8_safe
  · subst z; exact s2_12_safe
  · subst z; exact s2_16_safe
def s1_1 : State := ⟨[1,4,64,130], 1701411834604692317335319781236845642006, 0, 0, 1, 0⟩
theorem s1_1_edges : next config 1 s1_1 = [s2_149, s2_159, s2_107, s2_118, s2_137, s2_95, s2_83, s2_31, s2_49, s2_79, s2_39, s2_57, s2_67, s2_7, s2_24, s2_14, s2_18] := by decide
theorem s1_1_safe : Safe 12 1 s1_1 := by
  apply safe_succ 11 1 s1_1 [s2_149, s2_159, s2_107, s2_118, s2_137, s2_95, s2_83, s2_31, s2_49, s2_79, s2_39, s2_57, s2_67, s2_7, s2_24, s2_14, s2_18] (by decide) s1_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_149_safe
  · subst z; exact s2_159_safe
  · subst z; exact s2_107_safe
  · subst z; exact s2_118_safe
  · subst z; exact s2_137_safe
  · subst z; exact s2_95_safe
  · subst z; exact s2_83_safe
  · subst z; exact s2_31_safe
  · subst z; exact s2_49_safe
  · subst z; exact s2_79_safe
  · subst z; exact s2_39_safe
  · subst z; exact s2_57_safe
  · subst z; exact s2_67_safe
  · subst z; exact s2_7_safe
  · subst z; exact s2_24_safe
  · subst z; exact s2_14_safe
  · subst z; exact s2_18_safe
def s1_2 : State := ⟨[1,4,64,132], 5784800237655953878895815070418064179478, 0, 0, 1, 0⟩
theorem s1_2_edges : next config 1 s1_2 = [s2_150, s2_109, s2_119, s2_138, s2_96, s2_84, s2_32, s2_50, s2_80, s2_40, s2_58, s2_68, s2_26, s2_10] := by decide
theorem s1_2_safe : Safe 12 1 s1_2 := by
  apply safe_succ 11 1 s1_2 [s2_150, s2_109, s2_119, s2_138, s2_96, s2_84, s2_32, s2_50, s2_80, s2_40, s2_58, s2_68, s2_26, s2_10] (by decide) s1_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_150_safe
  · subst z; exact s2_109_safe
  · subst z; exact s2_119_safe
  · subst z; exact s2_138_safe
  · subst z; exact s2_96_safe
  · subst z; exact s2_84_safe
  · subst z; exact s2_32_safe
  · subst z; exact s2_50_safe
  · subst z; exact s2_80_safe
  · subst z; exact s2_40_safe
  · subst z; exact s2_58_safe
  · subst z; exact s2_68_safe
  · subst z; exact s2_26_safe
  · subst z; exact s2_10_safe
def s1_3 : State := ⟨[1,4,64,136], 87452568298681185110105720854042434928918, 0, 0, 1, 0⟩
theorem s1_3_edges : next config 1 s1_3 = [s2_151, s2_160, s2_110, s2_120, s2_139, s2_97, s2_104, s2_85, s2_33, s2_51, s2_41, s2_59, s2_69, s2_9, s2_11] := by decide
theorem s1_3_safe : Safe 12 1 s1_3 := by
  apply safe_succ 11 1 s1_3 [s2_151, s2_160, s2_110, s2_120, s2_139, s2_97, s2_104, s2_85, s2_33, s2_51, s2_41, s2_59, s2_69, s2_9, s2_11] (by decide) s1_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_151_safe
  · subst z; exact s2_160_safe
  · subst z; exact s2_110_safe
  · subst z; exact s2_120_safe
  · subst z; exact s2_139_safe
  · subst z; exact s2_97_safe
  · subst z; exact s2_104_safe
  · subst z; exact s2_85_safe
  · subst z; exact s2_33_safe
  · subst z; exact s2_51_safe
  · subst z; exact s2_41_safe
  · subst z; exact s2_59_safe
  · subst z; exact s2_69_safe
  · subst z; exact s2_9_safe
  · subst z; exact s2_11_safe
def s1_4 : State := ⟨[1,4,64,144], 22301085480897544079999200093999871278776598, 0, 0, 1, 0⟩
theorem s1_4_edges : next config 1 s1_4 = [s2_152, s2_111, s2_122, s2_140, s2_98, s2_87, s2_34, s2_52, s2_81, s2_42, s2_60, s2_70, s2_13, s2_28, s2_15, s2_20] := by decide
theorem s1_4_safe : Safe 12 1 s1_4 := by
  apply safe_succ 11 1 s1_4 [s2_152, s2_111, s2_122, s2_140, s2_98, s2_87, s2_34, s2_52, s2_81, s2_42, s2_60, s2_70, s2_13, s2_28, s2_15, s2_20] (by decide) s1_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_152_safe
  · subst z; exact s2_111_safe
  · subst z; exact s2_122_safe
  · subst z; exact s2_140_safe
  · subst z; exact s2_98_safe
  · subst z; exact s2_87_safe
  · subst z; exact s2_34_safe
  · subst z; exact s2_52_safe
  · subst z; exact s2_81_safe
  · subst z; exact s2_42_safe
  · subst z; exact s2_60_safe
  · subst z; exact s2_70_safe
  · subst z; exact s2_13_safe
  · subst z; exact s2_28_safe
  · subst z; exact s2_15_safe
  · subst z; exact s2_20_safe
def s1_5 : State := ⟨[1,4,64,160], 1461501637671185285124623296198104371165705339158, 0, 0, 1, 0⟩
theorem s1_5_edges : next config 1 s1_5 = [s2_153, s2_161, s2_112, s2_123, s2_141, s2_99, s2_88, s2_35, s2_53, s2_43, s2_61, s2_71, s2_17, s2_19, s2_21] := by decide
theorem s1_5_safe : Safe 12 1 s1_5 := by
  apply safe_succ 11 1 s1_5 [s2_153, s2_161, s2_112, s2_123, s2_141, s2_99, s2_88, s2_35, s2_53, s2_43, s2_61, s2_71, s2_17, s2_19, s2_21] (by decide) s1_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_153_safe
  · subst z; exact s2_161_safe
  · subst z; exact s2_112_safe
  · subst z; exact s2_123_safe
  · subst z; exact s2_141_safe
  · subst z; exact s2_99_safe
  · subst z; exact s2_88_safe
  · subst z; exact s2_35_safe
  · subst z; exact s2_53_safe
  · subst z; exact s2_43_safe
  · subst z; exact s2_61_safe
  · subst z; exact s2_71_safe
  · subst z; exact s2_17_safe
  · subst z; exact s2_19_safe
  · subst z; exact s2_21_safe
def s1_6 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879584176795973807309078, 0, 0, 1, 0⟩
theorem s1_6_edges : next config 1 s1_6 = [s2_154, s2_162, s2_113, s2_124, s2_143, s2_100, s2_105, s2_89, s2_36, s2_54, s2_44, s2_62, s2_72, s2_23, s2_27, s2_25, s2_29] := by decide
theorem s1_6_safe : Safe 12 1 s1_6 := by
  apply safe_succ 11 1 s1_6 [s2_154, s2_162, s2_113, s2_124, s2_143, s2_100, s2_105, s2_89, s2_36, s2_54, s2_44, s2_62, s2_72, s2_23, s2_27, s2_25, s2_29] (by decide) s1_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_154_safe
  · subst z; exact s2_162_safe
  · subst z; exact s2_113_safe
  · subst z; exact s2_124_safe
  · subst z; exact s2_143_safe
  · subst z; exact s2_100_safe
  · subst z; exact s2_105_safe
  · subst z; exact s2_89_safe
  · subst z; exact s2_36_safe
  · subst z; exact s2_54_safe
  · subst z; exact s2_44_safe
  · subst z; exact s2_62_safe
  · subst z; exact s2_72_safe
  · subst z; exact s2_23_safe
  · subst z; exact s2_27_safe
  · subst z; exact s2_25_safe
  · subst z; exact s2_29_safe
def s1_7 : State := ⟨[1,4,65,128], 340282366920938463518714839657191899414, 0, 0, 0, 0⟩
theorem s1_7_edges : next config 1 s1_7 = [s2_127, s2_90, s2_46, s2_30, s2_32, s2_37, s2_31, s2_33, s2_34, s2_35] := by decide
theorem s1_7_safe : Safe 12 1 s1_7 := by
  apply safe_succ 11 1 s1_7 [s2_127, s2_90, s2_46, s2_30, s2_32, s2_37, s2_31, s2_33, s2_34, s2_35] (by decide) s1_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_127_safe
  · subst z; exact s2_90_safe
  · subst z; exact s2_46_safe
  · subst z; exact s2_30_safe
  · subst z; exact s2_32_safe
  · subst z; exact s2_37_safe
  · subst z; exact s2_31_safe
  · subst z; exact s2_33_safe
  · subst z; exact s2_34_safe
  · subst z; exact s2_35_safe
def s1_8 : State := ⟨[1,4,66,128], 340282366920938463555608327804611002646, 0, 0, 0, 0⟩
theorem s1_8_edges : next config 1 s1_8 = [s2_128, s2_91, s2_47, s2_64, s2_38, s2_40, s2_45, s2_39, s2_41, s2_42, s2_43] := by decide
theorem s1_8_safe : Safe 12 1 s1_8 := by
  apply safe_succ 11 1 s1_8 [s2_128, s2_91, s2_47, s2_64, s2_38, s2_40, s2_45, s2_39, s2_41, s2_42, s2_43] (by decide) s1_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_128_safe
  · subst z; exact s2_91_safe
  · subst z; exact s2_47_safe
  · subst z; exact s2_64_safe
  · subst z; exact s2_38_safe
  · subst z; exact s2_40_safe
  · subst z; exact s2_45_safe
  · subst z; exact s2_39_safe
  · subst z; exact s2_41_safe
  · subst z; exact s2_42_safe
  · subst z; exact s2_43_safe
def s1_9 : State := ⟨[1,4,68,128], 340282366920938463776969256689125622038, 0, 0, 0, 0⟩
theorem s1_9_edges : next config 1 s1_9 = [s2_129, s2_48, s2_50, s2_55, s2_49, s2_51, s2_52, s2_53] := by decide
theorem s1_9_safe : Safe 12 1 s1_9 := by
  apply safe_succ 11 1 s1_9 [s2_129, s2_48, s2_50, s2_55, s2_49, s2_51, s2_52, s2_53] (by decide) s1_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s2_129_safe
  · subst z; exact s2_48_safe
  · subst z; exact s2_50_safe
  · subst z; exact s2_55_safe
  · subst z; exact s2_49_safe
  · subst z; exact s2_51_safe
  · subst z; exact s2_52_safe
  · subst z; exact s2_53_safe
def s1_10 : State := ⟨[1,4,80,128], 340282366920939672407640966138947502358, 0, 0, 0, 0⟩
theorem s1_10_edges : next config 1 s1_10 = [s2_130, s2_92, s2_65, s2_56, s2_58, s2_63, s2_57, s2_59, s2_60, s2_61] := by decide
theorem s1_10_safe : Safe 12 1 s1_10 := by
  apply safe_succ 11 1 s1_10 [s2_130, s2_92, s2_65, s2_56, s2_58, s2_63, s2_57, s2_59, s2_60, s2_61] (by decide) s1_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_130_safe
  · subst z; exact s2_92_safe
  · subst z; exact s2_65_safe
  · subst z; exact s2_56_safe
  · subst z; exact s2_58_safe
  · subst z; exact s2_63_safe
  · subst z; exact s2_57_safe
  · subst z; exact s2_59_safe
  · subst z; exact s2_60_safe
  · subst z; exact s2_61_safe
def s1_11 : State := ⟨[1,4,96,128], 340282367000166625996085689103316746518, 0, 0, 0, 0⟩
theorem s1_11_edges : next config 1 s1_11 = [s2_158, s2_115, s2_125, s2_132, s2_144, s2_103, s2_93, s2_74, s2_75, s2_76, s2_77, s2_66, s2_68, s2_73, s2_67, s2_69, s2_70, s2_71] := by decide
theorem s1_11_safe : Safe 12 1 s1_11 := by
  apply safe_succ 11 1 s1_11 [s2_158, s2_115, s2_125, s2_132, s2_144, s2_103, s2_93, s2_74, s2_75, s2_76, s2_77, s2_66, s2_68, s2_73, s2_67, s2_69, s2_70, s2_71] (by decide) s1_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_158_safe
  · subst z; exact s2_115_safe
  · subst z; exact s2_125_safe
  · subst z; exact s2_132_safe
  · subst z; exact s2_144_safe
  · subst z; exact s2_103_safe
  · subst z; exact s2_93_safe
  · subst z; exact s2_74_safe
  · subst z; exact s2_75_safe
  · subst z; exact s2_76_safe
  · subst z; exact s2_77_safe
  · subst z; exact s2_66_safe
  · subst z; exact s2_68_safe
  · subst z; exact s2_73_safe
  · subst z; exact s2_67_safe
  · subst z; exact s2_69_safe
  · subst z; exact s2_70_safe
  · subst z; exact s2_71_safe
def s1_12 : State := ⟨[1,12,64,128], 340282366920938463481821351509772800278, 2, 0, 0, 0⟩
theorem s1_12_edges : next config 1 s1_12 = [s2_157, s2_116, s2_133, s2_145, s2_2, s2_90, s2_91, s2_92, s2_93, s2_82, s2_86, s2_89, s2_83, s2_85, s2_87, s2_88] := by decide
theorem s1_12_safe : Safe 12 1 s1_12 := by
  apply safe_succ 11 1 s1_12 [s2_157, s2_116, s2_133, s2_145, s2_2, s2_90, s2_91, s2_92, s2_93, s2_82, s2_86, s2_89, s2_83, s2_85, s2_87, s2_88] (by decide) s1_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_157_safe
  · subst z; exact s2_116_safe
  · subst z; exact s2_133_safe
  · subst z; exact s2_145_safe
  · subst z; exact s2_2_safe
  · subst z; exact s2_90_safe
  · subst z; exact s2_91_safe
  · subst z; exact s2_92_safe
  · subst z; exact s2_93_safe
  · subst z; exact s2_82_safe
  · subst z; exact s2_86_safe
  · subst z; exact s2_89_safe
  · subst z; exact s2_83_safe
  · subst z; exact s2_85_safe
  · subst z; exact s2_87_safe
  · subst z; exact s2_88_safe
def s1_13 : State := ⟨[1,68,64,128], 340282366920938463776969256689125622038, 2, 0, 0, 0⟩
theorem s1_13_edges : next config 1 s1_13 = [s2_135, s2_5, s2_102, s2_94, s2_101, s2_100, s2_95, s2_97, s2_98, s2_99] := by decide
theorem s1_13_safe : Safe 12 1 s1_13 := by
  apply safe_succ 11 1 s1_13 [s2_135, s2_5, s2_102, s2_94, s2_101, s2_100, s2_95, s2_97, s2_98, s2_99] (by decide) s1_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_135_safe
  · subst z; exact s2_5_safe
  · subst z; exact s2_102_safe
  · subst z; exact s2_94_safe
  · subst z; exact s2_101_safe
  · subst z; exact s2_100_safe
  · subst z; exact s2_95_safe
  · subst z; exact s2_97_safe
  · subst z; exact s2_98_safe
  · subst z; exact s2_99_safe
def s1_14 : State := ⟨[3,4,64,128], 340282366920938463481821351509772796190, 1, 0, 0, 0⟩
theorem s1_14_edges : next config 1 s1_14 = [s2_0, s2_146, s2_116, s2_114, s2_115, s2_108, s2_109, s2_113, s2_107, s2_110, s2_111, s2_112] := by decide
theorem s1_14_safe : Safe 12 1 s1_14 := by
  apply safe_succ 11 1 s1_14 [s2_0, s2_146, s2_116, s2_114, s2_115, s2_108, s2_109, s2_113, s2_107, s2_110, s2_111, s2_112] (by decide) s1_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_0_safe
  · subst z; exact s2_146_safe
  · subst z; exact s2_116_safe
  · subst z; exact s2_114_safe
  · subst z; exact s2_115_safe
  · subst z; exact s2_108_safe
  · subst z; exact s2_109_safe
  · subst z; exact s2_113_safe
  · subst z; exact s2_107_safe
  · subst z; exact s2_110_safe
  · subst z; exact s2_111_safe
  · subst z; exact s2_112_safe
def s1_15 : State := ⟨[9,4,64,128], 340282366920938463481821351509772796694, 1, 0, 0, 0⟩
theorem s1_15_edges : next config 1 s1_15 = [s2_1, s2_125, s2_121, s2_119, s2_124, s2_118, s2_120, s2_122, s2_123] := by decide
theorem s1_15_safe : Safe 12 1 s1_15 := by
  apply safe_succ 11 1 s1_15 [s2_1, s2_125, s2_121, s2_119, s2_124, s2_118, s2_120, s2_122, s2_123] (by decide) s1_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s2_1_safe
  · subst z; exact s2_125_safe
  · subst z; exact s2_121_safe
  · subst z; exact s2_119_safe
  · subst z; exact s2_124_safe
  · subst z; exact s2_118_safe
  · subst z; exact s2_120_safe
  · subst z; exact s2_122_safe
  · subst z; exact s2_123_safe
def s1_16 : State := ⟨[17,4,64,128], 340282366920938463481821351509772927254, 1, 0, 0, 0⟩
theorem s1_16_edges : next config 1 s1_16 = [s2_134, s2_135, s2_133, s2_131, s2_129, s2_128, s2_130, s2_132, s2_126] := by decide
theorem s1_16_safe : Safe 12 1 s1_16 := by
  apply safe_succ 11 1 s1_16 [s2_134, s2_135, s2_133, s2_131, s2_129, s2_128, s2_130, s2_132, s2_126] (by decide) s1_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s2_134_safe
  · subst z; exact s2_135_safe
  · subst z; exact s2_133_safe
  · subst z; exact s2_131_safe
  · subst z; exact s2_129_safe
  · subst z; exact s2_128_safe
  · subst z; exact s2_130_safe
  · subst z; exact s2_132_safe
  · subst z; exact s2_126_safe
def s1_17 : State := ⟨[33,4,64,128], 340282366920938463481821351518362730774, 1, 0, 0, 0⟩
theorem s1_17_edges : next config 1 s1_17 = [s2_147, s2_3, s2_145, s2_144, s2_142, s2_138, s2_143, s2_137, s2_139, s2_140, s2_141] := by decide
theorem s1_17_safe : Safe 12 1 s1_17 := by
  apply safe_succ 11 1 s1_17 [s2_147, s2_3, s2_145, s2_144, s2_142, s2_138, s2_143, s2_137, s2_139, s2_140, s2_141] (by decide) s1_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_147_safe
  · subst z; exact s2_3_safe
  · subst z; exact s2_145_safe
  · subst z; exact s2_144_safe
  · subst z; exact s2_142_safe
  · subst z; exact s2_138_safe
  · subst z; exact s2_143_safe
  · subst z; exact s2_137_safe
  · subst z; exact s2_139_safe
  · subst z; exact s2_140_safe
  · subst z; exact s2_141_safe
def s1_18 : State := ⟨[65,4,64,128], 340282366920938463518714839657191899414, 1, 0, 0, 0⟩
theorem s1_18_edges : next config 1 s1_18 = [s2_4, s2_157, s2_156, s2_155, s2_150, s2_154, s2_149, s2_151, s2_152, s2_153] := by decide
theorem s1_18_safe : Safe 12 1 s1_18 := by
  apply safe_succ 11 1 s1_18 [s2_4, s2_157, s2_156, s2_155, s2_150, s2_154, s2_149, s2_151, s2_152, s2_153] (by decide) s1_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_4_safe
  · subst z; exact s2_157_safe
  · subst z; exact s2_156_safe
  · subst z; exact s2_155_safe
  · subst z; exact s2_150_safe
  · subst z; exact s2_154_safe
  · subst z; exact s2_149_safe
  · subst z; exact s2_151_safe
  · subst z; exact s2_152_safe
  · subst z; exact s2_153_safe
end HGP13.SectorGraph234
