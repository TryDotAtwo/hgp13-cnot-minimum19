import Graph234Layer4
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s3_0 : State := ⟨[1,4,64,129], 1020847100762815390408570566373309219102, 1, 1, 1, 0⟩
theorem s3_0_edges : next config 3 s3_0 = [s4_412, s4_189, s4_11] := by decide
theorem s3_0_safe : Safe 10 3 s3_0 := by
  apply safe_succ 9 3 s3_0 [s4_412, s4_189, s4_11] (by decide) s3_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_412_safe
  · subst z; exact s4_189_safe
  · subst z; exact s4_11_safe
def s3_1 : State := ⟨[1,4,64,129], 1020847100762815390408570566373309219606, 1, 1, 1, 0⟩
theorem s3_1_edges : next config 3 s3_1 = [s4_190, s4_12] := by decide
theorem s3_1_safe : Safe 10 3 s3_1 := by
  apply safe_succ 9 3 s3_1 [s4_190, s4_12] (by decide) s3_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_190_safe
  · subst z; exact s4_12_safe
def s3_2 : State := ⟨[1,4,64,129], 1020847100762815390408570566373309223190, 2, 2, 1, 0⟩
theorem s3_2_edges : next config 3 s3_2 = [s4_1089, s4_701, s4_943, s4_79, s4_385, s4_90, s4_139, s4_191, s4_65, s4_3, s4_13, s4_34] := by decide
theorem s3_2_safe : Safe 10 3 s3_2 := by
  apply safe_succ 9 3 s3_2 [s4_1089, s4_701, s4_943, s4_79, s4_385, s4_90, s4_139, s4_191, s4_65, s4_3, s4_13, s4_34] (by decide) s3_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1089_safe
  · subst z; exact s4_701_safe
  · subst z; exact s4_943_safe
  · subst z; exact s4_79_safe
  · subst z; exact s4_385_safe
  · subst z; exact s4_90_safe
  · subst z; exact s4_139_safe
  · subst z; exact s4_191_safe
  · subst z; exact s4_65_safe
  · subst z; exact s4_3_safe
  · subst z; exact s4_13_safe
  · subst z; exact s4_34_safe
def s3_3 : State := ⟨[1,4,64,129], 1020847100762815390408570566381899153686, 1, 1, 1, 0⟩
theorem s3_3_edges : next config 3 s3_3 = [s4_413, s4_192, s4_14] := by decide
theorem s3_3_safe : Safe 10 3 s3_3 := by
  apply safe_succ 9 3 s3_3 [s4_413, s4_192, s4_14] (by decide) s3_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_413_safe
  · subst z; exact s4_192_safe
  · subst z; exact s4_14_safe
def s3_4 : State := ⟨[1,4,64,129], 1020847100762815390445464054520728322326, 1, 1, 1, 0⟩
theorem s3_4_edges : next config 3 s3_4 = [s4_414, s4_193, s4_15] := by decide
theorem s3_4_safe : Safe 10 3 s3_4 := by
  apply safe_succ 9 3 s3_4 [s4_414, s4_193, s4_15] (by decide) s3_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_414_safe
  · subst z; exact s4_193_safe
  · subst z; exact s4_15_safe
def s3_5 : State := ⟨[1,4,64,129], 1020847100762815390703718471552662044950, 2, 2, 1, 0⟩
theorem s3_5_edges : next config 3 s3_5 = [s4_194, s4_16] := by decide
theorem s3_5_safe : Safe 10 3 s3_5 := by
  apply safe_succ 9 3 s3_5 [s4_194, s4_16] (by decide) s3_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_194_safe
  · subst z; exact s4_16_safe
def s3_6 : State := ⟨[1,4,64,130], 1701411834604692317335319781236845642014, 1, 1, 1, 0⟩
theorem s3_6_edges : next config 3 s3_6 = [s4_415, s4_197, s4_23, s4_36] := by decide
theorem s3_6_safe : Safe 10 3 s3_6 := by
  apply safe_succ 9 3 s3_6 [s4_415, s4_197, s4_23, s4_36] (by decide) s3_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_415_safe
  · subst z; exact s4_197_safe
  · subst z; exact s4_23_safe
  · subst z; exact s4_36_safe
def s3_7 : State := ⟨[1,4,64,130], 1701411834604692317335319781236845642518, 1, 1, 1, 0⟩
theorem s3_7_edges : next config 3 s3_7 = [s4_198, s4_37] := by decide
theorem s3_7_safe : Safe 10 3 s3_7 := by
  apply safe_succ 9 3 s3_7 [s4_198, s4_37] (by decide) s3_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_198_safe
  · subst z; exact s4_37_safe
def s3_8 : State := ⟨[1,4,64,130], 1701411834604692317335319781236845646102, 2, 2, 1, 0⟩
theorem s3_8_edges : next config 3 s3_8 = [s4_1090, s4_1203, s4_702, s4_944, s4_80, s4_387, s4_91, s4_140, s4_199, s4_4, s4_67, s4_24, s4_38] := by decide
theorem s3_8_safe : Safe 10 3 s3_8 := by
  apply safe_succ 9 3 s3_8 [s4_1090, s4_1203, s4_702, s4_944, s4_80, s4_387, s4_91, s4_140, s4_199, s4_4, s4_67, s4_24, s4_38] (by decide) s3_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1090_safe
  · subst z; exact s4_1203_safe
  · subst z; exact s4_702_safe
  · subst z; exact s4_944_safe
  · subst z; exact s4_80_safe
  · subst z; exact s4_387_safe
  · subst z; exact s4_91_safe
  · subst z; exact s4_140_safe
  · subst z; exact s4_199_safe
  · subst z; exact s4_4_safe
  · subst z; exact s4_67_safe
  · subst z; exact s4_24_safe
  · subst z; exact s4_38_safe
def s3_9 : State := ⟨[1,4,64,130], 1701411834604692317335319781245435576598, 1, 1, 1, 0⟩
theorem s3_9_edges : next config 3 s3_9 = [s4_416, s4_200] := by decide
theorem s3_9_safe : Safe 10 3 s3_9 := by
  apply safe_succ 9 3 s3_9 [s4_416, s4_200] (by decide) s3_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_416_safe
  · subst z; exact s4_200_safe
def s3_10 : State := ⟨[1,4,64,130], 1701411834604692317372213269384264745238, 1, 1, 1, 0⟩
theorem s3_10_edges : next config 3 s3_10 = [s4_417, s4_201, s4_25, s4_39] := by decide
theorem s3_10_safe : Safe 10 3 s3_10 := by
  apply safe_succ 9 3 s3_10 [s4_417, s4_201, s4_25, s4_39] (by decide) s3_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_417_safe
  · subst z; exact s4_201_safe
  · subst z; exact s4_25_safe
  · subst z; exact s4_39_safe
def s3_11 : State := ⟨[1,4,64,130], 1701411834604692317630467686416198467862, 2, 2, 1, 0⟩
theorem s3_11_edges : next config 3 s3_11 = [s4_202, s4_26] := by decide
theorem s3_11_safe : Safe 10 3 s3_11 := by
  apply safe_succ 9 3 s3_11 [s4_202, s4_26] (by decide) s3_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_202_safe
  · subst z; exact s4_26_safe
def s3_12 : State := ⟨[1,4,64,130], 4423670769972200025042316640690991333654, 1, 1, 1, 0⟩
theorem s3_12_edges : next config 3 s3_12 = [s4_418, s4_205, s4_27, s4_40] := by decide
theorem s3_12_safe : Safe 10 3 s3_12 := by
  apply safe_succ 9 3 s3_12 [s4_418, s4_205, s4_27, s4_40] (by decide) s3_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_418_safe
  · subst z; exact s4_205_safe
  · subst z; exact s4_27_safe
  · subst z; exact s4_40_safe
def s3_13 : State := ⟨[1,4,64,131], 3062541302288446171188818210963918487838, 1, 1, 1, 0⟩
theorem s3_13_edges : next config 3 s3_13 = [s4_419, s4_206, s4_48] := by decide
theorem s3_13_safe : Safe 10 3 s3_13 := by
  apply safe_succ 9 3 s3_13 [s4_419, s4_206, s4_48] (by decide) s3_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_419_safe
  · subst z; exact s4_206_safe
  · subst z; exact s4_48_safe
def s3_14 : State := ⟨[1,4,64,132], 5784800237655953878895815070418064179486, 1, 1, 1, 0⟩
theorem s3_14_edges : next config 3 s3_14 = [s4_420, s4_207, s4_5] := by decide
theorem s3_14_safe : Safe 10 3 s3_14 := by
  apply safe_succ 9 3 s3_14 [s4_420, s4_207, s4_5] (by decide) s3_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_420_safe
  · subst z; exact s4_207_safe
  · subst z; exact s4_5_safe
def s3_15 : State := ⟨[1,4,64,132], 5784800237655953878895815070418064179990, 1, 1, 1, 0⟩
theorem s3_15_edges : next config 3 s3_15 = [s4_208] := by decide
theorem s3_15_safe : Safe 10 3 s3_15 := by
  apply safe_succ 9 3 s3_15 [s4_208] (by decide) s3_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_208_safe
def s3_16 : State := ⟨[1,4,64,132], 5784800237655953878895815070418064183574, 2, 2, 1, 0⟩
theorem s3_16_edges : next config 3 s3_16 = [s4_1091, s4_704, s4_945, s4_81, s4_92, s4_141, s4_209] := by decide
theorem s3_16_safe : Safe 10 3 s3_16 := by
  apply safe_succ 9 3 s3_16 [s4_1091, s4_704, s4_945, s4_81, s4_92, s4_141, s4_209] (by decide) s3_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1091_safe
  · subst z; exact s4_704_safe
  · subst z; exact s4_945_safe
  · subst z; exact s4_81_safe
  · subst z; exact s4_92_safe
  · subst z; exact s4_141_safe
  · subst z; exact s4_209_safe
def s3_17 : State := ⟨[1,4,64,132], 5784800237655953878895815070426654114070, 1, 1, 1, 0⟩
theorem s3_17_edges : next config 3 s3_17 = [s4_421, s4_210, s4_6] := by decide
theorem s3_17_safe : Safe 10 3 s3_17 := by
  apply safe_succ 9 3 s3_17 [s4_421, s4_210, s4_6] (by decide) s3_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_421_safe
  · subst z; exact s4_210_safe
  · subst z; exact s4_6_safe
def s3_18 : State := ⟨[1,4,64,132], 5784800237655953878932708558565483282710, 1, 1, 1, 0⟩
theorem s3_18_edges : next config 3 s3_18 = [s4_422, s4_211, s4_7] := by decide
theorem s3_18_safe : Safe 10 3 s3_18 := by
  apply safe_succ 9 3 s3_18 [s4_422, s4_211, s4_7] (by decide) s3_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_422_safe
  · subst z; exact s4_211_safe
  · subst z; exact s4_7_safe
def s3_19 : State := ⟨[1,4,64,132], 5784800237655953879190962975597417005334, 2, 2, 1, 0⟩
theorem s3_19_edges : next config 3 s3_19 = [s4_212] := by decide
theorem s3_19_safe : Safe 10 3 s3_19 := by
  apply safe_succ 9 3 s3_19 [s4_212] (by decide) s3_19_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_212_safe
def s3_20 : State := ⟨[1,4,64,136], 87452568298681185110105720854042434928926, 1, 1, 1, 0⟩
theorem s3_20_edges : next config 3 s3_20 = [s4_662, s4_423, s4_215, s4_8] := by decide
theorem s3_20_safe : Safe 10 3 s3_20 := by
  apply safe_succ 9 3 s3_20 [s4_662, s4_423, s4_215, s4_8] (by decide) s3_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_662_safe
  · subst z; exact s4_423_safe
  · subst z; exact s4_215_safe
  · subst z; exact s4_8_safe
def s3_21 : State := ⟨[1,4,64,136], 87452568298681185110105720854042434929430, 1, 1, 1, 0⟩
theorem s3_21_edges : next config 3 s3_21 = [s4_216] := by decide
theorem s3_21_safe : Safe 10 3 s3_21 := by
  apply safe_succ 9 3 s3_21 [s4_216] (by decide) s3_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_216_safe
def s3_22 : State := ⟨[1,4,64,136], 87452568298681185110105720854042434933014, 2, 2, 1, 0⟩
theorem s3_22_edges : next config 3 s3_22 = [s4_1092, s4_705, s4_946, s4_82, s4_93, s4_142, s4_217] := by decide
theorem s3_22_safe : Safe 10 3 s3_22 := by
  apply safe_succ 9 3 s3_22 [s4_1092, s4_705, s4_946, s4_82, s4_93, s4_142, s4_217] (by decide) s3_22_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1092_safe
  · subst z; exact s4_705_safe
  · subst z; exact s4_946_safe
  · subst z; exact s4_82_safe
  · subst z; exact s4_93_safe
  · subst z; exact s4_142_safe
  · subst z; exact s4_217_safe
def s3_23 : State := ⟨[1,4,64,136], 87452568298681185110105720854051024863510, 1, 1, 1, 0⟩
theorem s3_23_edges : next config 3 s3_23 = [s4_663, s4_424, s4_218, s4_9] := by decide
theorem s3_23_safe : Safe 10 3 s3_23 := by
  apply safe_succ 9 3 s3_23 [s4_663, s4_424, s4_218, s4_9] (by decide) s3_23_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_663_safe
  · subst z; exact s4_424_safe
  · subst z; exact s4_218_safe
  · subst z; exact s4_9_safe
def s3_24 : State := ⟨[1,4,64,136], 87452568298681185110142614342189854032150, 1, 1, 1, 0⟩
theorem s3_24_edges : next config 3 s3_24 = [s4_664, s4_425, s4_219, s4_10] := by decide
theorem s3_24_safe : Safe 10 3 s3_24 := by
  apply safe_succ 9 3 s3_24 [s4_664, s4_425, s4_219, s4_10] (by decide) s3_24_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_664_safe
  · subst z; exact s4_425_safe
  · subst z; exact s4_219_safe
  · subst z; exact s4_10_safe
def s3_25 : State := ⟨[1,4,64,136], 87452568298681185110400868759221787754774, 2, 2, 1, 0⟩
theorem s3_25_edges : next config 3 s3_25 = [s4_220] := by decide
theorem s3_25_safe : Safe 10 3 s3_25 := by
  apply safe_succ 9 3 s3_25 [s4_220] (by decide) s3_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_220_safe
def s3_26 : State := ⟨[1,4,64,136], 261677140162201678403353519859107759194390, 1, 1, 1, 0⟩
theorem s3_26_edges : next config 3 s3_26 = [s4_223] := by decide
theorem s3_26_safe : Safe 10 3 s3_26 := by
  apply safe_succ 9 3 s3_26 [s4_223] (by decide) s3_26_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_223_safe
def s3_27 : State := ⟨[1,4,64,136], 1481249143206845131456088112894565029052694, 2, 2, 1, 0⟩
theorem s3_27_edges : next config 3 s3_27 = [s4_1093, s4_706, s4_947, s4_83, s4_94, s4_143, s4_224] := by decide
theorem s3_27_safe : Safe 10 3 s3_27 := by
  apply safe_succ 9 3 s3_27 [s4_1093, s4_706, s4_947, s4_83, s4_94, s4_143, s4_224] (by decide) s3_27_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1093_safe
  · subst z; exact s4_706_safe
  · subst z; exact s4_947_safe
  · subst z; exact s4_83_safe
  · subst z; exact s4_94_safe
  · subst z; exact s4_143_safe
  · subst z; exact s4_224_safe
def s3_28 : State := ⟨[1,4,64,137], 174564854230441431756729620356575097062166, 1, 1, 1, 0⟩
theorem s3_28_edges : next config 3 s3_28 = [s4_225] := by decide
theorem s3_28_safe : Safe 10 3 s3_28 := by
  apply safe_succ 9 3 s3_28 [s4_225] (by decide) s3_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_225_safe
def s3_29 : State := ⟨[1,4,64,140], 1394136857275084884809464213392032366924054, 2, 2, 1, 0⟩
theorem s3_29_edges : next config 3 s3_29 = [s4_1094, s4_707, s4_948, s4_84, s4_95, s4_144, s4_226] := by decide
theorem s3_29_safe : Safe 10 3 s3_29 := by
  apply safe_succ 9 3 s3_29 [s4_1094, s4_707, s4_948, s4_84, s4_95, s4_144, s4_226] (by decide) s3_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1094_safe
  · subst z; exact s4_707_safe
  · subst z; exact s4_948_safe
  · subst z; exact s4_84_safe
  · subst z; exact s4_95_safe
  · subst z; exact s4_144_safe
  · subst z; exact s4_226_safe
def s3_30 : State := ⟨[1,4,64,144], 22301085480897544079999200093999871278776606, 1, 1, 1, 0⟩
theorem s3_30_edges : next config 3 s3_30 = [s4_429, s4_227, s4_17, s4_28, s4_59] := by decide
theorem s3_30_safe : Safe 10 3 s3_30 := by
  apply safe_succ 9 3 s3_30 [s4_429, s4_227, s4_17, s4_28, s4_59] (by decide) s3_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_429_safe
  · subst z; exact s4_227_safe
  · subst z; exact s4_17_safe
  · subst z; exact s4_28_safe
  · subst z; exact s4_59_safe
def s3_31 : State := ⟨[1,4,64,144], 22301085480897544079999200093999871278777110, 1, 1, 1, 0⟩
theorem s3_31_edges : next config 3 s3_31 = [s4_228, s4_18] := by decide
theorem s3_31_safe : Safe 10 3 s3_31 := by
  apply safe_succ 9 3 s3_31 [s4_228, s4_18] (by decide) s3_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_228_safe
  · subst z; exact s4_18_safe
def s3_32 : State := ⟨[1,4,64,144], 22301085480897544079999200093999871278780694, 2, 2, 1, 0⟩
theorem s3_32_edges : next config 3 s3_32 = [s4_1095, s4_708, s4_949, s4_85, s4_390, s4_96, s4_145, s4_229, s4_19, s4_69, s4_29, s4_60] := by decide
theorem s3_32_safe : Safe 10 3 s3_32 := by
  apply safe_succ 9 3 s3_32 [s4_1095, s4_708, s4_949, s4_85, s4_390, s4_96, s4_145, s4_229, s4_19, s4_69, s4_29, s4_60] (by decide) s3_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1095_safe
  · subst z; exact s4_708_safe
  · subst z; exact s4_949_safe
  · subst z; exact s4_85_safe
  · subst z; exact s4_390_safe
  · subst z; exact s4_96_safe
  · subst z; exact s4_145_safe
  · subst z; exact s4_229_safe
  · subst z; exact s4_19_safe
  · subst z; exact s4_69_safe
  · subst z; exact s4_29_safe
  · subst z; exact s4_60_safe
def s3_33 : State := ⟨[1,4,64,144], 22301085480897544079999200093999879868711190, 1, 1, 1, 0⟩
theorem s3_33_edges : next config 3 s3_33 = [s4_430, s4_230, s4_20] := by decide
theorem s3_33_safe : Safe 10 3 s3_33 := by
  apply safe_succ 9 3 s3_33 [s4_430, s4_230, s4_20] (by decide) s3_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_430_safe
  · subst z; exact s4_230_safe
  · subst z; exact s4_20_safe
def s3_34 : State := ⟨[1,4,64,144], 22301085480897544079999236987488018697879830, 1, 1, 1, 0⟩
theorem s3_34_edges : next config 3 s3_34 = [s4_431, s4_231, s4_21, s4_30, s4_61] := by decide
theorem s3_34_safe : Safe 10 3 s3_34 := by
  apply safe_succ 9 3 s3_34 [s4_431, s4_231, s4_21, s4_30, s4_61] (by decide) s3_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_431_safe
  · subst z; exact s4_231_safe
  · subst z; exact s4_21_safe
  · subst z; exact s4_30_safe
  · subst z; exact s4_61_safe
def s3_35 : State := ⟨[1,4,64,144], 22301085480897544079999495241905050631602454, 2, 2, 1, 0⟩
theorem s3_35_edges : next config 3 s3_35 = [s4_232, s4_22, s4_31] := by decide
theorem s3_35_safe : Safe 10 3 s3_35 := by
  apply safe_succ 9 3 s3_35 [s4_232, s4_22, s4_31] (by decide) s3_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_232_safe
  · subst z; exact s4_22_safe
  · subst z; exact s4_31_safe
def s3_36 : State := ⟨[1,4,64,145], 44601830679428167221534918366648232784888086, 1, 1, 1, 0⟩
theorem s3_36_edges : next config 3 s3_36 = [s4_1096, s4_709, s4_813, s4_950, s4_589, s4_432, s4_86, s4_136, s4_391, s4_97, s4_146, s4_235] := by decide
theorem s3_36_safe : Safe 10 3 s3_36 := by
  apply safe_succ 9 3 s3_36 [s4_1096, s4_709, s4_813, s4_950, s4_589, s4_432, s4_86, s4_136, s4_391, s4_97, s4_146, s4_235] (by decide) s3_36_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1096_safe
  · subst z; exact s4_709_safe
  · subst z; exact s4_813_safe
  · subst z; exact s4_950_safe
  · subst z; exact s4_589_safe
  · subst z; exact s4_432_safe
  · subst z; exact s4_86_safe
  · subst z; exact s4_136_safe
  · subst z; exact s4_391_safe
  · subst z; exact s4_97_safe
  · subst z; exact s4_146_safe
  · subst z; exact s4_235_safe
def s3_37 : State := ⟨[1,4,64,150], 1516452374911916978316746177859869819252310294, 0, 0, 1, 0⟩
theorem s3_37_edges : next config 3 s3_37 = [s4_404, s4_236, s4_71] := by decide
theorem s3_37_safe : Safe 10 3 s3_37 := by
  apply safe_succ 9 3 s3_37 [s4_404, s4_236, s4_71] (by decide) s3_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_404_safe
  · subst z; exact s4_236_safe
  · subst z; exact s4_71_safe
def s3_38 : State := ⟨[1,4,64,150], 1538751758980979917704428042634088453685444886, 0, 0, 1, 0⟩
theorem s3_38_edges : next config 3 s3_38 = [s4_405, s4_237, s4_72] := by decide
theorem s3_38_safe : Safe 10 3 s3_38 := by
  apply safe_succ 9 3 s3_38 [s4_405, s4_237, s4_72] (by decide) s3_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_405_safe
  · subst z; exact s4_237_safe
  · subst z; exact s4_72_safe
def s3_39 : State := ⟨[1,4,64,160], 1461501637671185285124623296198104371165705339166, 1, 1, 1, 0⟩
theorem s3_39_edges : next config 3 s3_39 = [s4_433, s4_238, s4_41, s4_62] := by decide
theorem s3_39_safe : Safe 10 3 s3_39 := by
  apply safe_succ 9 3 s3_39 [s4_433, s4_238, s4_41, s4_62] (by decide) s3_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_433_safe
  · subst z; exact s4_238_safe
  · subst z; exact s4_41_safe
  · subst z; exact s4_62_safe
def s3_40 : State := ⟨[1,4,64,160], 1461501637671185285124623296198104371165705339670, 1, 1, 1, 0⟩
theorem s3_40_edges : next config 3 s3_40 = [s4_239, s4_42] := by decide
theorem s3_40_safe : Safe 10 3 s3_40 := by
  apply safe_succ 9 3 s3_40 [s4_239, s4_42] (by decide) s3_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_239_safe
  · subst z; exact s4_42_safe
def s3_41 : State := ⟨[1,4,64,160], 1461501637671185285124623296198104371165705343254, 2, 2, 1, 0⟩
theorem s3_41_edges : next config 3 s3_41 = [s4_1097, s4_1215, s4_712, s4_951, s4_87, s4_98, s4_147, s4_240, s4_35, s4_43, s4_63] := by decide
theorem s3_41_safe : Safe 10 3 s3_41 := by
  apply safe_succ 9 3 s3_41 [s4_1097, s4_1215, s4_712, s4_951, s4_87, s4_98, s4_147, s4_240, s4_35, s4_43, s4_63] (by decide) s3_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1097_safe
  · subst z; exact s4_1215_safe
  · subst z; exact s4_712_safe
  · subst z; exact s4_951_safe
  · subst z; exact s4_87_safe
  · subst z; exact s4_98_safe
  · subst z; exact s4_147_safe
  · subst z; exact s4_240_safe
  · subst z; exact s4_35_safe
  · subst z; exact s4_43_safe
  · subst z; exact s4_63_safe
def s3_42 : State := ⟨[1,4,64,160], 1461501637671185285124623296198104371174295273750, 1, 1, 1, 0⟩
theorem s3_42_edges : next config 3 s3_42 = [s4_434, s4_241] := by decide
theorem s3_42_safe : Safe 10 3 s3_42 := by
  apply safe_succ 9 3 s3_42 [s4_434, s4_241] (by decide) s3_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_434_safe
  · subst z; exact s4_241_safe
def s3_43 : State := ⟨[1,4,64,160], 1461501637671185285124623296234997859313124442390, 1, 1, 1, 0⟩
theorem s3_43_edges : next config 3 s3_43 = [s4_435, s4_242, s4_44, s4_64] := by decide
theorem s3_43_safe : Safe 10 3 s3_43 := by
  apply safe_succ 9 3 s3_43 [s4_435, s4_242, s4_44, s4_64] (by decide) s3_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_435_safe
  · subst z; exact s4_242_safe
  · subst z; exact s4_44_safe
  · subst z; exact s4_64_safe
def s3_44 : State := ⟨[1,4,64,160], 1461501637671185285124623296493252276345058165014, 2, 2, 1, 0⟩
theorem s3_44_edges : next config 3 s3_44 = [s4_243] := by decide
theorem s3_44_safe : Safe 10 3 s3_44 := by
  apply safe_succ 9 3 s3_44 [s4_243] (by decide) s3_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_243_safe
def s3_45 : State := ⟨[1,4,64,160], 4384504912332991121531992961630670410477570425110, 1, 1, 1, 0⟩
theorem s3_45_edges : next config 3 s3_45 = [s4_436, s4_246] := by decide
theorem s3_45_safe : Safe 10 3 s3_45 := by
  apply safe_succ 9 3 s3_45 [s4_436, s4_246] (by decide) s3_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_436_safe
  · subst z; exact s4_246_safe
def s3_46 : State := ⟨[1,4,64,161], 2923003275002088203328308128914387390830227816726, 1, 1, 1, 0⟩
theorem s3_46_edges : next config 3 s3_46 = [s4_437, s4_247, s4_50] := by decide
theorem s3_46_safe : Safe 10 3 s3_46 := by
  apply safe_succ 9 3 s3_46 [s4_437, s4_247, s4_50] (by decide) s3_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_437_safe
  · subst z; exact s4_247_safe
  · subst z; exact s4_50_safe
def s3_47 : State := ⟨[1,4,64,163], 11692013102390329381759801759845831583074915254550, 0, 0, 1, 0⟩
theorem s3_47_edges : next config 3 s3_47 = [s4_438, s4_250, s4_51] := by decide
theorem s3_47_safe : Safe 10 3 s3_47 := by
  apply safe_succ 9 3 s3_47 [s4_438, s4_250, s4_51] (by decide) s3_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_438_safe
  · subst z; exact s4_250_safe
  · subst z; exact s4_51_safe
def s3_48 : State := ⟨[1,4,64,163], 11692013103070894115601678686772580797938451677462, 0, 0, 1, 0⟩
theorem s3_48_edges : next config 3 s3_48 = [s4_439, s4_251, s4_52] := by decide
theorem s3_48_safe : Safe 10 3 s3_48 := by
  apply safe_succ 9 3 s3_48 [s4_439, s4_251, s4_52] (by decide) s3_48_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_439_safe
  · subst z; exact s4_251_safe
  · subst z; exact s4_52_safe
def s3_49 : State := ⟨[1,4,64,163], 14615016374329876282799663717571400762932634648854, 0, 0, 1, 0⟩
theorem s3_49_edges : next config 3 s3_49 = [s4_440, s4_252, s4_53] := by decide
theorem s3_49_safe : Safe 10 3 s3_49 := by
  apply safe_succ 9 3 s3_49 [s4_440, s4_252, s4_53] (by decide) s3_49_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_440_safe
  · subst z; exact s4_252_safe
  · subst z; exact s4_53_safe
def s3_50 : State := ⟨[1,4,64,163], 16076518010980214467161471623360934567725030768918, 0, 0, 1, 0⟩
theorem s3_50_edges : next config 3 s3_50 = [s4_441, s4_253, s4_54] := by decide
theorem s3_50_safe : Safe 10 3 s3_50 := by
  apply safe_succ 9 3 s3_50 [s4_441, s4_253, s4_54] (by decide) s3_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_441_safe
  · subst z; exact s4_253_safe
  · subst z; exact s4_54_safe
def s3_51 : State := ⟨[1,4,64,163], 17538019649672246853048910309930716017108036157718, 0, 0, 1, 0⟩
theorem s3_51_edges : next config 3 s3_51 = [s4_442, s4_254, s4_55] := by decide
theorem s3_51_safe : Safe 10 3 s3_51 := by
  apply safe_succ 9 3 s3_51 [s4_442, s4_254, s4_55] (by decide) s3_51_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_442_safe
  · subst z; exact s4_254_safe
  · subst z; exact s4_55_safe
def s3_52 : State := ⟨[1,4,64,163], 18999521285642020303568841288793500607036895854870, 0, 0, 1, 0⟩
theorem s3_52_edges : next config 3 s3_52 = [s4_443, s4_255, s4_56] := by decide
theorem s3_52_safe : Safe 10 3 s3_52 := by
  apply safe_succ 9 3 s3_52 [s4_443, s4_255, s4_56] (by decide) s3_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_443_safe
  · subst z; exact s4_255_safe
  · subst z; exact s4_56_safe
def s3_53 : State := ⟨[1,4,64,170], 1502423683177869611747992700349674263987535499821334, 0, 0, 1, 0⟩
theorem s3_53_edges : next config 3 s3_53 = [s4_1241, s4_256, s4_57] := by decide
theorem s3_53_safe : Safe 10 3 s3_53 := by
  apply safe_succ 9 3 s3_53 [s4_1241, s4_256, s4_57] (by decide) s3_53_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1241_safe
  · subst z; exact s4_256_safe
  · subst z; exact s4_57_safe
def s3_54 : State := ⟨[1,4,64,170], 1503885184813839385198512631328537048577464359518486, 0, 0, 1, 0⟩
theorem s3_54_edges : next config 3 s3_54 = [s4_1242, s4_257, s4_58] := by decide
theorem s3_54_safe : Safe 10 3 s3_54 := by
  apply safe_succ 9 3 s3_54 [s4_1242, s4_257, s4_58] (by decide) s3_54_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1242_safe
  · subst z; exact s4_257_safe
  · subst z; exact s4_58_safe
def s3_55 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879584176795973807309086, 1, 1, 1, 0⟩
theorem s3_55_edges : next config 3 s3_55 = [s4_444, s4_258] := by decide
theorem s3_55_safe : Safe 10 3 s3_55 := by
  apply safe_succ 9 3 s3_55 [s4_444, s4_258] (by decide) s3_55_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_444_safe
  · subst z; exact s4_258_safe
def s3_56 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879584176795973807309590, 1, 1, 1, 0⟩
theorem s3_56_edges : next config 3 s3_56 = [s4_259] := by decide
theorem s3_56_safe : Safe 10 3 s3_56 := by
  apply safe_succ 9 3 s3_56 [s4_259] (by decide) s3_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_259_safe
def s3_57 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879584176795973807313174, 2, 2, 1, 0⟩
theorem s3_57_edges : next config 3 s3_57 = [s4_1098, s4_1243, s4_715, s4_955, s4_88, s4_99, s4_148, s4_260, s4_66, s4_68, s4_70] := by decide
theorem s3_57_safe : Safe 10 3 s3_57 := by
  apply safe_succ 9 3 s3_57 [s4_1098, s4_1243, s4_715, s4_955, s4_88, s4_99, s4_148, s4_260, s4_66, s4_68, s4_70] (by decide) s3_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1098_safe
  · subst z; exact s4_1243_safe
  · subst z; exact s4_715_safe
  · subst z; exact s4_955_safe
  · subst z; exact s4_88_safe
  · subst z; exact s4_99_safe
  · subst z; exact s4_148_safe
  · subst z; exact s4_260_safe
  · subst z; exact s4_66_safe
  · subst z; exact s4_68_safe
  · subst z; exact s4_70_safe
def s3_58 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879584176795982397243670, 1, 1, 1, 0⟩
theorem s3_58_edges : next config 3 s3_58 = [s4_445, s4_261] := by decide
theorem s3_58_safe : Safe 10 3 s3_58 := by
  apply safe_succ 9 3 s3_58 [s4_445, s4_261] (by decide) s3_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_445_safe
  · subst z; exact s4_261_safe
def s3_59 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879621070284121226412310, 1, 1, 1, 0⟩
theorem s3_59_edges : next config 3 s3_59 = [s4_446, s4_262] := by decide
theorem s3_59_safe : Safe 10 3 s3_59 := by
  apply safe_succ 9 3 s3_59 [s4_446, s4_262] (by decide) s3_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_446_safe
  · subst z; exact s4_262_safe
def s3_60 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879879324701153160134934, 2, 2, 1, 0⟩
theorem s3_60_edges : next config 3 s3_60 = [s4_263] := by decide
theorem s3_60_safe : Safe 10 3 s3_60 := by
  apply safe_succ 9 3 s3_60 [s4_263] (by decide) s3_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_263_safe
def s3_61 : State := ⟨[1,4,64,192], 18831305206160042291847650636543937711788887684901876334870, 1, 1, 1, 0⟩
theorem s3_61_edges : next config 3 s3_61 = [s4_447, s4_266] := by decide
theorem s3_61_safe : Safe 10 3 s3_61 := by
  apply safe_succ 9 3 s3_61 [s4_447, s4_266] (by decide) s3_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_447_safe
  · subst z; exact s4_266_safe
def s3_62 : State := ⟨[1,4,64,192], 106710729501573572985548702561451267537221863907398359515414, 2, 2, 1, 0⟩
theorem s3_62_edges : next config 3 s3_62 = [s4_267] := by decide
theorem s3_62_safe : Safe 10 3 s3_62 := by
  apply safe_succ 9 3 s3_62 [s4_267] (by decide) s3_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_267_safe
def s3_63 : State := ⟨[1,4,64,193], 12554203470773361528011861213336271295723425728585260925206, 1, 1, 1, 0⟩
theorem s3_63_edges : next config 3 s3_63 = [s4_448, s4_268] := by decide
theorem s3_63_safe : Safe 10 3 s3_63 := by
  apply safe_succ 9 3 s3_63 [s4_448, s4_268] (by decide) s3_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_448_safe
  · subst z; exact s4_268_safe
def s3_64 : State := ⟨[1,4,64,196], 100433627766186892221712913138243601121414656368113677828374, 2, 2, 1, 0⟩
theorem s3_64_edges : next config 3 s3_64 = [s4_271] := by decide
theorem s3_64_safe : Safe 10 3 s3_64 := by
  apply safe_succ 9 3 s3_64 [s4_271] (by decide) s3_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_271_safe
def s3_65 : State := ⟨[1,4,64,210], 1645504557321206042244173864763307602241196074043954546218172694, 0, 0, 1, 0⟩
theorem s3_65_edges : next config 3 s3_65 = [s4_681, s4_449, s4_272, s4_73] := by decide
theorem s3_65_safe : Safe 10 3 s3_65 := by
  apply safe_succ 9 3 s3_65 [s4_681, s4_449, s4_272, s4_73] (by decide) s3_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_681_safe
  · subst z; exact s4_449_safe
  · subst z; exact s4_272_safe
  · subst z; exact s4_73_safe
def s3_66 : State := ⟨[1,4,64,210], 1645504557321206042266473248832370541628877938818173180651307286, 0, 0, 1, 0⟩
theorem s3_66_edges : next config 3 s3_66 = [s4_682, s4_450, s4_273, s4_74] := by decide
theorem s3_66_safe : Safe 10 3 s3_66 := by
  apply safe_succ 9 3 s3_66 [s4_682, s4_450, s4_273, s4_74] (by decide) s3_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_682_safe
  · subst z; exact s4_450_safe
  · subst z; exact s4_273_safe
  · subst z; exact s4_74_safe
def s3_67 : State := ⟨[1,4,64,210], 1645529665728147588878026227126877940340717610375138956332302614, 0, 0, 1, 0⟩
theorem s3_67_edges : next config 3 s3_67 = [s4_683, s4_451, s4_274, s4_75] := by decide
theorem s3_67_safe : Safe 10 3 s3_67 := by
  apply safe_succ 9 3 s3_67 [s4_683, s4_451, s4_274, s4_75] (by decide) s3_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_683_safe
  · subst z; exact s4_451_safe
  · subst z; exact s4_274_safe
  · subst z; exact s4_75_safe
def s3_68 : State := ⟨[1,4,64,210], 1645535942829882975558788701786833464253279859232153693293969686, 0, 0, 1, 0⟩
theorem s3_68_edges : next config 3 s3_68 = [s4_684, s4_452, s4_275, s4_76] := by decide
theorem s3_68_safe : Safe 10 3 s3_68 := by
  apply safe_succ 9 3 s3_68 [s4_684, s4_452, s4_275, s4_76] (by decide) s3_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_684_safe
  · subst z; exact s4_452_safe
  · subst z; exact s4_275_safe
  · subst z; exact s4_76_safe
def s3_69 : State := ⟨[1,4,64,210], 2056880696651507552716012563677585675308419032135974700464537878, 0, 0, 1, 0⟩
theorem s3_69_edges : next config 3 s3_69 = [s4_685, s4_453, s4_276, s4_77] := by decide
theorem s3_69_safe : Safe 10 3 s3_69 := by
  apply safe_succ 9 3 s3_69 [s4_685, s4_453, s4_276, s4_77] (by decide) s3_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_685_safe
  · subst z; exact s4_453_safe
  · subst z; exact s4_276_safe
  · subst z; exact s4_77_safe
def s3_70 : State := ⟨[1,4,64,210], 2056886973753242939374475654268478259833299416218770802993070358, 0, 0, 1, 0⟩
theorem s3_70_edges : next config 3 s3_70 = [s4_686, s4_454, s4_277, s4_78] := by decide
theorem s3_70_safe : Safe 10 3 s3_70 := by
  apply safe_succ 9 3 s3_70 [s4_686, s4_454, s4_277, s4_78] (by decide) s3_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_686_safe
  · subst z; exact s4_454_safe
  · subst z; exact s4_277_safe
  · subst z; exact s4_78_safe
def s3_71 : State := ⟨[1,4,65,128], 340282366920938463518714839657191903510, 2, 2, 0, 0⟩
theorem s3_71_edges : next config 3 s3_71 = [s4_837, s4_103, s4_79, s4_81, s4_89, s4_80, s4_82, s4_85, s4_87] := by decide
theorem s3_71_safe : Safe 10 3 s3_71 := by
  apply safe_succ 9 3 s3_71 [s4_837, s4_103, s4_79, s4_81, s4_89, s4_80, s4_82, s4_85, s4_87] (by decide) s3_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_837_safe
  · subst z; exact s4_103_safe
  · subst z; exact s4_79_safe
  · subst z; exact s4_81_safe
  · subst z; exact s4_89_safe
  · subst z; exact s4_80_safe
  · subst z; exact s4_82_safe
  · subst z; exact s4_85_safe
  · subst z; exact s4_87_safe
def s3_72 : State := ⟨[1,4,65,140], 1399581375145819900224915100599088077406486, 0, 0, 1, 0⟩
theorem s3_72_edges : next config 3 s3_72 = [s4_110] := by decide
theorem s3_72_safe : Safe 10 3 s3_72 := by
  apply safe_succ 9 3 s3_72 [s4_110] (by decide) s3_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_110_safe
def s3_73 : State := ⟨[1,4,65,140], 1481249143206845131456125006382712448155926, 0, 0, 1, 0⟩
theorem s3_73_edges : next config 3 s3_73 = [s4_112] := by decide
theorem s3_73_safe : Safe 10 3 s3_73 := by
  apply safe_succ 9 3 s3_73 [s4_112] (by decide) s3_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_112_safe
def s3_74 : State := ⟨[1,4,65,145], 44602511244162009098461882009351243740283158, 0, 0, 1, 0⟩
theorem s3_74_edges : next config 3 s3_74 = [s4_455, s4_115] := by decide
theorem s3_74_safe : Safe 10 3 s3_74 := by
  apply safe_succ 9 3 s3_74 [s4_455, s4_115] (by decide) s3_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_455_safe
  · subst z; exact s4_115_safe
def s3_75 : State := ⟨[1,4,65,145], 66902575877958790363070673532784741709840662, 0, 0, 1, 0⟩
theorem s3_75_edges : next config 3 s3_75 = [s4_456, s4_117] := by decide
theorem s3_75_safe : Safe 10 3 s3_75 := by
  apply safe_succ 9 3 s3_75 [s4_456, s4_117] (by decide) s3_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_456_safe
  · subst z; exact s4_117_safe
def s3_76 : State := ⟨[1,4,65,146], 89204682205957097258460245303862830288666902, 0, 0, 1, 0⟩
theorem s3_76_edges : next config 3 s3_76 = [s4_457, s4_119] := by decide
theorem s3_76_safe : Safe 10 3 s3_76 := by
  apply safe_succ 9 3 s3_76 [s4_457, s4_119] (by decide) s3_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_457_safe
  · subst z; exact s4_119_safe
def s3_77 : State := ⟨[1,4,65,146], 111504066275020036646142110078081464721801494, 0, 0, 1, 0⟩
theorem s3_77_edges : next config 3 s3_77 = [s4_458, s4_121] := by decide
theorem s3_77_safe : Safe 10 3 s3_77 := by
  apply safe_succ 9 3 s3_77 [s4_458, s4_121] (by decide) s3_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_458_safe
  · subst z; exact s4_121_safe
def s3_78 : State := ⟨[1,4,65,162], 5846006551025023507419431648237345348007994917142, 0, 0, 1, 0⟩
theorem s3_78_edges : next config 3 s3_78 = [s4_459, s4_124] := by decide
theorem s3_78_safe : Safe 10 3 s3_78 := by
  apply safe_succ 9 3 s3_78 [s4_459, s4_124] (by decide) s3_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_459_safe
  · subst z; exact s4_124_safe
def s3_79 : State := ⟨[1,4,65,162], 7307508186994796957939362627100129937936854614294, 0, 0, 1, 0⟩
theorem s3_79_edges : next config 3 s3_79 = [s4_460, s4_126] := by decide
theorem s3_79_safe : Safe 10 3 s3_79 := by
  apply safe_succ 9 3 s3_79 [s4_460, s4_126] (by decide) s3_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_460_safe
  · subst z; exact s4_126_safe
def s3_80 : State := ⟨[1,4,65,176], 95780971326419139128294233276893560963659213834354966, 0, 0, 1, 0⟩
theorem s3_80_edges : next config 3 s3_80 = [s4_461, s4_128] := by decide
theorem s3_80_safe : Safe 10 3 s3_80 := by
  apply safe_succ 9 3 s3_80 [s4_461, s4_128] (by decide) s3_80_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_461_safe
  · subst z; exact s4_128_safe
def s3_81 : State := ⟨[1,4,65,176], 95782432805755724832681813820190558974030508260917526, 0, 0, 1, 0⟩
theorem s3_81_edges : next config 3 s3_81 = [s4_462, s4_130] := by decide
theorem s3_81_safe : Safe 10 3 s3_81 := by
  apply safe_succ 9 3 s3_81 [s4_462, s4_130] (by decide) s3_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_462_safe
  · subst z; exact s4_130_safe
def s3_82 : State := ⟨[1,4,66,128], 340282366920938463555608327804611006742, 2, 2, 0, 0⟩
theorem s3_82_edges : next config 3 s3_82 = [s4_839, s4_104, s4_153, s4_90, s4_92, s4_100, s4_91, s4_93, s4_96, s4_98] := by decide
theorem s3_82_safe : Safe 10 3 s3_82 := by
  apply safe_succ 9 3 s3_82 [s4_839, s4_104, s4_153, s4_90, s4_92, s4_100, s4_91, s4_93, s4_96, s4_98] (by decide) s3_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_839_safe
  · subst z; exact s4_104_safe
  · subst z; exact s4_153_safe
  · subst z; exact s4_90_safe
  · subst z; exact s4_92_safe
  · subst z; exact s4_100_safe
  · subst z; exact s4_91_safe
  · subst z; exact s4_93_safe
  · subst z; exact s4_96_safe
  · subst z; exact s4_98_safe
def s3_83 : State := ⟨[1,4,66,140], 1399581375145819900224951994087235496509718, 0, 0, 1, 0⟩
theorem s3_83_edges : next config 3 s3_83 = [s4_111, s4_157] := by decide
theorem s3_83_safe : Safe 10 3 s3_83 := by
  apply safe_succ 9 3 s3_83 [s4_111, s4_157] (by decide) s3_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_111_safe
  · subst z; exact s4_157_safe
def s3_84 : State := ⟨[1,4,66,140], 1481249143206845131456161899870859867259158, 0, 0, 1, 0⟩
theorem s3_84_edges : next config 3 s3_84 = [s4_113, s4_159] := by decide
theorem s3_84_safe : Safe 10 3 s3_84 := by
  apply safe_succ 9 3 s3_84 [s4_113, s4_159] (by decide) s3_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_113_safe
  · subst z; exact s4_159_safe
def s3_85 : State := ⟨[1,4,66,145], 44602511244162009098461918902839391159386390, 0, 0, 1, 0⟩
theorem s3_85_edges : next config 3 s3_85 = [s4_463, s4_116, s4_161] := by decide
theorem s3_85_safe : Safe 10 3 s3_85 := by
  apply safe_succ 9 3 s3_85 [s4_463, s4_116, s4_161] (by decide) s3_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_463_safe
  · subst z; exact s4_116_safe
  · subst z; exact s4_161_safe
def s3_86 : State := ⟨[1,4,66,145], 66902575877958790363070710426272889128943894, 0, 0, 1, 0⟩
theorem s3_86_edges : next config 3 s3_86 = [s4_464, s4_118, s4_163] := by decide
theorem s3_86_safe : Safe 10 3 s3_86 := by
  apply safe_succ 9 3 s3_86 [s4_464, s4_118, s4_163] (by decide) s3_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_464_safe
  · subst z; exact s4_118_safe
  · subst z; exact s4_163_safe
def s3_87 : State := ⟨[1,4,66,146], 89204682205957097258460282197350977707770134, 0, 0, 1, 0⟩
theorem s3_87_edges : next config 3 s3_87 = [s4_465, s4_120] := by decide
theorem s3_87_safe : Safe 10 3 s3_87 := by
  apply safe_succ 9 3 s3_87 [s4_465, s4_120] (by decide) s3_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_465_safe
  · subst z; exact s4_120_safe
def s3_88 : State := ⟨[1,4,66,146], 111504066275020036646142146971569612140904726, 0, 0, 1, 0⟩
theorem s3_88_edges : next config 3 s3_88 = [s4_466, s4_122] := by decide
theorem s3_88_safe : Safe 10 3 s3_88 := by
  apply safe_succ 9 3 s3_88 [s4_466, s4_122] (by decide) s3_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_466_safe
  · subst z; exact s4_122_safe
def s3_89 : State := ⟨[1,4,66,162], 5846006551025023507419431648274238836155414020374, 0, 0, 1, 0⟩
theorem s3_89_edges : next config 3 s3_89 = [s4_467, s4_125] := by decide
theorem s3_89_safe : Safe 10 3 s3_89 := by
  apply safe_succ 9 3 s3_89 [s4_467, s4_125] (by decide) s3_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_467_safe
  · subst z; exact s4_125_safe
def s3_90 : State := ⟨[1,4,66,162], 7307508186994796957939362627137023426084273717526, 0, 0, 1, 0⟩
theorem s3_90_edges : next config 3 s3_90 = [s4_468, s4_127] := by decide
theorem s3_90_safe : Safe 10 3 s3_90 := by
  apply safe_succ 9 3 s3_90 [s4_468, s4_127] (by decide) s3_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_468_safe
  · subst z; exact s4_127_safe
def s3_91 : State := ⟨[1,4,66,176], 95780971326419139128294233276893597857147361253458198, 0, 0, 1, 0⟩
theorem s3_91_edges : next config 3 s3_91 = [s4_469, s4_129] := by decide
theorem s3_91_safe : Safe 10 3 s3_91 := by
  apply safe_succ 9 3 s3_91 [s4_469, s4_129] (by decide) s3_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_469_safe
  · subst z; exact s4_129_safe
def s3_92 : State := ⟨[1,4,66,176], 95782432805755724832681813820190595867518655680020758, 0, 0, 1, 0⟩
theorem s3_92_edges : next config 3 s3_92 = [s4_470, s4_131] := by decide
theorem s3_92_safe : Safe 10 3 s3_92 := by
  apply safe_succ 9 3 s3_92 [s4_470, s4_131] (by decide) s3_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_470_safe
  · subst z; exact s4_131_safe
def s3_93 : State := ⟨[1,4,66,210], 1645504557321206042177270268038248049062735139514556029465592086, 0, 0, 1, 0⟩
theorem s3_93_edges : next config 3 s3_93 = [s4_687, s4_471, s4_134, s4_101] := by decide
theorem s3_93_safe : Safe 10 3 s3_93 := by
  apply safe_succ 9 3 s3_93 [s4_687, s4_471, s4_134, s4_101] (by decide) s3_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_687_safe
  · subst z; exact s4_471_safe
  · subst z; exact s4_134_safe
  · subst z; exact s4_101_safe
def s3_94 : State := ⟨[1,4,66,210], 1645529665728147588878024865997410256586863830663685524097663254, 0, 0, 1, 0⟩
theorem s3_94_edges : next config 3 s3_94 = [s4_688, s4_472, s4_135, s4_102] := by decide
theorem s3_94_safe : Safe 10 3 s3_94 := by
  apply safe_succ 9 3 s3_94 [s4_688, s4_472, s4_135, s4_102] (by decide) s3_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_688_safe
  · subst z; exact s4_472_safe
  · subst z; exact s4_135_safe
  · subst z; exact s4_102_safe
def s3_95 : State := ⟨[1,4,67,128], 340282366920938463629395304099449209118, 1, 1, 0, 0⟩
theorem s3_95_edges : next config 3 s3_95 = [s4_841, s4_473, s4_105, s4_108, s4_133, s4_106, s4_109, s4_114, s4_123] := by decide
theorem s3_95_safe : Safe 10 3 s3_95 := by
  apply safe_succ 9 3 s3_95 [s4_841, s4_473, s4_105, s4_108, s4_133, s4_106, s4_109, s4_114, s4_123] (by decide) s3_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_841_safe
  · subst z; exact s4_473_safe
  · subst z; exact s4_105_safe
  · subst z; exact s4_108_safe
  · subst z; exact s4_133_safe
  · subst z; exact s4_106_safe
  · subst z; exact s4_109_safe
  · subst z; exact s4_114_safe
  · subst z; exact s4_123_safe
def s3_96 : State := ⟨[1,4,67,129], 1020847100762815390593038007110404735254, 0, 0, 1, 0⟩
theorem s3_96_edges : next config 3 s3_96 = [s4_474, s4_115] := by decide
theorem s3_96_safe : Safe 10 3 s3_96 := by
  apply safe_succ 9 3 s3_96 [s4_474, s4_115] (by decide) s3_96_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_474_safe
  · subst z; exact s4_115_safe
def s3_97 : State := ⟨[1,4,67,129], 1020847100762815390629931495257823838486, 0, 0, 1, 0⟩
theorem s3_97_edges : next config 3 s3_97 = [s4_475, s4_116] := by decide
theorem s3_97_safe : Safe 10 3 s3_97 := by
  apply safe_succ 9 3 s3_97 [s4_475, s4_116] (by decide) s3_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_475_safe
  · subst z; exact s4_116_safe
def s3_98 : State := ⟨[1,4,67,130], 1701411834604692317519787221973941158166, 0, 0, 1, 0⟩
theorem s3_98_edges : next config 3 s3_98 = [s4_476, s4_119, s4_124] := by decide
theorem s3_98_safe : Safe 10 3 s3_98 := by
  apply safe_succ 9 3 s3_98 [s4_476, s4_119, s4_124] (by decide) s3_98_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_476_safe
  · subst z; exact s4_119_safe
  · subst z; exact s4_124_safe
def s3_99 : State := ⟨[1,4,67,130], 1701411834604692317556680710121360261398, 0, 0, 1, 0⟩
theorem s3_99_edges : next config 3 s3_99 = [s4_477, s4_120, s4_125] := by decide
theorem s3_99_safe : Safe 10 3 s3_99 := by
  apply safe_succ 9 3 s3_99 [s4_477, s4_120, s4_125] (by decide) s3_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_477_safe
  · subst z; exact s4_120_safe
  · subst z; exact s4_125_safe
def s3_100 : State := ⟨[1,4,67,132], 5784800237655953879080282511155159695638, 0, 0, 1, 0⟩
theorem s3_100_edges : next config 3 s3_100 = [s4_478, s4_110] := by decide
theorem s3_100_safe : Safe 10 3 s3_100 := by
  apply safe_succ 9 3 s3_100 [s4_478, s4_110] (by decide) s3_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_478_safe
  · subst z; exact s4_110_safe
def s3_101 : State := ⟨[1,4,67,132], 5784800237655953879117175999302578798870, 0, 0, 1, 0⟩
theorem s3_101_edges : next config 3 s3_101 = [s4_479, s4_111] := by decide
theorem s3_101_safe : Safe 10 3 s3_101 := by
  apply safe_succ 9 3 s3_101 [s4_479, s4_111] (by decide) s3_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_479_safe
  · subst z; exact s4_111_safe
def s3_102 : State := ⟨[1,4,67,136], 87452568298681185110290188294779530445078, 0, 0, 1, 0⟩
theorem s3_102_edges : next config 3 s3_102 = [s4_665, s4_480, s4_112] := by decide
theorem s3_102_safe : Safe 10 3 s3_102 := by
  apply safe_succ 9 3 s3_102 [s4_665, s4_480, s4_112] (by decide) s3_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_665_safe
  · subst z; exact s4_480_safe
  · subst z; exact s4_112_safe
def s3_103 : State := ⟨[1,4,67,136], 87452568298681185110327081782926949548310, 0, 0, 1, 0⟩
theorem s3_103_edges : next config 3 s3_103 = [s4_666, s4_481, s4_113] := by decide
theorem s3_103_safe : Safe 10 3 s3_103 := by
  apply safe_succ 9 3 s3_103 [s4_666, s4_481, s4_113] (by decide) s3_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_666_safe
  · subst z; exact s4_481_safe
  · subst z; exact s4_113_safe
def s3_104 : State := ⟨[1,4,67,144], 22301085480897544079999384561440608374292758, 0, 0, 1, 0⟩
theorem s3_104_edges : next config 3 s3_104 = [s4_484, s4_117, s4_121, s4_128] := by decide
theorem s3_104_safe : Safe 10 3 s3_104 := by
  apply safe_succ 9 3 s3_104 [s4_484, s4_117, s4_121, s4_128] (by decide) s3_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_484_safe
  · subst z; exact s4_117_safe
  · subst z; exact s4_121_safe
  · subst z; exact s4_128_safe
def s3_105 : State := ⟨[1,4,67,144], 22301085480897544079999421454928755793395990, 0, 0, 1, 0⟩
theorem s3_105_edges : next config 3 s3_105 = [s4_485, s4_118, s4_122, s4_129] := by decide
theorem s3_105_safe : Safe 10 3 s3_105 := by
  apply safe_succ 9 3 s3_105 [s4_485, s4_118, s4_122, s4_129] (by decide) s3_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_485_safe
  · subst z; exact s4_118_safe
  · subst z; exact s4_122_safe
  · subst z; exact s4_129_safe
def s3_106 : State := ⟨[1,4,67,160], 1461501637671185285124623296382571811902800855318, 0, 0, 1, 0⟩
theorem s3_106_edges : next config 3 s3_106 = [s4_486, s4_126, s4_130] := by decide
theorem s3_106_safe : Safe 10 3 s3_106 := by
  apply safe_succ 9 3 s3_106 [s4_486, s4_126, s4_130] (by decide) s3_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_486_safe
  · subst z; exact s4_126_safe
  · subst z; exact s4_130_safe
def s3_107 : State := ⟨[1,4,67,160], 1461501637671185285124623296419465300050219958550, 0, 0, 1, 0⟩
theorem s3_107_edges : next config 3 s3_107 = [s4_487, s4_127, s4_131] := by decide
theorem s3_107_safe : Safe 10 3 s3_107 := by
  apply safe_succ 9 3 s3_107 [s4_487, s4_127, s4_131] (by decide) s3_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_487_safe
  · subst z; exact s4_127_safe
  · subst z; exact s4_131_safe
def s3_108 : State := ⟨[1,4,67,192], 6277101735386680764176071790128604879768644236710902825238, 0, 0, 1, 0⟩
theorem s3_108_edges : next config 3 s3_108 = [s4_488] := by decide
theorem s3_108_safe : Safe 10 3 s3_108 := by
  apply safe_succ 9 3 s3_108 [s4_488] (by decide) s3_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_488_safe
def s3_109 : State := ⟨[1,4,67,192], 6277101735386680764176071790128604879805537724858321928470, 0, 0, 1, 0⟩
theorem s3_109_edges : next config 3 s3_109 = [s4_489] := by decide
theorem s3_109_safe : Safe 10 3 s3_109 := by
  apply safe_succ 9 3 s3_109 [s4_489] (by decide) s3_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_489_safe
def s3_110 : State := ⟨[1,4,67,193], 12554203470773361528011861213336271295870999681174937338134, 0, 0, 1, 0⟩
theorem s3_110_edges : next config 3 s3_110 = [s4_490] := by decide
theorem s3_110_safe : Safe 10 3 s3_110 := by
  apply safe_succ 9 3 s3_110 [s4_490] (by decide) s3_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_490_safe
def s3_111 : State := ⟨[1,4,67,194], 25108406941546723055683440059751604128112604058250425467158, 0, 0, 1, 0⟩
theorem s3_111_edges : next config 3 s3_111 = [s4_491, s4_135] := by decide
theorem s3_111_safe : Safe 10 3 s3_111 := by
  apply safe_succ 9 3 s3_111 [s4_491, s4_135] (by decide) s3_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_491_safe
  · subst z; exact s4_135_safe
def s3_112 : State := ⟨[1,4,67,195], 50216813883093446111026597752582269792485132347959144415510, 0, 0, 1, 0⟩
theorem s3_112_edges : next config 3 s3_112 = [s4_492] := by decide
theorem s3_112_safe : Safe 10 3 s3_112 := by
  apply safe_succ 9 3 s3_112 [s4_492] (by decide) s3_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_492_safe
def s3_113 : State := ⟨[1,4,67,195], 50216813883093446111026597752582269792522025836106563518742, 0, 0, 1, 0⟩
theorem s3_113_edges : next config 3 s3_113 = [s4_493] := by decide
theorem s3_113_safe : Safe 10 3 s3_113 := by
  apply safe_succ 9 3 s3_113 [s4_493] (by decide) s3_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_493_safe
def s3_114 : State := ⟨[1,4,68,145], 44602511244162009098462140263768275674005782, 0, 0, 1, 0⟩
theorem s3_114_edges : next config 3 s3_114 = [] := by decide
theorem s3_114_safe : Safe 10 3 s3_114 := by
  apply safe_succ 9 3 s3_114 [] (by decide) s3_114_edges
  simp
def s3_115 : State := ⟨[1,4,68,145], 66902575877958790363070931787201773643563286, 0, 0, 1, 0⟩
theorem s3_115_edges : next config 3 s3_115 = [] := by decide
theorem s3_115_safe : Safe 10 3 s3_115 := by
  apply safe_succ 9 3 s3_115 [] (by decide) s3_115_edges
  simp
def s3_116 : State := ⟨[1,4,68,146], 89204682205957097258460503558279862222389526, 0, 0, 1, 0⟩
theorem s3_116_edges : next config 3 s3_116 = [s4_400, s4_137] := by decide
theorem s3_116_safe : Safe 10 3 s3_116 := by
  apply safe_succ 9 3 s3_116 [s4_400, s4_137] (by decide) s3_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_400_safe
  · subst z; exact s4_137_safe
def s3_117 : State := ⟨[1,4,68,146], 111504066275020036646142368332498496655524118, 0, 0, 1, 0⟩
theorem s3_117_edges : next config 3 s3_117 = [s4_401, s4_138] := by decide
theorem s3_117_safe : Safe 10 3 s3_117 := by
  apply safe_succ 9 3 s3_117 [s4_401, s4_138] (by decide) s3_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_401_safe
  · subst z; exact s4_138_safe
def s3_118 : State := ⟨[1,4,80,128], 340282366920939672407640966138947506454, 2, 2, 0, 0⟩
theorem s3_118_edges : next config 3 s3_118 = [s4_847, s4_154, s4_139, s4_141, s4_149, s4_140, s4_142, s4_145, s4_147] := by decide
theorem s3_118_safe : Safe 10 3 s3_118 := by
  apply safe_succ 9 3 s3_118 [s4_847, s4_154, s4_139, s4_141, s4_149, s4_140, s4_142, s4_145, s4_147] (by decide) s3_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_847_safe
  · subst z; exact s4_154_safe
  · subst z; exact s4_139_safe
  · subst z; exact s4_141_safe
  · subst z; exact s4_149_safe
  · subst z; exact s4_140_safe
  · subst z; exact s4_142_safe
  · subst z; exact s4_145_safe
  · subst z; exact s4_147_safe
def s3_119 : State := ⟨[1,4,80,140], 1399581375145819901433804026725569833009430, 0, 0, 1, 0⟩
theorem s3_119_edges : next config 3 s3_119 = [s4_158] := by decide
theorem s3_119_safe : Safe 10 3 s3_119 := by
  apply safe_succ 9 3 s3_119 [s4_158] (by decide) s3_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_158_safe
def s3_120 : State := ⟨[1,4,80,140], 1481249143206845132665013932509194203758870, 0, 0, 1, 0⟩
theorem s3_120_edges : next config 3 s3_120 = [s4_160] := by decide
theorem s3_120_safe : Safe 10 3 s3_120 := by
  apply safe_succ 9 3 s3_120 [s4_160] (by decide) s3_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_160_safe
def s3_121 : State := ⟨[1,4,80,145], 44602511244162009099670770935477725495886102, 0, 0, 1, 0⟩
theorem s3_121_edges : next config 3 s3_121 = [s4_494, s4_162] := by decide
theorem s3_121_safe : Safe 10 3 s3_121 := by
  apply safe_succ 9 3 s3_121 [s4_494, s4_162] (by decide) s3_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_494_safe
  · subst z; exact s4_162_safe
def s3_122 : State := ⟨[1,4,80,145], 66902575877958790364279562458911223465443606, 0, 0, 1, 0⟩
theorem s3_122_edges : next config 3 s3_122 = [s4_495, s4_164] := by decide
theorem s3_122_safe : Safe 10 3 s3_122 := by
  apply safe_succ 9 3 s3_122 [s4_495, s4_164] (by decide) s3_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_495_safe
  · subst z; exact s4_164_safe
def s3_123 : State := ⟨[1,4,80,210], 1645504557321206042154970883969185109676262126772975729368957206, 0, 0, 1, 0⟩
theorem s3_123_edges : next config 3 s3_123 = [s4_689, s4_496, s4_150] := by decide
theorem s3_123_safe : Safe 10 3 s3_123 := by
  apply safe_succ 9 3 s3_123 [s4_689, s4_496, s4_150] (by decide) s3_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_689_safe
  · subst z; exact s4_496_safe
  · subst z; exact s4_150_safe
def s3_124 : State := ⟨[1,4,80,210], 2056880696651507552693711818479055052168092239682940968133263638, 0, 0, 1, 0⟩
theorem s3_124_edges : next config 3 s3_124 = [s4_690, s4_497, s4_151] := by decide
theorem s3_124_safe : Safe 10 3 s3_124 := by
  apply safe_succ 9 3 s3_124 [s4_690, s4_497, s4_151] (by decide) s3_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_690_safe
  · subst z; exact s4_497_safe
  · subst z; exact s4_151_safe
def s3_125 : State := ⟨[1,4,82,129], 1020847100762820226185636001184846250262, 0, 0, 1, 0⟩
theorem s3_125_edges : next config 3 s3_125 = [s4_606, s4_498, s4_169, s4_161] := by decide
theorem s3_125_safe : Safe 10 3 s3_125 := by
  apply safe_succ 9 3 s3_125 [s4_606, s4_498, s4_169, s4_161] (by decide) s3_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_606_safe
  · subst z; exact s4_498_safe
  · subst z; exact s4_169_safe
  · subst z; exact s4_161_safe
def s3_126 : State := ⟨[1,4,82,129], 1020847100762821435037668639519182749974, 0, 0, 1, 0⟩
theorem s3_126_edges : next config 3 s3_126 = [s4_607, s4_499, s4_170, s4_162] := by decide
theorem s3_126_safe : Safe 10 3 s3_126 := by
  apply safe_succ 9 3 s3_126 [s4_607, s4_499, s4_170, s4_162] (by decide) s3_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_607_safe
  · subst z; exact s4_499_safe
  · subst z; exact s4_170_safe
  · subst z; exact s4_162_safe
def s3_127 : State := ⟨[1,4,82,130], 1701411834604697153112385216048382673174, 0, 0, 1, 0⟩
theorem s3_127_edges : next config 3 s3_127 = [s4_608, s4_500, s4_171] := by decide
theorem s3_127_safe : Safe 10 3 s3_127 := by
  apply safe_succ 9 3 s3_127 [s4_608, s4_500, s4_171] (by decide) s3_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_608_safe
  · subst z; exact s4_500_safe
  · subst z; exact s4_171_safe
def s3_128 : State := ⟨[1,4,82,130], 1701411834604698361964417854382719172886, 0, 0, 1, 0⟩
theorem s3_128_edges : next config 3 s3_128 = [s4_609, s4_501, s4_172] := by decide
theorem s3_128_safe : Safe 10 3 s3_128 := by
  apply safe_succ 9 3 s3_128 [s4_609, s4_501, s4_172] (by decide) s3_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_609_safe
  · subst z; exact s4_501_safe
  · subst z; exact s4_172_safe
def s3_129 : State := ⟨[1,4,82,132], 5784800237655958714672880505229601210646, 0, 0, 1, 0⟩
theorem s3_129_edges : next config 3 s3_129 = [s4_610, s4_502, s4_173, s4_396, s4_165, s4_157] := by decide
theorem s3_129_safe : Safe 10 3 s3_129 := by
  apply safe_succ 9 3 s3_129 [s4_610, s4_502, s4_173, s4_396, s4_165, s4_157] (by decide) s3_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_610_safe
  · subst z; exact s4_502_safe
  · subst z; exact s4_173_safe
  · subst z; exact s4_396_safe
  · subst z; exact s4_165_safe
  · subst z; exact s4_157_safe
def s3_130 : State := ⟨[1,4,82,132], 5784800237655959923524913143563937710358, 0, 0, 1, 0⟩
theorem s3_130_edges : next config 3 s3_130 = [s4_611, s4_503, s4_174, s4_397, s4_166, s4_158] := by decide
theorem s3_130_safe : Safe 10 3 s3_130 := by
  apply safe_succ 9 3 s3_130 [s4_611, s4_503, s4_174, s4_397, s4_166, s4_158] (by decide) s3_130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_611_safe
  · subst z; exact s4_503_safe
  · subst z; exact s4_174_safe
  · subst z; exact s4_397_safe
  · subst z; exact s4_166_safe
  · subst z; exact s4_158_safe
def s3_131 : State := ⟨[1,4,82,136], 87452568298681189945882786288853971960086, 0, 0, 1, 0⟩
theorem s3_131_edges : next config 3 s3_131 = [s4_612, s4_667, s4_504, s4_175, s4_159] := by decide
theorem s3_131_safe : Safe 10 3 s3_131 := by
  apply safe_succ 9 3 s3_131 [s4_612, s4_667, s4_504, s4_175, s4_159] (by decide) s3_131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_612_safe
  · subst z; exact s4_667_safe
  · subst z; exact s4_504_safe
  · subst z; exact s4_175_safe
  · subst z; exact s4_159_safe
def s3_132 : State := ⟨[1,4,82,136], 87452568298681191154734818927188308459798, 0, 0, 1, 0⟩
theorem s3_132_edges : next config 3 s3_132 = [s4_613, s4_668, s4_505, s4_176, s4_160] := by decide
theorem s3_132_safe : Safe 10 3 s3_132 := by
  apply safe_succ 9 3 s3_132 [s4_613, s4_668, s4_505, s4_176, s4_160] (by decide) s3_132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_613_safe
  · subst z; exact s4_668_safe
  · subst z; exact s4_505_safe
  · subst z; exact s4_176_safe
  · subst z; exact s4_160_safe
def s3_133 : State := ⟨[1,4,82,144], 22301085480897544084834977159434682815807766, 0, 0, 1, 0⟩
theorem s3_133_edges : next config 3 s3_133 = [s4_614, s4_508, s4_177, s4_163] := by decide
theorem s3_133_safe : Safe 10 3 s3_133 := by
  apply safe_succ 9 3 s3_133 [s4_614, s4_508, s4_177, s4_163] (by decide) s3_133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_614_safe
  · subst z; exact s4_508_safe
  · subst z; exact s4_177_safe
  · subst z; exact s4_163_safe
def s3_134 : State := ⟨[1,4,82,144], 22301085480897544086043829192073017152307478, 0, 0, 1, 0⟩
theorem s3_134_edges : next config 3 s3_134 = [s4_615, s4_509, s4_178, s4_164] := by decide
theorem s3_134_safe : Safe 10 3 s3_134 := by
  apply safe_succ 9 3 s3_134 [s4_615, s4_509, s4_178, s4_164] (by decide) s3_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_615_safe
  · subst z; exact s4_509_safe
  · subst z; exact s4_178_safe
  · subst z; exact s4_164_safe
def s3_135 : State := ⟨[1,4,82,160], 1461501637671185285124628131975169805977242370326, 0, 0, 1, 0⟩
theorem s3_135_edges : next config 3 s3_135 = [s4_616, s4_510, s4_179] := by decide
theorem s3_135_safe : Safe 10 3 s3_135 := by
  apply safe_succ 9 3 s3_135 [s4_616, s4_510, s4_179] (by decide) s3_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_616_safe
  · subst z; exact s4_510_safe
  · subst z; exact s4_179_safe
def s3_136 : State := ⟨[1,4,82,160], 1461501637671185285124629340827202444311578870038, 0, 0, 1, 0⟩
theorem s3_136_edges : next config 3 s3_136 = [s4_617, s4_511, s4_180] := by decide
theorem s3_136_safe : Safe 10 3 s3_136 := by
  apply safe_succ 9 3 s3_136 [s4_617, s4_511, s4_180] (by decide) s3_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_617_safe
  · subst z; exact s4_511_safe
  · subst z; exact s4_180_safe
def s3_137 : State := ⟨[1,4,82,192], 6277101735386680764176071790128609715361242230785344340246, 0, 0, 1, 0⟩
theorem s3_137_edges : next config 3 s3_137 = [s4_618, s4_512, s4_181] := by decide
theorem s3_137_safe : Safe 10 3 s3_137 := by
  apply safe_succ 9 3 s3_137 [s4_618, s4_512, s4_181] (by decide) s3_137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_618_safe
  · subst z; exact s4_512_safe
  · subst z; exact s4_181_safe
def s3_138 : State := ⟨[1,4,82,192], 6277101735386680764176071790128610924213274869119680839958, 0, 0, 1, 0⟩
theorem s3_138_edges : next config 3 s3_138 = [s4_619, s4_513, s4_182] := by decide
theorem s3_138_safe : Safe 10 3 s3_138 := by
  apply safe_succ 9 3 s3_138 [s4_619, s4_513, s4_182] (by decide) s3_138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_619_safe
  · subst z; exact s4_513_safe
  · subst z; exact s4_182_safe
def s3_139 : State := ⟨[1,4,82,194], 25108406941546723055683440059751608963668308564177447878934, 0, 0, 1, 0⟩
theorem s3_139_edges : next config 3 s3_139 = [s4_620, s4_514, s4_183] := by decide
theorem s3_139_safe : Safe 10 3 s3_139 := by
  apply safe_succ 9 3 s3_139 [s4_620, s4_514, s4_183] (by decide) s3_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_620_safe
  · subst z; exact s4_514_safe
  · subst z; exact s4_183_safe
def s3_140 : State := ⟨[1,4,82,208], 411376139330301510538742635921704547190192077327819621483479318, 0, 0, 1, 0⟩
theorem s3_140_edges : next config 3 s3_140 = [s4_621, s4_515, s4_184] := by decide
theorem s3_140_safe : Safe 10 3 s3_140 := by
  apply safe_succ 9 3 s3_140 [s4_621, s4_515, s4_184] (by decide) s3_140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_621_safe
  · subst z; exact s4_515_safe
  · subst z; exact s4_184_safe
def s3_141 : State := ⟨[1,4,82,210], 1645504557321206042154969522839717425926035124520366184658436374, 0, 0, 1, 0⟩
theorem s3_141_edges : next config 3 s3_141 = [s4_622, s4_691, s4_516, s4_185, s4_167] := by decide
theorem s3_141_safe : Safe 10 3 s3_141 := by
  apply safe_succ 9 3 s3_141 [s4_622, s4_691, s4_516, s4_185, s4_167] (by decide) s3_141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_622_safe
  · subst z; exact s4_691_safe
  · subst z; exact s4_516_safe
  · subst z; exact s4_185_safe
  · subst z; exact s4_167_safe
def s3_142 : State := ⟨[1,4,82,210], 1645504557321206042154969522839717425927243976553004518994936086, 0, 0, 1, 0⟩
theorem s3_142_edges : next config 3 s3_142 = [s4_623, s4_692, s4_517, s4_186, s4_168] := by decide
theorem s3_142_safe : Safe 10 3 s3_142 := by
  apply safe_succ 9 3 s3_142 [s4_623, s4_692, s4_517, s4_186, s4_168] (by decide) s3_142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_623_safe
  · subst z; exact s4_692_safe
  · subst z; exact s4_517_safe
  · subst z; exact s4_186_safe
  · subst z; exact s4_168_safe
def s3_143 : State := ⟨[1,4,86,128], 340282366921020670511342122588491022614, 0, 0, 0, 0⟩
theorem s3_143_edges : next config 3 s3_143 = [s4_853, s4_169, s4_173, s4_187, s4_171, s4_175, s4_177, s4_179] := by decide
theorem s3_143_safe : Safe 10 3 s3_143 := by
  apply safe_succ 9 3 s3_143 [s4_853, s4_169, s4_173, s4_187, s4_171, s4_175, s4_177, s4_179] (by decide) s3_143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_853_safe
  · subst z; exact s4_169_safe
  · subst z; exact s4_173_safe
  · subst z; exact s4_187_safe
  · subst z; exact s4_171_safe
  · subst z; exact s4_175_safe
  · subst z; exact s4_177_safe
  · subst z; exact s4_179_safe
def s3_144 : State := ⟨[1,4,86,128], 340282366921021879363374760922827522326, 0, 0, 0, 0⟩
theorem s3_144_edges : next config 3 s3_144 = [s4_854, s4_170, s4_174, s4_188, s4_172, s4_176, s4_178, s4_180] := by decide
theorem s3_144_safe : Safe 10 3 s3_144 := by
  apply safe_succ 9 3 s3_144 [s4_854, s4_170, s4_174, s4_188, s4_172, s4_176, s4_178, s4_180] (by decide) s3_144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_854_safe
  · subst z; exact s4_170_safe
  · subst z; exact s4_174_safe
  · subst z; exact s4_188_safe
  · subst z; exact s4_172_safe
  · subst z; exact s4_176_safe
  · subst z; exact s4_178_safe
  · subst z; exact s4_180_safe
def s3_145 : State := ⟨[1,4,96,128], 340282367000166625996085689103316746526, 1, 1, 0, 0⟩
theorem s3_145_edges : next config 3 s3_145 = [s4_855, s4_626, s4_518, s4_297, s4_313, s4_189, s4_207, s4_278, s4_197, s4_215, s4_227, s4_238] := by decide
theorem s3_145_safe : Safe 10 3 s3_145 := by
  apply safe_succ 9 3 s3_145 [s4_855, s4_626, s4_518, s4_297, s4_313, s4_189, s4_207, s4_278, s4_197, s4_215, s4_227, s4_238] (by decide) s3_145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_855_safe
  · subst z; exact s4_626_safe
  · subst z; exact s4_518_safe
  · subst z; exact s4_297_safe
  · subst z; exact s4_313_safe
  · subst z; exact s4_189_safe
  · subst z; exact s4_207_safe
  · subst z; exact s4_278_safe
  · subst z; exact s4_197_safe
  · subst z; exact s4_215_safe
  · subst z; exact s4_227_safe
  · subst z; exact s4_238_safe
def s3_146 : State := ⟨[1,4,96,128], 340282367000166625996085689103316747030, 1, 1, 0, 0⟩
theorem s3_146_edges : next config 3 s3_146 = [s4_856, s4_314, s4_190, s4_208, s4_279, s4_198, s4_216, s4_228, s4_239] := by decide
theorem s3_146_safe : Safe 10 3 s3_146 := by
  apply safe_succ 9 3 s3_146 [s4_856, s4_314, s4_190, s4_208, s4_279, s4_198, s4_216, s4_228, s4_239] (by decide) s3_146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_856_safe
  · subst z; exact s4_314_safe
  · subst z; exact s4_190_safe
  · subst z; exact s4_208_safe
  · subst z; exact s4_279_safe
  · subst z; exact s4_198_safe
  · subst z; exact s4_216_safe
  · subst z; exact s4_228_safe
  · subst z; exact s4_239_safe
def s3_147 : State := ⟨[1,4,96,128], 340282367000166625996085689103316750614, 2, 2, 0, 0⟩
theorem s3_147_edges : next config 3 s3_147 = [s4_1173, s4_729, s4_857, s4_956, s4_290, s4_315, s4_366, s4_191, s4_209, s4_280, s4_199, s4_217, s4_229, s4_240] := by decide
theorem s3_147_safe : Safe 10 3 s3_147 := by
  apply safe_succ 9 3 s3_147 [s4_1173, s4_729, s4_857, s4_956, s4_290, s4_315, s4_366, s4_191, s4_209, s4_280, s4_199, s4_217, s4_229, s4_240] (by decide) s3_147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1173_safe
  · subst z; exact s4_729_safe
  · subst z; exact s4_857_safe
  · subst z; exact s4_956_safe
  · subst z; exact s4_290_safe
  · subst z; exact s4_315_safe
  · subst z; exact s4_366_safe
  · subst z; exact s4_191_safe
  · subst z; exact s4_209_safe
  · subst z; exact s4_280_safe
  · subst z; exact s4_199_safe
  · subst z; exact s4_217_safe
  · subst z; exact s4_229_safe
  · subst z; exact s4_240_safe
def s3_148 : State := ⟨[1,4,96,128], 340282367000166625996085689111906681110, 1, 1, 0, 0⟩
theorem s3_148_edges : next config 3 s3_148 = [s4_859, s4_519, s4_316, s4_192, s4_210, s4_281, s4_200, s4_218, s4_230, s4_241] := by decide
theorem s3_148_safe : Safe 10 3 s3_148 := by
  apply safe_succ 9 3 s3_148 [s4_859, s4_519, s4_316, s4_192, s4_210, s4_281, s4_200, s4_218, s4_230, s4_241] (by decide) s3_148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_859_safe
  · subst z; exact s4_519_safe
  · subst z; exact s4_316_safe
  · subst z; exact s4_192_safe
  · subst z; exact s4_210_safe
  · subst z; exact s4_281_safe
  · subst z; exact s4_200_safe
  · subst z; exact s4_218_safe
  · subst z; exact s4_230_safe
  · subst z; exact s4_241_safe
def s3_149 : State := ⟨[1,4,96,128], 340282367000166626032979177250735849750, 1, 1, 0, 0⟩
theorem s3_149_edges : next config 3 s3_149 = [s4_860, s4_627, s4_520, s4_298, s4_317, s4_193, s4_211, s4_282, s4_201, s4_219, s4_231, s4_242] := by decide
theorem s3_149_safe : Safe 10 3 s3_149 := by
  apply safe_succ 9 3 s3_149 [s4_860, s4_627, s4_520, s4_298, s4_317, s4_193, s4_211, s4_282, s4_201, s4_219, s4_231, s4_242] (by decide) s3_149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_860_safe
  · subst z; exact s4_627_safe
  · subst z; exact s4_520_safe
  · subst z; exact s4_298_safe
  · subst z; exact s4_317_safe
  · subst z; exact s4_193_safe
  · subst z; exact s4_211_safe
  · subst z; exact s4_282_safe
  · subst z; exact s4_201_safe
  · subst z; exact s4_219_safe
  · subst z; exact s4_231_safe
  · subst z; exact s4_242_safe
def s3_150 : State := ⟨[1,4,96,128], 340282367000166626291233594282669572374, 2, 2, 0, 0⟩
theorem s3_150_edges : next config 3 s3_150 = [s4_861, s4_318, s4_194, s4_212, s4_283, s4_202, s4_220, s4_232, s4_243] := by decide
theorem s3_150_safe : Safe 10 3 s3_150 := by
  apply safe_succ 9 3 s3_150 [s4_861, s4_318, s4_194, s4_212, s4_283, s4_202, s4_220, s4_232, s4_243] (by decide) s3_150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_861_safe
  · subst z; exact s4_318_safe
  · subst z; exact s4_194_safe
  · subst z; exact s4_212_safe
  · subst z; exact s4_283_safe
  · subst z; exact s4_202_safe
  · subst z; exact s4_220_safe
  · subst z; exact s4_232_safe
  · subst z; exact s4_243_safe
def s3_151 : State := ⟨[1,4,96,128], 340282367158622951024614364290404647190, 1, 1, 0, 0⟩
theorem s3_151_edges : next config 3 s3_151 = [s4_862, s4_521, s4_319, s4_195, s4_213, s4_284, s4_203, s4_221, s4_233, s4_244] := by decide
theorem s3_151_safe : Safe 10 3 s3_151 := by
  apply safe_succ 9 3 s3_151 [s4_862, s4_521, s4_319, s4_195, s4_213, s4_284, s4_203, s4_221, s4_233, s4_244] (by decide) s3_151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_862_safe
  · subst z; exact s4_521_safe
  · subst z; exact s4_319_safe
  · subst z; exact s4_195_safe
  · subst z; exact s4_213_safe
  · subst z; exact s4_284_safe
  · subst z; exact s4_203_safe
  · subst z; exact s4_221_safe
  · subst z; exact s4_233_safe
  · subst z; exact s4_244_safe
def s3_152 : State := ⟨[1,4,96,128], 340282368267817226224315090600019951894, 2, 2, 0, 0⟩
theorem s3_152_edges : next config 3 s3_152 = [s4_730, s4_863, s4_320, s4_196, s4_214, s4_285, s4_204, s4_222, s4_234, s4_245] := by decide
theorem s3_152_safe : Safe 10 3 s3_152 := by
  apply safe_succ 9 3 s3_152 [s4_730, s4_863, s4_320, s4_196, s4_214, s4_285, s4_204, s4_222, s4_234, s4_245] (by decide) s3_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_730_safe
  · subst z; exact s4_863_safe
  · subst z; exact s4_320_safe
  · subst z; exact s4_196_safe
  · subst z; exact s4_214_safe
  · subst z; exact s4_285_safe
  · subst z; exact s4_204_safe
  · subst z; exact s4_222_safe
  · subst z; exact s4_234_safe
  · subst z; exact s4_245_safe
def s3_153 : State := ⟨[1,4,96,131], 3743106036209551260629831763420998861078, 0, 0, 1, 0⟩
theorem s3_153_edges : next config 3 s3_153 = [s4_628, s4_522, s4_299, s4_322, s4_250] := by decide
theorem s3_153_safe : Safe 10 3 s3_153 := by
  apply safe_succ 9 3 s3_153 [s4_628, s4_522, s4_299, s4_322, s4_250] (by decide) s3_153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_628_safe
  · subst z; exact s4_522_safe
  · subst z; exact s4_299_safe
  · subst z; exact s4_322_safe
  · subst z; exact s4_250_safe
def s3_154 : State := ⟨[1,4,96,131], 4423670770051428187556580978284535283990, 0, 0, 1, 0⟩
theorem s3_154_edges : next config 3 s3_154 = [s4_629, s4_523, s4_300, s4_323, s4_251] := by decide
theorem s3_154_safe : Safe 10 3 s3_154 := by
  apply safe_succ 9 3 s3_154 [s4_629, s4_523, s4_300, s4_323, s4_251] (by decide) s3_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_629_safe
  · subst z; exact s4_523_safe
  · subst z; exact s4_300_safe
  · subst z; exact s4_323_safe
  · subst z; exact s4_251_safe
def s3_155 : State := ⟨[1,4,96,137], 175245418964362536846170633909032177434902, 0, 0, 1, 0⟩
theorem s3_155_edges : next config 3 s3_155 = [s4_324] := by decide
theorem s3_155_safe : Safe 10 3 s3_155 := by
  apply safe_succ 9 3 s3_155 [s4_324] (by decide) s3_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_324_safe
def s3_156 : State := ⟨[1,4,96,137], 261677140162280906565867784196701303144726, 0, 0, 1, 0⟩
theorem s3_156_edges : next config 3 s3_156 = [s4_325] := by decide
theorem s3_156_safe : Safe 10 3 s3_156 := by
  apply safe_succ 9 3 s3_156 [s4_325] (by decide) s3_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_325_safe
def s3_157 : State := ⟨[1,4,96,140], 1399581375145899128387392471448534202253590, 0, 0, 1, 0⟩
theorem s3_157_edges : next config 3 s3_157 = [s4_1174, s4_731, s4_957, s4_291, s4_326, s4_367] := by decide
theorem s3_157_safe : Safe 10 3 s3_157 := by
  apply safe_succ 9 3 s3_157 [s4_1174, s4_731, s4_957, s4_291, s4_326, s4_367] (by decide) s3_157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1174_safe
  · subst z; exact s4_731_safe
  · subst z; exact s4_957_safe
  · subst z; exact s4_291_safe
  · subst z; exact s4_326_safe
  · subst z; exact s4_367_safe
def s3_158 : State := ⟨[1,4,96,140], 1481249143206924359618602377232158573003030, 0, 0, 1, 0⟩
theorem s3_158_edges : next config 3 s3_158 = [s4_1175, s4_732, s4_958, s4_292, s4_327, s4_368] := by decide
theorem s3_158_safe : Safe 10 3 s3_158 := by
  apply safe_succ 9 3 s3_158 [s4_1175, s4_732, s4_958, s4_292, s4_327, s4_368] (by decide) s3_158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1175_safe
  · subst z; exact s4_732_safe
  · subst z; exact s4_958_safe
  · subst z; exact s4_292_safe
  · subst z; exact s4_327_safe
  · subst z; exact s4_368_safe
def s3_159 : State := ⟨[1,4,96,145], 44602511244162088326624359380200689865130262, 0, 0, 1, 0⟩
theorem s3_159_edges : next config 3 s3_159 = [s4_1176, s4_733, s4_816, s4_959, s4_630, s4_524, s4_293, s4_301, s4_409, s4_328, s4_369] := by decide
theorem s3_159_safe : Safe 10 3 s3_159 := by
  apply safe_succ 9 3 s3_159 [s4_1176, s4_733, s4_816, s4_959, s4_630, s4_524, s4_293, s4_301, s4_409, s4_328, s4_369] (by decide) s3_159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1176_safe
  · subst z; exact s4_733_safe
  · subst z; exact s4_816_safe
  · subst z; exact s4_959_safe
  · subst z; exact s4_630_safe
  · subst z; exact s4_524_safe
  · subst z; exact s4_293_safe
  · subst z; exact s4_301_safe
  · subst z; exact s4_409_safe
  · subst z; exact s4_328_safe
  · subst z; exact s4_369_safe
def s3_160 : State := ⟨[1,4,96,145], 66902575877958869591233150903634187834687766, 0, 0, 1, 0⟩
theorem s3_160_edges : next config 3 s3_160 = [s4_1177, s4_734, s4_817, s4_960, s4_631, s4_525, s4_294, s4_302, s4_410, s4_329, s4_370] := by decide
theorem s3_160_safe : Safe 10 3 s3_160 := by
  apply safe_succ 9 3 s3_160 [s4_1177, s4_734, s4_817, s4_960, s4_631, s4_525, s4_294, s4_302, s4_410, s4_329, s4_370] (by decide) s3_160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1177_safe
  · subst z; exact s4_734_safe
  · subst z; exact s4_817_safe
  · subst z; exact s4_960_safe
  · subst z; exact s4_631_safe
  · subst z; exact s4_525_safe
  · subst z; exact s4_294_safe
  · subst z; exact s4_302_safe
  · subst z; exact s4_410_safe
  · subst z; exact s4_329_safe
  · subst z; exact s4_370_safe
def s3_161 : State := ⟨[1,4,96,146], 89204682205957176486622722674712276413514006, 0, 0, 1, 0⟩
theorem s3_161_edges : next config 3 s3_161 = [s4_735, s4_632, s4_672, s4_526, s4_303, s4_330, s4_236] := by decide
theorem s3_161_safe : Safe 10 3 s3_161 := by
  apply safe_succ 9 3 s3_161 [s4_735, s4_632, s4_672, s4_526, s4_303, s4_330, s4_236] (by decide) s3_161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_735_safe
  · subst z; exact s4_632_safe
  · subst z; exact s4_672_safe
  · subst z; exact s4_526_safe
  · subst z; exact s4_303_safe
  · subst z; exact s4_330_safe
  · subst z; exact s4_236_safe
def s3_162 : State := ⟨[1,4,96,146], 111504066275020115874304587448930910846648598, 0, 0, 1, 0⟩
theorem s3_162_edges : next config 3 s3_162 = [s4_736, s4_633, s4_673, s4_527, s4_304, s4_331, s4_237] := by decide
theorem s3_162_safe : Safe 10 3 s3_162 := by
  apply safe_succ 9 3 s3_162 [s4_736, s4_633, s4_673, s4_527, s4_304, s4_331, s4_237] (by decide) s3_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_736_safe
  · subst z; exact s4_633_safe
  · subst z; exact s4_673_safe
  · subst z; exact s4_527_safe
  · subst z; exact s4_304_safe
  · subst z; exact s4_331_safe
  · subst z; exact s4_237_safe
def s3_163 : State := ⟨[1,4,96,161], 2923003275682652937249413218355400943278718255382, 0, 0, 1, 0⟩
theorem s3_163_edges : next config 3 s3_163 = [s4_528, s4_332, s4_252] := by decide
theorem s3_163_safe : Safe 10 3 s3_163 := by
  apply safe_succ 9 3 s3_163 [s4_528, s4_332, s4_252] (by decide) s3_163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_528_safe
  · subst z; exact s4_332_safe
  · subst z; exact s4_252_safe
def s3_164 : State := ⟨[1,4,96,161], 4384504912332991121611221124144934748071114375446, 0, 0, 1, 0⟩
theorem s3_164_edges : next config 3 s3_164 = [s4_529, s4_333, s4_253] := by decide
theorem s3_164_safe : Safe 10 3 s3_164 := by
  apply safe_succ 9 3 s3_164 [s4_529, s4_333, s4_253] (by decide) s3_164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_529_safe
  · subst z; exact s4_333_safe
  · subst z; exact s4_253_safe
def s3_165 : State := ⟨[1,4,96,162], 5846006551025023507498659810714716197454119764246, 0, 0, 1, 0⟩
theorem s3_165_edges : next config 3 s3_165 = [s4_1178, s4_1223, s4_737, s4_818, s4_634, s4_530, s4_295, s4_305, s4_388, s4_334, s4_254, s4_269, s4_256] := by decide
theorem s3_165_safe : Safe 10 3 s3_165 := by
  apply safe_succ 9 3 s3_165 [s4_1178, s4_1223, s4_737, s4_818, s4_634, s4_530, s4_295, s4_305, s4_388, s4_334, s4_254, s4_269, s4_256] (by decide) s3_165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1178_safe
  · subst z; exact s4_1223_safe
  · subst z; exact s4_737_safe
  · subst z; exact s4_818_safe
  · subst z; exact s4_634_safe
  · subst z; exact s4_530_safe
  · subst z; exact s4_295_safe
  · subst z; exact s4_305_safe
  · subst z; exact s4_388_safe
  · subst z; exact s4_334_safe
  · subst z; exact s4_254_safe
  · subst z; exact s4_269_safe
  · subst z; exact s4_256_safe
def s3_166 : State := ⟨[1,4,96,162], 7307508186994796958018590789577500787382979461398, 0, 0, 1, 0⟩
theorem s3_166_edges : next config 3 s3_166 = [s4_1179, s4_1224, s4_738, s4_819, s4_635, s4_531, s4_296, s4_306, s4_389, s4_335, s4_255, s4_270, s4_257] := by decide
theorem s3_166_safe : Safe 10 3 s3_166 := by
  apply safe_succ 9 3 s3_166 [s4_1179, s4_1224, s4_738, s4_819, s4_635, s4_531, s4_296, s4_306, s4_389, s4_335, s4_255, s4_270, s4_257] (by decide) s3_166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1179_safe
  · subst z; exact s4_1224_safe
  · subst z; exact s4_738_safe
  · subst z; exact s4_819_safe
  · subst z; exact s4_635_safe
  · subst z; exact s4_531_safe
  · subst z; exact s4_296_safe
  · subst z; exact s4_306_safe
  · subst z; exact s4_389_safe
  · subst z; exact s4_335_safe
  · subst z; exact s4_255_safe
  · subst z; exact s4_270_safe
  · subst z; exact s4_257_safe
def s3_167 : State := ⟨[1,4,96,176], 95780971326419139128294312505056038334508659959202070, 0, 0, 1, 0⟩
theorem s3_167_edges : next config 3 s3_167 = [s4_741, s4_636, s4_532, s4_307, s4_336] := by decide
theorem s3_167_safe : Safe 10 3 s3_167 := by
  apply safe_succ 9 3 s3_167 [s4_741, s4_636, s4_532, s4_307, s4_336] (by decide) s3_167_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_741_safe
  · subst z; exact s4_636_safe
  · subst z; exact s4_532_safe
  · subst z; exact s4_307_safe
  · subst z; exact s4_336_safe
def s3_168 : State := ⟨[1,4,96,176], 95782432805755724832681893048353036344879954385764630, 0, 0, 1, 0⟩
theorem s3_168_edges : next config 3 s3_168 = [s4_742, s4_637, s4_533, s4_308, s4_337] := by decide
theorem s3_168_safe : Safe 10 3 s3_168 := by
  apply safe_succ 9 3 s3_168 [s4_742, s4_637, s4_533, s4_308, s4_337] (by decide) s3_168_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_742_safe
  · subst z; exact s4_637_safe
  · subst z; exact s4_533_safe
  · subst z; exact s4_308_safe
  · subst z; exact s4_337_safe
def s3_169 : State := ⟨[1,4,96,193], 12554203470773361528692425947257376385127545792894922195222, 0, 0, 1, 0⟩
theorem s3_169_edges : next config 3 s3_169 = [s4_638, s4_534, s4_309, s4_338] := by decide
theorem s3_169_safe : Safe 10 3 s3_169 := by
  apply safe_succ 9 3 s3_169 [s4_638, s4_534, s4_309, s4_338] (by decide) s3_169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_638_safe
  · subst z; exact s4_534_safe
  · subst z; exact s4_309_safe
  · subst z; exact s4_338_safe
def s3_170 : State := ⟨[1,4,96,193], 18831305206160042291847650636623165874303152022495420285206, 0, 0, 1, 0⟩
theorem s3_170_edges : next config 3 s3_170 = [s4_639, s4_535, s4_310, s4_339] := by decide
theorem s3_170_safe : Safe 10 3 s3_170 := by
  apply safe_succ 9 3 s3_170 [s4_639, s4_535, s4_310, s4_339] (by decide) s3_170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_639_safe
  · subst z; exact s4_535_safe
  · subst z; exact s4_310_safe
  · subst z; exact s4_339_safe
def s3_171 : State := ⟨[1,4,96,194], 25108406941546723057044569527514586144259005896686527643926, 0, 0, 1, 0⟩
theorem s3_171_edges : next config 3 s3_171 = [s4_640, s4_536, s4_311, s4_383, s4_340, s4_371, s4_248, s4_274] := by decide
theorem s3_171_safe : Safe 10 3 s3_171 := by
  apply safe_succ 9 3 s3_171 [s4_640, s4_536, s4_311, s4_383, s4_340, s4_371, s4_248, s4_274] (by decide) s3_171_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_640_safe
  · subst z; exact s4_536_safe
  · subst z; exact s4_311_safe
  · subst z; exact s4_383_safe
  · subst z; exact s4_340_safe
  · subst z; exact s4_371_safe
  · subst z; exact s4_248_safe
  · subst z; exact s4_274_safe
def s3_172 : State := ⟨[1,4,96,194], 31385508676933403819519229483038498706507862911423489310998, 0, 0, 1, 0⟩
theorem s3_172_edges : next config 3 s3_172 = [s4_641, s4_537, s4_312, s4_384, s4_341, s4_372, s4_249, s4_275] := by decide
theorem s3_172_safe : Safe 10 3 s3_172 := by
  apply safe_succ 9 3 s3_172 [s4_641, s4_537, s4_312, s4_384, s4_341, s4_372, s4_249, s4_275] (by decide) s3_172_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_641_safe
  · subst z; exact s4_537_safe
  · subst z; exact s4_312_safe
  · subst z; exact s4_384_safe
  · subst z; exact s4_341_safe
  · subst z; exact s4_372_safe
  · subst z; exact s4_249_safe
  · subst z; exact s4_275_safe
def s3_173 : State := ⟨[1,4,96,196], 100433627766186892227157431009057844699047766519436160336150, 0, 0, 1, 0⟩
theorem s3_173_edges : next config 3 s3_173 = [s4_342] := by decide
theorem s3_173_safe : Safe 10 3 s3_173 := by
  apply safe_succ 9 3 s3_173 [s4_342] (by decide) s3_173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_342_safe
def s3_174 : State := ⟨[1,4,96,196], 106710729501573572985548702561530495699736128244991903465750, 0, 0, 1, 0⟩
theorem s3_174_edges : next config 3 s3_174 = [s4_343] := by decide
theorem s3_174_safe : Safe 10 3 s3_174 := by
  apply safe_succ 9 3 s3_174 [s4_343] (by decide) s3_174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_343_safe
def s3_175 : State := ⟨[1,4,96,208], 411376139330301510561043381120235249553845680766732430659879190, 0, 0, 1, 0⟩
theorem s3_175_edges : next config 3 s3_175 = [s4_538, s4_344, s4_276] := by decide
theorem s3_175_safe : Safe 10 3 s3_175 := by
  apply safe_succ 9 3 s3_175 [s4_538, s4_344, s4_276] (by decide) s3_175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_538_safe
  · subst z; exact s4_344_safe
  · subst z; exact s4_276_safe
def s3_176 : State := ⟨[1,4,96,208], 411382416432036897219506471711127834078726064849528533188411670, 0, 0, 1, 0⟩
theorem s3_176_edges : next config 3 s3_176 = [s4_539, s4_345, s4_277] := by decide
theorem s3_176_safe : Safe 10 3 s3_176 := by
  apply safe_succ 9 3 s3_176 [s4_539, s4_345, s4_277] (by decide) s3_176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_539_safe
  · subst z; exact s4_345_safe
  · subst z; exact s4_277_safe
def s3_177 : State := ⟨[1,4,96,225], 53919893334301279589334030175060108448116332398003979866174073667862, 0, 0, 1, 0⟩
theorem s3_177_edges : next config 3 s3_177 = [s4_540, s4_346] := by decide
theorem s3_177_safe : Safe 10 3 s3_177 := by
  apply safe_succ 9 3 s3_177 [s4_540, s4_346] (by decide) s3_177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_540_safe
  · subst z; exact s4_346_safe
def s3_178 : State := ⟨[1,4,96,225], 80879840001451919384001045261399174387911599893617803132414147494166, 0, 0, 1, 0⟩
theorem s3_178_edges : next config 3 s3_178 = [s4_541, s4_347] := by decide
theorem s3_178_safe : Safe 10 3 s3_178 := by
  apply safe_succ 9 3 s3_178 [s4_541, s4_347] (by decide) s3_178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_541_safe
  · subst z; exact s4_347_safe
def s3_179 : State := ⟨[1,4,96,228], 431359146674410236714672241398098891015929492802059239105669372117270, 0, 0, 1, 0⟩
theorem s3_179_edges : next config 3 s3_179 = [s4_743, s4_348] := by decide
theorem s3_179_safe : Safe 10 3 s3_179 := by
  apply safe_succ 9 3 s3_179 [s4_743, s4_348] (by decide) s3_179_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_743_safe
  · subst z; exact s4_348_safe
def s3_180 : State := ⟨[1,4,96,228], 458319093341560876509339256479674003818831621809185817867864690983190, 0, 0, 1, 0⟩
theorem s3_180_edges : next config 3 s3_180 = [s4_744, s4_349] := by decide
theorem s3_180_safe : Safe 10 3 s3_180 := by
  apply safe_succ 9 3 s3_180 [s4_744, s4_349] (by decide) s3_180_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_744_safe
  · subst z; exact s4_349_safe
def s3_181 : State := ⟨[1,4,96,240], 1766847064778384329583297500765219601308381520183780672479943666115346710, 0, 0, 1, 0⟩
theorem s3_181_edges : next config 3 s3_181 = [s4_542, s4_352] := by decide
theorem s3_181_safe : Safe 10 3 s3_181 := by
  apply safe_succ 9 3 s3_181 [s4_542, s4_352] (by decide) s3_181_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_542_safe
  · subst z; exact s4_352_safe
def s3_182 : State := ⟨[1,4,96,240], 1766874024725051480223092167758005875740524534186667494779776408219615510, 0, 0, 1, 0⟩
theorem s3_182_edges : next config 3 s3_182 = [s4_543, s4_353] := by decide
theorem s3_182_safe : Safe 10 3 s3_182 := by
  apply safe_succ 9 3 s3_182 [s4_543, s4_353] (by decide) s3_182_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_543_safe
  · subst z; exact s4_353_safe
def s3_183 : State := ⟨[1,4,97,129], 1020847101000499877951363579153941070102, 0, 0, 1, 0⟩
theorem s3_183_edges : next config 3 s3_183 = [s4_544, s4_293] := by decide
theorem s3_183_safe : Safe 10 3 s3_183 := by
  apply safe_succ 9 3 s3_183 [s4_544, s4_293] (by decide) s3_183_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_544_safe
  · subst z; exact s4_293_safe
def s3_184 : State := ⟨[1,4,97,130], 1701411834842376804878112794017477493014, 0, 0, 1, 0⟩
theorem s3_184_edges : next config 3 s3_184 = [s4_545, s4_295] := by decide
theorem s3_184_safe : Safe 10 3 s3_184 := by
  apply safe_succ 9 3 s3_184 [s4_545, s4_295] (by decide) s3_184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_545_safe
  · subst z; exact s4_295_safe
def s3_185 : State := ⟨[1,4,97,132], 5784800237893638366438608083198696030486, 0, 0, 1, 0⟩
theorem s3_185_edges : next config 3 s3_185 = [s4_546, s4_291] := by decide
theorem s3_185_safe : Safe 10 3 s3_185 := by
  apply safe_succ 9 3 s3_185 [s4_546, s4_291] (by decide) s3_185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_546_safe
  · subst z; exact s4_291_safe
def s3_186 : State := ⟨[1,4,97,136], 87452568298918869597648513866823066779926, 0, 0, 1, 0⟩
theorem s3_186_edges : next config 3 s3_186 = [s4_669, s4_547, s4_292] := by decide
theorem s3_186_safe : Safe 10 3 s3_186 := by
  apply safe_succ 9 3 s3_186 [s4_669, s4_547, s4_292] (by decide) s3_186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_669_safe
  · subst z; exact s4_547_safe
  · subst z; exact s4_292_safe
def s3_187 : State := ⟨[1,4,97,144], 22301085480897781764486742887012651910627606, 0, 0, 1, 0⟩
theorem s3_187_edges : next config 3 s3_187 = [s4_549, s4_294] := by decide
theorem s3_187_safe : Safe 10 3 s3_187 := by
  apply safe_succ 9 3 s3_187 [s4_549, s4_294] (by decide) s3_187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_549_safe
  · subst z; exact s4_294_safe
def s3_188 : State := ⟨[1,4,97,160], 1461501637671185285362307783740897383946337190166, 0, 0, 1, 0⟩
theorem s3_188_edges : next config 3 s3_188 = [s4_550, s4_296] := by decide
theorem s3_188_safe : Safe 10 3 s3_188 := by
  apply safe_succ 9 3 s3_188 [s4_550, s4_296] (by decide) s3_188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_550_safe
  · subst z; exact s4_296_safe
def s3_189 : State := ⟨[1,4,97,192], 6277101735386680764176071790366289367126969808754439160086, 0, 0, 1, 0⟩
theorem s3_189_edges : next config 3 s3_189 = [s4_551] := by decide
theorem s3_189_safe : Safe 10 3 s3_189 := by
  apply safe_succ 9 3 s3_189 [s4_551] (by decide) s3_189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_551_safe
def s3_190 : State := ⟨[1,4,97,224], 26959946667150639794667015087359913040795767373565186845394014896406, 0, 0, 1, 0⟩
theorem s3_190_edges : next config 3 s3_190 = [s4_552] := by decide
theorem s3_190_safe : Safe 10 3 s3_190 := by
  apply safe_succ 9 3 s3_190 [s4_552] (by decide) s3_190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_552_safe
def s3_191 : State := ⟨[1,4,97,225], 53919893334301279589334030174379543714432911796105759326497625145622, 0, 0, 1, 0⟩
theorem s3_191_edges : next config 3 s3_191 = [s4_553] := by decide
theorem s3_191_safe : Safe 10 3 s3_191 := by
  apply safe_succ 9 3 s3_191 [s4_553] (by decide) s3_191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_553_safe
def s3_192 : State := ⟨[1,4,100,129], 1020847102109694153151064305463556374806, 0, 0, 1, 0⟩
theorem s3_192_edges : next config 3 s3_192 = [s4_745, s4_299, s4_301] := by decide
theorem s3_192_safe : Safe 10 3 s3_192 := by
  apply safe_succ 9 3 s3_192 [s4_745, s4_299, s4_301] (by decide) s3_192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_745_safe
  · subst z; exact s4_299_safe
  · subst z; exact s4_301_safe
def s3_193 : State := ⟨[1,4,100,130], 1701411835951571080077813520327092797718, 0, 0, 1, 0⟩
theorem s3_193_edges : next config 3 s3_193 = [s4_1206, s4_746, s4_300, s4_303, s4_305] := by decide
theorem s3_193_safe : Safe 10 3 s3_193 := by
  apply safe_succ 9 3 s3_193 [s4_1206, s4_746, s4_300, s4_303, s4_305] (by decide) s3_193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_1206_safe
  · subst z; exact s4_746_safe
  · subst z; exact s4_300_safe
  · subst z; exact s4_303_safe
  · subst z; exact s4_305_safe
def s3_194 : State := ⟨[1,4,100,132], 5784800239002832641638308809508311335190, 0, 0, 1, 0⟩
theorem s3_194_edges : next config 3 s3_194 = [s4_748] := by decide
theorem s3_194_safe : Safe 10 3 s3_194 := by
  apply safe_succ 9 3 s3_194 [s4_748] (by decide) s3_194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_748_safe
def s3_195 : State := ⟨[1,4,100,136], 87452568300028063872848214593132682084630, 0, 0, 1, 0⟩
theorem s3_195_edges : next config 3 s3_195 = [s4_749] := by decide
theorem s3_195_safe : Safe 10 3 s3_195 := by
  apply safe_succ 9 3 s3_195 [s4_749] (by decide) s3_195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_749_safe
def s3_196 : State := ⟨[1,4,100,144], 22301085480898890958761942587738961525932310, 0, 0, 1, 0⟩
theorem s3_196_edges : next config 3 s3_196 = [s4_750, s4_302, s4_304, s4_307] := by decide
theorem s3_196_safe : Safe 10 3 s3_196 := by
  apply safe_succ 9 3 s3_196 [s4_750, s4_302, s4_304, s4_307] (by decide) s3_196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_750_safe
  · subst z; exact s4_302_safe
  · subst z; exact s4_304_safe
  · subst z; exact s4_307_safe
def s3_197 : State := ⟨[1,4,100,160], 1461501637671185286471502058940598110255952494870, 0, 0, 1, 0⟩
theorem s3_197_edges : next config 3 s3_197 = [s4_751, s4_306, s4_308] := by decide
theorem s3_197_safe : Safe 10 3 s3_197 := by
  apply safe_succ 9 3 s3_197 [s4_751, s4_306, s4_308] (by decide) s3_197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_751_safe
  · subst z; exact s4_306_safe
  · subst z; exact s4_308_safe
def s3_198 : State := ⟨[1,4,100,192], 6277101735386680764176071791475483642326670535064054464790, 0, 0, 1, 0⟩
theorem s3_198_edges : next config 3 s3_198 = [s4_1244, s4_752, s4_310, s4_312] := by decide
theorem s3_198_safe : Safe 10 3 s3_198 := by
  apply safe_succ 9 3 s3_198 [s4_1244, s4_752, s4_310, s4_312] (by decide) s3_198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1244_safe
  · subst z; exact s4_752_safe
  · subst z; exact s4_310_safe
  · subst z; exact s4_312_safe
def s3_199 : State := ⟨[1,4,100,224], 26959946667150639794667015087359913041904961648764887571703630201110, 0, 0, 1, 0⟩
theorem s3_199_edges : next config 3 s3_199 = [s4_753] := by decide
theorem s3_199_safe : Safe 10 3 s3_199 := by
  apply safe_succ 9 3 s3_199 [s4_753] (by decide) s3_199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_753_safe
def s3_200 : State := ⟨[1,4,100,228], 431359146674410236714672241392654373146462127986873474788257783939350, 0, 0, 1, 0⟩
theorem s3_200_edges : next config 3 s3_200 = [s4_754] := by decide
theorem s3_200_safe : Safe 10 3 s3_200 := by
  apply safe_succ 9 3 s3_200 [s4_754] (by decide) s3_200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_754_safe
def s3_201 : State := ⟨[1,4,104,129], 1020847121124453156574505327914104455446, 0, 0, 1, 0⟩
theorem s3_201_edges : next config 3 s3_201 = [s4_755, s4_820, s4_963, s4_652, s4_554, s4_356, s4_373, s4_322, s4_324, s4_328, s4_332] := by decide
theorem s3_201_safe : Safe 10 3 s3_201 := by
  apply safe_succ 9 3 s3_201 [s4_755, s4_820, s4_963, s4_652, s4_554, s4_356, s4_373, s4_322, s4_324, s4_328, s4_332] (by decide) s3_201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_755_safe
  · subst z; exact s4_820_safe
  · subst z; exact s4_963_safe
  · subst z; exact s4_652_safe
  · subst z; exact s4_554_safe
  · subst z; exact s4_356_safe
  · subst z; exact s4_373_safe
  · subst z; exact s4_322_safe
  · subst z; exact s4_324_safe
  · subst z; exact s4_328_safe
  · subst z; exact s4_332_safe
def s3_202 : State := ⟨[1,4,104,130], 1701411854966330083501254542777640878358, 0, 0, 1, 0⟩
theorem s3_202_edges : next config 3 s3_202 = [s4_1207, s4_756, s4_821, s4_964, s4_653, s4_555, s4_357, s4_374, s4_323, s4_330, s4_334] := by decide
theorem s3_202_safe : Safe 10 3 s3_202 := by
  apply safe_succ 9 3 s3_202 [s4_1207, s4_756, s4_821, s4_964, s4_653, s4_555, s4_357, s4_374, s4_323, s4_330, s4_334] (by decide) s3_202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1207_safe
  · subst z; exact s4_756_safe
  · subst z; exact s4_821_safe
  · subst z; exact s4_964_safe
  · subst z; exact s4_653_safe
  · subst z; exact s4_555_safe
  · subst z; exact s4_357_safe
  · subst z; exact s4_374_safe
  · subst z; exact s4_323_safe
  · subst z; exact s4_330_safe
  · subst z; exact s4_334_safe
def s3_203 : State := ⟨[1,4,104,132], 5784800258017591645061749831958859415830, 0, 0, 1, 0⟩
theorem s3_203_edges : next config 3 s3_203 = [s4_758, s4_822, s4_965, s4_654, s4_556, s4_358, s4_407, s4_375, s4_350, s4_326] := by decide
theorem s3_203_safe : Safe 10 3 s3_203 := by
  apply safe_succ 9 3 s3_203 [s4_758, s4_822, s4_965, s4_654, s4_556, s4_358, s4_407, s4_375, s4_350, s4_326] (by decide) s3_203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_758_safe
  · subst z; exact s4_822_safe
  · subst z; exact s4_965_safe
  · subst z; exact s4_654_safe
  · subst z; exact s4_556_safe
  · subst z; exact s4_358_safe
  · subst z; exact s4_407_safe
  · subst z; exact s4_375_safe
  · subst z; exact s4_350_safe
  · subst z; exact s4_326_safe
def s3_204 : State := ⟨[1,4,104,136], 87452568319042822876271655615583230165270, 0, 0, 1, 0⟩
theorem s3_204_edges : next config 3 s3_204 = [s4_1212, s4_759, s4_823, s4_966, s4_655, s4_670, s4_557, s4_359, s4_376, s4_325, s4_327] := by decide
theorem s3_204_safe : Safe 10 3 s3_204 := by
  apply safe_succ 9 3 s3_204 [s4_1212, s4_759, s4_823, s4_966, s4_655, s4_670, s4_557, s4_359, s4_376, s4_325, s4_327] (by decide) s3_204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1212_safe
  · subst z; exact s4_759_safe
  · subst z; exact s4_823_safe
  · subst z; exact s4_966_safe
  · subst z; exact s4_655_safe
  · subst z; exact s4_670_safe
  · subst z; exact s4_557_safe
  · subst z; exact s4_359_safe
  · subst z; exact s4_376_safe
  · subst z; exact s4_325_safe
  · subst z; exact s4_327_safe
def s3_205 : State := ⟨[1,4,104,144], 22301085480917905717765366028761412074012950, 0, 0, 1, 0⟩
theorem s3_205_edges : next config 3 s3_205 = [s4_760, s4_825, s4_967, s4_656, s4_559, s4_360, s4_411, s4_377, s4_329, s4_354, s4_331, s4_336] := by decide
theorem s3_205_safe : Safe 10 3 s3_205 := by
  apply safe_succ 9 3 s3_205 [s4_760, s4_825, s4_967, s4_656, s4_559, s4_360, s4_411, s4_377, s4_329, s4_354, s4_331, s4_336] (by decide) s3_205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_760_safe
  · subst z; exact s4_825_safe
  · subst z; exact s4_967_safe
  · subst z; exact s4_656_safe
  · subst z; exact s4_559_safe
  · subst z; exact s4_360_safe
  · subst z; exact s4_411_safe
  · subst z; exact s4_377_safe
  · subst z; exact s4_329_safe
  · subst z; exact s4_354_safe
  · subst z; exact s4_331_safe
  · subst z; exact s4_336_safe
def s3_206 : State := ⟨[1,4,104,160], 1461501637671185305486261062364039132706500575510, 0, 0, 1, 0⟩
theorem s3_206_edges : next config 3 s3_206 = [s4_1216, s4_761, s4_826, s4_968, s4_657, s4_560, s4_361, s4_378, s4_333, s4_335, s4_337] := by decide
theorem s3_206_safe : Safe 10 3 s3_206 := by
  apply safe_succ 9 3 s3_206 [s4_1216, s4_761, s4_826, s4_968, s4_657, s4_560, s4_361, s4_378, s4_333, s4_335, s4_337] (by decide) s3_206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1216_safe
  · subst z; exact s4_761_safe
  · subst z; exact s4_826_safe
  · subst z; exact s4_968_safe
  · subst z; exact s4_657_safe
  · subst z; exact s4_560_safe
  · subst z; exact s4_361_safe
  · subst z; exact s4_378_safe
  · subst z; exact s4_333_safe
  · subst z; exact s4_335_safe
  · subst z; exact s4_337_safe
def s3_207 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645750111557514602545430, 0, 0, 1, 0⟩
theorem s3_207_edges : next config 3 s3_207 = [s4_1245, s4_762, s4_827, s4_970, s4_658, s4_676, s4_561, s4_362, s4_379, s4_339, s4_343, s4_341, s4_345] := by decide
theorem s3_207_safe : Safe 10 3 s3_207 := by
  apply safe_succ 9 3 s3_207 [s4_1245, s4_762, s4_827, s4_970, s4_658, s4_676, s4_561, s4_362, s4_379, s4_339, s4_343, s4_341, s4_345] (by decide) s3_207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1245_safe
  · subst z; exact s4_762_safe
  · subst z; exact s4_827_safe
  · subst z; exact s4_970_safe
  · subst z; exact s4_658_safe
  · subst z; exact s4_676_safe
  · subst z; exact s4_561_safe
  · subst z; exact s4_362_safe
  · subst z; exact s4_379_safe
  · subst z; exact s4_339_safe
  · subst z; exact s4_343_safe
  · subst z; exact s4_341_safe
  · subst z; exact s4_345_safe
def s3_208 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652188328594154178281750, 0, 0, 1, 0⟩
theorem s3_208_edges : next config 3 s3_208 = [s4_1248, s4_763, s4_828, s4_971, s4_659, s4_699, s4_562, s4_363, s4_380, s4_347, s4_349, s4_353] := by decide
theorem s3_208_safe : Safe 10 3 s3_208 := by
  apply safe_succ 9 3 s3_208 [s4_1248, s4_763, s4_828, s4_971, s4_659, s4_699, s4_562, s4_363, s4_380, s4_347, s4_349, s4_353] (by decide) s3_208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1248_safe
  · subst z; exact s4_763_safe
  · subst z; exact s4_828_safe
  · subst z; exact s4_971_safe
  · subst z; exact s4_659_safe
  · subst z; exact s4_699_safe
  · subst z; exact s4_562_safe
  · subst z; exact s4_363_safe
  · subst z; exact s4_380_safe
  · subst z; exact s4_347_safe
  · subst z; exact s4_349_safe
  · subst z; exact s4_353_safe
def s3_209 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791831830, 0, 0, 1, 0⟩
theorem s3_209_edges : next config 3 s3_209 = [s4_764, s4_829, s4_972, s4_660, s4_700, s4_563, s4_364, s4_381, s4_351, s4_355] := by decide
theorem s3_209_safe : Safe 10 3 s3_209 := by
  apply safe_succ 9 3 s3_209 [s4_764, s4_829, s4_972, s4_660, s4_700, s4_563, s4_364, s4_381, s4_351, s4_355] (by decide) s3_209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_764_safe
  · subst z; exact s4_829_safe
  · subst z; exact s4_972_safe
  · subst z; exact s4_660_safe
  · subst z; exact s4_700_safe
  · subst z; exact s4_563_safe
  · subst z; exact s4_364_safe
  · subst z; exact s4_381_safe
  · subst z; exact s4_351_safe
  · subst z; exact s4_355_safe
def s3_210 : State := ⟨[1,4,108,128], 340282711801129888074482896206588608790, 0, 0, 0, 0⟩
theorem s3_210_edges : next config 3 s3_210 = [s4_765, s4_867, s4_356, s4_358, s4_365, s4_357, s4_359, s4_360, s4_361] := by decide
theorem s3_210_safe : Safe 10 3 s3_210 := by
  apply safe_succ 9 3 s3_210 [s4_765, s4_867, s4_356, s4_358, s4_365, s4_357, s4_359, s4_360, s4_361] (by decide) s3_210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_765_safe
  · subst z; exact s4_867_safe
  · subst z; exact s4_356_safe
  · subst z; exact s4_358_safe
  · subst z; exact s4_365_safe
  · subst z; exact s4_357_safe
  · subst z; exact s4_359_safe
  · subst z; exact s4_360_safe
  · subst z; exact s4_361_safe
def s3_211 : State := ⟨[1,4,112,129], 1020852293138902087750463434463182389526, 0, 0, 1, 0⟩
theorem s3_211_edges : next config 3 s3_211 = [s4_564, s4_369] := by decide
theorem s3_211_safe : Safe 10 3 s3_211 := by
  apply safe_succ 9 3 s3_211 [s4_564, s4_369] (by decide) s3_211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_564_safe
  · subst z; exact s4_369_safe
def s3_212 : State := ⟨[1,4,112,130], 1701417026980779014677212649326718812438, 0, 0, 1, 0⟩
theorem s3_212_edges : next config 3 s3_212 = [s4_565] := by decide
theorem s3_212_safe : Safe 10 3 s3_212 := by
  apply safe_succ 9 3 s3_212 [s4_565] (by decide) s3_212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_565_safe
def s3_213 : State := ⟨[1,4,112,132], 5784805430032040576237707938507937349910, 0, 0, 1, 0⟩
theorem s3_213_edges : next config 3 s3_213 = [s4_566, s4_367] := by decide
theorem s3_213_safe : Safe 10 3 s3_213 := by
  apply safe_succ 9 3 s3_213 [s4_566, s4_367] (by decide) s3_213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_566_safe
  · subst z; exact s4_367_safe
def s3_214 : State := ⟨[1,4,112,136], 87452573491057271807447613722132308099350, 0, 0, 1, 0⟩
theorem s3_214_edges : next config 3 s3_214 = [s4_671, s4_567, s4_368] := by decide
theorem s3_214_safe : Safe 10 3 s3_214 := by
  apply safe_succ 9 3 s3_214 [s4_671, s4_567, s4_368] (by decide) s3_214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_671_safe
  · subst z; exact s4_567_safe
  · subst z; exact s4_368_safe
def s3_215 : State := ⟨[1,4,112,144], 22301085486089920166696541986867961151947030, 0, 0, 1, 0⟩
theorem s3_215_edges : next config 3 s3_215 = [s4_569, s4_370] := by decide
theorem s3_215_safe : Safe 10 3 s3_215 := by
  apply safe_succ 9 3 s3_215 [s4_569, s4_370] (by decide) s3_215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_569_safe
  · subst z; exact s4_370_safe
def s3_216 : State := ⟨[1,4,112,160], 1461501637671190477500709993539997239255578509590, 0, 0, 1, 0⟩
theorem s3_216_edges : next config 3 s3_216 = [s4_570] := by decide
theorem s3_216_safe : Safe 10 3 s3_216 := by
  apply safe_succ 9 3 s3_216 [s4_570] (by decide) s3_216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_570_safe
def s3_217 : State := ⟨[1,4,112,192], 6277101735386680764176076982504691576926069664063680479510, 0, 0, 1, 0⟩
theorem s3_217_edges : next config 3 s3_217 = [s4_571, s4_372] := by decide
theorem s3_217_safe : Safe 10 3 s3_217 := by
  apply safe_succ 9 3 s3_217 [s4_571, s4_372] (by decide) s3_217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_571_safe
  · subst z; exact s4_372_safe
def s3_218 : State := ⟨[1,4,112,224], 26959946667150639794667015087359918232934169583364286700703256215830, 0, 0, 1, 0⟩
theorem s3_218_edges : next config 3 s3_218 = [s4_572] := by decide
theorem s3_218_safe : Safe 10 3 s3_218 := by
  apply safe_succ 9 3 s3_218 [s4_572] (by decide) s3_218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_572_safe
def s3_219 : State := ⟨[1,4,112,240], 1766847064778384329583297500742918856115043193900779781835825800938586390, 0, 0, 1, 0⟩
theorem s3_219_edges : next config 3 s3_219 = [s4_573] := by decide
theorem s3_219_safe : Safe 10 3 s3_219 := by
  apply safe_succ 9 3 s3_219 [s4_573] (by decide) s3_219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_573_safe
def s3_220 : State := ⟨[1,4,120,128], 341611615278361145520659920110848377110, 0, 0, 0, 0⟩
theorem s3_220_edges : next config 3 s3_220 = [s4_870, s4_373, s4_375, s4_382, s4_374, s4_376, s4_377, s4_378] := by decide
theorem s3_220_safe : Safe 10 3 s3_220 := by
  apply safe_succ 9 3 s3_220 [s4_870, s4_373, s4_375, s4_382, s4_374, s4_376, s4_377, s4_378] (by decide) s3_220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_870_safe
  · subst z; exact s4_373_safe
  · subst z; exact s4_375_safe
  · subst z; exact s4_382_safe
  · subst z; exact s4_374_safe
  · subst z; exact s4_376_safe
  · subst z; exact s4_377_safe
  · subst z; exact s4_378_safe
def s3_221 : State := ⟨[1,4,193,145], 12554203470773406130182823008424431294049826752024390205718, 0, 0, 1, 0⟩
theorem s3_221_edges : next config 3 s3_221 = [s4_574] := by decide
theorem s3_221_safe : Safe 10 3 s3_221 := by
  apply safe_succ 9 3 s3_221 [s4_574] (by decide) s3_221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_574_safe
def s3_222 : State := ⟨[1,4,194,146], 25108406941546812260025363649927924124617832152539007615254, 0, 0, 1, 0⟩
theorem s3_222_edges : next config 3 s3_222 = [s4_575] := by decide
theorem s3_222_safe : Safe 10 3 s3_222 := by
  apply safe_succ 9 3 s3_222 [s4_575] (by decide) s3_222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_575_safe
def s3_223 : State := ⟨[1,4,194,162], 25108406947392729606368181200250097312609873637716713865494, 0, 0, 1, 0⟩
theorem s3_223_edges : next config 3 s3_223 = [s4_576, s4_248, s4_386] := by decide
theorem s3_223_safe : Safe 10 3 s3_223 := by
  apply safe_succ 9 3 s3_223 [s4_576, s4_248, s4_386] (by decide) s3_223_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_576_safe
  · subst z; exact s4_248_safe
  · subst z; exact s4_386_safe
def s3_224 : State := ⟨[1,4,208,145], 411376139330301510605644871517296416608754603047691560127889686, 0, 0, 1, 0⟩
theorem s3_224_edges : next config 3 s3_224 = [s4_577, s4_393] := by decide
theorem s3_224_safe : Safe 10 3 s3_224 := by
  apply safe_succ 9 3 s3_224 [s4_577, s4_393] (by decide) s3_224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_577_safe
  · subst z; exact s4_393_safe
def s3_225 : State := ⟨[1,4,209,145], 822752278660603021122087102522837261589829777932653027995484438, 0, 0, 1, 0⟩
theorem s3_225_edges : next config 3 s3_225 = [s4_578] := by decide
theorem s3_225_safe : Safe 10 3 s3_225 := by
  apply safe_succ 9 3 s3_225 [s4_578] (by decide) s3_225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_578_safe
def s3_226 : State := ⟨[1,4,209,145], 822752278660603021144387167156634042854438569456086525965041942, 0, 0, 1, 0⟩
theorem s3_226_edges : next config 3 s3_226 = [s4_579] := by decide
theorem s3_226_safe : Safe 10 3 s3_226 := by
  apply safe_succ 9 3 s3_226 [s4_579] (by decide) s3_226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_579_safe
def s3_227 : State := ⟨[1,4,210,130], 1645504557321206042154970883969185109676262126772975729368957206, 0, 0, 1, 0⟩
theorem s3_227_edges : next config 3 s3_227 = [s4_693, s4_580, s4_394] := by decide
theorem s3_227_safe : Safe 10 3 s3_227 := by
  apply safe_succ 9 3 s3_227 [s4_693, s4_580, s4_394] (by decide) s3_227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_693_safe
  · subst z; exact s4_580_safe
  · subst z; exact s4_394_safe
def s3_228 : State := ⟨[1,4,210,130], 1645529665728147588878026227126877940340717610375138956332302614, 0, 0, 1, 0⟩
theorem s3_228_edges : next config 3 s3_228 = [s4_694, s4_581, s4_395] := by decide
theorem s3_228_safe : Safe 10 3 s3_228 := by
  apply safe_succ 9 3 s3_228 [s4_694, s4_581, s4_395] (by decide) s3_228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_694_safe
  · subst z; exact s4_581_safe
  · subst z; exact s4_395_safe
def s3_229 : State := ⟨[1,4,210,144], 1645504557321206042177270268038248049062735139514556029465592086, 0, 0, 1, 0⟩
theorem s3_229_edges : next config 3 s3_229 = [s4_695, s4_582, s4_398, s4_392] := by decide
theorem s3_229_safe : Safe 10 3 s3_229 := by
  apply safe_succ 9 3 s3_229 [s4_695, s4_582, s4_398, s4_392] (by decide) s3_229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_695_safe
  · subst z; exact s4_582_safe
  · subst z; exact s4_398_safe
  · subst z; exact s4_392_safe
def s3_230 : State := ⟨[1,4,210,144], 2056880696651507552716012563677585675308419032135974700464537878, 0, 0, 1, 0⟩
theorem s3_230_edges : next config 3 s3_230 = [s4_696, s4_583, s4_399, s4_393] := by decide
theorem s3_230_safe : Safe 10 3 s3_230 := by
  apply safe_succ 9 3 s3_230 [s4_696, s4_583, s4_399, s4_393] (by decide) s3_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_696_safe
  · subst z; exact s4_583_safe
  · subst z; exact s4_399_safe
  · subst z; exact s4_393_safe
def s3_231 : State := ⟨[1,4,210,146], 1645504557321206042244173864763307602241196074043954546218172694, 0, 0, 1, 0⟩
theorem s3_231_edges : next config 3 s3_231 = [s4_697, s4_584, s4_402] := by decide
theorem s3_231_safe : Safe 10 3 s3_231 := by
  apply safe_succ 9 3 s3_231 [s4_697, s4_584, s4_402] (by decide) s3_231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_697_safe
  · subst z; exact s4_584_safe
  · subst z; exact s4_402_safe
def s3_232 : State := ⟨[1,4,210,146], 1645504557321206042266473248832370541628877938818173180651307286, 0, 0, 1, 0⟩
theorem s3_232_edges : next config 3 s3_232 = [s4_698, s4_585, s4_403] := by decide
theorem s3_232_safe : Safe 10 3 s3_232 := by
  apply safe_succ 9 3 s3_232 [s4_698, s4_585, s4_403] (by decide) s3_232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_698_safe
  · subst z; exact s4_585_safe
  · subst z; exact s4_403_safe
def s3_233 : State := ⟨[1,4,225,129], 53919893334301279589334030175060108448116332398003979866174073667862, 0, 0, 1, 0⟩
theorem s3_233_edges : next config 3 s3_233 = [s4_586, s4_406] := by decide
theorem s3_233_safe : Safe 10 3 s3_233 := by
  apply safe_succ 9 3 s3_233 [s4_586, s4_406] (by decide) s3_233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_586_safe
  · subst z; exact s4_406_safe
def s3_234 : State := ⟨[1,4,228,132], 431359146674410236714672241398098891015929492802059239105669372117270, 0, 0, 1, 0⟩
theorem s3_234_edges : next config 3 s3_234 = [s4_766] := by decide
theorem s3_234_safe : Safe 10 3 s3_234 := by
  apply safe_succ 9 3 s3_234 [s4_766] (by decide) s3_234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_766_safe
def s3_235 : State := ⟨[1,4,240,144], 1766847064778384329583297500765219601308381520183780672479943666115346710, 0, 0, 1, 0⟩
theorem s3_235_edges : next config 3 s3_235 = [s4_587, s4_408] := by decide
theorem s3_235_safe : Safe 10 3 s3_235 := by
  apply safe_succ 9 3 s3_235 [s4_587, s4_408] (by decide) s3_235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_587_safe
  · subst z; exact s4_408_safe
def s3_236 : State := ⟨[1,12,64,128], 340282366920938463481821351509772800286, 3, 1, 0, 0⟩
theorem s3_236_edges : next config 3 s3_236 = [s4_873, s4_0, s4_518, s4_412, s4_426, s4_444, s4_415, s4_423, s4_429, s4_433] := by decide
theorem s3_236_safe : Safe 10 3 s3_236 := by
  apply safe_succ 9 3 s3_236 [s4_873, s4_0, s4_518, s4_412, s4_426, s4_444, s4_415, s4_423, s4_429, s4_433] (by decide) s3_236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_873_safe
  · subst z; exact s4_0_safe
  · subst z; exact s4_518_safe
  · subst z; exact s4_412_safe
  · subst z; exact s4_426_safe
  · subst z; exact s4_444_safe
  · subst z; exact s4_415_safe
  · subst z; exact s4_423_safe
  · subst z; exact s4_429_safe
  · subst z; exact s4_433_safe
def s3_237 : State := ⟨[1,12,64,128], 340282366920938463481821351518362734870, 3, 1, 0, 0⟩
theorem s3_237_edges : next config 3 s3_237 = [s4_875, s4_1, s4_519, s4_413, s4_427, s4_445, s4_416, s4_424, s4_430, s4_434] := by decide
theorem s3_237_safe : Safe 10 3 s3_237 := by
  apply safe_succ 9 3 s3_237 [s4_875, s4_1, s4_519, s4_413, s4_427, s4_445, s4_416, s4_424, s4_430, s4_434] (by decide) s3_237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_875_safe
  · subst z; exact s4_1_safe
  · subst z; exact s4_519_safe
  · subst z; exact s4_413_safe
  · subst z; exact s4_427_safe
  · subst z; exact s4_445_safe
  · subst z; exact s4_416_safe
  · subst z; exact s4_424_safe
  · subst z; exact s4_430_safe
  · subst z; exact s4_434_safe
def s3_238 : State := ⟨[1,12,64,128], 340282366920938463518714839657191903510, 3, 1, 0, 0⟩
theorem s3_238_edges : next config 3 s3_238 = [s4_876, s4_2, s4_520, s4_414, s4_428, s4_446, s4_417, s4_425, s4_431, s4_435] := by decide
theorem s3_238_safe : Safe 10 3 s3_238 := by
  apply safe_succ 9 3 s3_238 [s4_876, s4_2, s4_520, s4_414, s4_428, s4_446, s4_417, s4_425, s4_431, s4_435] (by decide) s3_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_876_safe
  · subst z; exact s4_2_safe
  · subst z; exact s4_520_safe
  · subst z; exact s4_414_safe
  · subst z; exact s4_428_safe
  · subst z; exact s4_446_safe
  · subst z; exact s4_417_safe
  · subst z; exact s4_425_safe
  · subst z; exact s4_431_safe
  · subst z; exact s4_435_safe
def s3_239 : State := ⟨[1,12,64,131], 3743106036130323098115567425827454914838, 2, 0, 1, 0⟩
theorem s3_239_edges : next config 3 s3_239 = [s4_3, s4_522, s4_438] := by decide
theorem s3_239_safe : Safe 10 3 s3_239 := by
  apply safe_succ 9 3 s3_239 [s4_3, s4_522, s4_438] (by decide) s3_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_3_safe
  · subst z; exact s4_522_safe
  · subst z; exact s4_438_safe
def s3_240 : State := ⟨[1,12,64,131], 4423670769972200025042316640690991337750, 2, 0, 1, 0⟩
theorem s3_240_edges : next config 3 s3_240 = [s4_4, s4_523, s4_439] := by decide
theorem s3_240_safe : Safe 10 3 s3_240 := by
  apply safe_succ 9 3 s3_240 [s4_4, s4_523, s4_439] (by decide) s3_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_4_safe
  · subst z; exact s4_523_safe
  · subst z; exact s4_439_safe
def s3_241 : State := ⟨[1,12,64,145], 44602511244162009098461845115863096321184022, 2, 0, 1, 0⟩
theorem s3_241_edges : next config 3 s3_241 = [s4_1136, s4_767, s4_973, s4_13, s4_455, s4_578, s4_463, s4_494, s4_524] := by decide
theorem s3_241_safe : Safe 10 3 s3_241 := by
  apply safe_succ 9 3 s3_241 [s4_1136, s4_767, s4_973, s4_13, s4_455, s4_578, s4_463, s4_494, s4_524] (by decide) s3_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1136_safe
  · subst z; exact s4_767_safe
  · subst z; exact s4_973_safe
  · subst z; exact s4_13_safe
  · subst z; exact s4_455_safe
  · subst z; exact s4_578_safe
  · subst z; exact s4_463_safe
  · subst z; exact s4_494_safe
  · subst z; exact s4_524_safe
def s3_242 : State := ⟨[1,12,64,145], 66902575877958790363070636639296594290741526, 2, 0, 1, 0⟩
theorem s3_242_edges : next config 3 s3_242 = [s4_1137, s4_768, s4_974, s4_19, s4_456, s4_579, s4_464, s4_495, s4_525] := by decide
theorem s3_242_safe : Safe 10 3 s3_242 := by
  apply safe_succ 9 3 s3_242 [s4_1137, s4_768, s4_974, s4_19, s4_456, s4_579, s4_464, s4_495, s4_525] (by decide) s3_242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1137_safe
  · subst z; exact s4_768_safe
  · subst z; exact s4_974_safe
  · subst z; exact s4_19_safe
  · subst z; exact s4_456_safe
  · subst z; exact s4_579_safe
  · subst z; exact s4_464_safe
  · subst z; exact s4_495_safe
  · subst z; exact s4_525_safe
def s3_243 : State := ⟨[1,12,64,146], 89204682205957097258460208410374682869567766, 2, 0, 1, 0⟩
theorem s3_243_edges : next config 3 s3_243 = [s4_1138, s4_769, s4_24, s4_457, s4_584, s4_465, s4_526, s4_449] := by decide
theorem s3_243_safe : Safe 10 3 s3_243 := by
  apply safe_succ 9 3 s3_243 [s4_1138, s4_769, s4_24, s4_457, s4_584, s4_465, s4_526, s4_449] (by decide) s3_243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_1138_safe
  · subst z; exact s4_769_safe
  · subst z; exact s4_24_safe
  · subst z; exact s4_457_safe
  · subst z; exact s4_584_safe
  · subst z; exact s4_465_safe
  · subst z; exact s4_526_safe
  · subst z; exact s4_449_safe
def s3_244 : State := ⟨[1,12,64,146], 111504066275020036646142073184593317302702358, 2, 0, 1, 0⟩
theorem s3_244_edges : next config 3 s3_244 = [s4_1139, s4_770, s4_29, s4_458, s4_585, s4_466, s4_527, s4_450] := by decide
theorem s3_244_safe : Safe 10 3 s3_244 := by
  apply safe_succ 9 3 s3_244 [s4_1139, s4_770, s4_29, s4_458, s4_585, s4_466, s4_527, s4_450] (by decide) s3_244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_1139_safe
  · subst z; exact s4_770_safe
  · subst z; exact s4_29_safe
  · subst z; exact s4_458_safe
  · subst z; exact s4_585_safe
  · subst z; exact s4_466_safe
  · subst z; exact s4_527_safe
  · subst z; exact s4_450_safe
def s3_245 : State := ⟨[1,12,64,161], 2923003275682652937170185055841136605685174309142, 2, 0, 1, 0⟩
theorem s3_245_edges : next config 3 s3_245 = [s4_34, s4_528, s4_440] := by decide
theorem s3_245_safe : Safe 10 3 s3_245 := by
  apply safe_succ 9 3 s3_245 [s4_34, s4_528, s4_440] (by decide) s3_245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_34_safe
  · subst z; exact s4_528_safe
  · subst z; exact s4_440_safe
def s3_246 : State := ⟨[1,12,64,161], 4384504912332991121531992961630670410477570429206, 2, 0, 1, 0⟩
theorem s3_246_edges : next config 3 s3_246 = [s4_35, s4_529, s4_441] := by decide
theorem s3_246_safe : Safe 10 3 s3_246 := by
  apply safe_succ 9 3 s3_246 [s4_35, s4_529, s4_441] (by decide) s3_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_35_safe
  · subst z; exact s4_529_safe
  · subst z; exact s4_441_safe
def s3_247 : State := ⟨[1,12,64,162], 5846006551025023507419431648200451859860575818006, 2, 0, 1, 0⟩
theorem s3_247_edges : next config 3 s3_247 = [s4_1140, s4_1229, s4_771, s4_38, s4_459, s4_467, s4_530, s4_442] := by decide
theorem s3_247_safe : Safe 10 3 s3_247 := by
  apply safe_succ 9 3 s3_247 [s4_1140, s4_1229, s4_771, s4_38, s4_459, s4_467, s4_530, s4_442] (by decide) s3_247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_1140_safe
  · subst z; exact s4_1229_safe
  · subst z; exact s4_771_safe
  · subst z; exact s4_38_safe
  · subst z; exact s4_459_safe
  · subst z; exact s4_467_safe
  · subst z; exact s4_530_safe
  · subst z; exact s4_442_safe
def s3_248 : State := ⟨[1,12,64,162], 7307508186994796957939362627063236449789435515158, 2, 0, 1, 0⟩
theorem s3_248_edges : next config 3 s3_248 = [s4_1141, s4_1230, s4_772, s4_43, s4_460, s4_468, s4_531, s4_443] := by decide
theorem s3_248_safe : Safe 10 3 s3_248 := by
  apply safe_succ 9 3 s3_248 [s4_1141, s4_1230, s4_772, s4_43, s4_460, s4_468, s4_531, s4_443] (by decide) s3_248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_1141_safe
  · subst z; exact s4_1230_safe
  · subst z; exact s4_772_safe
  · subst z; exact s4_43_safe
  · subst z; exact s4_460_safe
  · subst z; exact s4_468_safe
  · subst z; exact s4_531_safe
  · subst z; exact s4_443_safe
def s3_249 : State := ⟨[1,12,64,176], 95780971326419139128294233276893524070171066415255830, 2, 0, 1, 0⟩
theorem s3_249_edges : next config 3 s3_249 = [s4_1142, s4_775, s4_60, s4_461, s4_469, s4_532] := by decide
theorem s3_249_safe : Safe 10 3 s3_249 := by
  apply safe_succ 9 3 s3_249 [s4_1142, s4_775, s4_60, s4_461, s4_469, s4_532] (by decide) s3_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1142_safe
  · subst z; exact s4_775_safe
  · subst z; exact s4_60_safe
  · subst z; exact s4_461_safe
  · subst z; exact s4_469_safe
  · subst z; exact s4_532_safe
def s3_250 : State := ⟨[1,12,64,176], 95782432805755724832681813820190522080542360841818390, 2, 0, 1, 0⟩
theorem s3_250_edges : next config 3 s3_250 = [s4_1143, s4_776, s4_63, s4_462, s4_470, s4_533] := by decide
theorem s3_250_safe : Safe 10 3 s3_250 := by
  apply safe_succ 9 3 s3_250 [s4_1143, s4_776, s4_63, s4_462, s4_470, s4_533] (by decide) s3_250_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1143_safe
  · subst z; exact s4_776_safe
  · subst z; exact s4_63_safe
  · subst z; exact s4_462_safe
  · subst z; exact s4_470_safe
  · subst z; exact s4_533_safe
def s3_251 : State := ⟨[1,12,64,193], 12554203470773361528692425947178148222613281455301378248982, 2, 0, 1, 0⟩
theorem s3_251_edges : next config 3 s3_251 = [s4_65, s4_534] := by decide
theorem s3_251_safe : Safe 10 3 s3_251 := by
  apply safe_succ 9 3 s3_251 [s4_65, s4_534] (by decide) s3_251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_65_safe
  · subst z; exact s4_534_safe
def s3_252 : State := ⟨[1,12,64,193], 18831305206160042291847650636543937711788887684901876338966, 2, 0, 1, 0⟩
theorem s3_252_edges : next config 3 s3_252 = [s4_66, s4_535] := by decide
theorem s3_252_safe : Safe 10 3 s3_252 := by
  apply safe_succ 9 3 s3_252 [s4_66, s4_535] (by decide) s3_252_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_66_safe
  · subst z; exact s4_535_safe
def s3_253 : State := ⟨[1,12,64,194], 25108406941546723057044569527435357981744741559092983697686, 2, 0, 1, 0⟩
theorem s3_253_edges : next config 3 s3_253 = [s4_67, s4_536, s4_451] := by decide
theorem s3_253_safe : Safe 10 3 s3_253 := by
  apply safe_succ 9 3 s3_253 [s4_67, s4_536, s4_451] (by decide) s3_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_67_safe
  · subst z; exact s4_536_safe
  · subst z; exact s4_451_safe
def s3_254 : State := ⟨[1,12,64,194], 31385508676933403819519229482959270543993598573829945364758, 2, 0, 1, 0⟩
theorem s3_254_edges : next config 3 s3_254 = [s4_68, s4_537, s4_452] := by decide
theorem s3_254_safe : Safe 10 3 s3_254 := by
  apply safe_succ 9 3 s3_254 [s4_68, s4_537, s4_452] (by decide) s3_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_68_safe
  · subst z; exact s4_537_safe
  · subst z; exact s4_452_safe
def s3_255 : State := ⟨[1,12,64,208], 411376139330301510561043381120235170325683166502394837115932950, 2, 0, 1, 0⟩
theorem s3_255_edges : next config 3 s3_255 = [s4_69, s4_538, s4_453] := by decide
theorem s3_255_safe : Safe 10 3 s3_255 := by
  apply safe_succ 9 3 s3_255 [s4_69, s4_538, s4_453] (by decide) s3_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_69_safe
  · subst z; exact s4_538_safe
  · subst z; exact s4_453_safe
def s3_256 : State := ⟨[1,12,64,208], 411382416432036897219506471711127754850563550585190939644465430, 2, 0, 1, 0⟩
theorem s3_256_edges : next config 3 s3_256 = [s4_70, s4_539, s4_454] := by decide
theorem s3_256_safe : Safe 10 3 s3_256 := by
  apply safe_succ 9 3 s3_256 [s4_70, s4_539, s4_454] (by decide) s3_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_70_safe
  · subst z; exact s4_539_safe
  · subst z; exact s4_454_safe
def s3_257 : State := ⟨[1,12,65,129], 1020847100762815390445464054520728326422, 2, 0, 1, 0⟩
theorem s3_257_edges : next config 3 s3_257 = [s4_79, s4_474, s4_455] := by decide
theorem s3_257_safe : Safe 10 3 s3_257 := by
  apply safe_succ 9 3 s3_257 [s4_79, s4_474, s4_455] (by decide) s3_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_79_safe
  · subst z; exact s4_474_safe
  · subst z; exact s4_455_safe
def s3_258 : State := ⟨[1,12,65,130], 1701411834604692317372213269384264749334, 2, 0, 1, 0⟩
theorem s3_258_edges : next config 3 s3_258 = [s4_80, s4_476, s4_457, s4_459] := by decide
theorem s3_258_safe : Safe 10 3 s3_258 := by
  apply safe_succ 9 3 s3_258 [s4_80, s4_476, s4_457, s4_459] (by decide) s3_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_80_safe
  · subst z; exact s4_476_safe
  · subst z; exact s4_457_safe
  · subst z; exact s4_459_safe
def s3_259 : State := ⟨[1,12,65,132], 5784800237655953878932708558565483286806, 2, 0, 1, 0⟩
theorem s3_259_edges : next config 3 s3_259 = [s4_81, s4_478] := by decide
theorem s3_259_safe : Safe 10 3 s3_259 := by
  apply safe_succ 9 3 s3_259 [s4_81, s4_478] (by decide) s3_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_81_safe
  · subst z; exact s4_478_safe
def s3_260 : State := ⟨[1,12,65,136], 87452568298681185110142614342189854036246, 2, 0, 1, 0⟩
theorem s3_260_edges : next config 3 s3_260 = [s4_82, s4_480] := by decide
theorem s3_260_safe : Safe 10 3 s3_260 := by
  apply safe_succ 9 3 s3_260 [s4_82, s4_480] (by decide) s3_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_82_safe
  · subst z; exact s4_480_safe
def s3_261 : State := ⟨[1,12,65,140], 1394136857275084884809501106880179786027286, 2, 0, 1, 0⟩
theorem s3_261_edges : next config 3 s3_261 = [s4_84, s4_482] := by decide
theorem s3_261_safe : Safe 10 3 s3_261 := by
  apply safe_succ 9 3 s3_261 [s4_84, s4_482] (by decide) s3_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_84_safe
  · subst z; exact s4_482_safe
def s3_262 : State := ⟨[1,12,65,144], 22301085480897544079999236987488018697883926, 2, 0, 1, 0⟩
theorem s3_262_edges : next config 3 s3_262 = [s4_85, s4_484, s4_456, s4_458, s4_461] := by decide
theorem s3_262_safe : Safe 10 3 s3_262 := by
  apply safe_succ 9 3 s3_262 [s4_85, s4_484, s4_456, s4_458, s4_461] (by decide) s3_262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_85_safe
  · subst z; exact s4_484_safe
  · subst z; exact s4_456_safe
  · subst z; exact s4_458_safe
  · subst z; exact s4_461_safe
def s3_263 : State := ⟨[1,12,65,160], 1461501637671185285124623296234997859313124446486, 2, 0, 1, 0⟩
theorem s3_263_edges : next config 3 s3_263 = [s4_87, s4_486, s4_460, s4_462] := by decide
theorem s3_263_safe : Safe 10 3 s3_263 := by
  apply safe_succ 9 3 s3_263 [s4_87, s4_486, s4_460, s4_462] (by decide) s3_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_87_safe
  · subst z; exact s4_486_safe
  · subst z; exact s4_460_safe
  · subst z; exact s4_462_safe
def s3_264 : State := ⟨[1,12,65,192], 6277101735386680764176071790128604879621070284121226416406, 2, 0, 1, 0⟩
theorem s3_264_edges : next config 3 s3_264 = [s4_88, s4_488] := by decide
theorem s3_264_safe : Safe 10 3 s3_264 := by
  apply safe_succ 9 3 s3_264 [s4_88, s4_488] (by decide) s3_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_88_safe
  · subst z; exact s4_488_safe
def s3_265 : State := ⟨[1,12,65,193], 12554203470773361528011861213336271295723425728585260929302, 2, 0, 1, 0⟩
theorem s3_265_edges : next config 3 s3_265 = [s4_89, s4_490] := by decide
theorem s3_265_safe : Safe 10 3 s3_265 := by
  apply safe_succ 9 3 s3_265 [s4_89, s4_490] (by decide) s3_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_89_safe
  · subst z; exact s4_490_safe
def s3_266 : State := ⟨[1,12,66,129], 1020847100762815390482357542668147429654, 2, 0, 1, 0⟩
theorem s3_266_edges : next config 3 s3_266 = [s4_90, s4_475, s4_498, s4_463] := by decide
theorem s3_266_safe : Safe 10 3 s3_266 := by
  apply safe_succ 9 3 s3_266 [s4_90, s4_475, s4_498, s4_463] (by decide) s3_266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_90_safe
  · subst z; exact s4_475_safe
  · subst z; exact s4_498_safe
  · subst z; exact s4_463_safe
def s3_267 : State := ⟨[1,12,66,130], 1701411834604692317409106757531683852566, 2, 0, 1, 0⟩
theorem s3_267_edges : next config 3 s3_267 = [s4_91, s4_477, s4_500, s4_465, s4_467] := by decide
theorem s3_267_safe : Safe 10 3 s3_267 := by
  apply safe_succ 9 3 s3_267 [s4_91, s4_477, s4_500, s4_465, s4_467] (by decide) s3_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_91_safe
  · subst z; exact s4_477_safe
  · subst z; exact s4_500_safe
  · subst z; exact s4_465_safe
  · subst z; exact s4_467_safe
def s3_268 : State := ⟨[1,12,66,132], 5784800237655953878969602046712902390038, 2, 0, 1, 0⟩
theorem s3_268_edges : next config 3 s3_268 = [s4_92, s4_479, s4_502] := by decide
theorem s3_268_safe : Safe 10 3 s3_268 := by
  apply safe_succ 9 3 s3_268 [s4_92, s4_479, s4_502] (by decide) s3_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_92_safe
  · subst z; exact s4_479_safe
  · subst z; exact s4_502_safe
def s3_269 : State := ⟨[1,12,66,136], 87452568298681185110179507830337273139478, 2, 0, 1, 0⟩
theorem s3_269_edges : next config 3 s3_269 = [s4_93, s4_481, s4_504] := by decide
theorem s3_269_safe : Safe 10 3 s3_269 := by
  apply safe_succ 9 3 s3_269 [s4_93, s4_481, s4_504] (by decide) s3_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_93_safe
  · subst z; exact s4_481_safe
  · subst z; exact s4_504_safe
def s3_270 : State := ⟨[1,12,66,140], 1394136857275084884809538000368327205130518, 2, 0, 1, 0⟩
theorem s3_270_edges : next config 3 s3_270 = [s4_95, s4_483, s4_506] := by decide
theorem s3_270_safe : Safe 10 3 s3_270 := by
  apply safe_succ 9 3 s3_270 [s4_95, s4_483, s4_506] (by decide) s3_270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_95_safe
  · subst z; exact s4_483_safe
  · subst z; exact s4_506_safe
def s3_271 : State := ⟨[1,12,66,144], 22301085480897544079999273880976166116987158, 2, 0, 1, 0⟩
theorem s3_271_edges : next config 3 s3_271 = [s4_96, s4_485, s4_582, s4_508, s4_464, s4_471, s4_466, s4_469] := by decide
theorem s3_271_safe : Safe 10 3 s3_271 := by
  apply safe_succ 9 3 s3_271 [s4_96, s4_485, s4_582, s4_508, s4_464, s4_471, s4_466, s4_469] (by decide) s3_271_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_96_safe
  · subst z; exact s4_485_safe
  · subst z; exact s4_582_safe
  · subst z; exact s4_508_safe
  · subst z; exact s4_464_safe
  · subst z; exact s4_471_safe
  · subst z; exact s4_466_safe
  · subst z; exact s4_469_safe
def s3_272 : State := ⟨[1,12,66,160], 1461501637671185285124623296271891347460543549718, 2, 0, 1, 0⟩
theorem s3_272_edges : next config 3 s3_272 = [s4_98, s4_487, s4_510, s4_468, s4_470] := by decide
theorem s3_272_safe : Safe 10 3 s3_272 := by
  apply safe_succ 9 3 s3_272 [s4_98, s4_487, s4_510, s4_468, s4_470] (by decide) s3_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_98_safe
  · subst z; exact s4_487_safe
  · subst z; exact s4_510_safe
  · subst z; exact s4_468_safe
  · subst z; exact s4_470_safe
def s3_273 : State := ⟨[1,12,66,192], 6277101735386680764176071790128604879657963772268645519638, 2, 0, 1, 0⟩
theorem s3_273_edges : next config 3 s3_273 = [s4_99, s4_489, s4_512] := by decide
theorem s3_273_safe : Safe 10 3 s3_273 := by
  apply safe_succ 9 3 s3_273 [s4_99, s4_489, s4_512] (by decide) s3_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_99_safe
  · subst z; exact s4_489_safe
  · subst z; exact s4_512_safe
def s3_274 : State := ⟨[1,12,66,194], 25108406941546723055683440059751604127965030105660749058326, 2, 0, 1, 0⟩
theorem s3_274_edges : next config 3 s3_274 = [s4_100, s4_491, s4_514, s4_472] := by decide
theorem s3_274_safe : Safe 10 3 s3_274 := by
  apply safe_succ 9 3 s3_274 [s4_100, s4_491, s4_514, s4_472] (by decide) s3_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_100_safe
  · subst z; exact s4_491_safe
  · subst z; exact s4_514_safe
  · subst z; exact s4_472_safe
def s3_275 : State := ⟨[1,12,67,128], 340282366920938463666288792246868316438, 2, 0, 0, 0⟩
theorem s3_275_edges : next config 3 s3_275 = [s4_879, s4_103, s4_474, s4_482, s4_492, s4_476, s4_480, s4_484, s4_486] := by decide
theorem s3_275_safe : Safe 10 3 s3_275 := by
  apply safe_succ 9 3 s3_275 [s4_879, s4_103, s4_474, s4_482, s4_492, s4_476, s4_480, s4_484, s4_486] (by decide) s3_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_879_safe
  · subst z; exact s4_103_safe
  · subst z; exact s4_474_safe
  · subst z; exact s4_482_safe
  · subst z; exact s4_492_safe
  · subst z; exact s4_476_safe
  · subst z; exact s4_480_safe
  · subst z; exact s4_484_safe
  · subst z; exact s4_486_safe
def s3_276 : State := ⟨[1,12,67,128], 340282366920938463703182280394287419670, 2, 0, 0, 0⟩
theorem s3_276_edges : next config 3 s3_276 = [s4_880, s4_104, s4_475, s4_483, s4_493, s4_477, s4_481, s4_485, s4_487] := by decide
theorem s3_276_safe : Safe 10 3 s3_276 := by
  apply safe_succ 9 3 s3_276 [s4_880, s4_104, s4_475, s4_483, s4_493, s4_477, s4_481, s4_485, s4_487] (by decide) s3_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_880_safe
  · subst z; exact s4_104_safe
  · subst z; exact s4_475_safe
  · subst z; exact s4_483_safe
  · subst z; exact s4_493_safe
  · subst z; exact s4_477_safe
  · subst z; exact s4_481_safe
  · subst z; exact s4_485_safe
  · subst z; exact s4_487_safe
def s3_277 : State := ⟨[1,12,80,129], 1020847100762816599334390181002483929366, 2, 0, 1, 0⟩
theorem s3_277_edges : next config 3 s3_277 = [s4_139, s4_499, s4_494] := by decide
theorem s3_277_safe : Safe 10 3 s3_277 := by
  apply safe_succ 9 3 s3_277 [s4_139, s4_499, s4_494] (by decide) s3_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_139_safe
  · subst z; exact s4_499_safe
  · subst z; exact s4_494_safe
def s3_278 : State := ⟨[1,12,80,130], 1701411834604693526261139395866020352278, 2, 0, 1, 0⟩
theorem s3_278_edges : next config 3 s3_278 = [s4_140, s4_580, s4_501, s4_496] := by decide
theorem s3_278_safe : Safe 10 3 s3_278 := by
  apply safe_succ 9 3 s3_278 [s4_140, s4_580, s4_501, s4_496] (by decide) s3_278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_140_safe
  · subst z; exact s4_580_safe
  · subst z; exact s4_501_safe
  · subst z; exact s4_496_safe
def s3_279 : State := ⟨[1,12,80,132], 5784800237655955087821634685047238889750, 2, 0, 1, 0⟩
theorem s3_279_edges : next config 3 s3_279 = [s4_141, s4_503] := by decide
theorem s3_279_safe : Safe 10 3 s3_279 := by
  apply safe_succ 9 3 s3_279 [s4_141, s4_503] (by decide) s3_279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_141_safe
  · subst z; exact s4_503_safe
def s3_280 : State := ⟨[1,12,80,136], 87452568298681186319031540468671609639190, 2, 0, 1, 0⟩
theorem s3_280_edges : next config 3 s3_280 = [s4_142, s4_505] := by decide
theorem s3_280_safe : Safe 10 3 s3_280 := by
  apply safe_succ 9 3 s3_280 [s4_142, s4_505] (by decide) s3_280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_142_safe
  · subst z; exact s4_505_safe
def s3_281 : State := ⟨[1,12,80,140], 1394136857275084886018390033006661541630230, 2, 0, 1, 0⟩
theorem s3_281_edges : next config 3 s3_281 = [s4_144, s4_507] := by decide
theorem s3_281_safe : Safe 10 3 s3_281 := by
  apply safe_succ 9 3 s3_281 [s4_144, s4_507] (by decide) s3_281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_144_safe
  · subst z; exact s4_507_safe
def s3_282 : State := ⟨[1,12,80,144], 22301085480897544081208125913614500453486870, 2, 0, 1, 0⟩
theorem s3_282_edges : next config 3 s3_282 = [s4_145, s4_509, s4_495] := by decide
theorem s3_282_safe : Safe 10 3 s3_282 := by
  apply safe_succ 9 3 s3_282 [s4_145, s4_509, s4_495] (by decide) s3_282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_145_safe
  · subst z; exact s4_509_safe
  · subst z; exact s4_495_safe
def s3_283 : State := ⟨[1,12,80,160], 1461501637671185285124624505123923985794880049430, 2, 0, 1, 0⟩
theorem s3_283_edges : next config 3 s3_283 = [s4_147, s4_511] := by decide
theorem s3_283_safe : Safe 10 3 s3_283 := by
  apply safe_succ 9 3 s3_283 [s4_147, s4_511] (by decide) s3_283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_147_safe
  · subst z; exact s4_511_safe
def s3_284 : State := ⟨[1,12,80,192], 6277101735386680764176071790128606088509996410602982019350, 2, 0, 1, 0⟩
theorem s3_284_edges : next config 3 s3_284 = [s4_148, s4_513] := by decide
theorem s3_284_safe : Safe 10 3 s3_284 := by
  apply safe_succ 9 3 s3_284 [s4_148, s4_513] (by decide) s3_284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_148_safe
  · subst z; exact s4_513_safe
def s3_285 : State := ⟨[1,12,80,208], 411376139330301510538742635921704547185356374049361104784658710, 2, 0, 1, 0⟩
theorem s3_285_edges : next config 3 s3_285 = [s4_149, s4_515, s4_497] := by decide
theorem s3_285_safe : Safe 10 3 s3_285 := by
  apply safe_succ 9 3 s3_285 [s4_149, s4_515, s4_497] (by decide) s3_285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_149_safe
  · subst z; exact s4_515_safe
  · subst z; exact s4_497_safe
def s3_286 : State := ⟨[1,12,82,128], 340282366920943299258886786321309831446, 2, 0, 0, 0⟩
theorem s3_286_edges : next config 3 s3_286 = [s4_883, s4_153, s4_498, s4_506, s4_516, s4_500, s4_504, s4_508, s4_510] := by decide
theorem s3_286_safe : Safe 10 3 s3_286 := by
  apply safe_succ 9 3 s3_286 [s4_883, s4_153, s4_498, s4_506, s4_516, s4_500, s4_504, s4_508, s4_510] (by decide) s3_286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_883_safe
  · subst z; exact s4_153_safe
  · subst z; exact s4_498_safe
  · subst z; exact s4_506_safe
  · subst z; exact s4_516_safe
  · subst z; exact s4_500_safe
  · subst z; exact s4_504_safe
  · subst z; exact s4_508_safe
  · subst z; exact s4_510_safe
def s3_287 : State := ⟨[1,12,82,128], 340282366920944508110919424655646331158, 2, 0, 0, 0⟩
theorem s3_287_edges : next config 3 s3_287 = [s4_884, s4_154, s4_499, s4_507, s4_517, s4_501, s4_505, s4_509, s4_511] := by decide
theorem s3_287_safe : Safe 10 3 s3_287 := by
  apply safe_succ 9 3 s3_287 [s4_884, s4_154, s4_499, s4_507, s4_517, s4_501, s4_505, s4_509, s4_511] (by decide) s3_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_884_safe
  · subst z; exact s4_154_safe
  · subst z; exact s4_499_safe
  · subst z; exact s4_507_safe
  · subst z; exact s4_517_safe
  · subst z; exact s4_501_safe
  · subst z; exact s4_505_safe
  · subst z; exact s4_509_safe
  · subst z; exact s4_511_safe
def s3_288 : State := ⟨[1,12,96,129], 1020847100842043552922834903966853173526, 2, 0, 1, 0⟩
theorem s3_288_edges : next config 3 s3_288 = [s4_1190, s4_787, s4_977, s4_191, s4_544, s4_586, s4_554, s4_564, s4_540, s4_522, s4_524, s4_528] := by decide
theorem s3_288_safe : Safe 10 3 s3_288 := by
  apply safe_succ 9 3 s3_288 [s4_1190, s4_787, s4_977, s4_191, s4_544, s4_586, s4_554, s4_564, s4_540, s4_522, s4_524, s4_528] (by decide) s3_288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1190_safe
  · subst z; exact s4_787_safe
  · subst z; exact s4_977_safe
  · subst z; exact s4_191_safe
  · subst z; exact s4_544_safe
  · subst z; exact s4_586_safe
  · subst z; exact s4_554_safe
  · subst z; exact s4_564_safe
  · subst z; exact s4_540_safe
  · subst z; exact s4_522_safe
  · subst z; exact s4_524_safe
  · subst z; exact s4_528_safe
def s3_289 : State := ⟨[1,12,96,130], 1701411834683920479849584118830389596438, 2, 0, 1, 0⟩
theorem s3_289_edges : next config 3 s3_289 = [s4_1191, s4_1210, s4_788, s4_978, s4_199, s4_545, s4_555, s4_565, s4_523, s4_526, s4_530] := by decide
theorem s3_289_safe : Safe 10 3 s3_289 := by
  apply safe_succ 9 3 s3_289 [s4_1191, s4_1210, s4_788, s4_978, s4_199, s4_545, s4_555, s4_565, s4_523, s4_526, s4_530] (by decide) s3_289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1191_safe
  · subst z; exact s4_1210_safe
  · subst z; exact s4_788_safe
  · subst z; exact s4_978_safe
  · subst z; exact s4_199_safe
  · subst z; exact s4_545_safe
  · subst z; exact s4_555_safe
  · subst z; exact s4_565_safe
  · subst z; exact s4_523_safe
  · subst z; exact s4_526_safe
  · subst z; exact s4_530_safe
def s3_290 : State := ⟨[1,12,96,132], 5784800237735182041410079408011608133910, 2, 0, 1, 0⟩
theorem s3_290_edges : next config 3 s3_290 = [s4_1192, s4_790, s4_979, s4_209, s4_546, s4_556, s4_566] := by decide
theorem s3_290_safe : Safe 10 3 s3_290 := by
  apply safe_succ 9 3 s3_290 [s4_1192, s4_790, s4_979, s4_209, s4_546, s4_556, s4_566] (by decide) s3_290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1192_safe
  · subst z; exact s4_790_safe
  · subst z; exact s4_979_safe
  · subst z; exact s4_209_safe
  · subst z; exact s4_546_safe
  · subst z; exact s4_556_safe
  · subst z; exact s4_566_safe
def s3_291 : State := ⟨[1,12,96,136], 87452568298760413272619985191635978883350, 2, 0, 1, 0⟩
theorem s3_291_edges : next config 3 s3_291 = [s4_1193, s4_791, s4_980, s4_217, s4_547, s4_557, s4_567] := by decide
theorem s3_291_safe : Safe 10 3 s3_291 := by
  apply safe_succ 9 3 s3_291 [s4_1193, s4_791, s4_980, s4_217, s4_547, s4_557, s4_567] (by decide) s3_291_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1193_safe
  · subst z; exact s4_791_safe
  · subst z; exact s4_980_safe
  · subst z; exact s4_217_safe
  · subst z; exact s4_547_safe
  · subst z; exact s4_557_safe
  · subst z; exact s4_567_safe
def s3_292 : State := ⟨[1,12,96,140], 1394136857275164112971978477729625910874390, 2, 0, 1, 0⟩
theorem s3_292_edges : next config 3 s3_292 = [s4_1194, s4_792, s4_981, s4_226, s4_548, s4_558, s4_568] := by decide
theorem s3_292_safe : Safe 10 3 s3_292 := by
  apply safe_succ 9 3 s3_292 [s4_1194, s4_792, s4_981, s4_226, s4_548, s4_558, s4_568] (by decide) s3_292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1194_safe
  · subst z; exact s4_792_safe
  · subst z; exact s4_981_safe
  · subst z; exact s4_226_safe
  · subst z; exact s4_548_safe
  · subst z; exact s4_558_safe
  · subst z; exact s4_568_safe
def s3_293 : State := ⟨[1,12,96,144], 22301085480897623308161714358337464822731030, 2, 0, 1, 0⟩
theorem s3_293_edges : next config 3 s3_293 = [s4_1195, s4_793, s4_982, s4_229, s4_549, s4_587, s4_559, s4_569, s4_525, s4_542, s4_527, s4_532] := by decide
theorem s3_293_safe : Safe 10 3 s3_293 := by
  apply safe_succ 9 3 s3_293 [s4_1195, s4_793, s4_982, s4_229, s4_549, s4_587, s4_559, s4_569, s4_525, s4_542, s4_527, s4_532] (by decide) s3_293_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1195_safe
  · subst z; exact s4_793_safe
  · subst z; exact s4_982_safe
  · subst z; exact s4_229_safe
  · subst z; exact s4_549_safe
  · subst z; exact s4_587_safe
  · subst z; exact s4_559_safe
  · subst z; exact s4_569_safe
  · subst z; exact s4_525_safe
  · subst z; exact s4_542_safe
  · subst z; exact s4_527_safe
  · subst z; exact s4_532_safe
def s3_294 : State := ⟨[1,12,96,160], 1461501637671185285203851458712368708759249293590, 2, 0, 1, 0⟩
theorem s3_294_edges : next config 3 s3_294 = [s4_1196, s4_1217, s4_794, s4_983, s4_240, s4_550, s4_560, s4_570, s4_529, s4_531, s4_533] := by decide
theorem s3_294_safe : Safe 10 3 s3_294 := by
  apply safe_succ 9 3 s3_294 [s4_1196, s4_1217, s4_794, s4_983, s4_240, s4_550, s4_560, s4_570, s4_529, s4_531, s4_533] (by decide) s3_294_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1196_safe
  · subst z; exact s4_1217_safe
  · subst z; exact s4_794_safe
  · subst z; exact s4_983_safe
  · subst z; exact s4_240_safe
  · subst z; exact s4_550_safe
  · subst z; exact s4_560_safe
  · subst z; exact s4_570_safe
  · subst z; exact s4_529_safe
  · subst z; exact s4_531_safe
  · subst z; exact s4_533_safe
def s3_295 : State := ⟨[1,12,96,192], 6277101735386680764176071790207833042098441133567351263510, 2, 0, 1, 0⟩
theorem s3_295_edges : next config 3 s3_295 = [s4_1197, s4_1246, s4_795, s4_985, s4_260, s4_551, s4_561, s4_571, s4_535, s4_537, s4_539] := by decide
theorem s3_295_safe : Safe 10 3 s3_295 := by
  apply safe_succ 9 3 s3_295 [s4_1197, s4_1246, s4_795, s4_985, s4_260, s4_551, s4_561, s4_571, s4_535, s4_537, s4_539] (by decide) s3_295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1197_safe
  · subst z; exact s4_1246_safe
  · subst z; exact s4_795_safe
  · subst z; exact s4_985_safe
  · subst z; exact s4_260_safe
  · subst z; exact s4_551_safe
  · subst z; exact s4_561_safe
  · subst z; exact s4_571_safe
  · subst z; exact s4_535_safe
  · subst z; exact s4_537_safe
  · subst z; exact s4_539_safe
def s3_296 : State := ⟨[1,12,96,224], 26959946667150639794667015087359913040637311048536658170206926999830, 2, 0, 1, 0⟩
theorem s3_296_edges : next config 3 s3_296 = [s4_1198, s4_1249, s4_796, s4_986, s4_280, s4_552, s4_562, s4_572, s4_541, s4_543] := by decide
theorem s3_296_safe : Safe 10 3 s3_296 := by
  apply safe_succ 9 3 s3_296 [s4_1198, s4_1249, s4_796, s4_986, s4_280, s4_552, s4_562, s4_572, s4_541, s4_543] (by decide) s3_296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1198_safe
  · subst z; exact s4_1249_safe
  · subst z; exact s4_796_safe
  · subst z; exact s4_986_safe
  · subst z; exact s4_280_safe
  · subst z; exact s4_552_safe
  · subst z; exact s4_562_safe
  · subst z; exact s4_572_safe
  · subst z; exact s4_541_safe
  · subst z; exact s4_543_safe
def s3_297 : State := ⟨[1,12,97,128], 340282367158622951024614364290404651286, 2, 0, 0, 0⟩
theorem s3_297_edges : next config 3 s3_297 = [s4_886, s4_290, s4_544, s4_548, s4_553, s4_545, s4_547, s4_549, s4_550] := by decide
theorem s3_297_safe : Safe 10 3 s3_297 := by
  apply safe_succ 9 3 s3_297 [s4_886, s4_290, s4_544, s4_548, s4_553, s4_545, s4_547, s4_549, s4_550] (by decide) s3_297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_886_safe
  · subst z; exact s4_290_safe
  · subst z; exact s4_544_safe
  · subst z; exact s4_548_safe
  · subst z; exact s4_553_safe
  · subst z; exact s4_545_safe
  · subst z; exact s4_547_safe
  · subst z; exact s4_549_safe
  · subst z; exact s4_550_safe
def s3_298 : State := ⟨[1,12,104,128], 340282387282576229647756113050568036630, 2, 0, 0, 0⟩
theorem s3_298_edges : next config 3 s3_298 = [s4_797, s4_887, s4_987, s4_315, s4_554, s4_558, s4_563, s4_555, s4_557, s4_559, s4_560] := by decide
theorem s3_298_safe : Safe 10 3 s3_298 := by
  apply safe_succ 9 3 s3_298 [s4_797, s4_887, s4_987, s4_315, s4_554, s4_558, s4_563, s4_555, s4_557, s4_559, s4_560] (by decide) s3_298_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_797_safe
  · subst z; exact s4_887_safe
  · subst z; exact s4_987_safe
  · subst z; exact s4_315_safe
  · subst z; exact s4_554_safe
  · subst z; exact s4_558_safe
  · subst z; exact s4_563_safe
  · subst z; exact s4_555_safe
  · subst z; exact s4_557_safe
  · subst z; exact s4_559_safe
  · subst z; exact s4_560_safe
def s3_299 : State := ⟨[1,12,112,128], 340287559297025160823714219599645970710, 2, 0, 0, 0⟩
theorem s3_299_edges : next config 3 s3_299 = [s4_888, s4_366, s4_564, s4_568, s4_573, s4_565, s4_567, s4_569, s4_570] := by decide
theorem s3_299_safe : Safe 10 3 s3_299 := by
  apply safe_succ 9 3 s3_299 [s4_888, s4_366, s4_564, s4_568, s4_573, s4_565, s4_567, s4_569, s4_570] (by decide) s3_299_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_888_safe
  · subst z; exact s4_366_safe
  · subst z; exact s4_564_safe
  · subst z; exact s4_568_safe
  · subst z; exact s4_573_safe
  · subst z; exact s4_565_safe
  · subst z; exact s4_567_safe
  · subst z; exact s4_569_safe
  · subst z; exact s4_570_safe
def s3_300 : State := ⟨[1,12,193,129], 12554203470773361528692425947178148222613281455301378248982, 2, 0, 1, 0⟩
theorem s3_300_edges : next config 3 s3_300 = [s4_385, s4_574] := by decide
theorem s3_300_safe : Safe 10 3 s3_300 := by
  apply safe_succ 9 3 s3_300 [s4_385, s4_574] (by decide) s3_300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_385_safe
  · subst z; exact s4_574_safe
def s3_301 : State := ⟨[1,12,194,130], 25108406941546723057044569527435357981744741559092983697686, 2, 0, 1, 0⟩
theorem s3_301_edges : next config 3 s3_301 = [s4_387, s4_581, s4_575, s4_576] := by decide
theorem s3_301_safe : Safe 10 3 s3_301 := by
  apply safe_succ 9 3 s3_301 [s4_387, s4_581, s4_575, s4_576] (by decide) s3_301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_387_safe
  · subst z; exact s4_581_safe
  · subst z; exact s4_575_safe
  · subst z; exact s4_576_safe
def s3_302 : State := ⟨[1,12,208,144], 411376139330301510561043381120235170325683166502394837115932950, 2, 0, 1, 0⟩
theorem s3_302_edges : next config 3 s3_302 = [s4_390, s4_583, s4_577] := by decide
theorem s3_302_safe : Safe 10 3 s3_302 := by
  apply safe_succ 9 3 s3_302 [s4_390, s4_583, s4_577] (by decide) s3_302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_390_safe
  · subst z; exact s4_583_safe
  · subst z; exact s4_577_safe
def s3_303 : State := ⟨[1,68,64,145], 44602511244162009098462140263768275674005782, 2, 0, 1, 0⟩
theorem s3_303_edges : next config 3 s3_303 = [s4_16, s4_592] := by decide
theorem s3_303_safe : Safe 10 3 s3_303 := by
  apply safe_succ 9 3 s3_303 [s4_16, s4_592] (by decide) s3_303_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_16_safe
  · subst z; exact s4_592_safe
def s3_304 : State := ⟨[1,68,64,145], 66902575877958790363070931787201773643563286, 2, 0, 1, 0⟩
theorem s3_304_edges : next config 3 s3_304 = [s4_22, s4_593] := by decide
theorem s3_304_safe : Safe 10 3 s3_304 := by
  apply safe_succ 9 3 s3_304 [s4_22, s4_593] (by decide) s3_304_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_22_safe
  · subst z; exact s4_593_safe
def s3_305 : State := ⟨[1,68,64,146], 89204682205957097258460503558279862222389526, 2, 0, 1, 0⟩
theorem s3_305_edges : next config 3 s3_305 = [s4_26, s4_677, s4_594, s4_590] := by decide
theorem s3_305_safe : Safe 10 3 s3_305 := by
  apply safe_succ 9 3 s3_305 [s4_26, s4_677, s4_594, s4_590] (by decide) s3_305_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_26_safe
  · subst z; exact s4_677_safe
  · subst z; exact s4_594_safe
  · subst z; exact s4_590_safe
def s3_306 : State := ⟨[1,68,64,146], 111504066275020036646142368332498496655524118, 2, 0, 1, 0⟩
theorem s3_306_edges : next config 3 s3_306 = [s4_31, s4_678, s4_595, s4_591] := by decide
theorem s3_306_safe : Safe 10 3 s3_306 := by
  apply safe_succ 9 3 s3_306 [s4_31, s4_678, s4_595, s4_591] (by decide) s3_306_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_31_safe
  · subst z; exact s4_678_safe
  · subst z; exact s4_595_safe
  · subst z; exact s4_591_safe
def s3_307 : State := ⟨[1,68,96,129], 1020847100842043553217982809146205995286, 2, 0, 1, 0⟩
theorem s3_307_edges : next config 3 s3_307 = [s4_596, s4_592] := by decide
theorem s3_307_safe : Safe 10 3 s3_307 := by
  apply safe_succ 9 3 s3_307 [s4_596, s4_592] (by decide) s3_307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_596_safe
  · subst z; exact s4_592_safe
def s3_308 : State := ⟨[1,68,96,130], 1701411834683920480144732024009742418198, 2, 0, 1, 0⟩
theorem s3_308_edges : next config 3 s3_308 = [s4_597, s4_594] := by decide
theorem s3_308_safe : Safe 10 3 s3_308 := by
  apply safe_succ 9 3 s3_308 [s4_597, s4_594] (by decide) s3_308_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_597_safe
  · subst z; exact s4_594_safe
def s3_309 : State := ⟨[1,68,96,132], 5784800237735182041705227313190960955670, 2, 0, 1, 0⟩
theorem s3_309_edges : next config 3 s3_309 = [s4_598] := by decide
theorem s3_309_safe : Safe 10 3 s3_309 := by
  apply safe_succ 9 3 s3_309 [s4_598] (by decide) s3_309_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_598_safe
def s3_310 : State := ⟨[1,68,96,136], 87452568298760413272915133096815331705110, 2, 0, 1, 0⟩
theorem s3_310_edges : next config 3 s3_310 = [s4_599] := by decide
theorem s3_310_safe : Safe 10 3 s3_310 := by
  apply safe_succ 9 3 s3_310 [s4_599] (by decide) s3_310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_599_safe
def s3_311 : State := ⟨[1,68,96,144], 22301085480897623308162009506242644175552790, 2, 0, 1, 0⟩
theorem s3_311_edges : next config 3 s3_311 = [s4_600, s4_593, s4_595] := by decide
theorem s3_311_safe : Safe 10 3 s3_311 := by
  apply safe_succ 9 3 s3_311 [s4_600, s4_593, s4_595] (by decide) s3_311_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_600_safe
  · subst z; exact s4_593_safe
  · subst z; exact s4_595_safe
def s3_312 : State := ⟨[1,68,96,160], 1461501637671185285203851459007516613938602115350, 2, 0, 1, 0⟩
theorem s3_312_edges : next config 3 s3_312 = [s4_601] := by decide
theorem s3_312_safe : Safe 10 3 s3_312 := by
  apply safe_succ 9 3 s3_312 [s4_601] (by decide) s3_312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_601_safe
def s3_313 : State := ⟨[1,68,96,192], 6277101735386680764176071790207833042393589038746704085270, 2, 0, 1, 0⟩
theorem s3_313_edges : next config 3 s3_313 = [s4_602] := by decide
theorem s3_313_safe : Safe 10 3 s3_313 := by
  apply safe_succ 9 3 s3_313 [s4_602] (by decide) s3_313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_602_safe
def s3_314 : State := ⟨[1,68,96,196], 100433627766186892221712913138322829283928920705707221778710, 2, 0, 1, 0⟩
theorem s3_314_edges : next config 3 s3_314 = [s4_603] := by decide
theorem s3_314_safe : Safe 10 3 s3_314 := by
  apply safe_succ 9 3 s3_314 [s4_603] (by decide) s3_314_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_603_safe
def s3_315 : State := ⟨[1,68,96,224], 26959946667150639794667015087359913040637311048831806075386279821590, 2, 0, 1, 0⟩
theorem s3_315_edges : next config 3 s3_315 = [s4_604] := by decide
theorem s3_315_safe : Safe 10 3 s3_315 := by
  apply safe_succ 9 3 s3_315 [s4_604] (by decide) s3_315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_604_safe
def s3_316 : State := ⟨[1,68,104,128], 340282387282576229942904018229920858390, 2, 0, 0, 0⟩
theorem s3_316_edges : next config 3 s3_316 = [s4_922, s4_596, s4_603, s4_605, s4_597, s4_599, s4_600, s4_601] := by decide
theorem s3_316_safe : Safe 10 3 s3_316 := by
  apply safe_succ 9 3 s3_316 [s4_922, s4_596, s4_603, s4_605, s4_597, s4_599, s4_600, s4_601] (by decide) s3_316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_922_safe
  · subst z; exact s4_596_safe
  · subst z; exact s4_603_safe
  · subst z; exact s4_605_safe
  · subst z; exact s4_597_safe
  · subst z; exact s4_599_safe
  · subst z; exact s4_600_safe
  · subst z; exact s4_601_safe
def s3_317 : State := ⟨[1,86,82,128], 340282366921020670511342122588491022614, 2, 0, 0, 0⟩
theorem s3_317_edges : next config 3 s3_317 = [s4_923, s4_155, s4_606, s4_624, s4_622, s4_608, s4_612, s4_614, s4_616] := by decide
theorem s3_317_safe : Safe 10 3 s3_317 := by
  apply safe_succ 9 3 s3_317 [s4_923, s4_155, s4_606, s4_624, s4_622, s4_608, s4_612, s4_614, s4_616] (by decide) s3_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_923_safe
  · subst z; exact s4_155_safe
  · subst z; exact s4_606_safe
  · subst z; exact s4_624_safe
  · subst z; exact s4_622_safe
  · subst z; exact s4_608_safe
  · subst z; exact s4_612_safe
  · subst z; exact s4_614_safe
  · subst z; exact s4_616_safe
def s3_318 : State := ⟨[1,86,82,128], 340282366921021879363374760922827522326, 2, 0, 0, 0⟩
theorem s3_318_edges : next config 3 s3_318 = [s4_924, s4_156, s4_607, s4_625, s4_623, s4_609, s4_613, s4_615, s4_617] := by decide
theorem s3_318_safe : Safe 10 3 s3_318 := by
  apply safe_succ 9 3 s3_318 [s4_924, s4_156, s4_607, s4_625, s4_623, s4_609, s4_613, s4_615, s4_617] (by decide) s3_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_924_safe
  · subst z; exact s4_156_safe
  · subst z; exact s4_607_safe
  · subst z; exact s4_625_safe
  · subst z; exact s4_623_safe
  · subst z; exact s4_609_safe
  · subst z; exact s4_613_safe
  · subst z; exact s4_615_safe
  · subst z; exact s4_617_safe
def s3_319 : State := ⟨[1,100,96,129], 1020847102109694153151064305463556374806, 2, 0, 1, 0⟩
theorem s3_319_edges : next config 3 s3_319 = [s4_798, s4_196, s4_642, s4_628, s4_630] := by decide
theorem s3_319_safe : Safe 10 3 s3_319 := by
  apply safe_succ 9 3 s3_319 [s4_798, s4_196, s4_642, s4_628, s4_630] (by decide) s3_319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_798_safe
  · subst z; exact s4_196_safe
  · subst z; exact s4_642_safe
  · subst z; exact s4_628_safe
  · subst z; exact s4_630_safe
def s3_320 : State := ⟨[1,100,96,130], 1701411835951571080077813520327092797718, 2, 0, 1, 0⟩
theorem s3_320_edges : next config 3 s3_320 = [s4_1211, s4_799, s4_204, s4_643, s4_629, s4_632, s4_634] := by decide
theorem s3_320_safe : Safe 10 3 s3_320 := by
  apply safe_succ 9 3 s3_320 [s4_1211, s4_799, s4_204, s4_643, s4_629, s4_632, s4_634] (by decide) s3_320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1211_safe
  · subst z; exact s4_799_safe
  · subst z; exact s4_204_safe
  · subst z; exact s4_643_safe
  · subst z; exact s4_629_safe
  · subst z; exact s4_632_safe
  · subst z; exact s4_634_safe
def s3_321 : State := ⟨[1,100,96,132], 5784800239002832641638308809508311335190, 2, 0, 1, 0⟩
theorem s3_321_edges : next config 3 s3_321 = [s4_801, s4_214, s4_644] := by decide
theorem s3_321_safe : Safe 10 3 s3_321 := by
  apply safe_succ 9 3 s3_321 [s4_801, s4_214, s4_644] (by decide) s3_321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_801_safe
  · subst z; exact s4_214_safe
  · subst z; exact s4_644_safe
def s3_322 : State := ⟨[1,100,96,136], 87452568300028063872848214593132682084630, 2, 0, 1, 0⟩
theorem s3_322_edges : next config 3 s3_322 = [s4_802, s4_222, s4_645] := by decide
theorem s3_322_safe : Safe 10 3 s3_322 := by
  apply safe_succ 9 3 s3_322 [s4_802, s4_222, s4_645] (by decide) s3_322_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_802_safe
  · subst z; exact s4_222_safe
  · subst z; exact s4_645_safe
def s3_323 : State := ⟨[1,100,96,144], 22301085480898890958761942587738961525932310, 2, 0, 1, 0⟩
theorem s3_323_edges : next config 3 s3_323 = [s4_803, s4_234, s4_646, s4_631, s4_633, s4_636] := by decide
theorem s3_323_safe : Safe 10 3 s3_323 := by
  apply safe_succ 9 3 s3_323 [s4_803, s4_234, s4_646, s4_631, s4_633, s4_636] (by decide) s3_323_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_803_safe
  · subst z; exact s4_234_safe
  · subst z; exact s4_646_safe
  · subst z; exact s4_631_safe
  · subst z; exact s4_633_safe
  · subst z; exact s4_636_safe
def s3_324 : State := ⟨[1,100,96,160], 1461501637671185286471502058940598110255952494870, 2, 0, 1, 0⟩
theorem s3_324_edges : next config 3 s3_324 = [s4_804, s4_245, s4_647, s4_635, s4_637] := by decide
theorem s3_324_safe : Safe 10 3 s3_324 := by
  apply safe_succ 9 3 s3_324 [s4_804, s4_245, s4_647, s4_635, s4_637] (by decide) s3_324_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_804_safe
  · subst z; exact s4_245_safe
  · subst z; exact s4_647_safe
  · subst z; exact s4_635_safe
  · subst z; exact s4_637_safe
def s3_325 : State := ⟨[1,100,96,192], 6277101735386680764176071791475483642326670535064054464790, 2, 0, 1, 0⟩
theorem s3_325_edges : next config 3 s3_325 = [s4_1247, s4_805, s4_265, s4_648, s4_639, s4_641] := by decide
theorem s3_325_safe : Safe 10 3 s3_325 := by
  apply safe_succ 9 3 s3_325 [s4_1247, s4_805, s4_265, s4_648, s4_639, s4_641] (by decide) s3_325_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1247_safe
  · subst z; exact s4_805_safe
  · subst z; exact s4_265_safe
  · subst z; exact s4_648_safe
  · subst z; exact s4_639_safe
  · subst z; exact s4_641_safe
def s3_326 : State := ⟨[1,100,96,224], 26959946667150639794667015087359913041904961648764887571703630201110, 2, 0, 1, 0⟩
theorem s3_326_edges : next config 3 s3_326 = [s4_806, s4_285, s4_649] := by decide
theorem s3_326_safe : Safe 10 3 s3_326 := by
  apply safe_succ 9 3 s3_326 [s4_806, s4_285, s4_649] (by decide) s3_326_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_806_safe
  · subst z; exact s4_285_safe
  · subst z; exact s4_649_safe
def s3_327 : State := ⟨[1,100,96,228], 431359146674410236714672241392654373146462127986873474788257783939350, 2, 0, 1, 0⟩
theorem s3_327_edges : next config 3 s3_327 = [s4_807, s4_289, s4_650] := by decide
theorem s3_327_safe : Safe 10 3 s3_327 := by
  apply safe_succ 9 3 s3_327 [s4_807, s4_289, s4_650] (by decide) s3_327_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_807_safe
  · subst z; exact s4_289_safe
  · subst z; exact s4_650_safe
def s3_328 : State := ⟨[1,100,104,128], 340282388550226829875985514547271237910, 2, 0, 0, 0⟩
theorem s3_328_edges : next config 3 s3_328 = [s4_808, s4_926, s4_642, s4_650, s4_651, s4_643, s4_645, s4_646, s4_647] := by decide
theorem s3_328_safe : Safe 10 3 s3_328 := by
  apply safe_succ 9 3 s3_328 [s4_808, s4_926, s4_642, s4_650, s4_651, s4_643, s4_645, s4_646, s4_647] (by decide) s3_328_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_808_safe
  · subst z; exact s4_926_safe
  · subst z; exact s4_642_safe
  · subst z; exact s4_650_safe
  · subst z; exact s4_651_safe
  · subst z; exact s4_643_safe
  · subst z; exact s4_645_safe
  · subst z; exact s4_646_safe
  · subst z; exact s4_647_safe
def s3_329 : State := ⟨[1,108,104,128], 340282711801129888074482896206588608790, 2, 0, 0, 0⟩
theorem s3_329_edges : next config 3 s3_329 = [s4_809, s4_927, s4_321, s4_652, s4_661, s4_660, s4_653, s4_655, s4_656, s4_657] := by decide
theorem s3_329_safe : Safe 10 3 s3_329 := by
  apply safe_succ 9 3 s3_329 [s4_809, s4_927, s4_321, s4_652, s4_661, s4_660, s4_653, s4_655, s4_656, s4_657] (by decide) s3_329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_809_safe
  · subst z; exact s4_927_safe
  · subst z; exact s4_321_safe
  · subst z; exact s4_652_safe
  · subst z; exact s4_661_safe
  · subst z; exact s4_660_safe
  · subst z; exact s4_653_safe
  · subst z; exact s4_655_safe
  · subst z; exact s4_656_safe
  · subst z; exact s4_657_safe
def s3_330 : State := ⟨[1,140,65,136], 1481249143206845131456125006382712448155926, 2, 0, 1, 0⟩
theorem s3_330_edges : next config 3 s3_330 = [s4_83, s4_665] := by decide
theorem s3_330_safe : Safe 10 3 s3_330 := by
  apply safe_succ 9 3 s3_330 [s4_83, s4_665] (by decide) s3_330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_83_safe
  · subst z; exact s4_665_safe
def s3_331 : State := ⟨[1,140,66,136], 1481249143206845131456161899870859867259158, 2, 0, 1, 0⟩
theorem s3_331_edges : next config 3 s3_331 = [s4_94, s4_666, s4_667] := by decide
theorem s3_331_safe : Safe 10 3 s3_331 := by
  apply safe_succ 9 3 s3_331 [s4_94, s4_666, s4_667] (by decide) s3_331_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_94_safe
  · subst z; exact s4_666_safe
  · subst z; exact s4_667_safe
def s3_332 : State := ⟨[1,140,80,136], 1481249143206845132665013932509194203758870, 2, 0, 1, 0⟩
theorem s3_332_edges : next config 3 s3_332 = [s4_143, s4_668] := by decide
theorem s3_332_safe : Safe 10 3 s3_332 := by
  apply safe_succ 9 3 s3_332 [s4_143, s4_668] (by decide) s3_332_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_143_safe
  · subst z; exact s4_668_safe
def s3_333 : State := ⟨[1,140,96,136], 1481249143206924359618602377232158573003030, 2, 0, 1, 0⟩
theorem s3_333_edges : next config 3 s3_333 = [s4_1201, s4_811, s4_988, s4_224, s4_669, s4_670, s4_671] := by decide
theorem s3_333_safe : Safe 10 3 s3_333 := by
  apply safe_succ 9 3 s3_333 [s4_1201, s4_811, s4_988, s4_224, s4_669, s4_670, s4_671] (by decide) s3_333_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1201_safe
  · subst z; exact s4_811_safe
  · subst z; exact s4_988_safe
  · subst z; exact s4_224_safe
  · subst z; exact s4_669_safe
  · subst z; exact s4_670_safe
  · subst z; exact s4_671_safe
def s3_334 : State := ⟨[1,150,64,146], 1516452374911916978316746177859869819252310294, 2, 0, 1, 0⟩
theorem s3_334_edges : next config 3 s3_334 = [s4_679, s4_32, s4_674, s4_672] := by decide
theorem s3_334_safe : Safe 10 3 s3_334 := by
  apply safe_succ 9 3 s3_334 [s4_679, s4_32, s4_674, s4_672] (by decide) s3_334_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_679_safe
  · subst z; exact s4_32_safe
  · subst z; exact s4_674_safe
  · subst z; exact s4_672_safe
def s3_335 : State := ⟨[1,150,64,146], 1538751758980979917704428042634088453685444886, 2, 0, 1, 0⟩
theorem s3_335_edges : next config 3 s3_335 = [s4_680, s4_33, s4_675, s4_673] := by decide
theorem s3_335_safe : Safe 10 3 s3_335 := by
  apply safe_succ 9 3 s3_335 [s4_680, s4_33, s4_675, s4_673] (by decide) s3_335_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_680_safe
  · subst z; exact s4_33_safe
  · subst z; exact s4_675_safe
  · subst z; exact s4_673_safe
def s3_336 : State := ⟨[1,196,96,192], 106710729501573572985548702561530495699736128244991903465750, 2, 0, 1, 0⟩
theorem s3_336_edges : next config 3 s3_336 = [s4_267, s4_676] := by decide
theorem s3_336_safe : Safe 10 3 s3_336 := by
  apply safe_succ 9 3 s3_336 [s4_267, s4_676] (by decide) s3_336_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_267_safe
  · subst z; exact s4_676_safe
def s3_337 : State := ⟨[1,228,96,224], 458319093341560876509339256479674003818831621809185817867864690983190, 2, 0, 1, 0⟩
theorem s3_337_edges : next config 3 s3_337 = [s4_812, s4_287, s4_699] := by decide
theorem s3_337_safe : Safe 10 3 s3_337 := by
  apply safe_succ 9 3 s3_337 [s4_812, s4_287, s4_699] (by decide) s3_337_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_812_safe
  · subst z; exact s4_287_safe
  · subst z; exact s4_699_safe
def s3_338 : State := ⟨[3,4,64,128], 340282366920938463481821351509772800286, 3, 2, 0, 0⟩
theorem s3_338_edges : next config 3 s3_338 = [s4_0, s4_989, s4_716, s4_729, s4_703, s4_704, s4_715, s4_702, s4_705, s4_708, s4_712] := by decide
theorem s3_338_safe : Safe 10 3 s3_338 := by
  apply safe_succ 9 3 s3_338 [s4_0, s4_989, s4_716, s4_729, s4_703, s4_704, s4_715, s4_702, s4_705, s4_708, s4_712] (by decide) s3_338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_0_safe
  · subst z; exact s4_989_safe
  · subst z; exact s4_716_safe
  · subst z; exact s4_729_safe
  · subst z; exact s4_703_safe
  · subst z; exact s4_704_safe
  · subst z; exact s4_715_safe
  · subst z; exact s4_702_safe
  · subst z; exact s4_705_safe
  · subst z; exact s4_708_safe
  · subst z; exact s4_712_safe
def s3_339 : State := ⟨[3,4,64,140], 1399581375145819900224878207110940658303262, 1, 0, 1, 0⟩
theorem s3_339_edges : next config 3 s3_339 = [s4_5, s4_991, s4_717, s4_731] := by decide
theorem s3_339_safe : Safe 10 3 s3_339 := by
  apply safe_succ 9 3 s3_339 [s4_5, s4_991, s4_717, s4_731] (by decide) s3_339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_5_safe
  · subst z; exact s4_991_safe
  · subst z; exact s4_717_safe
  · subst z; exact s4_731_safe
def s3_340 : State := ⟨[3,4,64,140], 1481249143206845131456088112894565029052702, 1, 0, 1, 0⟩
theorem s3_340_edges : next config 3 s3_340 = [s4_8, s4_993, s4_718, s4_732] := by decide
theorem s3_340_safe : Safe 10 3 s3_340 := by
  apply safe_succ 9 3 s3_340 [s4_8, s4_993, s4_718, s4_732] (by decide) s3_340_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_8_safe
  · subst z; exact s4_993_safe
  · subst z; exact s4_718_safe
  · subst z; exact s4_732_safe
def s3_341 : State := ⟨[3,4,64,145], 44602511244162009098461845115863096321179934, 1, 0, 1, 0⟩
theorem s3_341_edges : next config 3 s3_341 = [s4_1213, s4_11, s4_995, s4_767, s4_719, s4_733] := by decide
theorem s3_341_safe : Safe 10 3 s3_341 := by
  apply safe_succ 9 3 s3_341 [s4_1213, s4_11, s4_995, s4_767, s4_719, s4_733] (by decide) s3_341_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1213_safe
  · subst z; exact s4_11_safe
  · subst z; exact s4_995_safe
  · subst z; exact s4_767_safe
  · subst z; exact s4_719_safe
  · subst z; exact s4_733_safe
def s3_342 : State := ⟨[3,4,64,145], 66902575877958790363070636639296594290737438, 1, 0, 1, 0⟩
theorem s3_342_edges : next config 3 s3_342 = [s4_1214, s4_17, s4_997, s4_768, s4_720, s4_734] := by decide
theorem s3_342_safe : Safe 10 3 s3_342 := by
  apply safe_succ 9 3 s3_342 [s4_1214, s4_17, s4_997, s4_768, s4_720, s4_734] (by decide) s3_342_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1214_safe
  · subst z; exact s4_17_safe
  · subst z; exact s4_997_safe
  · subst z; exact s4_768_safe
  · subst z; exact s4_720_safe
  · subst z; exact s4_734_safe
def s3_343 : State := ⟨[3,4,64,146], 89204682205957097258460208410374682869563678, 1, 0, 1, 0⟩
theorem s3_343_edges : next config 3 s3_343 = [s4_23, s4_769, s4_721, s4_735, s4_710] := by decide
theorem s3_343_safe : Safe 10 3 s3_343 := by
  apply safe_succ 9 3 s3_343 [s4_23, s4_769, s4_721, s4_735, s4_710] (by decide) s3_343_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_23_safe
  · subst z; exact s4_769_safe
  · subst z; exact s4_721_safe
  · subst z; exact s4_735_safe
  · subst z; exact s4_710_safe
def s3_344 : State := ⟨[3,4,64,146], 111504066275020036646142073184593317302698270, 1, 0, 1, 0⟩
theorem s3_344_edges : next config 3 s3_344 = [s4_28, s4_770, s4_722, s4_736, s4_711] := by decide
theorem s3_344_safe : Safe 10 3 s3_344 := by
  apply safe_succ 9 3 s3_344 [s4_28, s4_770, s4_722, s4_736, s4_711] (by decide) s3_344_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_28_safe
  · subst z; exact s4_770_safe
  · subst z; exact s4_722_safe
  · subst z; exact s4_736_safe
  · subst z; exact s4_711_safe
def s3_345 : State := ⟨[3,4,64,162], 5846006551025023507419431648200451859860575813918, 1, 0, 1, 0⟩
theorem s3_345_edges : next config 3 s3_345 = [s4_36, s4_771, s4_723, s4_737] := by decide
theorem s3_345_safe : Safe 10 3 s3_345 := by
  apply safe_succ 9 3 s3_345 [s4_36, s4_771, s4_723, s4_737] (by decide) s3_345_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_36_safe
  · subst z; exact s4_771_safe
  · subst z; exact s4_723_safe
  · subst z; exact s4_737_safe
def s3_346 : State := ⟨[3,4,64,162], 7307508186994796957939362627063236449789435511070, 1, 0, 1, 0⟩
theorem s3_346_edges : next config 3 s3_346 = [s4_41, s4_772, s4_724, s4_738] := by decide
theorem s3_346_safe : Safe 10 3 s3_346 := by
  apply safe_succ 9 3 s3_346 [s4_41, s4_772, s4_724, s4_738] (by decide) s3_346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_41_safe
  · subst z; exact s4_772_safe
  · subst z; exact s4_724_safe
  · subst z; exact s4_738_safe
def s3_347 : State := ⟨[3,4,64,163], 11692013101709764647917924832919082368211378831646, 1, 0, 1, 0⟩
theorem s3_347_edges : next config 3 s3_347 = [s4_48, s4_773, s4_725, s4_739, s4_713] := by decide
theorem s3_347_safe : Safe 10 3 s3_347 := by
  apply safe_succ 9 3 s3_347 [s4_48, s4_773, s4_725, s4_739, s4_713] (by decide) s3_347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_48_safe
  · subst z; exact s4_773_safe
  · subst z; exact s4_725_safe
  · subst z; exact s4_739_safe
  · subst z; exact s4_713_safe
def s3_348 : State := ⟨[3,4,64,163], 13153514736318408630754101957928368528413165682974, 1, 0, 1, 0⟩
theorem s3_348_edges : next config 3 s3_348 = [s4_49, s4_774, s4_726, s4_740, s4_714] := by decide
theorem s3_348_safe : Safe 10 3 s3_348 := by
  apply safe_succ 9 3 s3_348 [s4_49, s4_774, s4_726, s4_740, s4_714] (by decide) s3_348_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_49_safe
  · subst z; exact s4_774_safe
  · subst z; exact s4_726_safe
  · subst z; exact s4_740_safe
  · subst z; exact s4_714_safe
def s3_349 : State := ⟨[3,4,64,176], 95780971326419139128294233276893524070171066415251742, 1, 0, 1, 0⟩
theorem s3_349_edges : next config 3 s3_349 = [s4_59, s4_775, s4_727, s4_741] := by decide
theorem s3_349_safe : Safe 10 3 s3_349 := by
  apply safe_succ 9 3 s3_349 [s4_59, s4_775, s4_727, s4_741] (by decide) s3_349_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_59_safe
  · subst z; exact s4_775_safe
  · subst z; exact s4_727_safe
  · subst z; exact s4_741_safe
def s3_350 : State := ⟨[3,4,64,176], 95782432805755724832681813820190522080542360841814302, 1, 0, 1, 0⟩
theorem s3_350_edges : next config 3 s3_350 = [s4_62, s4_776, s4_728, s4_742] := by decide
theorem s3_350_safe : Safe 10 3 s3_350 := by
  apply safe_succ 9 3 s3_350 [s4_62, s4_776, s4_728, s4_742] (by decide) s3_350_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_62_safe
  · subst z; exact s4_776_safe
  · subst z; exact s4_728_safe
  · subst z; exact s4_742_safe
def s3_351 : State := ⟨[3,4,67,129], 1020847100762815390556144518962985632030, 1, 0, 1, 0⟩
theorem s3_351_edges : next config 3 s3_351 = [s4_105, s4_1005, s4_777, s4_719] := by decide
theorem s3_351_safe : Safe 10 3 s3_351 := by
  apply safe_succ 9 3 s3_351 [s4_105, s4_1005, s4_777, s4_719] (by decide) s3_351_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_105_safe
  · subst z; exact s4_1005_safe
  · subst z; exact s4_777_safe
  · subst z; exact s4_719_safe
def s3_352 : State := ⟨[3,4,67,130], 1701411834604692317482893733826522054942, 1, 0, 1, 0⟩
theorem s3_352_edges : next config 3 s3_352 = [s4_106, s4_1006, s4_778, s4_721, s4_723] := by decide
theorem s3_352_safe : Safe 10 3 s3_352 := by
  apply safe_succ 9 3 s3_352 [s4_106, s4_1006, s4_778, s4_721, s4_723] (by decide) s3_352_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_106_safe
  · subst z; exact s4_1006_safe
  · subst z; exact s4_778_safe
  · subst z; exact s4_721_safe
  · subst z; exact s4_723_safe
def s3_353 : State := ⟨[3,4,67,131], 3062541302288446171336392163553594900766, 1, 0, 1, 0⟩
theorem s3_353_edges : next config 3 s3_353 = [s4_107, s4_1007, s4_779, s4_725] := by decide
theorem s3_353_safe : Safe 10 3 s3_353 := by
  apply safe_succ 9 3 s3_353 [s4_107, s4_1007, s4_779, s4_725] (by decide) s3_353_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_107_safe
  · subst z; exact s4_1007_safe
  · subst z; exact s4_779_safe
  · subst z; exact s4_725_safe
def s3_354 : State := ⟨[3,4,67,132], 5784800237655953879043389023007740592414, 1, 0, 1, 0⟩
theorem s3_354_edges : next config 3 s3_354 = [s4_108, s4_1008, s4_780, s4_717] := by decide
theorem s3_354_safe : Safe 10 3 s3_354 := by
  apply safe_succ 9 3 s3_354 [s4_108, s4_1008, s4_780, s4_717] (by decide) s3_354_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_108_safe
  · subst z; exact s4_1008_safe
  · subst z; exact s4_780_safe
  · subst z; exact s4_717_safe
def s3_355 : State := ⟨[3,4,67,136], 87452568298681185110253294806632111341854, 1, 0, 1, 0⟩
theorem s3_355_edges : next config 3 s3_355 = [s4_109, s4_1009, s4_810, s4_781, s4_718] := by decide
theorem s3_355_safe : Safe 10 3 s3_355 := by
  apply safe_succ 9 3 s3_355 [s4_109, s4_1009, s4_810, s4_781, s4_718] (by decide) s3_355_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_109_safe
  · subst z; exact s4_1009_safe
  · subst z; exact s4_810_safe
  · subst z; exact s4_781_safe
  · subst z; exact s4_718_safe
def s3_356 : State := ⟨[3,4,67,144], 22301085480897544079999347667952460955189534, 1, 0, 1, 0⟩
theorem s3_356_edges : next config 3 s3_356 = [s4_114, s4_1010, s4_783, s4_722, s4_727] := by decide
theorem s3_356_safe : Safe 10 3 s3_356 := by
  apply safe_succ 9 3 s3_356 [s4_114, s4_1010, s4_783, s4_722, s4_727] (by decide) s3_356_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_114_safe
  · subst z; exact s4_1010_safe
  · subst z; exact s4_783_safe
  · subst z; exact s4_722_safe
  · subst z; exact s4_727_safe
def s3_357 : State := ⟨[3,4,67,160], 1461501637671185285124623296345678323755381752094, 1, 0, 1, 0⟩
theorem s3_357_edges : next config 3 s3_357 = [s4_1218, s4_123, s4_1011, s4_784, s4_726, s4_724, s4_728] := by decide
theorem s3_357_safe : Safe 10 3 s3_357 := by
  apply safe_succ 9 3 s3_357 [s4_1218, s4_123, s4_1011, s4_784, s4_726, s4_724, s4_728] (by decide) s3_357_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1218_safe
  · subst z; exact s4_123_safe
  · subst z; exact s4_1011_safe
  · subst z; exact s4_784_safe
  · subst z; exact s4_726_safe
  · subst z; exact s4_724_safe
  · subst z; exact s4_728_safe
def s3_358 : State := ⟨[3,4,67,192], 6277101735386680764176071790128604879731750748563483722014, 1, 0, 1, 0⟩
theorem s3_358_edges : next config 3 s3_358 = [s4_132, s4_1013, s4_785] := by decide
theorem s3_358_safe : Safe 10 3 s3_358 := by
  apply safe_succ 9 3 s3_358 [s4_132, s4_1013, s4_785] (by decide) s3_358_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_132_safe
  · subst z; exact s4_1013_safe
  · subst z; exact s4_785_safe
def s3_359 : State := ⟨[3,4,67,195], 50216813883093446111026597752582269792448238859811725312286, 1, 0, 1, 0⟩
theorem s3_359_edges : next config 3 s3_359 = [s4_133, s4_1014, s4_786] := by decide
theorem s3_359_safe : Safe 10 3 s3_359 := by
  apply safe_succ 9 3 s3_359 [s4_133, s4_1014, s4_786] (by decide) s3_359_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_133_safe
  · subst z; exact s4_1014_safe
  · subst z; exact s4_786_safe
def s3_360 : State := ⟨[3,4,96,129], 1020847100842043552922834903966853169438, 1, 0, 1, 0⟩
theorem s3_360_edges : next config 3 s3_360 = [s4_189, s4_1015, s4_798, s4_787, s4_745, s4_755, s4_733] := by decide
theorem s3_360_safe : Safe 10 3 s3_360 := by
  apply safe_succ 9 3 s3_360 [s4_189, s4_1015, s4_798, s4_787, s4_745, s4_755, s4_733] (by decide) s3_360_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_189_safe
  · subst z; exact s4_1015_safe
  · subst z; exact s4_798_safe
  · subst z; exact s4_787_safe
  · subst z; exact s4_745_safe
  · subst z; exact s4_755_safe
  · subst z; exact s4_733_safe
def s3_361 : State := ⟨[3,4,96,130], 1701411834683920479849584118830389592350, 1, 0, 1, 0⟩
theorem s3_361_edges : next config 3 s3_361 = [s4_197, s4_1017, s4_799, s4_788, s4_746, s4_756, s4_735, s4_737] := by decide
theorem s3_361_safe : Safe 10 3 s3_361 := by
  apply safe_succ 9 3 s3_361 [s4_197, s4_1017, s4_799, s4_788, s4_746, s4_756, s4_735, s4_737] (by decide) s3_361_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_197_safe
  · subst z; exact s4_1017_safe
  · subst z; exact s4_799_safe
  · subst z; exact s4_788_safe
  · subst z; exact s4_746_safe
  · subst z; exact s4_756_safe
  · subst z; exact s4_735_safe
  · subst z; exact s4_737_safe
def s3_362 : State := ⟨[3,4,96,131], 3062541302367674333703082548557462438174, 1, 0, 1, 0⟩
theorem s3_362_edges : next config 3 s3_362 = [s4_206, s4_1019, s4_800, s4_789, s4_747, s4_757, s4_739] := by decide
theorem s3_362_safe : Safe 10 3 s3_362 := by
  apply safe_succ 9 3 s3_362 [s4_206, s4_1019, s4_800, s4_789, s4_747, s4_757, s4_739] (by decide) s3_362_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_206_safe
  · subst z; exact s4_1019_safe
  · subst z; exact s4_800_safe
  · subst z; exact s4_789_safe
  · subst z; exact s4_747_safe
  · subst z; exact s4_757_safe
  · subst z; exact s4_739_safe
def s3_363 : State := ⟨[3,4,96,132], 5784800237735182041410079408011608129822, 1, 0, 1, 0⟩
theorem s3_363_edges : next config 3 s3_363 = [s4_207, s4_1020, s4_801, s4_790, s4_748, s4_766, s4_758, s4_743, s4_731] := by decide
theorem s3_363_safe : Safe 10 3 s3_363 := by
  apply safe_succ 9 3 s3_363 [s4_207, s4_1020, s4_801, s4_790, s4_748, s4_766, s4_758, s4_743, s4_731] (by decide) s3_363_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_207_safe
  · subst z; exact s4_1020_safe
  · subst z; exact s4_801_safe
  · subst z; exact s4_790_safe
  · subst z; exact s4_748_safe
  · subst z; exact s4_766_safe
  · subst z; exact s4_758_safe
  · subst z; exact s4_743_safe
  · subst z; exact s4_731_safe
def s3_364 : State := ⟨[3,4,96,136], 87452568298760413272619985191635978879262, 1, 0, 1, 0⟩
theorem s3_364_edges : next config 3 s3_364 = [s4_215, s4_1022, s4_802, s4_811, s4_791, s4_749, s4_759, s4_732] := by decide
theorem s3_364_safe : Safe 10 3 s3_364 := by
  apply safe_succ 9 3 s3_364 [s4_215, s4_1022, s4_802, s4_811, s4_791, s4_749, s4_759, s4_732] (by decide) s3_364_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_215_safe
  · subst z; exact s4_1022_safe
  · subst z; exact s4_802_safe
  · subst z; exact s4_811_safe
  · subst z; exact s4_791_safe
  · subst z; exact s4_749_safe
  · subst z; exact s4_759_safe
  · subst z; exact s4_732_safe
def s3_365 : State := ⟨[3,4,96,144], 22301085480897623308161714358337464822726942, 1, 0, 1, 0⟩
theorem s3_365_edges : next config 3 s3_365 = [s4_227, s4_1024, s4_803, s4_793, s4_750, s4_760, s4_736, s4_741] := by decide
theorem s3_365_safe : Safe 10 3 s3_365 := by
  apply safe_succ 9 3 s3_365 [s4_227, s4_1024, s4_803, s4_793, s4_750, s4_760, s4_736, s4_741] (by decide) s3_365_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_227_safe
  · subst z; exact s4_1024_safe
  · subst z; exact s4_803_safe
  · subst z; exact s4_793_safe
  · subst z; exact s4_750_safe
  · subst z; exact s4_760_safe
  · subst z; exact s4_736_safe
  · subst z; exact s4_741_safe
def s3_366 : State := ⟨[3,4,96,160], 1461501637671185285203851458712368708759249289502, 1, 0, 1, 0⟩
theorem s3_366_edges : next config 3 s3_366 = [s4_1221, s4_238, s4_1026, s4_804, s4_794, s4_751, s4_761, s4_740, s4_738, s4_742] := by decide
theorem s3_366_safe : Safe 10 3 s3_366 := by
  apply safe_succ 9 3 s3_366 [s4_1221, s4_238, s4_1026, s4_804, s4_794, s4_751, s4_761, s4_740, s4_738, s4_742] (by decide) s3_366_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1221_safe
  · subst z; exact s4_238_safe
  · subst z; exact s4_1026_safe
  · subst z; exact s4_804_safe
  · subst z; exact s4_794_safe
  · subst z; exact s4_751_safe
  · subst z; exact s4_761_safe
  · subst z; exact s4_740_safe
  · subst z; exact s4_738_safe
  · subst z; exact s4_742_safe
def s3_367 : State := ⟨[3,4,96,192], 6277101735386680764176071790207833042098441133567351259422, 1, 0, 1, 0⟩
theorem s3_367_edges : next config 3 s3_367 = [s4_258, s4_1031, s4_805, s4_795, s4_752, s4_762] := by decide
theorem s3_367_safe : Safe 10 3 s3_367 := by
  apply safe_succ 9 3 s3_367 [s4_258, s4_1031, s4_805, s4_795, s4_752, s4_762] (by decide) s3_367_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_258_safe
  · subst z; exact s4_1031_safe
  · subst z; exact s4_805_safe
  · subst z; exact s4_795_safe
  · subst z; exact s4_752_safe
  · subst z; exact s4_762_safe
def s3_368 : State := ⟨[3,4,96,224], 26959946667150639794667015087359913040637311048536658170206926995742, 1, 0, 1, 0⟩
theorem s3_368_edges : next config 3 s3_368 = [s4_278, s4_1033, s4_806, s4_812, s4_796, s4_753, s4_763, s4_744] := by decide
theorem s3_368_safe : Safe 10 3 s3_368 := by
  apply safe_succ 9 3 s3_368 [s4_278, s4_1033, s4_806, s4_812, s4_796, s4_753, s4_763, s4_744] (by decide) s3_368_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_278_safe
  · subst z; exact s4_1033_safe
  · subst z; exact s4_806_safe
  · subst z; exact s4_812_safe
  · subst z; exact s4_796_safe
  · subst z; exact s4_753_safe
  · subst z; exact s4_763_safe
  · subst z; exact s4_744_safe
def s3_369 : State := ⟨[3,4,100,128], 340282368267817226224315090600019951902, 1, 0, 0, 0⟩
theorem s3_369_edges : next config 3 s3_369 = [s4_297, s4_747, s4_748, s4_754, s4_746, s4_749, s4_750, s4_751] := by decide
theorem s3_369_safe : Safe 10 3 s3_369 := by
  apply safe_succ 9 3 s3_369 [s4_297, s4_747, s4_748, s4_754, s4_746, s4_749, s4_750, s4_751] (by decide) s3_369_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_297_safe
  · subst z; exact s4_747_safe
  · subst z; exact s4_748_safe
  · subst z; exact s4_754_safe
  · subst z; exact s4_746_safe
  · subst z; exact s4_749_safe
  · subst z; exact s4_750_safe
  · subst z; exact s4_751_safe
def s3_370 : State := ⟨[3,4,104,128], 340282387282576229647756113050568032542, 1, 0, 0, 0⟩
theorem s3_370_edges : next config 3 s3_370 = [s4_313, s4_1035, s4_809, s4_797, s4_765, s4_757, s4_758, s4_764, s4_756, s4_759, s4_760, s4_761] := by decide
theorem s3_370_safe : Safe 10 3 s3_370 := by
  apply safe_succ 9 3 s3_370 [s4_313, s4_1035, s4_809, s4_797, s4_765, s4_757, s4_758, s4_764, s4_756, s4_759, s4_760, s4_761] (by decide) s3_370_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_313_safe
  · subst z; exact s4_1035_safe
  · subst z; exact s4_809_safe
  · subst z; exact s4_797_safe
  · subst z; exact s4_765_safe
  · subst z; exact s4_757_safe
  · subst z; exact s4_758_safe
  · subst z; exact s4_764_safe
  · subst z; exact s4_756_safe
  · subst z; exact s4_759_safe
  · subst z; exact s4_760_safe
  · subst z; exact s4_761_safe
def s3_371 : State := ⟨[3,12,64,129], 1020847100762815390408570566373309223198, 3, 0, 1, 0⟩
theorem s3_371_edges : next config 3 s3_371 = [s4_412, s4_1037, s4_701, s4_777, s4_787, s4_767] := by decide
theorem s3_371_safe : Safe 10 3 s3_371 := by
  apply safe_succ 9 3 s3_371 [s4_412, s4_1037, s4_701, s4_777, s4_787, s4_767] (by decide) s3_371_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_412_safe
  · subst z; exact s4_1037_safe
  · subst z; exact s4_701_safe
  · subst z; exact s4_777_safe
  · subst z; exact s4_787_safe
  · subst z; exact s4_767_safe
def s3_372 : State := ⟨[3,12,64,130], 1701411834604692317335319781236845646110, 3, 0, 1, 0⟩
theorem s3_372_edges : next config 3 s3_372 = [s4_415, s4_1039, s4_702, s4_778, s4_788, s4_769, s4_771] := by decide
theorem s3_372_safe : Safe 10 3 s3_372 := by
  apply safe_succ 9 3 s3_372 [s4_415, s4_1039, s4_702, s4_778, s4_788, s4_769, s4_771] (by decide) s3_372_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_415_safe
  · subst z; exact s4_1039_safe
  · subst z; exact s4_702_safe
  · subst z; exact s4_778_safe
  · subst z; exact s4_788_safe
  · subst z; exact s4_769_safe
  · subst z; exact s4_771_safe
def s3_373 : State := ⟨[3,12,64,131], 3062541302288446171188818210963918491934, 3, 0, 1, 0⟩
theorem s3_373_edges : next config 3 s3_373 = [s4_419, s4_1041, s4_703, s4_779, s4_789, s4_773] := by decide
theorem s3_373_safe : Safe 10 3 s3_373 := by
  apply safe_succ 9 3 s3_373 [s4_419, s4_1041, s4_703, s4_779, s4_789, s4_773] (by decide) s3_373_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_419_safe
  · subst z; exact s4_1041_safe
  · subst z; exact s4_703_safe
  · subst z; exact s4_779_safe
  · subst z; exact s4_789_safe
  · subst z; exact s4_773_safe
def s3_374 : State := ⟨[3,12,64,132], 5784800237655953878895815070418064183582, 3, 0, 1, 0⟩
theorem s3_374_edges : next config 3 s3_374 = [s4_420, s4_1042, s4_704, s4_780, s4_790] := by decide
theorem s3_374_safe : Safe 10 3 s3_374 := by
  apply safe_succ 9 3 s3_374 [s4_420, s4_1042, s4_704, s4_780, s4_790] (by decide) s3_374_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_420_safe
  · subst z; exact s4_1042_safe
  · subst z; exact s4_704_safe
  · subst z; exact s4_780_safe
  · subst z; exact s4_790_safe
def s3_375 : State := ⟨[3,12,64,136], 87452568298681185110105720854042434933022, 3, 0, 1, 0⟩
theorem s3_375_edges : next config 3 s3_375 = [s4_423, s4_1044, s4_705, s4_781, s4_791] := by decide
theorem s3_375_safe : Safe 10 3 s3_375 := by
  apply safe_succ 9 3 s3_375 [s4_423, s4_1044, s4_705, s4_781, s4_791] (by decide) s3_375_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_423_safe
  · subst z; exact s4_1044_safe
  · subst z; exact s4_705_safe
  · subst z; exact s4_781_safe
  · subst z; exact s4_791_safe
def s3_376 : State := ⟨[3,12,64,140], 1394136857275084884809464213392032366924062, 3, 0, 1, 0⟩
theorem s3_376_edges : next config 3 s3_376 = [s4_426, s4_1046, s4_707, s4_782, s4_792] := by decide
theorem s3_376_safe : Safe 10 3 s3_376 := by
  apply safe_succ 9 3 s3_376 [s4_426, s4_1046, s4_707, s4_782, s4_792] (by decide) s3_376_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_426_safe
  · subst z; exact s4_1046_safe
  · subst z; exact s4_707_safe
  · subst z; exact s4_782_safe
  · subst z; exact s4_792_safe
def s3_377 : State := ⟨[3,12,64,144], 22301085480897544079999200093999871278780702, 3, 0, 1, 0⟩
theorem s3_377_edges : next config 3 s3_377 = [s4_429, s4_1048, s4_708, s4_783, s4_793, s4_770, s4_775] := by decide
theorem s3_377_safe : Safe 10 3 s3_377 := by
  apply safe_succ 9 3 s3_377 [s4_429, s4_1048, s4_708, s4_783, s4_793, s4_770, s4_775] (by decide) s3_377_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_429_safe
  · subst z; exact s4_1048_safe
  · subst z; exact s4_708_safe
  · subst z; exact s4_783_safe
  · subst z; exact s4_793_safe
  · subst z; exact s4_770_safe
  · subst z; exact s4_775_safe
def s3_378 : State := ⟨[3,12,64,160], 1461501637671185285124623296198104371165705343262, 3, 0, 1, 0⟩
theorem s3_378_edges : next config 3 s3_378 = [s4_1227, s4_433, s4_1050, s4_712, s4_784, s4_794, s4_774, s4_772, s4_776] := by decide
theorem s3_378_safe : Safe 10 3 s3_378 := by
  apply safe_succ 9 3 s3_378 [s4_1227, s4_433, s4_1050, s4_712, s4_784, s4_794, s4_774, s4_772, s4_776] (by decide) s3_378_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1227_safe
  · subst z; exact s4_433_safe
  · subst z; exact s4_1050_safe
  · subst z; exact s4_712_safe
  · subst z; exact s4_784_safe
  · subst z; exact s4_794_safe
  · subst z; exact s4_774_safe
  · subst z; exact s4_772_safe
  · subst z; exact s4_776_safe
def s3_379 : State := ⟨[3,12,64,192], 6277101735386680764176071790128604879584176795973807313182, 3, 0, 1, 0⟩
theorem s3_379_edges : next config 3 s3_379 = [s4_444, s4_1055, s4_715, s4_785, s4_795] := by decide
theorem s3_379_safe : Safe 10 3 s3_379 := by
  apply safe_succ 9 3 s3_379 [s4_444, s4_1055, s4_715, s4_785, s4_795] (by decide) s3_379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_444_safe
  · subst z; exact s4_1055_safe
  · subst z; exact s4_715_safe
  · subst z; exact s4_785_safe
  · subst z; exact s4_795_safe
def s3_380 : State := ⟨[3,12,67,128], 340282366920938463629395304099449213214, 3, 0, 0, 0⟩
theorem s3_380_edges : next config 3 s3_380 = [s4_473, s4_1057, s4_716, s4_779, s4_782, s4_786, s4_778, s4_781, s4_783, s4_784] := by decide
theorem s3_380_safe : Safe 10 3 s3_380 := by
  apply safe_succ 9 3 s3_380 [s4_473, s4_1057, s4_716, s4_779, s4_782, s4_786, s4_778, s4_781, s4_783, s4_784] (by decide) s3_380_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_473_safe
  · subst z; exact s4_1057_safe
  · subst z; exact s4_716_safe
  · subst z; exact s4_779_safe
  · subst z; exact s4_782_safe
  · subst z; exact s4_786_safe
  · subst z; exact s4_778_safe
  · subst z; exact s4_781_safe
  · subst z; exact s4_783_safe
  · subst z; exact s4_784_safe
def s3_381 : State := ⟨[3,12,96,128], 340282367000166625996085689103316750622, 3, 0, 0, 0⟩
theorem s3_381_edges : next config 3 s3_381 = [s4_518, s4_1058, s4_729, s4_797, s4_789, s4_792, s4_796, s4_788, s4_791, s4_793, s4_794] := by decide
theorem s3_381_safe : Safe 10 3 s3_381 := by
  apply safe_succ 9 3 s3_381 [s4_518, s4_1058, s4_729, s4_797, s4_789, s4_792, s4_796, s4_788, s4_791, s4_793, s4_794] (by decide) s3_381_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_518_safe
  · subst z; exact s4_1058_safe
  · subst z; exact s4_729_safe
  · subst z; exact s4_797_safe
  · subst z; exact s4_789_safe
  · subst z; exact s4_792_safe
  · subst z; exact s4_796_safe
  · subst z; exact s4_788_safe
  · subst z; exact s4_791_safe
  · subst z; exact s4_793_safe
  · subst z; exact s4_794_safe
def s3_382 : State := ⟨[3,100,96,128], 340282368267817226224315090600019951902, 3, 0, 0, 0⟩
theorem s3_382_edges : next config 3 s3_382 = [s4_626, s4_730, s4_808, s4_800, s4_807, s4_806, s4_799, s4_802, s4_803, s4_804] := by decide
theorem s3_382_safe : Safe 10 3 s3_382 := by
  apply safe_succ 9 3 s3_382 [s4_626, s4_730, s4_808, s4_800, s4_807, s4_806, s4_799, s4_802, s4_803, s4_804] (by decide) s3_382_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_626_safe
  · subst z; exact s4_730_safe
  · subst z; exact s4_808_safe
  · subst z; exact s4_800_safe
  · subst z; exact s4_807_safe
  · subst z; exact s4_806_safe
  · subst z; exact s4_799_safe
  · subst z; exact s4_802_safe
  · subst z; exact s4_803_safe
  · subst z; exact s4_804_safe
def s3_383 : State := ⟨[3,140,64,136], 1481249143206845131456088112894565029052702, 3, 0, 1, 0⟩
theorem s3_383_edges : next config 3 s3_383 = [s4_662, s4_1060, s4_706, s4_810, s4_811] := by decide
theorem s3_383_safe : Safe 10 3 s3_383 := by
  apply safe_succ 9 3 s3_383 [s4_662, s4_1060, s4_706, s4_810, s4_811] (by decide) s3_383_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_662_safe
  · subst z; exact s4_1060_safe
  · subst z; exact s4_706_safe
  · subst z; exact s4_810_safe
  · subst z; exact s4_811_safe
def s3_384 : State := ⟨[9,4,64,145], 44602511244162009098461845115863096321180438, 1, 0, 1, 0⟩
theorem s3_384_edges : next config 3 s3_384 = [s4_12, s4_816] := by decide
theorem s3_384_safe : Safe 10 3 s3_384 := by
  apply safe_succ 9 3 s3_384 [s4_12, s4_816] (by decide) s3_384_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_12_safe
  · subst z; exact s4_816_safe
def s3_385 : State := ⟨[9,4,64,145], 66902575877958790363070636639296594290737942, 1, 0, 1, 0⟩
theorem s3_385_edges : next config 3 s3_385 = [s4_18, s4_817] := by decide
theorem s3_385_safe : Safe 10 3 s3_385 := by
  apply safe_succ 9 3 s3_385 [s4_18, s4_817] (by decide) s3_385_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_18_safe
  · subst z; exact s4_817_safe
def s3_386 : State := ⟨[9,4,64,162], 5846006551025023507419431648200451859860575814422, 1, 0, 1, 0⟩
theorem s3_386_edges : next config 3 s3_386 = [s4_1237, s4_37, s4_818, s4_814] := by decide
theorem s3_386_safe : Safe 10 3 s3_386 := by
  apply safe_succ 9 3 s3_386 [s4_1237, s4_37, s4_818, s4_814] (by decide) s3_386_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1237_safe
  · subst z; exact s4_37_safe
  · subst z; exact s4_818_safe
  · subst z; exact s4_814_safe
def s3_387 : State := ⟨[9,4,64,162], 7307508186994796957939362627063236449789435511574, 1, 0, 1, 0⟩
theorem s3_387_edges : next config 3 s3_387 = [s4_1238, s4_42, s4_819, s4_815] := by decide
theorem s3_387_safe : Safe 10 3 s3_387 := by
  apply safe_succ 9 3 s3_387 [s4_1238, s4_42, s4_819, s4_815] (by decide) s3_387_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1238_safe
  · subst z; exact s4_42_safe
  · subst z; exact s4_819_safe
  · subst z; exact s4_815_safe
def s3_388 : State := ⟨[9,4,96,129], 1020847100842043552922834903966853169942, 1, 0, 1, 0⟩
theorem s3_388_edges : next config 3 s3_388 = [s4_190, s4_820, s4_816] := by decide
theorem s3_388_safe : Safe 10 3 s3_388 := by
  apply safe_succ 9 3 s3_388 [s4_190, s4_820, s4_816] (by decide) s3_388_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_190_safe
  · subst z; exact s4_820_safe
  · subst z; exact s4_816_safe
def s3_389 : State := ⟨[9,4,96,130], 1701411834683920479849584118830389592854, 1, 0, 1, 0⟩
theorem s3_389_edges : next config 3 s3_389 = [s4_198, s4_821, s4_818] := by decide
theorem s3_389_safe : Safe 10 3 s3_389 := by
  apply safe_succ 9 3 s3_389 [s4_198, s4_821, s4_818] (by decide) s3_389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_198_safe
  · subst z; exact s4_821_safe
  · subst z; exact s4_818_safe
def s3_390 : State := ⟨[9,4,96,132], 5784800237735182041410079408011608130326, 1, 0, 1, 0⟩
theorem s3_390_edges : next config 3 s3_390 = [s4_208, s4_822] := by decide
theorem s3_390_safe : Safe 10 3 s3_390 := by
  apply safe_succ 9 3 s3_390 [s4_208, s4_822] (by decide) s3_390_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_208_safe
  · subst z; exact s4_822_safe
def s3_391 : State := ⟨[9,4,96,136], 87452568298760413272619985191635978879766, 1, 0, 1, 0⟩
theorem s3_391_edges : next config 3 s3_391 = [s4_216, s4_823] := by decide
theorem s3_391_safe : Safe 10 3 s3_391 := by
  apply safe_succ 9 3 s3_391 [s4_216, s4_823] (by decide) s3_391_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_216_safe
  · subst z; exact s4_823_safe
def s3_392 : State := ⟨[9,4,96,137], 174564854230520659919243884694168641012502, 1, 0, 1, 0⟩
theorem s3_392_edges : next config 3 s3_392 = [s4_225, s4_824] := by decide
theorem s3_392_safe : Safe 10 3 s3_392 := by
  apply safe_succ 9 3 s3_392 [s4_225, s4_824] (by decide) s3_392_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_225_safe
  · subst z; exact s4_824_safe
def s3_393 : State := ⟨[9,4,96,144], 22301085480897623308161714358337464822727446, 1, 0, 1, 0⟩
theorem s3_393_edges : next config 3 s3_393 = [s4_228, s4_825] := by decide
theorem s3_393_safe : Safe 10 3 s3_393 := by
  apply safe_succ 9 3 s3_393 [s4_228, s4_825] (by decide) s3_393_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_228_safe
  · subst z; exact s4_825_safe
def s3_394 : State := ⟨[9,4,96,160], 1461501637671185285203851458712368708759249290006, 1, 0, 1, 0⟩
theorem s3_394_edges : next config 3 s3_394 = [s4_239, s4_826, s4_819] := by decide
theorem s3_394_safe : Safe 10 3 s3_394 := by
  apply safe_succ 9 3 s3_394 [s4_239, s4_826, s4_819] (by decide) s3_394_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_239_safe
  · subst z; exact s4_826_safe
  · subst z; exact s4_819_safe
def s3_395 : State := ⟨[9,4,96,192], 6277101735386680764176071790207833042098441133567351259926, 1, 0, 1, 0⟩
theorem s3_395_edges : next config 3 s3_395 = [s4_259, s4_827] := by decide
theorem s3_395_safe : Safe 10 3 s3_395 := by
  apply safe_succ 9 3 s3_395 [s4_259, s4_827] (by decide) s3_395_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_259_safe
  · subst z; exact s4_827_safe
def s3_396 : State := ⟨[9,4,96,224], 26959946667150639794667015087359913040637311048536658170206926996246, 1, 0, 1, 0⟩
theorem s3_396_edges : next config 3 s3_396 = [s4_279, s4_828] := by decide
theorem s3_396_safe : Safe 10 3 s3_396 := by
  apply safe_succ 9 3 s3_396 [s4_279, s4_828] (by decide) s3_396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_279_safe
  · subst z; exact s4_828_safe
def s3_397 : State := ⟨[9,4,104,128], 340282387282576229647756113050568033046, 1, 0, 0, 0⟩
theorem s3_397_edges : next config 3 s3_397 = [s4_314, s4_824, s4_822, s4_829, s4_821, s4_823, s4_825, s4_826] := by decide
theorem s3_397_safe : Safe 10 3 s3_397 := by
  apply safe_succ 9 3 s3_397 [s4_314, s4_824, s4_822, s4_829, s4_821, s4_823, s4_825, s4_826] (by decide) s3_397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_314_safe
  · subst z; exact s4_824_safe
  · subst z; exact s4_822_safe
  · subst z; exact s4_829_safe
  · subst z; exact s4_821_safe
  · subst z; exact s4_823_safe
  · subst z; exact s4_825_safe
  · subst z; exact s4_826_safe
def s3_398 : State := ⟨[17,4,64,128], 340282366920938463481821351509772927262, 1, 1, 0, 0⟩
theorem s3_398_edges : next config 3 s3_398 = [s4_891, s4_873, s4_855, s4_830] := by decide
theorem s3_398_safe : Safe 10 3 s3_398 := by
  apply safe_succ 9 3 s3_398 [s4_891, s4_873, s4_855, s4_830] (by decide) s3_398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_891_safe
  · subst z; exact s4_873_safe
  · subst z; exact s4_855_safe
  · subst z; exact s4_830_safe
def s3_399 : State := ⟨[17,4,64,128], 340282366920938463481821351509772927766, 1, 1, 0, 0⟩
theorem s3_399_edges : next config 3 s3_399 = [s4_892, s4_856, s4_831] := by decide
theorem s3_399_safe : Safe 10 3 s3_399 := by
  apply safe_succ 9 3 s3_399 [s4_892, s4_856, s4_831] (by decide) s3_399_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_892_safe
  · subst z; exact s4_856_safe
  · subst z; exact s4_831_safe
def s3_400 : State := ⟨[17,4,64,128], 340282366920938463481821351509772931350, 3, 2, 0, 0⟩
theorem s3_400_edges : next config 3 s3_400 = [s4_893, s4_849, s4_839, s4_847, s4_857, s4_832] := by decide
theorem s3_400_safe : Safe 10 3 s3_400 := by
  apply safe_succ 9 3 s3_400 [s4_893, s4_849, s4_839, s4_847, s4_857, s4_832] (by decide) s3_400_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_893_safe
  · subst z; exact s4_849_safe
  · subst z; exact s4_839_safe
  · subst z; exact s4_847_safe
  · subst z; exact s4_857_safe
  · subst z; exact s4_832_safe
def s3_401 : State := ⟨[17,4,64,128], 340282366920938463481821351509775024406, 3, 2, 0, 0⟩
theorem s3_401_edges : next config 3 s3_401 = [s4_920, s4_874, s4_850, s4_846, s4_840, s4_848, s4_858, s4_833] := by decide
theorem s3_401_safe : Safe 10 3 s3_401 := by
  apply safe_succ 9 3 s3_401 [s4_920, s4_874, s4_850, s4_846, s4_840, s4_848, s4_858, s4_833] (by decide) s3_401_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_920_safe
  · subst z; exact s4_874_safe
  · subst z; exact s4_850_safe
  · subst z; exact s4_846_safe
  · subst z; exact s4_840_safe
  · subst z; exact s4_848_safe
  · subst z; exact s4_858_safe
  · subst z; exact s4_833_safe
def s3_402 : State := ⟨[17,4,64,128], 340282366920938463481821351518362861846, 1, 1, 0, 0⟩
theorem s3_402_edges : next config 3 s3_402 = [s4_894, s4_875, s4_859, s4_834] := by decide
theorem s3_402_safe : Safe 10 3 s3_402 := by
  apply safe_succ 9 3 s3_402 [s4_894, s4_875, s4_859, s4_834] (by decide) s3_402_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_894_safe
  · subst z; exact s4_875_safe
  · subst z; exact s4_859_safe
  · subst z; exact s4_834_safe
def s3_403 : State := ⟨[17,4,64,128], 340282366920938463518714839657192030486, 1, 1, 0, 0⟩
theorem s3_403_edges : next config 3 s3_403 = [s4_895, s4_876, s4_860, s4_835] := by decide
theorem s3_403_safe : Safe 10 3 s3_403 := by
  apply safe_succ 9 3 s3_403 [s4_895, s4_876, s4_860, s4_835] (by decide) s3_403_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_895_safe
  · subst z; exact s4_876_safe
  · subst z; exact s4_860_safe
  · subst z; exact s4_835_safe
def s3_404 : State := ⟨[17,4,64,128], 340282366920938463776969256689125753110, 3, 2, 0, 0⟩
theorem s3_404_edges : next config 3 s3_404 = [s4_896, s4_861, s4_836] := by decide
theorem s3_404_safe : Safe 10 3 s3_404 := by
  apply safe_succ 9 3 s3_404 [s4_896, s4_861, s4_836] (by decide) s3_404_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_896_safe
  · subst z; exact s4_861_safe
  · subst z; exact s4_836_safe
def s3_405 : State := ⟨[17,4,65,145], 44601830679428167221534955260136380203991318, 1, 0, 1, 0⟩
theorem s3_405_edges : next config 3 s3_405 = [s4_929, s4_938, s4_86, s4_897, s4_877, s4_844] := by decide
theorem s3_405_safe : Safe 10 3 s3_405 := by
  apply safe_succ 9 3 s3_405 [s4_929, s4_938, s4_86, s4_897, s4_877, s4_844] (by decide) s3_405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_929_safe
  · subst z; exact s4_938_safe
  · subst z; exact s4_86_safe
  · subst z; exact s4_897_safe
  · subst z; exact s4_877_safe
  · subst z; exact s4_844_safe
def s3_406 : State := ⟨[17,4,66,145], 44601830679428167221534992153624527623094550, 1, 0, 1, 0⟩
theorem s3_406_edges : next config 3 s3_406 = [s4_930, s4_939, s4_97, s4_898, s4_878, s4_851] := by decide
theorem s3_406_safe : Safe 10 3 s3_406 := by
  apply safe_succ 9 3 s3_406 [s4_930, s4_939, s4_97, s4_898, s4_878, s4_851] (by decide) s3_406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_930_safe
  · subst z; exact s4_939_safe
  · subst z; exact s4_97_safe
  · subst z; exact s4_898_safe
  · subst z; exact s4_878_safe
  · subst z; exact s4_851_safe
def s3_407 : State := ⟨[17,4,67,128], 340282366920938463666288792246868443414, 1, 0, 0, 0⟩
theorem s3_407_edges : next config 3 s3_407 = [s4_899, s4_879, s4_844] := by decide
theorem s3_407_safe : Safe 10 3 s3_407 := by
  apply safe_succ 9 3 s3_407 [s4_899, s4_879, s4_844] (by decide) s3_407_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_899_safe
  · subst z; exact s4_879_safe
  · subst z; exact s4_844_safe
def s3_408 : State := ⟨[17,4,67,128], 340282366920938463703182280394287546646, 1, 0, 0, 0⟩
theorem s3_408_edges : next config 3 s3_408 = [s4_900, s4_880, s4_845] := by decide
theorem s3_408_safe : Safe 10 3 s3_408 := by
  apply safe_succ 9 3 s3_408 [s4_900, s4_880, s4_845] (by decide) s3_408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_900_safe
  · subst z; exact s4_880_safe
  · subst z; exact s4_845_safe
def s3_409 : State := ⟨[17,4,68,145], 44601830679428167221535213514553412137713942, 1, 0, 1, 0⟩
theorem s3_409_edges : next config 3 s3_409 = [s4_931, s4_136, s4_901] := by decide
theorem s3_409_safe : Safe 10 3 s3_409 := by
  apply safe_succ 9 3 s3_409 [s4_931, s4_136, s4_901] (by decide) s3_409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_931_safe
  · subst z; exact s4_136_safe
  · subst z; exact s4_901_safe
def s3_410 : State := ⟨[17,4,80,145], 44601830679428167222743844186262861959594262, 1, 0, 1, 0⟩
theorem s3_410_edges : next config 3 s3_410 = [s4_932, s4_146, s4_902, s4_881, s4_852] := by decide
theorem s3_410_safe : Safe 10 3 s3_410 := by
  apply safe_succ 9 3 s3_410 [s4_932, s4_146, s4_902, s4_881, s4_852] (by decide) s3_410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_932_safe
  · subst z; exact s4_146_safe
  · subst z; exact s4_902_safe
  · subst z; exact s4_881_safe
  · subst z; exact s4_852_safe
def s3_411 : State := ⟨[17,4,81,145], 44601830679428167223952770005877491134300438, 1, 0, 1, 0⟩
theorem s3_411_edges : next config 3 s3_411 = [s4_933, s4_152, s4_903, s4_882] := by decide
theorem s3_411_safe : Safe 10 3 s3_411 := by
  apply safe_succ 9 3 s3_411 [s4_933, s4_152, s4_903, s4_882] (by decide) s3_411_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_933_safe
  · subst z; exact s4_152_safe
  · subst z; exact s4_903_safe
  · subst z; exact s4_882_safe
def s3_412 : State := ⟨[17,4,82,128], 340282366920943299258886786321309958422, 1, 0, 0, 0⟩
theorem s3_412_edges : next config 3 s3_412 = [s4_904, s4_923, s4_883, s4_842, s4_853, s4_851] := by decide
theorem s3_412_safe : Safe 10 3 s3_412 := by
  apply safe_succ 9 3 s3_412 [s4_904, s4_923, s4_883, s4_842, s4_853, s4_851] (by decide) s3_412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_904_safe
  · subst z; exact s4_923_safe
  · subst z; exact s4_883_safe
  · subst z; exact s4_842_safe
  · subst z; exact s4_853_safe
  · subst z; exact s4_851_safe
def s3_413 : State := ⟨[17,4,82,128], 340282366920944508110919424655646458134, 1, 0, 0, 0⟩
theorem s3_413_edges : next config 3 s3_413 = [s4_905, s4_924, s4_884, s4_843, s4_854, s4_852] := by decide
theorem s3_413_safe : Safe 10 3 s3_413 := by
  apply safe_succ 9 3 s3_413 [s4_905, s4_924, s4_884, s4_843, s4_854, s4_852] (by decide) s3_413_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_905_safe
  · subst z; exact s4_924_safe
  · subst z; exact s4_884_safe
  · subst z; exact s4_843_safe
  · subst z; exact s4_854_safe
  · subst z; exact s4_852_safe
def s3_414 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826328838422, 1, 0, 1, 0⟩
theorem s3_414_edges : next config 3 s3_414 = [s4_934, s4_1202, s4_940, s4_235, s4_1085, s4_906, s4_925, s4_885, s4_869, s4_865, s4_872, s4_866, s4_868] := by decide
theorem s3_414_safe : Safe 10 3 s3_414 := by
  apply safe_succ 9 3 s3_414 [s4_934, s4_1202, s4_940, s4_235, s4_1085, s4_906, s4_925, s4_885, s4_869, s4_865, s4_872, s4_866, s4_868] (by decide) s3_414_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_934_safe
  · subst z; exact s4_1202_safe
  · subst z; exact s4_940_safe
  · subst z; exact s4_235_safe
  · subst z; exact s4_1085_safe
  · subst z; exact s4_906_safe
  · subst z; exact s4_925_safe
  · subst z; exact s4_885_safe
  · subst z; exact s4_869_safe
  · subst z; exact s4_865_safe
  · subst z; exact s4_872_safe
  · subst z; exact s4_866_safe
  · subst z; exact s4_868_safe
def s3_415 : State := ⟨[17,4,97,128], 340282367158622951024614364290404778262, 1, 0, 0, 0⟩
theorem s3_415_edges : next config 3 s3_415 = [s4_907, s4_886, s4_864] := by decide
theorem s3_415_safe : Safe 10 3 s3_415 := by
  apply safe_succ 9 3 s3_415 [s4_907, s4_886, s4_864] (by decide) s3_415_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_907_safe
  · subst z; exact s4_886_safe
  · subst z; exact s4_864_safe
def s3_416 : State := ⟨[17,4,100,128], 340282368267817226224315090600020082966, 1, 0, 0, 0⟩
theorem s3_416_edges : next config 3 s3_416 = [s4_908, s4_865] := by decide
theorem s3_416_safe : Safe 10 3 s3_416 := by
  apply safe_succ 9 3 s3_416 [s4_908, s4_865] (by decide) s3_416_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_908_safe
  · subst z; exact s4_865_safe
def s3_417 : State := ⟨[17,4,104,128], 340282387282576229647756113050568163606, 1, 0, 0, 0⟩
theorem s3_417_edges : next config 3 s3_417 = [s4_909, s4_927, s4_887, s4_871, s4_867, s4_870, s4_866] := by decide
theorem s3_417_safe : Safe 10 3 s3_417 := by
  apply safe_succ 9 3 s3_417 [s4_909, s4_927, s4_887, s4_871, s4_867, s4_870, s4_866] (by decide) s3_417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_909_safe
  · subst z; exact s4_927_safe
  · subst z; exact s4_887_safe
  · subst z; exact s4_871_safe
  · subst z; exact s4_867_safe
  · subst z; exact s4_870_safe
  · subst z; exact s4_866_safe
def s3_418 : State := ⟨[17,4,112,128], 340287559297025160823714219599646097686, 1, 0, 0, 0⟩
theorem s3_418_edges : next config 3 s3_418 = [s4_910, s4_888, s4_868] := by decide
theorem s3_418_safe : Safe 10 3 s3_418 := by
  apply safe_succ 9 3 s3_418 [s4_910, s4_888, s4_868] (by decide) s3_418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_910_safe
  · subst z; exact s4_888_safe
  · subst z; exact s4_868_safe
def s3_419 : State := ⟨[17,4,113,128], 340292751593883695651342750095975317782, 1, 0, 0, 0⟩
theorem s3_419_edges : next config 3 s3_419 = [s4_911, s4_889, s4_869] := by decide
theorem s3_419_safe : Safe 10 3 s3_419 := by
  apply safe_succ 9 3 s3_419 [s4_911, s4_889, s4_869] (by decide) s3_419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_911_safe
  · subst z; exact s4_889_safe
  · subst z; exact s4_869_safe
def s3_420 : State := ⟨[17,4,209,145], 822752278660603021122086421958103419712902851183438164459192598, 1, 0, 1, 0⟩
theorem s3_420_edges : next config 3 s3_420 = [s4_935, s4_391, s4_913, s4_890] := by decide
theorem s3_420_safe : Safe 10 3 s3_420 := by
  apply safe_succ 9 3 s3_420 [s4_935, s4_391, s4_913, s4_890] (by decide) s3_420_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_935_safe
  · subst z; exact s4_391_safe
  · subst z; exact s4_913_safe
  · subst z; exact s4_890_safe
def s3_421 : State := ⟨[17,12,64,145], 44601830679428167221534918366648232784892182, 3, 0, 1, 0⟩
theorem s3_421_edges : next config 3 s3_421 = [s4_1170, s4_432, s4_1086, s4_832, s4_882, s4_890, s4_878, s4_881, s4_885] := by decide
theorem s3_421_safe : Safe 10 3 s3_421 := by
  apply safe_succ 9 3 s3_421 [s4_1170, s4_432, s4_1086, s4_832, s4_882, s4_890, s4_878, s4_881, s4_885] (by decide) s3_421_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1170_safe
  · subst z; exact s4_432_safe
  · subst z; exact s4_1086_safe
  · subst z; exact s4_832_safe
  · subst z; exact s4_882_safe
  · subst z; exact s4_890_safe
  · subst z; exact s4_878_safe
  · subst z; exact s4_881_safe
  · subst z; exact s4_885_safe
def s3_422 : State := ⟨[17,12,65,128], 340282366920938463518714839657192034582, 3, 0, 0, 0⟩
theorem s3_422_edges : next config 3 s3_422 = [s4_837, s4_879, s4_877] := by decide
theorem s3_422_safe : Safe 10 3 s3_422 := by
  apply safe_succ 9 3 s3_422 [s4_837, s4_879, s4_877] (by decide) s3_422_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_837_safe
  · subst z; exact s4_879_safe
  · subst z; exact s4_877_safe
def s3_423 : State := ⟨[17,12,66,128], 340282366920938463555608327804611137814, 3, 0, 0, 0⟩
theorem s3_423_edges : next config 3 s3_423 = [s4_839, s4_883, s4_878] := by decide
theorem s3_423_safe : Safe 10 3 s3_423 := by
  apply safe_succ 9 3 s3_423 [s4_839, s4_883, s4_878] (by decide) s3_423_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_839_safe
  · subst z; exact s4_883_safe
  · subst z; exact s4_878_safe
def s3_424 : State := ⟨[17,12,80,128], 340282366920939672407640966138947637526, 3, 0, 0, 0⟩
theorem s3_424_edges : next config 3 s3_424 = [s4_847, s4_884, s4_881] := by decide
theorem s3_424_safe : Safe 10 3 s3_424 := by
  apply safe_succ 9 3 s3_424 [s4_847, s4_884, s4_881] (by decide) s3_424_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_847_safe
  · subst z; exact s4_884_safe
  · subst z; exact s4_881_safe
def s3_425 : State := ⟨[17,12,81,128], 340282366920940881333460580768122343702, 3, 0, 0, 0⟩
theorem s3_425_edges : next config 3 s3_425 = [s4_849, s4_882] := by decide
theorem s3_425_safe : Safe 10 3 s3_425 := by
  apply safe_succ 9 3 s3_425 [s4_849, s4_882] (by decide) s3_425_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_849_safe
  · subst z; exact s4_882_safe
def s3_426 : State := ⟨[17,12,96,128], 340282367000166625996085689103316881686, 3, 0, 0, 0⟩
theorem s3_426_edges : next config 3 s3_426 = [s4_857, s4_889, s4_887, s4_888, s4_885] := by decide
theorem s3_426_safe : Safe 10 3 s3_426 := by
  apply safe_succ 9 3 s3_426 [s4_857, s4_889, s4_887, s4_888, s4_885] (by decide) s3_426_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_857_safe
  · subst z; exact s4_889_safe
  · subst z; exact s4_887_safe
  · subst z; exact s4_888_safe
  · subst z; exact s4_885_safe
def s3_427 : State := ⟨[17,21,64,145], 44601830679428167221534918366648232786985238, 3, 0, 1, 0⟩
theorem s3_427_edges : next config 3 s3_427 = [s4_1171, s4_941, s4_588, s4_1087, s4_833, s4_914, s4_918, s4_903, s4_913, s4_898, s4_902, s4_906] := by decide
theorem s3_427_safe : Safe 10 3 s3_427 := by
  apply safe_succ 9 3 s3_427 [s4_1171, s4_941, s4_588, s4_1087, s4_833, s4_914, s4_918, s4_903, s4_913, s4_898, s4_902, s4_906] (by decide) s3_427_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1171_safe
  · subst z; exact s4_941_safe
  · subst z; exact s4_588_safe
  · subst z; exact s4_1087_safe
  · subst z; exact s4_833_safe
  · subst z; exact s4_914_safe
  · subst z; exact s4_918_safe
  · subst z; exact s4_903_safe
  · subst z; exact s4_913_safe
  · subst z; exact s4_898_safe
  · subst z; exact s4_902_safe
  · subst z; exact s4_906_safe
def s3_428 : State := ⟨[17,21,65,128], 340282366920938463518714839657194127638, 3, 0, 0, 0⟩
theorem s3_428_edges : next config 3 s3_428 = [s4_838, s4_915, s4_899, s4_897] := by decide
theorem s3_428_safe : Safe 10 3 s3_428 := by
  apply safe_succ 9 3 s3_428 [s4_838, s4_915, s4_899, s4_897] (by decide) s3_428_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_838_safe
  · subst z; exact s4_915_safe
  · subst z; exact s4_899_safe
  · subst z; exact s4_897_safe
def s3_429 : State := ⟨[17,21,66,128], 340282366920938463555608327804613230870, 3, 0, 0, 0⟩
theorem s3_429_edges : next config 3 s3_429 = [s4_840, s4_916, s4_904, s4_898] := by decide
theorem s3_429_safe : Safe 10 3 s3_429 := by
  apply safe_succ 9 3 s3_429 [s4_840, s4_916, s4_904, s4_898] (by decide) s3_429_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_840_safe
  · subst z; exact s4_916_safe
  · subst z; exact s4_904_safe
  · subst z; exact s4_898_safe
def s3_430 : State := ⟨[17,21,68,128], 340282366920938463776969256689127850262, 3, 0, 0, 0⟩
theorem s3_430_edges : next config 3 s3_430 = [s4_846, s4_901] := by decide
theorem s3_430_safe : Safe 10 3 s3_430 := by
  apply safe_succ 9 3 s3_430 [s4_846, s4_901] (by decide) s3_430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_846_safe
  · subst z; exact s4_901_safe
def s3_431 : State := ⟨[17,21,80,128], 340282366920939672407640966138949730582, 3, 0, 0, 0⟩
theorem s3_431_edges : next config 3 s3_431 = [s4_848, s4_905, s4_902] := by decide
theorem s3_431_safe : Safe 10 3 s3_431 := by
  apply safe_succ 9 3 s3_431 [s4_848, s4_905, s4_902] (by decide) s3_431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_848_safe
  · subst z; exact s4_905_safe
  · subst z; exact s4_902_safe
def s3_432 : State := ⟨[17,21,81,128], 340282366920940881333460580768124436758, 3, 0, 0, 0⟩
theorem s3_432_edges : next config 3 s3_432 = [s4_850, s4_903] := by decide
theorem s3_432_safe : Safe 10 3 s3_432 := by
  apply safe_succ 9 3 s3_432 [s4_850, s4_903] (by decide) s3_432_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_850_safe
  · subst z; exact s4_903_safe
def s3_433 : State := ⟨[17,21,96,128], 340282367000166625996085689103318974742, 3, 0, 0, 0⟩
theorem s3_433_edges : next config 3 s3_433 = [s4_858, s4_928, s4_917, s4_919, s4_911, s4_912, s4_909, s4_910, s4_906] := by decide
theorem s3_433_safe : Safe 10 3 s3_433 := by
  apply safe_succ 9 3 s3_433 [s4_858, s4_928, s4_917, s4_919, s4_911, s4_912, s4_909, s4_910, s4_906] (by decide) s3_433_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_858_safe
  · subst z; exact s4_928_safe
  · subst z; exact s4_917_safe
  · subst z; exact s4_919_safe
  · subst z; exact s4_911_safe
  · subst z; exact s4_912_safe
  · subst z; exact s4_909_safe
  · subst z; exact s4_910_safe
  · subst z; exact s4_906_safe
def s3_434 : State := ⟨[17,29,64,128], 340282366920938463481821351510311895318, 3, 0, 0, 0⟩
theorem s3_434_edges : next config 3 s3_434 = [s4_916, s4_917, s4_914] := by decide
theorem s3_434_safe : Safe 10 3 s3_434 := by
  apply safe_succ 9 3 s3_434 [s4_916, s4_917, s4_914] (by decide) s3_434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_916_safe
  · subst z; exact s4_917_safe
  · subst z; exact s4_914_safe
def s3_435 : State := ⟨[17,53,64,128], 340282366920938463481830358709029765398, 3, 0, 0, 0⟩
theorem s3_435_edges : next config 3 s3_435 = [s4_919, s4_918] := by decide
theorem s3_435_safe : Safe 10 3 s3_435 := by
  apply safe_succ 9 3 s3_435 [s4_919, s4_918] (by decide) s3_435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_919_safe
  · subst z; exact s4_918_safe
def s3_436 : State := ⟨[17,68,64,145], 44601830679428167221535213514553412137713942, 3, 0, 1, 0⟩
theorem s3_436_edges : next config 3 s3_436 = [s4_589, s4_836, s4_921] := by decide
theorem s3_436_safe : Safe 10 3 s3_436 := by
  apply safe_succ 9 3 s3_436 [s4_589, s4_836, s4_921] (by decide) s3_436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_589_safe
  · subst z; exact s4_836_safe
  · subst z; exact s4_921_safe
def s3_437 : State := ⟨[17,68,96,128], 340282367000166626291233594282669703446, 3, 0, 0, 0⟩
theorem s3_437_edges : next config 3 s3_437 = [s4_922, s4_921] := by decide
theorem s3_437_safe : Safe 10 3 s3_437 := by
  apply safe_succ 9 3 s3_437 [s4_922, s4_921] (by decide) s3_437_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_922_safe
  · subst z; exact s4_921_safe
def s3_438 : State := ⟨[17,100,96,128], 340282368267817226224315090600020082966, 3, 0, 0, 0⟩
theorem s3_438_edges : next config 3 s3_438 = [s4_863, s4_926, s4_925] := by decide
theorem s3_438_safe : Safe 10 3 s3_438 := by
  apply safe_succ 9 3 s3_438 [s4_863, s4_926, s4_925] (by decide) s3_438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_863_safe
  · subst z; exact s4_926_safe
  · subst z; exact s4_925_safe
def s3_439 : State := ⟨[21,4,64,145], 44601830679428167221534918366648232786985238, 1, 0, 1, 0⟩
theorem s3_439_edges : next config 3 s3_439 = [s4_942, s4_1088, s4_937, s4_936, s4_931, s4_935, s4_930, s4_932, s4_934] := by decide
theorem s3_439_safe : Safe 10 3 s3_439 := by
  apply safe_succ 9 3 s3_439 [s4_942, s4_1088, s4_937, s4_936, s4_931, s4_935, s4_930, s4_932, s4_934] (by decide) s3_439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_942_safe
  · subst z; exact s4_1088_safe
  · subst z; exact s4_937_safe
  · subst z; exact s4_936_safe
  · subst z; exact s4_931_safe
  · subst z; exact s4_935_safe
  · subst z; exact s4_930_safe
  · subst z; exact s4_932_safe
  · subst z; exact s4_934_safe
def s3_440 : State := ⟨[25,4,64,145], 44601830679428167221534918366648232818442518, 1, 0, 1, 0⟩
theorem s3_440_edges : next config 3 s3_440 = [s4_939, s4_940] := by decide
theorem s3_440_safe : Safe 10 3 s3_440 := by
  apply safe_succ 9 3 s3_440 [s4_939, s4_940] (by decide) s3_440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_939_safe
  · subst z; exact s4_940_safe
def s3_441 : State := ⟨[33,4,64,128], 340282366920938463481821351518362734870, 3, 2, 0, 0⟩
theorem s3_441_edges : next config 3 s3_441 = [s4_990, s4_1, s4_956, s4_952, s4_945, s4_955, s4_944, s4_946, s4_949, s4_951] := by decide
theorem s3_441_safe : Safe 10 3 s3_441 := by
  apply safe_succ 9 3 s3_441 [s4_990, s4_1, s4_956, s4_952, s4_945, s4_955, s4_944, s4_946, s4_949, s4_951] (by decide) s3_441_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_990_safe
  · subst z; exact s4_1_safe
  · subst z; exact s4_956_safe
  · subst z; exact s4_952_safe
  · subst z; exact s4_945_safe
  · subst z; exact s4_955_safe
  · subst z; exact s4_944_safe
  · subst z; exact s4_946_safe
  · subst z; exact s4_949_safe
  · subst z; exact s4_951_safe
def s3_442 : State := ⟨[33,4,64,140], 1399581375145819900224878207110949248237846, 1, 0, 1, 0⟩
theorem s3_442_edges : next config 3 s3_442 = [s4_992, s4_6, s4_957] := by decide
theorem s3_442_safe : Safe 10 3 s3_442 := by
  apply safe_succ 9 3 s3_442 [s4_992, s4_6, s4_957] (by decide) s3_442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_992_safe
  · subst z; exact s4_6_safe
  · subst z; exact s4_957_safe
def s3_443 : State := ⟨[33,4,64,140], 1481249143206845131456088112894573618987286, 1, 0, 1, 0⟩
theorem s3_443_edges : next config 3 s3_443 = [s4_994, s4_9, s4_958] := by decide
theorem s3_443_safe : Safe 10 3 s3_443 := by
  apply safe_succ 9 3 s3_443 [s4_994, s4_9, s4_958] (by decide) s3_443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_994_safe
  · subst z; exact s4_9_safe
  · subst z; exact s4_958_safe
def s3_444 : State := ⟨[33,4,64,145], 44602511244162009098461845115863104911114518, 1, 0, 1, 0⟩
theorem s3_444_edges : next config 3 s3_444 = [s4_996, s4_14, s4_973, s4_959] := by decide
theorem s3_444_safe : Safe 10 3 s3_444 := by
  apply safe_succ 9 3 s3_444 [s4_996, s4_14, s4_973, s4_959] (by decide) s3_444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_996_safe
  · subst z; exact s4_14_safe
  · subst z; exact s4_973_safe
  · subst z; exact s4_959_safe
def s3_445 : State := ⟨[33,4,64,145], 66902575877958790363070636639296602880672022, 1, 0, 1, 0⟩
theorem s3_445_edges : next config 3 s3_445 = [s4_998, s4_20, s4_974, s4_960] := by decide
theorem s3_445_safe : Safe 10 3 s3_445 := by
  apply safe_succ 9 3 s3_445 [s4_998, s4_20, s4_974, s4_960] (by decide) s3_445_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_998_safe
  · subst z; exact s4_20_safe
  · subst z; exact s4_974_safe
  · subst z; exact s4_960_safe
def s3_446 : State := ⟨[33,4,64,163], 11692013100348635180234170979065583938492895920406, 1, 0, 1, 0⟩
theorem s3_446_edges : next config 3 s3_446 = [s4_47, s4_975, s4_961, s4_953] := by decide
theorem s3_446_safe : Safe 10 3 s3_446 := by
  apply safe_succ 9 3 s3_446 [s4_47, s4_975, s4_961, s4_953] (by decide) s3_446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_47_safe
  · subst z; exact s4_975_safe
  · subst z; exact s4_961_safe
  · subst z; exact s4_953_safe
def s3_447 : State := ⟨[33,4,64,163], 14615016373649311548957786790644651548077688160534, 1, 0, 1, 0⟩
theorem s3_447_edges : next config 3 s3_447 = [s4_50, s4_976, s4_962, s4_954] := by decide
theorem s3_447_safe : Safe 10 3 s3_447 := by
  apply safe_succ 9 3 s3_447 [s4_50, s4_976, s4_962, s4_954] (by decide) s3_447_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_50_safe
  · subst z; exact s4_976_safe
  · subst z; exact s4_962_safe
  · subst z; exact s4_954_safe
def s3_448 : State := ⟨[33,4,96,129], 1020847100842043552922834903975443104022, 1, 0, 1, 0⟩
theorem s3_448_edges : next config 3 s3_448 = [s4_1016, s4_192, s4_977, s4_963, s4_959] := by decide
theorem s3_448_safe : Safe 10 3 s3_448 := by
  apply safe_succ 9 3 s3_448 [s4_1016, s4_192, s4_977, s4_963, s4_959] (by decide) s3_448_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_1016_safe
  · subst z; exact s4_192_safe
  · subst z; exact s4_977_safe
  · subst z; exact s4_963_safe
  · subst z; exact s4_959_safe
def s3_449 : State := ⟨[33,4,96,130], 1701411834683920479849584118838979526934, 1, 0, 1, 0⟩
theorem s3_449_edges : next config 3 s3_449 = [s4_1219, s4_1018, s4_200, s4_978, s4_964, s4_961] := by decide
theorem s3_449_safe : Safe 10 3 s3_449 := by
  apply safe_succ 9 3 s3_449 [s4_1219, s4_1018, s4_200, s4_978, s4_964, s4_961] (by decide) s3_449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1219_safe
  · subst z; exact s4_1018_safe
  · subst z; exact s4_200_safe
  · subst z; exact s4_978_safe
  · subst z; exact s4_964_safe
  · subst z; exact s4_961_safe
def s3_450 : State := ⟨[33,4,96,132], 5784800237735182041410079408020198064406, 1, 0, 1, 0⟩
theorem s3_450_edges : next config 3 s3_450 = [s4_1021, s4_210, s4_979, s4_965, s4_957] := by decide
theorem s3_450_safe : Safe 10 3 s3_450 := by
  apply safe_succ 9 3 s3_450 [s4_1021, s4_210, s4_979, s4_965, s4_957] (by decide) s3_450_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_1021_safe
  · subst z; exact s4_210_safe
  · subst z; exact s4_979_safe
  · subst z; exact s4_965_safe
  · subst z; exact s4_957_safe
def s3_451 : State := ⟨[33,4,96,136], 87452568298760413272619985191644568813846, 1, 0, 1, 0⟩
theorem s3_451_edges : next config 3 s3_451 = [s4_1023, s4_218, s4_988, s4_980, s4_966, s4_958] := by decide
theorem s3_451_safe : Safe 10 3 s3_451 := by
  apply safe_succ 9 3 s3_451 [s4_1023, s4_218, s4_988, s4_980, s4_966, s4_958] (by decide) s3_451_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1023_safe
  · subst z; exact s4_218_safe
  · subst z; exact s4_988_safe
  · subst z; exact s4_980_safe
  · subst z; exact s4_966_safe
  · subst z; exact s4_958_safe
def s3_452 : State := ⟨[33,4,96,144], 22301085480897623308161714358337473412661526, 1, 0, 1, 0⟩
theorem s3_452_edges : next config 3 s3_452 = [s4_1025, s4_230, s4_982, s4_967] := by decide
theorem s3_452_safe : Safe 10 3 s3_452 := by
  apply safe_succ 9 3 s3_452 [s4_1025, s4_230, s4_982, s4_967] (by decide) s3_452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1025_safe
  · subst z; exact s4_230_safe
  · subst z; exact s4_982_safe
  · subst z; exact s4_967_safe
def s3_453 : State := ⟨[33,4,96,160], 1461501637671185285203851458712368708767839224086, 1, 0, 1, 0⟩
theorem s3_453_edges : next config 3 s3_453 = [s4_1027, s4_241, s4_983, s4_968] := by decide
theorem s3_453_safe : Safe 10 3 s3_453 := by
  apply safe_succ 9 3 s3_453 [s4_1027, s4_241, s4_983, s4_968] (by decide) s3_453_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1027_safe
  · subst z; exact s4_241_safe
  · subst z; exact s4_983_safe
  · subst z; exact s4_968_safe
def s3_454 : State := ⟨[33,4,96,161], 2923003275002088203407536291428651728423771767062, 1, 0, 1, 0⟩
theorem s3_454_edges : next config 3 s3_454 = [s4_1028, s4_247, s4_984, s4_969, s4_962] := by decide
theorem s3_454_safe : Safe 10 3 s3_454 := by
  apply safe_succ 9 3 s3_454 [s4_1028, s4_247, s4_984, s4_969, s4_962] (by decide) s3_454_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_1028_safe
  · subst z; exact s4_247_safe
  · subst z; exact s4_984_safe
  · subst z; exact s4_969_safe
  · subst z; exact s4_962_safe
def s3_455 : State := ⟨[33,4,96,192], 6277101735386680764176071790207833042098441133575941194006, 1, 0, 1, 0⟩
theorem s3_455_edges : next config 3 s3_455 = [s4_1032, s4_261, s4_985, s4_970] := by decide
theorem s3_455_safe : Safe 10 3 s3_455 := by
  apply safe_succ 9 3 s3_455 [s4_1032, s4_261, s4_985, s4_970] (by decide) s3_455_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1032_safe
  · subst z; exact s4_261_safe
  · subst z; exact s4_985_safe
  · subst z; exact s4_970_safe
def s3_456 : State := ⟨[33,4,96,224], 26959946667150639794667015087359913040637311048536658170215516930326, 1, 0, 1, 0⟩
theorem s3_456_edges : next config 3 s3_456 = [s4_1034, s4_281, s4_986, s4_971] := by decide
theorem s3_456_safe : Safe 10 3 s3_456 := by
  apply safe_succ 9 3 s3_456 [s4_1034, s4_281, s4_986, s4_971] (by decide) s3_456_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1034_safe
  · subst z; exact s4_281_safe
  · subst z; exact s4_986_safe
  · subst z; exact s4_971_safe
def s3_457 : State := ⟨[33,4,104,128], 340282387282576229647756113059157967126, 1, 0, 0, 0⟩
theorem s3_457_edges : next config 3 s3_457 = [s4_1036, s4_316, s4_987, s4_969, s4_965, s4_972, s4_964, s4_966, s4_967, s4_968] := by decide
theorem s3_457_safe : Safe 10 3 s3_457 := by
  apply safe_succ 9 3 s3_457 [s4_1036, s4_316, s4_987, s4_969, s4_965, s4_972, s4_964, s4_966, s4_967, s4_968] (by decide) s3_457_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1036_safe
  · subst z; exact s4_316_safe
  · subst z; exact s4_987_safe
  · subst z; exact s4_969_safe
  · subst z; exact s4_965_safe
  · subst z; exact s4_972_safe
  · subst z; exact s4_964_safe
  · subst z; exact s4_966_safe
  · subst z; exact s4_967_safe
  · subst z; exact s4_968_safe
def s3_458 : State := ⟨[33,12,64,129], 1020847100762815390408570566381899157782, 3, 0, 1, 0⟩
theorem s3_458_edges : next config 3 s3_458 = [s4_1038, s4_413, s4_943, s4_977, s4_973] := by decide
theorem s3_458_safe : Safe 10 3 s3_458 := by
  apply safe_succ 9 3 s3_458 [s4_1038, s4_413, s4_943, s4_977, s4_973] (by decide) s3_458_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_1038_safe
  · subst z; exact s4_413_safe
  · subst z; exact s4_943_safe
  · subst z; exact s4_977_safe
  · subst z; exact s4_973_safe
def s3_459 : State := ⟨[33,12,64,130], 1701411834604692317335319781245435580694, 3, 0, 1, 0⟩
theorem s3_459_edges : next config 3 s3_459 = [s4_1225, s4_1040, s4_416, s4_944, s4_978, s4_975] := by decide
theorem s3_459_safe : Safe 10 3 s3_459 := by
  apply safe_succ 9 3 s3_459 [s4_1225, s4_1040, s4_416, s4_944, s4_978, s4_975] (by decide) s3_459_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1225_safe
  · subst z; exact s4_1040_safe
  · subst z; exact s4_416_safe
  · subst z; exact s4_944_safe
  · subst z; exact s4_978_safe
  · subst z; exact s4_975_safe
def s3_460 : State := ⟨[33,12,64,132], 5784800237655953878895815070426654118166, 3, 0, 1, 0⟩
theorem s3_460_edges : next config 3 s3_460 = [s4_1043, s4_421, s4_945, s4_979] := by decide
theorem s3_460_safe : Safe 10 3 s3_460 := by
  apply safe_succ 9 3 s3_460 [s4_1043, s4_421, s4_945, s4_979] (by decide) s3_460_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1043_safe
  · subst z; exact s4_421_safe
  · subst z; exact s4_945_safe
  · subst z; exact s4_979_safe
def s3_461 : State := ⟨[33,12,64,136], 87452568298681185110105720854051024867606, 3, 0, 1, 0⟩
theorem s3_461_edges : next config 3 s3_461 = [s4_1045, s4_424, s4_946, s4_980] := by decide
theorem s3_461_safe : Safe 10 3 s3_461 := by
  apply safe_succ 9 3 s3_461 [s4_1045, s4_424, s4_946, s4_980] (by decide) s3_461_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1045_safe
  · subst z; exact s4_424_safe
  · subst z; exact s4_946_safe
  · subst z; exact s4_980_safe
def s3_462 : State := ⟨[33,12,64,140], 1394136857275084884809464213392040956858646, 3, 0, 1, 0⟩
theorem s3_462_edges : next config 3 s3_462 = [s4_1047, s4_427, s4_948, s4_981] := by decide
theorem s3_462_safe : Safe 10 3 s3_462 := by
  apply safe_succ 9 3 s3_462 [s4_1047, s4_427, s4_948, s4_981] (by decide) s3_462_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1047_safe
  · subst z; exact s4_427_safe
  · subst z; exact s4_948_safe
  · subst z; exact s4_981_safe
def s3_463 : State := ⟨[33,12,64,144], 22301085480897544079999200093999879868715286, 3, 0, 1, 0⟩
theorem s3_463_edges : next config 3 s3_463 = [s4_1049, s4_430, s4_949, s4_982] := by decide
theorem s3_463_safe : Safe 10 3 s3_463 := by
  apply safe_succ 9 3 s3_463 [s4_1049, s4_430, s4_949, s4_982] (by decide) s3_463_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1049_safe
  · subst z; exact s4_430_safe
  · subst z; exact s4_949_safe
  · subst z; exact s4_982_safe
def s3_464 : State := ⟨[33,12,64,160], 1461501637671185285124623296198104371174295277846, 3, 0, 1, 0⟩
theorem s3_464_edges : next config 3 s3_464 = [s4_1051, s4_434, s4_951, s4_983] := by decide
theorem s3_464_safe : Safe 10 3 s3_464 := by
  apply safe_succ 9 3 s3_464 [s4_1051, s4_434, s4_951, s4_983] (by decide) s3_464_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1051_safe
  · subst z; exact s4_434_safe
  · subst z; exact s4_951_safe
  · subst z; exact s4_983_safe
def s3_465 : State := ⟨[33,12,64,161], 2923003275002088203328308128914387390830227820822, 3, 0, 1, 0⟩
theorem s3_465_edges : next config 3 s3_465 = [s4_1052, s4_437, s4_952, s4_984, s4_976] := by decide
theorem s3_465_safe : Safe 10 3 s3_465 := by
  apply safe_succ 9 3 s3_465 [s4_1052, s4_437, s4_952, s4_984, s4_976] (by decide) s3_465_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_1052_safe
  · subst z; exact s4_437_safe
  · subst z; exact s4_952_safe
  · subst z; exact s4_984_safe
  · subst z; exact s4_976_safe
def s3_466 : State := ⟨[33,12,64,192], 6277101735386680764176071790128604879584176795982397247766, 3, 0, 1, 0⟩
theorem s3_466_edges : next config 3 s3_466 = [s4_1056, s4_445, s4_955, s4_985] := by decide
theorem s3_466_safe : Safe 10 3 s3_466 := by
  apply safe_succ 9 3 s3_466 [s4_1056, s4_445, s4_955, s4_985] (by decide) s3_466_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1056_safe
  · subst z; exact s4_445_safe
  · subst z; exact s4_955_safe
  · subst z; exact s4_985_safe
def s3_467 : State := ⟨[33,12,96,128], 340282367000166625996085689111906685206, 3, 0, 0, 0⟩
theorem s3_467_edges : next config 3 s3_467 = [s4_1059, s4_519, s4_956, s4_987, s4_984, s4_981, s4_986, s4_978, s4_980, s4_982, s4_983] := by decide
theorem s3_467_safe : Safe 10 3 s3_467 := by
  apply safe_succ 9 3 s3_467 [s4_1059, s4_519, s4_956, s4_987, s4_984, s4_981, s4_986, s4_978, s4_980, s4_982, s4_983] (by decide) s3_467_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1059_safe
  · subst z; exact s4_519_safe
  · subst z; exact s4_956_safe
  · subst z; exact s4_987_safe
  · subst z; exact s4_984_safe
  · subst z; exact s4_981_safe
  · subst z; exact s4_986_safe
  · subst z; exact s4_978_safe
  · subst z; exact s4_980_safe
  · subst z; exact s4_982_safe
  · subst z; exact s4_983_safe
def s3_468 : State := ⟨[33,140,64,136], 1481249143206845131456088112894573618987286, 3, 0, 1, 0⟩
theorem s3_468_edges : next config 3 s3_468 = [s4_1061, s4_663, s4_947, s4_988] := by decide
theorem s3_468_safe : Safe 10 3 s3_468 := by
  apply safe_succ 9 3 s3_468 [s4_1061, s4_663, s4_947, s4_988] (by decide) s3_468_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1061_safe
  · subst z; exact s4_663_safe
  · subst z; exact s4_947_safe
  · subst z; exact s4_988_safe
def s3_469 : State := ⟨[35,4,64,129], 1020847100762815390408570566407668957470, 1, 0, 1, 0⟩
theorem s3_469_edges : next config 3 s3_469 = [s4_1062, s4_1037, s4_1015, s4_995] := by decide
theorem s3_469_safe : Safe 10 3 s3_469 := by
  apply safe_succ 9 3 s3_469 [s4_1062, s4_1037, s4_1015, s4_995] (by decide) s3_469_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1062_safe
  · subst z; exact s4_1037_safe
  · subst z; exact s4_1015_safe
  · subst z; exact s4_995_safe
def s3_470 : State := ⟨[35,4,64,129], 1020847100762815390408570566416258892054, 1, 0, 1, 0⟩
theorem s3_470_edges : next config 3 s3_470 = [s4_1063, s4_1038, s4_1016, s4_996] := by decide
theorem s3_470_safe : Safe 10 3 s3_470 := by
  apply safe_succ 9 3 s3_470 [s4_1063, s4_1038, s4_1016, s4_996] (by decide) s3_470_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1063_safe
  · subst z; exact s4_1038_safe
  · subst z; exact s4_1016_safe
  · subst z; exact s4_996_safe
def s3_471 : State := ⟨[35,4,64,130], 1701411834604692317335319781271205380382, 1, 0, 1, 0⟩
theorem s3_471_edges : next config 3 s3_471 = [s4_1064, s4_1039, s4_1017] := by decide
theorem s3_471_safe : Safe 10 3 s3_471 := by
  apply safe_succ 9 3 s3_471 [s4_1064, s4_1039, s4_1017] (by decide) s3_471_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1064_safe
  · subst z; exact s4_1039_safe
  · subst z; exact s4_1017_safe
def s3_472 : State := ⟨[35,4,64,130], 1701411834604692317335319781279795314966, 1, 0, 1, 0⟩
theorem s3_472_edges : next config 3 s3_472 = [s4_1065, s4_1040, s4_1018] := by decide
theorem s3_472_safe : Safe 10 3 s3_472 := by
  apply safe_succ 9 3 s3_472 [s4_1065, s4_1040, s4_1018] (by decide) s3_472_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1065_safe
  · subst z; exact s4_1040_safe
  · subst z; exact s4_1018_safe
def s3_473 : State := ⟨[35,4,64,131], 3062541302288446171188818210998278226206, 1, 0, 1, 0⟩
theorem s3_473_edges : next config 3 s3_473 = [s4_1066, s4_1041, s4_1019] := by decide
theorem s3_473_safe : Safe 10 3 s3_473 := by
  apply safe_succ 9 3 s3_473 [s4_1066, s4_1041, s4_1019] (by decide) s3_473_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1066_safe
  · subst z; exact s4_1041_safe
  · subst z; exact s4_1019_safe
def s3_474 : State := ⟨[35,4,64,132], 5784800237655953878895815070452423917854, 1, 0, 1, 0⟩
theorem s3_474_edges : next config 3 s3_474 = [s4_1067, s4_1042, s4_1020, s4_991] := by decide
theorem s3_474_safe : Safe 10 3 s3_474 := by
  apply safe_succ 9 3 s3_474 [s4_1067, s4_1042, s4_1020, s4_991] (by decide) s3_474_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1067_safe
  · subst z; exact s4_1042_safe
  · subst z; exact s4_1020_safe
  · subst z; exact s4_991_safe
def s3_475 : State := ⟨[35,4,64,132], 5784800237655953878895815070461013852438, 1, 0, 1, 0⟩
theorem s3_475_edges : next config 3 s3_475 = [s4_1068, s4_1043, s4_1021, s4_992] := by decide
theorem s3_475_safe : Safe 10 3 s3_475 := by
  apply safe_succ 9 3 s3_475 [s4_1068, s4_1043, s4_1021, s4_992] (by decide) s3_475_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1068_safe
  · subst z; exact s4_1043_safe
  · subst z; exact s4_1021_safe
  · subst z; exact s4_992_safe
def s3_476 : State := ⟨[35,4,64,136], 87452568298681185110105720854076794667294, 1, 0, 1, 0⟩
theorem s3_476_edges : next config 3 s3_476 = [s4_1233, s4_1069, s4_1060, s4_1044, s4_1022, s4_999, s4_993] := by decide
theorem s3_476_safe : Safe 10 3 s3_476 := by
  apply safe_succ 9 3 s3_476 [s4_1233, s4_1069, s4_1060, s4_1044, s4_1022, s4_999, s4_993] (by decide) s3_476_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1233_safe
  · subst z; exact s4_1069_safe
  · subst z; exact s4_1060_safe
  · subst z; exact s4_1044_safe
  · subst z; exact s4_1022_safe
  · subst z; exact s4_999_safe
  · subst z; exact s4_993_safe
def s3_477 : State := ⟨[35,4,64,136], 87452568298681185110105720854085384601878, 1, 0, 1, 0⟩
theorem s3_477_edges : next config 3 s3_477 = [s4_1234, s4_1070, s4_1061, s4_1045, s4_1023, s4_1000, s4_994] := by decide
theorem s3_477_safe : Safe 10 3 s3_477 := by
  apply safe_succ 9 3 s3_477 [s4_1234, s4_1070, s4_1061, s4_1045, s4_1023, s4_1000, s4_994] (by decide) s3_477_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1234_safe
  · subst z; exact s4_1070_safe
  · subst z; exact s4_1061_safe
  · subst z; exact s4_1045_safe
  · subst z; exact s4_1023_safe
  · subst z; exact s4_1000_safe
  · subst z; exact s4_994_safe
def s3_478 : State := ⟨[35,4,64,144], 22301085480897544079999200093999905638514974, 1, 0, 1, 0⟩
theorem s3_478_edges : next config 3 s3_478 = [s4_1071, s4_1048, s4_1024] := by decide
theorem s3_478_safe : Safe 10 3 s3_478 := by
  apply safe_succ 9 3 s3_478 [s4_1071, s4_1048, s4_1024] (by decide) s3_478_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1071_safe
  · subst z; exact s4_1048_safe
  · subst z; exact s4_1024_safe
def s3_479 : State := ⟨[35,4,64,144], 22301085480897544079999200093999914228449558, 1, 0, 1, 0⟩
theorem s3_479_edges : next config 3 s3_479 = [s4_1072, s4_1049, s4_1025] := by decide
theorem s3_479_safe : Safe 10 3 s3_479 := by
  apply safe_succ 9 3 s3_479 [s4_1072, s4_1049, s4_1025] (by decide) s3_479_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1072_safe
  · subst z; exact s4_1049_safe
  · subst z; exact s4_1025_safe
def s3_480 : State := ⟨[35,4,64,160], 1461501637671185285124623296198104371200065077534, 1, 0, 1, 0⟩
theorem s3_480_edges : next config 3 s3_480 = [s4_1073, s4_1050, s4_1026] := by decide
theorem s3_480_safe : Safe 10 3 s3_480 := by
  apply safe_succ 9 3 s3_480 [s4_1073, s4_1050, s4_1026] (by decide) s3_480_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1073_safe
  · subst z; exact s4_1050_safe
  · subst z; exact s4_1026_safe
def s3_481 : State := ⟨[35,4,64,160], 1461501637671185285124623296198104371208655012118, 1, 0, 1, 0⟩
theorem s3_481_edges : next config 3 s3_481 = [s4_1074, s4_1051, s4_1027] := by decide
theorem s3_481_safe : Safe 10 3 s3_481 := by
  apply safe_succ 9 3 s3_481 [s4_1074, s4_1051, s4_1027] (by decide) s3_481_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1074_safe
  · subst z; exact s4_1051_safe
  · subst z; exact s4_1027_safe
def s3_482 : State := ⟨[35,4,64,161], 2923003275002088203328308128914387390864587555094, 1, 0, 1, 0⟩
theorem s3_482_edges : next config 3 s3_482 = [s4_1075, s4_1052, s4_1028] := by decide
theorem s3_482_safe : Safe 10 3 s3_482 := by
  apply safe_succ 9 3 s3_482 [s4_1075, s4_1052, s4_1028] (by decide) s3_482_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1075_safe
  · subst z; exact s4_1052_safe
  · subst z; exact s4_1028_safe
def s3_483 : State := ⟨[35,4,64,163], 11692013098987505712550417125212085508791592878366, 1, 0, 1, 0⟩
theorem s3_483_edges : next config 3 s3_483 = [s4_1076, s4_1053, s4_1029, s4_1001] := by decide
theorem s3_483_safe : Safe 10 3 s3_483 := by
  apply safe_succ 9 3 s3_483 [s4_1076, s4_1053, s4_1029, s4_1001] (by decide) s3_483_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1076_safe
  · subst z; exact s4_1053_safe
  · subst z; exact s4_1029_safe
  · subst z; exact s4_1001_safe
def s3_484 : State := ⟨[35,4,64,163], 11692013098987505712550417125212085508800182812950, 1, 0, 1, 0⟩
theorem s3_484_edges : next config 3 s3_484 = [s4_1077, s4_1054, s4_1030, s4_1002] := by decide
theorem s3_484_safe : Safe 10 3 s3_484 := by
  apply safe_succ 9 3 s3_484 [s4_1077, s4_1054, s4_1030, s4_1002] (by decide) s3_484_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1077_safe
  · subst z; exact s4_1054_safe
  · subst z; exact s4_1030_safe
  · subst z; exact s4_1002_safe
def s3_485 : State := ⟨[35,4,64,192], 6277101735386680764176071790128604879584176796008167047454, 1, 0, 1, 0⟩
theorem s3_485_edges : next config 3 s3_485 = [s4_1080, s4_1055, s4_1031] := by decide
theorem s3_485_safe : Safe 10 3 s3_485 := by
  apply safe_succ 9 3 s3_485 [s4_1080, s4_1055, s4_1031] (by decide) s3_485_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1080_safe
  · subst z; exact s4_1055_safe
  · subst z; exact s4_1031_safe
def s3_486 : State := ⟨[35,4,64,192], 6277101735386680764176071790128604879584176796016756982038, 1, 0, 1, 0⟩
theorem s3_486_edges : next config 3 s3_486 = [s4_1081, s4_1056, s4_1032] := by decide
theorem s3_486_safe : Safe 10 3 s3_486 := by
  apply safe_succ 9 3 s3_486 [s4_1081, s4_1056, s4_1032] (by decide) s3_486_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1081_safe
  · subst z; exact s4_1056_safe
  · subst z; exact s4_1032_safe
def s3_487 : State := ⟨[35,4,67,128], 340282366920938463629395304133808947486, 1, 0, 0, 0⟩
theorem s3_487_edges : next config 3 s3_487 = [s4_1172, s4_1082, s4_1057, s4_1012, s4_1008, s4_1014, s4_1006, s4_1009, s4_1010, s4_1011] := by decide
theorem s3_487_safe : Safe 10 3 s3_487 := by
  apply safe_succ 9 3 s3_487 [s4_1172, s4_1082, s4_1057, s4_1012, s4_1008, s4_1014, s4_1006, s4_1009, s4_1010, s4_1011] (by decide) s3_487_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1172_safe
  · subst z; exact s4_1082_safe
  · subst z; exact s4_1057_safe
  · subst z; exact s4_1012_safe
  · subst z; exact s4_1008_safe
  · subst z; exact s4_1014_safe
  · subst z; exact s4_1006_safe
  · subst z; exact s4_1009_safe
  · subst z; exact s4_1010_safe
  · subst z; exact s4_1011_safe
def s3_488 : State := ⟨[35,4,96,128], 340282367000166625996085689137676484894, 1, 0, 0, 0⟩
theorem s3_488_edges : next config 3 s3_488 = [s4_1083, s4_1058, s4_1003, s4_1035, s4_1029, s4_1020, s4_1033, s4_1017, s4_1022, s4_1024, s4_1026] := by decide
theorem s3_488_safe : Safe 10 3 s3_488 := by
  apply safe_succ 9 3 s3_488 [s4_1083, s4_1058, s4_1003, s4_1035, s4_1029, s4_1020, s4_1033, s4_1017, s4_1022, s4_1024, s4_1026] (by decide) s3_488_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1083_safe
  · subst z; exact s4_1058_safe
  · subst z; exact s4_1003_safe
  · subst z; exact s4_1035_safe
  · subst z; exact s4_1029_safe
  · subst z; exact s4_1020_safe
  · subst z; exact s4_1033_safe
  · subst z; exact s4_1017_safe
  · subst z; exact s4_1022_safe
  · subst z; exact s4_1024_safe
  · subst z; exact s4_1026_safe
def s3_489 : State := ⟨[35,4,96,128], 340282367000166625996085689146266419478, 1, 0, 0, 0⟩
theorem s3_489_edges : next config 3 s3_489 = [s4_1084, s4_1059, s4_1004, s4_1036, s4_1030, s4_1021, s4_1034, s4_1018, s4_1023, s4_1025, s4_1027] := by decide
theorem s3_489_safe : Safe 10 3 s3_489 := by
  apply safe_succ 9 3 s3_489 [s4_1084, s4_1059, s4_1004, s4_1036, s4_1030, s4_1021, s4_1034, s4_1018, s4_1023, s4_1025, s4_1027] (by decide) s3_489_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1084_safe
  · subst z; exact s4_1059_safe
  · subst z; exact s4_1004_safe
  · subst z; exact s4_1036_safe
  · subst z; exact s4_1030_safe
  · subst z; exact s4_1021_safe
  · subst z; exact s4_1034_safe
  · subst z; exact s4_1018_safe
  · subst z; exact s4_1023_safe
  · subst z; exact s4_1025_safe
  · subst z; exact s4_1027_safe
def s3_490 : State := ⟨[35,12,64,128], 340282366920938463481821351544132538654, 3, 0, 0, 0⟩
theorem s3_490_edges : next config 3 s3_490 = [s4_989, s4_1058, s4_1053, s4_1046, s4_1055, s4_1039, s4_1044, s4_1048, s4_1050] := by decide
theorem s3_490_safe : Safe 10 3 s3_490 := by
  apply safe_succ 9 3 s3_490 [s4_989, s4_1058, s4_1053, s4_1046, s4_1055, s4_1039, s4_1044, s4_1048, s4_1050] (by decide) s3_490_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_989_safe
  · subst z; exact s4_1058_safe
  · subst z; exact s4_1053_safe
  · subst z; exact s4_1046_safe
  · subst z; exact s4_1055_safe
  · subst z; exact s4_1039_safe
  · subst z; exact s4_1044_safe
  · subst z; exact s4_1048_safe
  · subst z; exact s4_1050_safe
def s3_491 : State := ⟨[35,12,64,128], 340282366920938463481821351552722473238, 3, 0, 0, 0⟩
theorem s3_491_edges : next config 3 s3_491 = [s4_990, s4_1059, s4_1054, s4_1047, s4_1056, s4_1040, s4_1045, s4_1049, s4_1051] := by decide
theorem s3_491_safe : Safe 10 3 s3_491 := by
  apply safe_succ 9 3 s3_491 [s4_990, s4_1059, s4_1054, s4_1047, s4_1056, s4_1040, s4_1045, s4_1049, s4_1051] (by decide) s3_491_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_990_safe
  · subst z; exact s4_1059_safe
  · subst z; exact s4_1054_safe
  · subst z; exact s4_1047_safe
  · subst z; exact s4_1056_safe
  · subst z; exact s4_1040_safe
  · subst z; exact s4_1045_safe
  · subst z; exact s4_1049_safe
  · subst z; exact s4_1051_safe
def s3_492 : State := ⟨[43,4,64,128], 340282366920938463481821360340225556766, 1, 0, 0, 0⟩
theorem s3_492_edges : next config 3 s3_492 = [s4_1083, s4_1078, s4_1067, s4_1080, s4_1064, s4_1069, s4_1071, s4_1073] := by decide
theorem s3_492_safe : Safe 10 3 s3_492 := by
  apply safe_succ 9 3 s3_492 [s4_1083, s4_1078, s4_1067, s4_1080, s4_1064, s4_1069, s4_1071, s4_1073] (by decide) s3_492_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_1083_safe
  · subst z; exact s4_1078_safe
  · subst z; exact s4_1067_safe
  · subst z; exact s4_1080_safe
  · subst z; exact s4_1064_safe
  · subst z; exact s4_1069_safe
  · subst z; exact s4_1071_safe
  · subst z; exact s4_1073_safe
def s3_493 : State := ⟨[43,4,64,128], 340282366920938463481821360348815491350, 1, 0, 0, 0⟩
theorem s3_493_edges : next config 3 s3_493 = [s4_1084, s4_1079, s4_1068, s4_1081, s4_1065, s4_1070, s4_1072, s4_1074] := by decide
theorem s3_493_safe : Safe 10 3 s3_493 := by
  apply safe_succ 9 3 s3_493 [s4_1084, s4_1079, s4_1068, s4_1081, s4_1065, s4_1070, s4_1072, s4_1074] (by decide) s3_493_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_1084_safe
  · subst z; exact s4_1079_safe
  · subst z; exact s4_1068_safe
  · subst z; exact s4_1081_safe
  · subst z; exact s4_1065_safe
  · subst z; exact s4_1070_safe
  · subst z; exact s4_1072_safe
  · subst z; exact s4_1074_safe
def s3_494 : State := ⟨[49,4,64,145], 44601830679428167221534918367211182738309398, 1, 0, 1, 0⟩
theorem s3_494_edges : next config 3 s3_494 = [s4_1086, s4_1085] := by decide
theorem s3_494_safe : Safe 10 3 s3_494 := by
  apply safe_succ 9 3 s3_494 [s4_1086, s4_1085] (by decide) s3_494_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_1086_safe
  · subst z; exact s4_1085_safe
def s3_495 : State := ⟨[65,4,64,128], 340282366920938463518714839657191903510, 3, 2, 0, 0⟩
theorem s3_495_edges : next config 3 s3_495 = [s4_2, s4_1100, s4_1099, s4_1091, s4_1098, s4_1090, s4_1092, s4_1095, s4_1097] := by decide
theorem s3_495_safe : Safe 10 3 s3_495 := by
  apply safe_succ 9 3 s3_495 [s4_2, s4_1100, s4_1099, s4_1091, s4_1098, s4_1090, s4_1092, s4_1095, s4_1097] (by decide) s3_495_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_2_safe
  · subst z; exact s4_1100_safe
  · subst z; exact s4_1099_safe
  · subst z; exact s4_1091_safe
  · subst z; exact s4_1098_safe
  · subst z; exact s4_1090_safe
  · subst z; exact s4_1092_safe
  · subst z; exact s4_1095_safe
  · subst z; exact s4_1097_safe
def s3_496 : State := ⟨[65,4,64,140], 1399581375145819900224915100599088077406486, 1, 0, 1, 0⟩
theorem s3_496_edges : next config 3 s3_496 = [s4_7, s4_1102] := by decide
theorem s3_496_safe : Safe 10 3 s3_496 := by
  apply safe_succ 9 3 s3_496 [s4_7, s4_1102] (by decide) s3_496_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_7_safe
  · subst z; exact s4_1102_safe
def s3_497 : State := ⟨[65,4,64,140], 1481249143206845131456125006382712448155926, 1, 0, 1, 0⟩
theorem s3_497_edges : next config 3 s3_497 = [s4_10, s4_1103] := by decide
theorem s3_497_safe : Safe 10 3 s3_497 := by
  apply safe_succ 9 3 s3_497 [s4_10, s4_1103] (by decide) s3_497_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_10_safe
  · subst z; exact s4_1103_safe
def s3_498 : State := ⟨[65,4,64,145], 44602511244162009098461882009351243740283158, 1, 0, 1, 0⟩
theorem s3_498_edges : next config 3 s3_498 = [s4_15, s4_1136, s4_1104] := by decide
theorem s3_498_safe : Safe 10 3 s3_498 := by
  apply safe_succ 9 3 s3_498 [s4_15, s4_1136, s4_1104] (by decide) s3_498_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_15_safe
  · subst z; exact s4_1136_safe
  · subst z; exact s4_1104_safe
def s3_499 : State := ⟨[65,4,64,145], 66902575877958790363070673532784741709840662, 1, 0, 1, 0⟩
theorem s3_499_edges : next config 3 s3_499 = [s4_21, s4_1137, s4_1105] := by decide
theorem s3_499_safe : Safe 10 3 s3_499 := by
  apply safe_succ 9 3 s3_499 [s4_21, s4_1137, s4_1105] (by decide) s3_499_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_21_safe
  · subst z; exact s4_1137_safe
  · subst z; exact s4_1105_safe
def s3_500 : State := ⟨[65,4,64,146], 89204682205957097258460245303862830288666902, 1, 0, 1, 0⟩
theorem s3_500_edges : next config 3 s3_500 = [s4_25, s4_1138, s4_1106] := by decide
theorem s3_500_safe : Safe 10 3 s3_500 := by
  apply safe_succ 9 3 s3_500 [s4_25, s4_1138, s4_1106] (by decide) s3_500_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_25_safe
  · subst z; exact s4_1138_safe
  · subst z; exact s4_1106_safe
def s3_501 : State := ⟨[65,4,64,146], 111504066275020036646142110078081464721801494, 1, 0, 1, 0⟩
theorem s3_501_edges : next config 3 s3_501 = [s4_30, s4_1139, s4_1107] := by decide
theorem s3_501_safe : Safe 10 3 s3_501 := by
  apply safe_succ 9 3 s3_501 [s4_30, s4_1139, s4_1107] (by decide) s3_501_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_30_safe
  · subst z; exact s4_1139_safe
  · subst z; exact s4_1107_safe
def s3_502 : State := ⟨[65,4,64,162], 5846006551025023507419431648237345348007994917142, 1, 0, 1, 0⟩
theorem s3_502_edges : next config 3 s3_502 = [s4_39, s4_1140, s4_1108] := by decide
theorem s3_502_safe : Safe 10 3 s3_502 := by
  apply safe_succ 9 3 s3_502 [s4_39, s4_1140, s4_1108] (by decide) s3_502_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_39_safe
  · subst z; exact s4_1140_safe
  · subst z; exact s4_1108_safe
def s3_503 : State := ⟨[65,4,64,162], 7307508186994796957939362627100129937936854614294, 1, 0, 1, 0⟩
theorem s3_503_edges : next config 3 s3_503 = [s4_44, s4_1141, s4_1109] := by decide
theorem s3_503_safe : Safe 10 3 s3_503 := by
  apply safe_succ 9 3 s3_503 [s4_44, s4_1141, s4_1109] (by decide) s3_503_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_44_safe
  · subst z; exact s4_1141_safe
  · subst z; exact s4_1109_safe
def s3_504 : State := ⟨[65,4,64,176], 95780971326419139128294233276893560963659213834354966, 1, 0, 1, 0⟩
theorem s3_504_edges : next config 3 s3_504 = [s4_61, s4_1142, s4_1110] := by decide
theorem s3_504_safe : Safe 10 3 s3_504 := by
  apply safe_succ 9 3 s3_504 [s4_61, s4_1142, s4_1110] (by decide) s3_504_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_61_safe
  · subst z; exact s4_1142_safe
  · subst z; exact s4_1110_safe
def s3_505 : State := ⟨[65,4,64,176], 95782432805755724832681813820190558974030508260917526, 1, 0, 1, 0⟩
theorem s3_505_edges : next config 3 s3_505 = [s4_64, s4_1143, s4_1111] := by decide
theorem s3_505_safe : Safe 10 3 s3_505 := by
  apply safe_succ 9 3 s3_505 [s4_64, s4_1143, s4_1111] (by decide) s3_505_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_64_safe
  · subst z; exact s4_1143_safe
  · subst z; exact s4_1111_safe
def s3_506 : State := ⟨[65,4,96,129], 1020847100842043552959728392114272272662, 1, 0, 1, 0⟩
theorem s3_506_edges : next config 3 s3_506 = [s4_1155, s4_1144, s4_1114, s4_1124, s4_1104] := by decide
theorem s3_506_safe : Safe 10 3 s3_506 := by
  apply safe_succ 9 3 s3_506 [s4_1155, s4_1144, s4_1114, s4_1124, s4_1104] (by decide) s3_506_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_1155_safe
  · subst z; exact s4_1144_safe
  · subst z; exact s4_1114_safe
  · subst z; exact s4_1124_safe
  · subst z; exact s4_1104_safe
def s3_507 : State := ⟨[65,4,96,130], 1701411834683920479886477606977808695574, 1, 0, 1, 0⟩
theorem s3_507_edges : next config 3 s3_507 = [s4_1156, s4_1145, s4_1115, s4_1125, s4_1106, s4_1108] := by decide
theorem s3_507_safe : Safe 10 3 s3_507 := by
  apply safe_succ 9 3 s3_507 [s4_1156, s4_1145, s4_1115, s4_1125, s4_1106, s4_1108] (by decide) s3_507_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1156_safe
  · subst z; exact s4_1145_safe
  · subst z; exact s4_1115_safe
  · subst z; exact s4_1125_safe
  · subst z; exact s4_1106_safe
  · subst z; exact s4_1108_safe
def s3_508 : State := ⟨[65,4,96,132], 5784800237735182041446972896159027233046, 1, 0, 1, 0⟩
theorem s3_508_edges : next config 3 s3_508 = [s4_1157, s4_1146, s4_1116, s4_1135, s4_1126, s4_1112, s4_1102] := by decide
theorem s3_508_safe : Safe 10 3 s3_508 := by
  apply safe_succ 9 3 s3_508 [s4_1157, s4_1146, s4_1116, s4_1135, s4_1126, s4_1112, s4_1102] (by decide) s3_508_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1157_safe
  · subst z; exact s4_1146_safe
  · subst z; exact s4_1116_safe
  · subst z; exact s4_1135_safe
  · subst z; exact s4_1126_safe
  · subst z; exact s4_1112_safe
  · subst z; exact s4_1102_safe
def s3_509 : State := ⟨[65,4,96,136], 87452568298760413272656878679783397982486, 1, 0, 1, 0⟩
theorem s3_509_edges : next config 3 s3_509 = [s4_1158, s4_1167, s4_1147, s4_1117, s4_1127, s4_1103] := by decide
theorem s3_509_safe : Safe 10 3 s3_509 := by
  apply safe_succ 9 3 s3_509 [s4_1158, s4_1167, s4_1147, s4_1117, s4_1127, s4_1103] (by decide) s3_509_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1158_safe
  · subst z; exact s4_1167_safe
  · subst z; exact s4_1147_safe
  · subst z; exact s4_1117_safe
  · subst z; exact s4_1127_safe
  · subst z; exact s4_1103_safe
def s3_510 : State := ⟨[65,4,96,144], 22301085480897623308161751251825612241830166, 1, 0, 1, 0⟩
theorem s3_510_edges : next config 3 s3_510 = [s4_1159, s4_1149, s4_1118, s4_1128, s4_1107, s4_1110] := by decide
theorem s3_510_safe : Safe 10 3 s3_510 := by
  apply safe_succ 9 3 s3_510 [s4_1159, s4_1149, s4_1118, s4_1128, s4_1107, s4_1110] (by decide) s3_510_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1159_safe
  · subst z; exact s4_1149_safe
  · subst z; exact s4_1118_safe
  · subst z; exact s4_1128_safe
  · subst z; exact s4_1107_safe
  · subst z; exact s4_1110_safe
def s3_511 : State := ⟨[65,4,96,160], 1461501637671185285203851458749262196906668392726, 1, 0, 1, 0⟩
theorem s3_511_edges : next config 3 s3_511 = [s4_1160, s4_1150, s4_1119, s4_1129, s4_1109, s4_1111] := by decide
theorem s3_511_safe : Safe 10 3 s3_511 := by
  apply safe_succ 9 3 s3_511 [s4_1160, s4_1150, s4_1119, s4_1129, s4_1109, s4_1111] (by decide) s3_511_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1160_safe
  · subst z; exact s4_1150_safe
  · subst z; exact s4_1119_safe
  · subst z; exact s4_1129_safe
  · subst z; exact s4_1109_safe
  · subst z; exact s4_1111_safe
def s3_512 : State := ⟨[65,4,96,192], 6277101735386680764176071790207833042135334621714770362646, 1, 0, 1, 0⟩
theorem s3_512_edges : next config 3 s3_512 = [s4_1161, s4_1151, s4_1120, s4_1130] := by decide
theorem s3_512_safe : Safe 10 3 s3_512 := by
  apply safe_succ 9 3 s3_512 [s4_1161, s4_1151, s4_1120, s4_1130] (by decide) s3_512_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1161_safe
  · subst z; exact s4_1151_safe
  · subst z; exact s4_1120_safe
  · subst z; exact s4_1130_safe
def s3_513 : State := ⟨[65,4,96,193], 12554203470773361528011861213415499458237690066178804875542, 1, 0, 1, 0⟩
theorem s3_513_edges : next config 3 s3_513 = [s4_1162, s4_1152, s4_1121, s4_1131] := by decide
theorem s3_513_safe : Safe 10 3 s3_513 := by
  apply safe_succ 9 3 s3_513 [s4_1162, s4_1152, s4_1121, s4_1131] (by decide) s3_513_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_1162_safe
  · subst z; exact s4_1152_safe
  · subst z; exact s4_1121_safe
  · subst z; exact s4_1131_safe
def s3_514 : State := ⟨[65,4,96,224], 26959946667150639794667015087359913040637311048573551658354346098966, 1, 0, 1, 0⟩
theorem s3_514_edges : next config 3 s3_514 = [s4_1163, s4_1168, s4_1153, s4_1122, s4_1132, s4_1113] := by decide
theorem s3_514_safe : Safe 10 3 s3_514 := by
  apply safe_succ 9 3 s3_514 [s4_1163, s4_1168, s4_1153, s4_1122, s4_1132, s4_1113] (by decide) s3_514_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_1163_safe
  · subst z; exact s4_1168_safe
  · subst z; exact s4_1153_safe
  · subst z; exact s4_1122_safe
  · subst z; exact s4_1132_safe
  · subst z; exact s4_1113_safe
def s3_515 : State := ⟨[65,4,100,128], 340282368267817226261208578747439055126, 1, 0, 0, 0⟩
theorem s3_515_edges : next config 3 s3_515 = [s4_1121, s4_1116, s4_1123, s4_1115, s4_1117, s4_1118, s4_1119] := by decide
theorem s3_515_safe : Safe 10 3 s3_515 := by
  apply safe_succ 9 3 s3_515 [s4_1121, s4_1116, s4_1123, s4_1115, s4_1117, s4_1118, s4_1119] (by decide) s3_515_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_1121_safe
  · subst z; exact s4_1116_safe
  · subst z; exact s4_1123_safe
  · subst z; exact s4_1115_safe
  · subst z; exact s4_1117_safe
  · subst z; exact s4_1118_safe
  · subst z; exact s4_1119_safe
def s3_516 : State := ⟨[65,4,104,128], 340282387282576229684649601197987135766, 1, 0, 0, 0⟩
theorem s3_516_edges : next config 3 s3_516 = [s4_1166, s4_1154, s4_1134, s4_1131, s4_1126, s4_1133, s4_1125, s4_1127, s4_1128, s4_1129] := by decide
theorem s3_516_safe : Safe 10 3 s3_516 := by
  apply safe_succ 9 3 s3_516 [s4_1166, s4_1154, s4_1134, s4_1131, s4_1126, s4_1133, s4_1125, s4_1127, s4_1128, s4_1129] (by decide) s3_516_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1166_safe
  · subst z; exact s4_1154_safe
  · subst z; exact s4_1134_safe
  · subst z; exact s4_1131_safe
  · subst z; exact s4_1126_safe
  · subst z; exact s4_1133_safe
  · subst z; exact s4_1125_safe
  · subst z; exact s4_1127_safe
  · subst z; exact s4_1128_safe
  · subst z; exact s4_1129_safe
def s3_517 : State := ⟨[65,12,64,129], 1020847100762815390445464054520728326422, 3, 0, 1, 0⟩
theorem s3_517_edges : next config 3 s3_517 = [s4_414, s4_1089, s4_1144, s4_1136] := by decide
theorem s3_517_safe : Safe 10 3 s3_517 := by
  apply safe_succ 9 3 s3_517 [s4_414, s4_1089, s4_1144, s4_1136] (by decide) s3_517_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_414_safe
  · subst z; exact s4_1089_safe
  · subst z; exact s4_1144_safe
  · subst z; exact s4_1136_safe
def s3_518 : State := ⟨[65,12,64,130], 1701411834604692317372213269384264749334, 3, 0, 1, 0⟩
theorem s3_518_edges : next config 3 s3_518 = [s4_417, s4_1090, s4_1145, s4_1138, s4_1140] := by decide
theorem s3_518_safe : Safe 10 3 s3_518 := by
  apply safe_succ 9 3 s3_518 [s4_417, s4_1090, s4_1145, s4_1138, s4_1140] (by decide) s3_518_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_417_safe
  · subst z; exact s4_1090_safe
  · subst z; exact s4_1145_safe
  · subst z; exact s4_1138_safe
  · subst z; exact s4_1140_safe
def s3_519 : State := ⟨[65,12,64,132], 5784800237655953878932708558565483286806, 3, 0, 1, 0⟩
theorem s3_519_edges : next config 3 s3_519 = [s4_422, s4_1091, s4_1146] := by decide
theorem s3_519_safe : Safe 10 3 s3_519 := by
  apply safe_succ 9 3 s3_519 [s4_422, s4_1091, s4_1146] (by decide) s3_519_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_422_safe
  · subst z; exact s4_1091_safe
  · subst z; exact s4_1146_safe
def s3_520 : State := ⟨[65,12,64,136], 87452568298681185110142614342189854036246, 3, 0, 1, 0⟩
theorem s3_520_edges : next config 3 s3_520 = [s4_425, s4_1092, s4_1147] := by decide
theorem s3_520_safe : Safe 10 3 s3_520 := by
  apply safe_succ 9 3 s3_520 [s4_425, s4_1092, s4_1147] (by decide) s3_520_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_425_safe
  · subst z; exact s4_1092_safe
  · subst z; exact s4_1147_safe
def s3_521 : State := ⟨[65,12,64,140], 1394136857275084884809501106880179786027286, 3, 0, 1, 0⟩
theorem s3_521_edges : next config 3 s3_521 = [s4_428, s4_1094, s4_1148] := by decide
theorem s3_521_safe : Safe 10 3 s3_521 := by
  apply safe_succ 9 3 s3_521 [s4_428, s4_1094, s4_1148] (by decide) s3_521_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_428_safe
  · subst z; exact s4_1094_safe
  · subst z; exact s4_1148_safe
def s3_522 : State := ⟨[65,12,64,144], 22301085480897544079999236987488018697883926, 3, 0, 1, 0⟩
theorem s3_522_edges : next config 3 s3_522 = [s4_431, s4_1095, s4_1149, s4_1139, s4_1142] := by decide
theorem s3_522_safe : Safe 10 3 s3_522 := by
  apply safe_succ 9 3 s3_522 [s4_431, s4_1095, s4_1149, s4_1139, s4_1142] (by decide) s3_522_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_431_safe
  · subst z; exact s4_1095_safe
  · subst z; exact s4_1149_safe
  · subst z; exact s4_1139_safe
  · subst z; exact s4_1142_safe
def s3_523 : State := ⟨[65,12,64,160], 1461501637671185285124623296234997859313124446486, 3, 0, 1, 0⟩
theorem s3_523_edges : next config 3 s3_523 = [s4_435, s4_1097, s4_1150, s4_1141, s4_1143] := by decide
theorem s3_523_safe : Safe 10 3 s3_523 := by
  apply safe_succ 9 3 s3_523 [s4_435, s4_1097, s4_1150, s4_1141, s4_1143] (by decide) s3_523_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_435_safe
  · subst z; exact s4_1097_safe
  · subst z; exact s4_1150_safe
  · subst z; exact s4_1141_safe
  · subst z; exact s4_1143_safe
def s3_524 : State := ⟨[65,12,64,192], 6277101735386680764176071790128604879621070284121226416406, 3, 0, 1, 0⟩
theorem s3_524_edges : next config 3 s3_524 = [s4_446, s4_1098, s4_1151] := by decide
theorem s3_524_safe : Safe 10 3 s3_524 := by
  apply safe_succ 9 3 s3_524 [s4_446, s4_1098, s4_1151] (by decide) s3_524_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_446_safe
  · subst z; exact s4_1098_safe
  · subst z; exact s4_1151_safe
def s3_525 : State := ⟨[65,12,64,193], 12554203470773361528011861213336271295723425728585260929302, 3, 0, 1, 0⟩
theorem s3_525_edges : next config 3 s3_525 = [s4_448, s4_1099, s4_1152] := by decide
theorem s3_525_safe : Safe 10 3 s3_525 := by
  apply safe_succ 9 3 s3_525 [s4_448, s4_1099, s4_1152] (by decide) s3_525_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_448_safe
  · subst z; exact s4_1099_safe
  · subst z; exact s4_1152_safe
def s3_526 : State := ⟨[65,12,96,128], 340282367000166626032979177250735853846, 3, 0, 0, 0⟩
theorem s3_526_edges : next config 3 s3_526 = [s4_1100, s4_1154, s4_1152, s4_1148, s4_1153, s4_1145, s4_1147, s4_1149, s4_1150] := by decide
theorem s3_526_safe : Safe 10 3 s3_526 := by
  apply safe_succ 9 3 s3_526 [s4_1100, s4_1154, s4_1152, s4_1148, s4_1153, s4_1145, s4_1147, s4_1149, s4_1150] (by decide) s3_526_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1100_safe
  · subst z; exact s4_1154_safe
  · subst z; exact s4_1152_safe
  · subst z; exact s4_1148_safe
  · subst z; exact s4_1153_safe
  · subst z; exact s4_1145_safe
  · subst z; exact s4_1147_safe
  · subst z; exact s4_1149_safe
  · subst z; exact s4_1150_safe
def s3_527 : State := ⟨[65,100,96,128], 340282368267817226261208578747439055126, 3, 0, 0, 0⟩
theorem s3_527_edges : next config 3 s3_527 = [s4_1101, s4_1165, s4_1162, s4_1164, s4_1163, s4_1156, s4_1158, s4_1159, s4_1160] := by decide
theorem s3_527_safe : Safe 10 3 s3_527 := by
  apply safe_succ 9 3 s3_527 [s4_1101, s4_1165, s4_1162, s4_1164, s4_1163, s4_1156, s4_1158, s4_1159, s4_1160] (by decide) s3_527_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_1101_safe
  · subst z; exact s4_1165_safe
  · subst z; exact s4_1162_safe
  · subst z; exact s4_1164_safe
  · subst z; exact s4_1163_safe
  · subst z; exact s4_1156_safe
  · subst z; exact s4_1158_safe
  · subst z; exact s4_1159_safe
  · subst z; exact s4_1160_safe
def s3_528 : State := ⟨[65,140,64,136], 1481249143206845131456125006382712448155926, 3, 0, 1, 0⟩
theorem s3_528_edges : next config 3 s3_528 = [s4_664, s4_1093, s4_1167] := by decide
theorem s3_528_safe : Safe 10 3 s3_528 := by
  apply safe_succ 9 3 s3_528 [s4_664, s4_1093, s4_1167] (by decide) s3_528_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_664_safe
  · subst z; exact s4_1093_safe
  · subst z; exact s4_1167_safe
def s3_529 : State := ⟨[81,4,64,145], 44601830679428167223952770005877491134300438, 1, 0, 1, 0⟩
theorem s3_529_edges : next config 3 s3_529 = [s4_1170, s4_1169] := by decide
theorem s3_529_safe : Safe 10 3 s3_529 := by
  apply safe_succ 9 3 s3_529 [s4_1170, s4_1169] (by decide) s3_529_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_1170_safe
  · subst z; exact s4_1169_safe
def s3_530 : State := ⟨[97,4,96,129], 1020847101000499877951363579153941070102, 1, 0, 1, 0⟩
theorem s3_530_edges : next config 3 s3_530 = [s4_195, s4_1190, s4_1180, s4_1176] := by decide
theorem s3_530_safe : Safe 10 3 s3_530 := by
  apply safe_succ 9 3 s3_530 [s4_195, s4_1190, s4_1180, s4_1176] (by decide) s3_530_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_195_safe
  · subst z; exact s4_1190_safe
  · subst z; exact s4_1180_safe
  · subst z; exact s4_1176_safe
def s3_531 : State := ⟨[97,4,96,130], 1701411834842376804878112794017477493014, 1, 0, 1, 0⟩
theorem s3_531_edges : next config 3 s3_531 = [s4_203, s4_1191, s4_1181, s4_1178] := by decide
theorem s3_531_safe : Safe 10 3 s3_531 := by
  apply safe_succ 9 3 s3_531 [s4_203, s4_1191, s4_1181, s4_1178] (by decide) s3_531_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_203_safe
  · subst z; exact s4_1191_safe
  · subst z; exact s4_1181_safe
  · subst z; exact s4_1178_safe
def s3_532 : State := ⟨[97,4,96,132], 5784800237893638366438608083198696030486, 1, 0, 1, 0⟩
theorem s3_532_edges : next config 3 s3_532 = [s4_213, s4_1192, s4_1182, s4_1174] := by decide
theorem s3_532_safe : Safe 10 3 s3_532 := by
  apply safe_succ 9 3 s3_532 [s4_213, s4_1192, s4_1182, s4_1174] (by decide) s3_532_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_213_safe
  · subst z; exact s4_1192_safe
  · subst z; exact s4_1182_safe
  · subst z; exact s4_1174_safe
def s3_533 : State := ⟨[97,4,96,136], 87452568298918869597648513866823066779926, 1, 0, 1, 0⟩
theorem s3_533_edges : next config 3 s3_533 = [s4_221, s4_1201, s4_1193, s4_1183, s4_1175] := by decide
theorem s3_533_safe : Safe 10 3 s3_533 := by
  apply safe_succ 9 3 s3_533 [s4_221, s4_1201, s4_1193, s4_1183, s4_1175] (by decide) s3_533_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_221_safe
  · subst z; exact s4_1201_safe
  · subst z; exact s4_1193_safe
  · subst z; exact s4_1183_safe
  · subst z; exact s4_1175_safe
def s3_534 : State := ⟨[97,4,96,144], 22301085480897781764486742887012651910627606, 1, 0, 1, 0⟩
theorem s3_534_edges : next config 3 s3_534 = [s4_233, s4_1195, s4_1184] := by decide
theorem s3_534_safe : Safe 10 3 s3_534 := by
  apply safe_succ 9 3 s3_534 [s4_233, s4_1195, s4_1184] (by decide) s3_534_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_233_safe
  · subst z; exact s4_1195_safe
  · subst z; exact s4_1184_safe
def s3_535 : State := ⟨[97,4,96,160], 1461501637671185285362307783740897383946337190166, 1, 0, 1, 0⟩
theorem s3_535_edges : next config 3 s3_535 = [s4_244, s4_1196, s4_1185, s4_1179] := by decide
theorem s3_535_safe : Safe 10 3 s3_535 := by
  apply safe_succ 9 3 s3_535 [s4_244, s4_1196, s4_1185, s4_1179] (by decide) s3_535_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_244_safe
  · subst z; exact s4_1196_safe
  · subst z; exact s4_1185_safe
  · subst z; exact s4_1179_safe
def s3_536 : State := ⟨[97,4,96,192], 6277101735386680764176071790366289367126969808754439160086, 1, 0, 1, 0⟩
theorem s3_536_edges : next config 3 s3_536 = [s4_264, s4_1197, s4_1186] := by decide
theorem s3_536_safe : Safe 10 3 s3_536 := by
  apply safe_succ 9 3 s3_536 [s4_264, s4_1197, s4_1186] (by decide) s3_536_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_264_safe
  · subst z; exact s4_1197_safe
  · subst z; exact s4_1186_safe
def s3_537 : State := ⟨[97,4,96,224], 26959946667150639794667015087359913040795767373565186845394014896406, 1, 0, 1, 0⟩
theorem s3_537_edges : next config 3 s3_537 = [s4_284, s4_1198, s4_1187] := by decide
theorem s3_537_safe : Safe 10 3 s3_537 := by
  apply safe_succ 9 3 s3_537 [s4_284, s4_1198, s4_1187] (by decide) s3_537_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_284_safe
  · subst z; exact s4_1198_safe
  · subst z; exact s4_1187_safe
def s3_538 : State := ⟨[97,4,96,225], 53919893334301279589334030174379543714432911796105759326497625145622, 1, 0, 1, 0⟩
theorem s3_538_edges : next config 3 s3_538 = [s4_288, s4_1199, s4_1188] := by decide
theorem s3_538_safe : Safe 10 3 s3_538 := by
  apply safe_succ 9 3 s3_538 [s4_288, s4_1199, s4_1188] (by decide) s3_538_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_288_safe
  · subst z; exact s4_1199_safe
  · subst z; exact s4_1188_safe
def s3_539 : State := ⟨[97,4,104,128], 340282387441032554676284788237655933206, 1, 0, 0, 0⟩
theorem s3_539_edges : next config 3 s3_539 = [s4_1200, s4_1188, s4_1182, s4_1189, s4_1181, s4_1183, s4_1184, s4_1185] := by decide
theorem s3_539_safe : Safe 10 3 s3_539 := by
  apply safe_succ 9 3 s3_539 [s4_1200, s4_1188, s4_1182, s4_1189, s4_1181, s4_1183, s4_1184, s4_1185] (by decide) s3_539_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_1200_safe
  · subst z; exact s4_1188_safe
  · subst z; exact s4_1182_safe
  · subst z; exact s4_1189_safe
  · subst z; exact s4_1181_safe
  · subst z; exact s4_1183_safe
  · subst z; exact s4_1184_safe
  · subst z; exact s4_1185_safe
def s3_540 : State := ⟨[97,12,96,128], 340282367158622951024614364290404651286, 3, 0, 0, 0⟩
theorem s3_540_edges : next config 3 s3_540 = [s4_521, s4_1173, s4_1200, s4_1199, s4_1194, s4_1198, s4_1191, s4_1193, s4_1195, s4_1196] := by decide
theorem s3_540_safe : Safe 10 3 s3_540 := by
  apply safe_succ 9 3 s3_540 [s4_521, s4_1173, s4_1200, s4_1199, s4_1194, s4_1198, s4_1191, s4_1193, s4_1195, s4_1196] (by decide) s3_540_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s4_521_safe
  · subst z; exact s4_1173_safe
  · subst z; exact s4_1200_safe
  · subst z; exact s4_1199_safe
  · subst z; exact s4_1194_safe
  · subst z; exact s4_1198_safe
  · subst z; exact s4_1191_safe
  · subst z; exact s4_1193_safe
  · subst z; exact s4_1195_safe
  · subst z; exact s4_1196_safe
def s3_541 : State := ⟨[131,4,64,146], 89207404464892464766167915407234137015255318, 1, 0, 1, 0⟩
theorem s3_541_edges : next config 3 s3_541 = [s4_1208, s4_1204] := by decide
theorem s3_541_safe : Safe 10 3 s3_541 := by
  apply safe_succ 9 3 s3_541 [s4_1208, s4_1204] (by decide) s3_541_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_1208_safe
  · subst z; exact s4_1204_safe
def s3_542 : State := ⟨[131,4,64,162], 5846006553747282442786939355907448719314721505558, 1, 0, 1, 0⟩
theorem s3_542_edges : next config 3 s3_542 = [s4_1209, s4_1205] := by decide
theorem s3_542_safe : Safe 10 3 s3_542 := by
  apply safe_succ 9 3 s3_542 [s4_1209, s4_1205] (by decide) s3_542_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_1209_safe
  · subst z; exact s4_1205_safe
def s3_543 : State := ⟨[131,4,96,130], 4423670770051428187556580978284535283990, 1, 0, 1, 0⟩
theorem s3_543_edges : next config 3 s3_543 = [s4_205, s4_1220, s4_1211, s4_1210, s4_1206, s4_1207, s4_1204, s4_1205] := by decide
theorem s3_543_safe : Safe 10 3 s3_543 := by
  apply safe_succ 9 3 s3_543 [s4_205, s4_1220, s4_1211, s4_1210, s4_1206, s4_1207, s4_1204, s4_1205] (by decide) s3_543_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_205_safe
  · subst z; exact s4_1220_safe
  · subst z; exact s4_1211_safe
  · subst z; exact s4_1210_safe
  · subst z; exact s4_1206_safe
  · subst z; exact s4_1207_safe
  · subst z; exact s4_1204_safe
  · subst z; exact s4_1205_safe
def s3_544 : State := ⟨[131,12,64,130], 4423670769972200025042316640690991337750, 3, 0, 1, 0⟩
theorem s3_544_edges : next config 3 s3_544 = [s4_418, s4_1226, s4_1203, s4_1210, s4_1208, s4_1209] := by decide
theorem s3_544_safe : Safe 10 3 s3_544 := by
  apply safe_succ 9 3 s3_544 [s4_418, s4_1226, s4_1203, s4_1210, s4_1208, s4_1209] (by decide) s3_544_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_418_safe
  · subst z; exact s4_1226_safe
  · subst z; exact s4_1203_safe
  · subst z; exact s4_1210_safe
  · subst z; exact s4_1208_safe
  · subst z; exact s4_1209_safe
def s3_545 : State := ⟨[137,4,96,136], 261677140162280906565867784196701303144726, 1, 0, 1, 0⟩
theorem s3_545_edges : next config 3 s3_545 = [s4_223, s4_1212] := by decide
theorem s3_545_safe : Safe 10 3 s3_545 := by
  apply safe_succ 9 3 s3_545 [s4_223, s4_1212] (by decide) s3_545_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_223_safe
  · subst z; exact s4_1212_safe
def s3_546 : State := ⟨[161,4,96,160], 4384504912332991121611221124144934748071114375446, 1, 0, 1, 0⟩
theorem s3_546_edges : next config 3 s3_546 = [s4_246, s4_1222, s4_1217, s4_1216] := by decide
theorem s3_546_safe : Safe 10 3 s3_546 := by
  apply safe_succ 9 3 s3_546 [s4_246, s4_1222, s4_1217, s4_1216] (by decide) s3_546_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_246_safe
  · subst z; exact s4_1222_safe
  · subst z; exact s4_1217_safe
  · subst z; exact s4_1216_safe
def s3_547 : State := ⟨[161,12,64,160], 4384504912332991121531992961630670410477570429206, 3, 0, 1, 0⟩
theorem s3_547_edges : next config 3 s3_547 = [s4_436, s4_1228, s4_1215, s4_1217] := by decide
theorem s3_547_safe : Safe 10 3 s3_547 := by
  apply safe_succ 9 3 s3_547 [s4_436, s4_1228, s4_1215, s4_1217] (by decide) s3_547_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_436_safe
  · subst z; exact s4_1228_safe
  · subst z; exact s4_1215_safe
  · subst z; exact s4_1217_safe
def s3_548 : State := ⟨[163,4,64,130], 11692013100348635180234170979065583938492895920406, 1, 0, 1, 0⟩
theorem s3_548_edges : next config 3 s3_548 = [s4_1231, s4_1225, s4_1219] := by decide
theorem s3_548_safe : Safe 10 3 s3_548 := by
  apply safe_succ 9 3 s3_548 [s4_1231, s4_1225, s4_1219] (by decide) s3_548_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1231_safe
  · subst z; exact s4_1225_safe
  · subst z; exact s4_1219_safe
def s3_549 : State := ⟨[163,4,64,130], 11692013103070894115601678686772580797938451677462, 1, 0, 1, 0⟩
theorem s3_549_edges : next config 3 s3_549 = [s4_1232, s4_1226, s4_1220] := by decide
theorem s3_549_safe : Safe 10 3 s3_549 := by
  apply safe_succ 9 3 s3_549 [s4_1232, s4_1226, s4_1220] (by decide) s3_549_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1232_safe
  · subst z; exact s4_1226_safe
  · subst z; exact s4_1220_safe
def s3_550 : State := ⟨[163,4,64,160], 13153514736318408630754101957928368528413165682974, 1, 0, 1, 0⟩
theorem s3_550_edges : next config 3 s3_550 = [s4_1235, s4_1227, s4_1221] := by decide
theorem s3_550_safe : Safe 10 3 s3_550 := by
  apply safe_succ 9 3 s3_550 [s4_1235, s4_1227, s4_1221] (by decide) s3_550_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1235_safe
  · subst z; exact s4_1227_safe
  · subst z; exact s4_1221_safe
def s3_551 : State := ⟨[163,4,64,160], 16076518010980214467161471623360934567725030768918, 1, 0, 1, 0⟩
theorem s3_551_edges : next config 3 s3_551 = [s4_1236, s4_1228, s4_1222] := by decide
theorem s3_551_safe : Safe 10 3 s3_551 := by
  apply safe_succ 9 3 s3_551 [s4_1236, s4_1228, s4_1222] (by decide) s3_551_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_1236_safe
  · subst z; exact s4_1228_safe
  · subst z; exact s4_1222_safe
def s3_552 : State := ⟨[163,4,64,162], 17538019649672246853048910309930716017108036157718, 1, 0, 1, 0⟩
theorem s3_552_edges : next config 3 s3_552 = [s4_45, s4_1239, s4_1229, s4_1223] := by decide
theorem s3_552_safe : Safe 10 3 s3_552 := by
  apply safe_succ 9 3 s3_552 [s4_45, s4_1239, s4_1229, s4_1223] (by decide) s3_552_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_45_safe
  · subst z; exact s4_1239_safe
  · subst z; exact s4_1229_safe
  · subst z; exact s4_1223_safe
def s3_553 : State := ⟨[163,4,64,162], 18999521285642020303568841288793500607036895854870, 1, 0, 1, 0⟩
theorem s3_553_edges : next config 3 s3_553 = [s4_46, s4_1240, s4_1230, s4_1224] := by decide
theorem s3_553_safe : Safe 10 3 s3_553 := by
  apply safe_succ 9 3 s3_553 [s4_46, s4_1240, s4_1230, s4_1224] (by decide) s3_553_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_46_safe
  · subst z; exact s4_1240_safe
  · subst z; exact s4_1230_safe
  · subst z; exact s4_1224_safe
def s3_554 : State := ⟨[193,4,96,192], 18831305206160042291847650636623165874303152022495420285206, 1, 0, 1, 0⟩
theorem s3_554_edges : next config 3 s3_554 = [s4_266, s4_1247, s4_1246, s4_1244, s4_1245] := by decide
theorem s3_554_safe : Safe 10 3 s3_554 := by
  apply safe_succ 9 3 s3_554 [s4_266, s4_1247, s4_1246, s4_1244, s4_1245] (by decide) s3_554_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_266_safe
  · subst z; exact s4_1247_safe
  · subst z; exact s4_1246_safe
  · subst z; exact s4_1244_safe
  · subst z; exact s4_1245_safe
def s3_555 : State := ⟨[193,12,64,192], 18831305206160042291847650636543937711788887684901876338966, 3, 0, 1, 0⟩
theorem s3_555_edges : next config 3 s3_555 = [s4_447, s4_1243, s4_1246] := by decide
theorem s3_555_safe : Safe 10 3 s3_555 := by
  apply safe_succ 9 3 s3_555 [s4_447, s4_1243, s4_1246] (by decide) s3_555_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_447_safe
  · subst z; exact s4_1243_safe
  · subst z; exact s4_1246_safe
def s3_556 : State := ⟨[225,4,96,224], 80879840001451919384001045261399174387911599893617803132414147494166, 1, 0, 1, 0⟩
theorem s3_556_edges : next config 3 s3_556 = [s4_286, s4_1249, s4_1248] := by decide
theorem s3_556_safe : Safe 10 3 s3_556 := by
  apply safe_succ 9 3 s3_556 [s4_286, s4_1249, s4_1248] (by decide) s3_556_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_286_safe
  · subst z; exact s4_1249_safe
  · subst z; exact s4_1248_safe
end HGP13.SectorGraph234
