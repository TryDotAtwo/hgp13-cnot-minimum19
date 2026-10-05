import Graph234Layer6
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s5_0 : State := ⟨[1,4,64,129], 1020847100762815390408570566373309223198, 3, 3, 1, 0⟩
theorem s5_0_edges : next config 5 s5_0 = [s6_82, s6_0] := by decide
theorem s5_0_safe : Safe 8 5 s5_0 := by
  apply safe_succ 7 5 s5_0 [s6_82, s6_0] (by decide) s5_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_82_safe
  · subst z; exact s6_0_safe
def s5_1 : State := ⟨[1,4,64,129], 1020847100762815390408570566381899157782, 3, 3, 1, 0⟩
theorem s5_1_edges : next config 5 s5_1 = [s6_83, s6_1] := by decide
theorem s5_1_safe : Safe 8 5 s5_1 := by
  apply safe_succ 7 5 s5_1 [s6_83, s6_1] (by decide) s5_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_83_safe
  · subst z; exact s6_1_safe
def s5_2 : State := ⟨[1,4,64,129], 1020847100762815390445464054520728326422, 3, 3, 1, 0⟩
theorem s5_2_edges : next config 5 s5_2 = [s6_84, s6_2] := by decide
theorem s5_2_safe : Safe 8 5 s5_2 := by
  apply safe_succ 7 5 s5_2 [s6_84, s6_2] (by decide) s5_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_84_safe
  · subst z; exact s6_2_safe
def s5_3 : State := ⟨[1,4,64,130], 1701411834604692317335319781236845646110, 3, 3, 1, 0⟩
theorem s5_3_edges : next config 5 s5_3 = [s6_88, s6_6, s6_11] := by decide
theorem s5_3_safe : Safe 8 5 s5_3 := by
  apply safe_succ 7 5 s5_3 [s6_88, s6_6, s6_11] (by decide) s5_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_88_safe
  · subst z; exact s6_6_safe
  · subst z; exact s6_11_safe
def s5_4 : State := ⟨[1,4,64,130], 1701411834604692317335319781245435580694, 3, 3, 1, 0⟩
theorem s5_4_edges : next config 5 s5_4 = [s6_89] := by decide
theorem s5_4_safe : Safe 8 5 s5_4 := by
  apply safe_succ 7 5 s5_4 [s6_89] (by decide) s5_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_89_safe
def s5_5 : State := ⟨[1,4,64,130], 1701411834604692317372213269384264749334, 3, 3, 1, 0⟩
theorem s5_5_edges : next config 5 s5_5 = [s6_90, s6_7, s6_12] := by decide
theorem s5_5_safe : Safe 8 5 s5_5 := by
  apply safe_succ 7 5 s5_5 [s6_90, s6_7, s6_12] (by decide) s5_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_90_safe
  · subst z; exact s6_7_safe
  · subst z; exact s6_12_safe
def s5_6 : State := ⟨[1,4,64,130], 4423670769972200025042316640690991337750, 3, 3, 1, 0⟩
theorem s5_6_edges : next config 5 s5_6 = [s6_94, s6_8, s6_13] := by decide
theorem s5_6_safe : Safe 8 5 s5_6 := by
  apply safe_succ 7 5 s5_6 [s6_94, s6_8, s6_13] (by decide) s5_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_94_safe
  · subst z; exact s6_8_safe
  · subst z; exact s6_13_safe
def s5_7 : State := ⟨[1,4,64,131], 3062541302288446171188818210963918491934, 3, 3, 1, 0⟩
theorem s5_7_edges : next config 5 s5_7 = [s6_96, s6_19] := by decide
theorem s5_7_safe : Safe 8 5 s5_7 := by
  apply safe_succ 7 5 s5_7 [s6_96, s6_19] (by decide) s5_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_96_safe
  · subst z; exact s6_19_safe
def s5_8 : State := ⟨[1,4,64,132], 5784800237655953878895815070418064183582, 3, 3, 1, 0⟩
theorem s5_8_edges : next config 5 s5_8 = [s6_98] := by decide
theorem s5_8_safe : Safe 8 5 s5_8 := by
  apply safe_succ 7 5 s5_8 [s6_98] (by decide) s5_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_98_safe
def s5_9 : State := ⟨[1,4,64,132], 5784800237655953878895815070426654118166, 3, 3, 1, 0⟩
theorem s5_9_edges : next config 5 s5_9 = [s6_99] := by decide
theorem s5_9_safe : Safe 8 5 s5_9 := by
  apply safe_succ 7 5 s5_9 [s6_99] (by decide) s5_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_99_safe
def s5_10 : State := ⟨[1,4,64,132], 5784800237655953878932708558565483286806, 3, 3, 1, 0⟩
theorem s5_10_edges : next config 5 s5_10 = [s6_100] := by decide
theorem s5_10_safe : Safe 8 5 s5_10 := by
  apply safe_succ 7 5 s5_10 [s6_100] (by decide) s5_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_100_safe
def s5_11 : State := ⟨[1,4,64,136], 87452568298681185110105720854042434933022, 3, 3, 1, 0⟩
theorem s5_11_edges : next config 5 s5_11 = [s6_104] := by decide
theorem s5_11_safe : Safe 8 5 s5_11 := by
  apply safe_succ 7 5 s5_11 [s6_104] (by decide) s5_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_104_safe
def s5_12 : State := ⟨[1,4,64,136], 87452568298681185110105720854051024867606, 3, 3, 1, 0⟩
theorem s5_12_edges : next config 5 s5_12 = [s6_105] := by decide
theorem s5_12_safe : Safe 8 5 s5_12 := by
  apply safe_succ 7 5 s5_12 [s6_105] (by decide) s5_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_105_safe
def s5_13 : State := ⟨[1,4,64,136], 87452568298681185110142614342189854036246, 3, 3, 1, 0⟩
theorem s5_13_edges : next config 5 s5_13 = [s6_106] := by decide
theorem s5_13_safe : Safe 8 5 s5_13 := by
  apply safe_succ 7 5 s5_13 [s6_106] (by decide) s5_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_106_safe
def s5_14 : State := ⟨[1,4,64,136], 1481249143206845131456088112894565029052702, 3, 3, 1, 0⟩
theorem s5_14_edges : next config 5 s5_14 = [s6_110] := by decide
theorem s5_14_safe : Safe 8 5 s5_14 := by
  apply safe_succ 7 5 s5_14 [s6_110] (by decide) s5_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_110_safe
def s5_15 : State := ⟨[1,4,64,136], 1481249143206845131456088112894573618987286, 3, 3, 1, 0⟩
theorem s5_15_edges : next config 5 s5_15 = [s6_111] := by decide
theorem s5_15_safe : Safe 8 5 s5_15 := by
  apply safe_succ 7 5 s5_15 [s6_111] (by decide) s5_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_111_safe
def s5_16 : State := ⟨[1,4,64,136], 1481249143206845131456125006382712448155926, 3, 3, 1, 0⟩
theorem s5_16_edges : next config 5 s5_16 = [s6_112] := by decide
theorem s5_16_safe : Safe 8 5 s5_16 := by
  apply safe_succ 7 5 s5_16 [s6_112] (by decide) s5_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_112_safe
def s5_17 : State := ⟨[1,4,64,140], 1394136857275084884809464213392032366924062, 3, 3, 1, 0⟩
theorem s5_17_edges : next config 5 s5_17 = [s6_114] := by decide
theorem s5_17_safe : Safe 8 5 s5_17 := by
  apply safe_succ 7 5 s5_17 [s6_114] (by decide) s5_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_114_safe
def s5_18 : State := ⟨[1,4,64,140], 1394136857275084884809464213392040956858646, 3, 3, 1, 0⟩
theorem s5_18_edges : next config 5 s5_18 = [s6_115] := by decide
theorem s5_18_safe : Safe 8 5 s5_18 := by
  apply safe_succ 7 5 s5_18 [s6_115] (by decide) s5_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_115_safe
def s5_19 : State := ⟨[1,4,64,140], 1394136857275084884809501106880179786027286, 3, 3, 1, 0⟩
theorem s5_19_edges : next config 5 s5_19 = [s6_116] := by decide
theorem s5_19_safe : Safe 8 5 s5_19 := by
  apply safe_succ 7 5 s5_19 [s6_116] (by decide) s5_19_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_116_safe
def s5_20 : State := ⟨[1,4,64,144], 22301085480897544079999200093999871278780702, 3, 3, 1, 0⟩
theorem s5_20_edges : next config 5 s5_20 = [s6_118, s6_3, s6_9, s6_22] := by decide
theorem s5_20_safe : Safe 8 5 s5_20 := by
  apply safe_succ 7 5 s5_20 [s6_118, s6_3, s6_9, s6_22] (by decide) s5_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_118_safe
  · subst z; exact s6_3_safe
  · subst z; exact s6_9_safe
  · subst z; exact s6_22_safe
def s5_21 : State := ⟨[1,4,64,144], 22301085480897544079999200093999879868715286, 3, 3, 1, 0⟩
theorem s5_21_edges : next config 5 s5_21 = [s6_119, s6_4] := by decide
theorem s5_21_safe : Safe 8 5 s5_21 := by
  apply safe_succ 7 5 s5_21 [s6_119, s6_4] (by decide) s5_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_119_safe
  · subst z; exact s6_4_safe
def s5_22 : State := ⟨[1,4,64,144], 22301085480897544079999236987488018697883926, 3, 3, 1, 0⟩
theorem s5_22_edges : next config 5 s5_22 = [s6_120, s6_5, s6_10, s6_23] := by decide
theorem s5_22_safe : Safe 8 5 s5_22 := by
  apply safe_succ 7 5 s5_22 [s6_120, s6_5, s6_10, s6_23] (by decide) s5_22_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_120_safe
  · subst z; exact s6_5_safe
  · subst z; exact s6_10_safe
  · subst z; exact s6_23_safe
def s5_23 : State := ⟨[1,4,64,145], 44601830679428167221534918366648232784892182, 3, 3, 1, 0⟩
theorem s5_23_edges : next config 5 s5_23 = [s6_1224, s6_636, s6_993, s6_26, s6_394, s6_28, s6_68, s6_124] := by decide
theorem s5_23_safe : Safe 8 5 s5_23 := by
  apply safe_succ 7 5 s5_23 [s6_1224, s6_636, s6_993, s6_26, s6_394, s6_28, s6_68, s6_124] (by decide) s5_23_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1224_safe
  · subst z; exact s6_636_safe
  · subst z; exact s6_993_safe
  · subst z; exact s6_26_safe
  · subst z; exact s6_394_safe
  · subst z; exact s6_28_safe
  · subst z; exact s6_68_safe
  · subst z; exact s6_124_safe
def s5_24 : State := ⟨[1,4,64,145], 44601830679428167221534918366648232786985238, 3, 3, 1, 0⟩
theorem s5_24_edges : next config 5 s5_24 = [s6_1225, s6_637, s6_738, s6_994, s6_548, s6_411, s6_27, s6_67, s6_395, s6_29, s6_69, s6_125] := by decide
theorem s5_24_safe : Safe 8 5 s5_24 := by
  apply safe_succ 7 5 s5_24 [s6_1225, s6_637, s6_738, s6_994, s6_548, s6_411, s6_27, s6_67, s6_395, s6_29, s6_69, s6_125] (by decide) s5_24_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1225_safe
  · subst z; exact s6_637_safe
  · subst z; exact s6_738_safe
  · subst z; exact s6_994_safe
  · subst z; exact s6_548_safe
  · subst z; exact s6_411_safe
  · subst z; exact s6_27_safe
  · subst z; exact s6_67_safe
  · subst z; exact s6_395_safe
  · subst z; exact s6_29_safe
  · subst z; exact s6_69_safe
  · subst z; exact s6_125_safe
def s5_25 : State := ⟨[1,4,64,145], 44601830679428167221535213514553412137713942, 3, 3, 1, 0⟩
theorem s5_25_edges : next config 5 s5_25 = [s6_126] := by decide
theorem s5_25_safe : Safe 8 5 s5_25 := by
  apply safe_succ 7 5 s5_25 [s6_126] (by decide) s5_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_126_safe
def s5_26 : State := ⟨[1,4,64,145], 133806172603018343541531644955671405881524510, 1, 1, 1, 0⟩
theorem s5_26_edges : next config 5 s5_26 = [s6_412, s6_128] := by decide
theorem s5_26_safe : Safe 8 5 s5_26 := by
  apply safe_succ 7 5 s5_26 [s6_412, s6_128] (by decide) s5_26_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_412_safe
  · subst z; exact s6_128_safe
def s5_27 : State := ⟨[1,4,64,145], 156105556672081282929213509729890040314659102, 1, 1, 1, 0⟩
theorem s5_27_edges : next config 5 s5_27 = [s6_413, s6_129] := by decide
theorem s5_27_safe : Safe 8 5 s5_27 := by
  apply safe_succ 7 5 s5_27 [s6_413, s6_129] (by decide) s5_27_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_413_safe
  · subst z; exact s6_129_safe
def s5_28 : State := ⟨[1,4,64,160], 1461501637671185285124623296198104371165705343262, 3, 3, 1, 0⟩
theorem s5_28_edges : next config 5 s5_28 = [s6_130, s6_14, s6_24] := by decide
theorem s5_28_safe : Safe 8 5 s5_28 := by
  apply safe_succ 7 5 s5_28 [s6_130, s6_14, s6_24] (by decide) s5_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_130_safe
  · subst z; exact s6_14_safe
  · subst z; exact s6_24_safe
def s5_29 : State := ⟨[1,4,64,160], 1461501637671185285124623296198104371174295277846, 3, 3, 1, 0⟩
theorem s5_29_edges : next config 5 s5_29 = [s6_131] := by decide
theorem s5_29_safe : Safe 8 5 s5_29 := by
  apply safe_succ 7 5 s5_29 [s6_131] (by decide) s5_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_131_safe
def s5_30 : State := ⟨[1,4,64,160], 1461501637671185285124623296234997859313124446486, 3, 3, 1, 0⟩
theorem s5_30_edges : next config 5 s5_30 = [s6_132, s6_15, s6_25] := by decide
theorem s5_30_safe : Safe 8 5 s5_30 := by
  apply safe_succ 7 5 s5_30 [s6_132, s6_15, s6_25] (by decide) s5_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_132_safe
  · subst z; exact s6_15_safe
  · subst z; exact s6_25_safe
def s5_31 : State := ⟨[1,4,64,160], 4384504912332991121531992961630670410477570429206, 3, 3, 1, 0⟩
theorem s5_31_edges : next config 5 s5_31 = [s6_136] := by decide
theorem s5_31_safe : Safe 8 5 s5_31 := by
  apply safe_succ 7 5 s5_31 [s6_136] (by decide) s5_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_136_safe
def s5_32 : State := ⟨[1,4,64,161], 2923003275002088203328308128914387390830227820822, 3, 3, 1, 0⟩
theorem s5_32_edges : next config 5 s5_32 = [s6_137, s6_21] := by decide
theorem s5_32_safe : Safe 8 5 s5_32 := by
  apply safe_succ 7 5 s5_32 [s6_137, s6_21] (by decide) s5_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_137_safe
  · subst z; exact s6_21_safe
def s5_33 : State := ⟨[1,4,64,163], 11692013102390329381759801759845831583074915258646, 2, 2, 1, 0⟩
theorem s5_33_edges : next config 5 s5_33 = [s6_140] := by decide
theorem s5_33_safe : Safe 8 5 s5_33 := by
  apply safe_succ 7 5 s5_33 [s6_140] (by decide) s5_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_140_safe
def s5_34 : State := ⟨[1,4,64,163], 11692013103070894115601678686772580797938451681558, 2, 2, 1, 0⟩
theorem s5_34_edges : next config 5 s5_34 = [s6_141] := by decide
theorem s5_34_safe : Safe 8 5 s5_34 := by
  apply safe_succ 7 5 s5_34 [s6_141] (by decide) s5_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_141_safe
def s5_35 : State := ⟨[1,4,64,163], 14615016374329876282799663717571400762932634652950, 2, 2, 1, 0⟩
theorem s5_35_edges : next config 5 s5_35 = [s6_142] := by decide
theorem s5_35_safe : Safe 8 5 s5_35 := by
  apply safe_succ 7 5 s5_35 [s6_142] (by decide) s5_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_142_safe
def s5_36 : State := ⟨[1,4,64,163], 16076518010980214467161471623360934567725030773014, 2, 2, 1, 0⟩
theorem s5_36_edges : next config 5 s5_36 = [s6_143] := by decide
theorem s5_36_safe : Safe 8 5 s5_36 := by
  apply safe_succ 7 5 s5_36 [s6_143] (by decide) s5_36_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_143_safe
def s5_37 : State := ⟨[1,4,64,163], 17538019649672246853048910309930716017108036161814, 2, 2, 1, 0⟩
theorem s5_37_edges : next config 5 s5_37 = [s6_144] := by decide
theorem s5_37_safe : Safe 8 5 s5_37 := by
  apply safe_succ 7 5 s5_37 [s6_144] (by decide) s5_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_144_safe
def s5_38 : State := ⟨[1,4,64,163], 18999521285642020303568841288793500607036895858966, 2, 2, 1, 0⟩
theorem s5_38_edges : next config 5 s5_38 = [s6_145] := by decide
theorem s5_38_safe : Safe 8 5 s5_38 := by
  apply safe_succ 7 5 s5_38 [s6_145] (by decide) s5_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_145_safe
def s5_39 : State := ⟨[1,4,64,170], 4495579036431558788229139237752621888242885347836182, 1, 1, 1, 0⟩
theorem s5_39_edges : next config 5 s5_39 = [s6_146] := by decide
theorem s5_39_safe : Safe 8 5 s5_39 := by
  apply safe_succ 7 5 s5_39 [s6_146] (by decide) s5_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_146_safe
def s5_40 : State := ⟨[1,4,64,170], 4497040538067528561679659168731484672832814207533334, 1, 1, 1, 0⟩
theorem s5_40_edges : next config 5 s5_40 = [s6_147] := by decide
theorem s5_40_safe : Safe 8 5 s5_40 := by
  apply safe_succ 7 5 s5_40 [s6_147] (by decide) s5_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_147_safe
def s5_41 : State := ⟨[1,4,64,171], 2999001359804714199988565969051148076115210423829270, 1, 1, 1, 0⟩
theorem s5_41_edges : next config 5 s5_41 = [s6_148] := by decide
theorem s5_41_safe : Safe 8 5 s5_41 := by
  apply safe_succ 7 5 s5_41 [s6_148] (by decide) s5_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_148_safe
def s5_42 : State := ⟨[1,4,64,171], 3000462861440683973439085900030010860705139283526422, 1, 1, 1, 0⟩
theorem s5_42_edges : next config 5 s5_42 = [s6_149] := by decide
theorem s5_42_safe : Safe 8 5 s5_42 := by
  apply safe_succ 7 5 s5_42 [s6_149] (by decide) s5_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_149_safe
def s5_43 : State := ⟨[1,4,64,171], 3004847366354037811661380708382013208193842743935254, 1, 1, 1, 0⟩
theorem s5_43_edges : next config 5 s5_43 = [s6_150] := by decide
theorem s5_43_safe : Safe 8 5 s5_43 := by
  apply safe_succ 7 5 s5_43 [s6_150] (by decide) s5_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_150_safe
def s5_44 : State := ⟨[1,4,64,171], 3004847366355398941129064462235866706623561226846494, 1, 1, 1, 0⟩
theorem s5_44_edges : next config 5 s5_44 = [s6_151] := by decide
theorem s5_44_safe : Safe 8 5 s5_44 := by
  apply safe_succ 7 5 s5_44 [s6_151] (by decide) s5_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_151_safe
def s5_45 : State := ⟨[1,4,64,171], 3006308867990007585111900639360875992783763013697822, 1, 1, 1, 0⟩
theorem s5_45_edges : next config 5 s5_45 = [s6_152] := by decide
theorem s5_45_safe : Safe 8 5 s5_45 := by
  apply safe_succ 7 5 s5_45 [s6_152] (by decide) s5_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_152_safe
def s5_46 : State := ⟨[1,4,64,171], 3007770369627338488030104324193592275803427536175382, 1, 1, 1, 0⟩
theorem s5_46_edges : next config 5 s5_46 = [s6_153] := by decide
theorem s5_46_safe : Safe 8 5 s5_46 := by
  apply safe_succ 7 5 s5_46 [s6_153] (by decide) s5_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_153_safe
def s5_47 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879584176795973807313182, 3, 3, 1, 0⟩
theorem s5_47_edges : next config 5 s5_47 = [s6_154] := by decide
theorem s5_47_safe : Safe 8 5 s5_47 := by
  apply safe_succ 7 5 s5_47 [s6_154] (by decide) s5_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_154_safe
def s5_48 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879584176795982397247766, 3, 3, 1, 0⟩
theorem s5_48_edges : next config 5 s5_48 = [s6_155] := by decide
theorem s5_48_safe : Safe 8 5 s5_48 := by
  apply safe_succ 7 5 s5_48 [s6_155] (by decide) s5_48_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_155_safe
def s5_49 : State := ⟨[1,4,64,192], 6277101735386680764176071790128604879621070284121226416406, 3, 3, 1, 0⟩
theorem s5_49_edges : next config 5 s5_49 = [s6_156] := by decide
theorem s5_49_safe : Safe 8 5 s5_49 := by
  apply safe_succ 7 5 s5_49 [s6_156] (by decide) s5_49_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_156_safe
def s5_50 : State := ⟨[1,4,64,192], 18831305206160042291847650636543937711788887684901876338966, 3, 3, 1, 0⟩
theorem s5_50_edges : next config 5 s5_50 = [s6_160] := by decide
theorem s5_50_safe : Safe 8 5 s5_50 := by
  apply safe_succ 7 5 s5_50 [s6_160] (by decide) s5_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_160_safe
def s5_51 : State := ⟨[1,4,64,193], 12554203470773361528011861213336271295723425728585260929302, 3, 3, 1, 0⟩
theorem s5_51_edges : next config 5 s5_51 = [s6_162] := by decide
theorem s5_51_safe : Safe 8 5 s5_51 := by
  apply safe_succ 7 5 s5_51 [s6_162] (by decide) s5_51_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_162_safe
def s5_52 : State := ⟨[1,4,64,210], 1645504557321206042244173864763307602241196074043954546218176790, 2, 2, 1, 0⟩
theorem s5_52_edges : next config 5 s5_52 = [s6_166] := by decide
theorem s5_52_safe : Safe 8 5 s5_52 := by
  apply safe_succ 7 5 s5_52 [s6_166] (by decide) s5_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_166_safe
def s5_53 : State := ⟨[1,4,64,210], 1645504557321206042266473248832370541628877938818173180651311382, 2, 2, 1, 0⟩
theorem s5_53_edges : next config 5 s5_53 = [s6_167] := by decide
theorem s5_53_safe : Safe 8 5 s5_53 := by
  apply safe_succ 7 5 s5_53 [s6_167] (by decide) s5_53_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_167_safe
def s5_54 : State := ⟨[1,4,64,210], 1645529665728147588878026227126877940340717610375138956332306710, 2, 2, 1, 0⟩
theorem s5_54_edges : next config 5 s5_54 = [s6_168] := by decide
theorem s5_54_safe : Safe 8 5 s5_54 := by
  apply safe_succ 7 5 s5_54 [s6_168] (by decide) s5_54_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_168_safe
def s5_55 : State := ⟨[1,4,64,210], 1645535942829882975558788701786833464253279859232153693293973782, 2, 2, 1, 0⟩
theorem s5_55_edges : next config 5 s5_55 = [s6_169] := by decide
theorem s5_55_safe : Safe 8 5 s5_55 := by
  apply safe_succ 7 5 s5_55 [s6_169] (by decide) s5_55_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_169_safe
def s5_56 : State := ⟨[1,4,64,210], 2056880696651507552716012563677585675308419032135974700464541974, 2, 2, 1, 0⟩
theorem s5_56_edges : next config 5 s5_56 = [s6_170] := by decide
theorem s5_56_safe : Safe 8 5 s5_56 := by
  apply safe_succ 7 5 s5_56 [s6_170] (by decide) s5_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_170_safe
def s5_57 : State := ⟨[1,4,64,210], 2056886973753242939374475654268478259833299416218770802993074454, 2, 2, 1, 0⟩
theorem s5_57_edges : next config 5 s5_57 = [s6_171] := by decide
theorem s5_57_safe : Safe 8 5 s5_57 := by
  apply safe_succ 7 5 s5_57 [s6_171] (by decide) s5_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_171_safe
def s5_58 : State := ⟨[1,4,64,210], 27973577474460502716723680785680915681964969924181232359795917078, 2, 2, 1, 0⟩
theorem s5_58_edges : next config 5 s5_58 = [s6_172] := by decide
theorem s5_58_safe : Safe 8 5 s5_58 := by
  apply safe_succ 7 5 s5_58 [s6_172] (by decide) s5_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_172_safe
def s5_59 : State := ⟨[1,4,64,210], 27973577474460502716745980169749978621352651788955450994229051670, 2, 2, 1, 0⟩
theorem s5_59_edges : next config 5 s5_59 = [s6_173] := by decide
theorem s5_59_safe : Safe 8 5 s5_59 := by
  apply safe_succ 7 5 s5_59 [s6_173] (by decide) s5_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_173_safe
def s5_60 : State := ⟨[1,4,64,210], 27973602582867444263357533148044486020064491460512416769910046998, 2, 2, 1, 0⟩
theorem s5_60_edges : next config 5 s5_60 = [s6_174] := by decide
theorem s5_60_safe : Safe 8 5 s5_60 := by
  apply safe_succ 7 5 s5_60 [s6_174] (by decide) s5_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_174_safe
def s5_61 : State := ⟨[1,4,64,210], 27973608859969179650038295622704441543977053709369431506871714070, 2, 2, 1, 0⟩
theorem s5_61_edges : next config 5 s5_61 = [s6_175] := by decide
theorem s5_61_safe : Safe 8 5 s5_61 := by
  apply safe_succ 7 5 s5_61 [s6_175] (by decide) s5_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_175_safe
def s5_62 : State := ⟨[1,4,64,210], 28384953613790804227195519484595193755032192882273252514042282262, 2, 2, 1, 0⟩
theorem s5_62_edges : next config 5 s5_62 = [s6_176] := by decide
theorem s5_62_safe : Safe 8 5 s5_62 := by
  apply safe_succ 7 5 s5_62 [s6_176] (by decide) s5_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_176_safe
def s5_63 : State := ⟨[1,4,64,210], 28384959890892539613853982575186086339557073266356048616570814742, 2, 2, 1, 0⟩
theorem s5_63_edges : next config 5 s5_63 = [s6_177] := by decide
theorem s5_63_safe : Safe 8 5 s5_63 := by
  apply safe_succ 7 5 s5_63 [s6_177] (by decide) s5_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_177_safe
def s5_64 : State := ⟨[1,4,64,214], 26328072917139296674568711603123565176982234353695557675800133910, 2, 2, 1, 0⟩
theorem s5_64_edges : next config 5 s5_64 = [s6_178] := by decide
theorem s5_64_safe : Safe 8 5 s5_64 := by
  apply safe_succ 7 5 s5_64 [s6_178] (by decide) s5_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_178_safe
def s5_65 : State := ⟨[1,4,64,214], 26328072917139296674591010987192628116369916218469776310233268502, 2, 2, 1, 0⟩
theorem s5_65_edges : next config 5 s5_65 = [s6_179] := by decide
theorem s5_65_safe : Safe 8 5 s5_65 := by
  apply safe_succ 7 5 s5_65 [s6_179] (by decide) s5_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_179_safe
def s5_66 : State := ⟨[1,4,65,145], 44602511244162009098461882009351243740287254, 2, 2, 1, 0⟩
theorem s5_66_edges : next config 5 s5_66 = [s6_40] := by decide
theorem s5_66_safe : Safe 8 5 s5_66 := by
  apply safe_succ 7 5 s5_66 [s6_40] (by decide) s5_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_40_safe
def s5_67 : State := ⟨[1,4,65,145], 66902575877958790363070673532784741709844758, 2, 2, 1, 0⟩
theorem s5_67_edges : next config 5 s5_67 = [s6_42] := by decide
theorem s5_67_safe : Safe 8 5 s5_67 := by
  apply safe_succ 7 5 s5_67 [s6_42] (by decide) s5_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_42_safe
def s5_68 : State := ⟨[1,4,65,146], 89204682205957097258460245303862830288670998, 2, 2, 1, 0⟩
theorem s5_68_edges : next config 5 s5_68 = [s6_46] := by decide
theorem s5_68_safe : Safe 8 5 s5_68 := by
  apply safe_succ 7 5 s5_68 [s6_46] (by decide) s5_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_46_safe
def s5_69 : State := ⟨[1,4,65,146], 111504066275020036646142110078081464721805590, 2, 2, 1, 0⟩
theorem s5_69_edges : next config 5 s5_69 = [s6_48] := by decide
theorem s5_69_safe : Safe 8 5 s5_69 := by
  apply safe_succ 7 5 s5_69 [s6_48] (by decide) s5_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_48_safe
def s5_70 : State := ⟨[1,4,65,162], 5846006551025023507419431648237345348007994921238, 2, 2, 1, 0⟩
theorem s5_70_edges : next config 5 s5_70 = [s6_51] := by decide
theorem s5_70_safe : Safe 8 5 s5_70 := by
  apply safe_succ 7 5 s5_70 [s6_51] (by decide) s5_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_51_safe
def s5_71 : State := ⟨[1,4,65,162], 7307508186994796957939362627100129937936854618390, 2, 2, 1, 0⟩
theorem s5_71_edges : next config 5 s5_71 = [s6_53] := by decide
theorem s5_71_safe : Safe 8 5 s5_71 := by
  apply safe_succ 7 5 s5_71 [s6_53] (by decide) s5_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_53_safe
def s5_72 : State := ⟨[1,4,65,176], 95780971326419139128294233276893560963659213834359062, 2, 2, 1, 0⟩
theorem s5_72_edges : next config 5 s5_72 = [s6_57] := by decide
theorem s5_72_safe : Safe 8 5 s5_72 := by
  apply safe_succ 7 5 s5_72 [s6_57] (by decide) s5_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_57_safe
def s5_73 : State := ⟨[1,4,65,176], 95782432805755724832681813820190558974030508260921622, 2, 2, 1, 0⟩
theorem s5_73_edges : next config 5 s5_73 = [s6_59] := by decide
theorem s5_73_safe : Safe 8 5 s5_73 := by
  apply safe_succ 7 5 s5_73 [s6_59] (by decide) s5_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_59_safe
def s5_74 : State := ⟨[1,4,66,145], 44602511244162009098461918902839391159390486, 2, 2, 1, 0⟩
theorem s5_74_edges : next config 5 s5_74 = [s6_41, s6_72] := by decide
theorem s5_74_safe : Safe 8 5 s5_74 := by
  apply safe_succ 7 5 s5_74 [s6_41, s6_72] (by decide) s5_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_41_safe
  · subst z; exact s6_72_safe
def s5_75 : State := ⟨[1,4,66,145], 66902575877958790363070710426272889128947990, 2, 2, 1, 0⟩
theorem s5_75_edges : next config 5 s5_75 = [s6_43, s6_76] := by decide
theorem s5_75_safe : Safe 8 5 s5_75 := by
  apply safe_succ 7 5 s5_75 [s6_43, s6_76] (by decide) s5_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_43_safe
  · subst z; exact s6_76_safe
def s5_76 : State := ⟨[1,4,66,146], 89204682205957097258460282197350977707774230, 2, 2, 1, 0⟩
theorem s5_76_edges : next config 5 s5_76 = [s6_47] := by decide
theorem s5_76_safe : Safe 8 5 s5_76 := by
  apply safe_succ 7 5 s5_76 [s6_47] (by decide) s5_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_47_safe
def s5_77 : State := ⟨[1,4,66,146], 111504066275020036646142146971569612140908822, 2, 2, 1, 0⟩
theorem s5_77_edges : next config 5 s5_77 = [s6_49] := by decide
theorem s5_77_safe : Safe 8 5 s5_77 := by
  apply safe_succ 7 5 s5_77 [s6_49] (by decide) s5_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_49_safe
def s5_78 : State := ⟨[1,4,66,162], 5846006551025023507419431648274238836155414024470, 2, 2, 1, 0⟩
theorem s5_78_edges : next config 5 s5_78 = [s6_52] := by decide
theorem s5_78_safe : Safe 8 5 s5_78 := by
  apply safe_succ 7 5 s5_78 [s6_52] (by decide) s5_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_52_safe
def s5_79 : State := ⟨[1,4,66,162], 7307508186994796957939362627137023426084273721622, 2, 2, 1, 0⟩
theorem s5_79_edges : next config 5 s5_79 = [s6_54] := by decide
theorem s5_79_safe : Safe 8 5 s5_79 := by
  apply safe_succ 7 5 s5_79 [s6_54] (by decide) s5_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_54_safe
def s5_80 : State := ⟨[1,4,66,176], 95780971326419139128294233276893597857147361253462294, 2, 2, 1, 0⟩
theorem s5_80_edges : next config 5 s5_80 = [s6_58] := by decide
theorem s5_80_safe : Safe 8 5 s5_80 := by
  apply safe_succ 7 5 s5_80 [s6_58] (by decide) s5_80_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_58_safe
def s5_81 : State := ⟨[1,4,66,176], 95782432805755724832681813820190595867518655680024854, 2, 2, 1, 0⟩
theorem s5_81_edges : next config 5 s5_81 = [s6_60] := by decide
theorem s5_81_safe : Safe 8 5 s5_81 := by
  apply safe_succ 7 5 s5_81 [s6_60] (by decide) s5_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_60_safe
def s5_82 : State := ⟨[1,4,66,210], 1645504557321206042177270268038248049062735139514556029465596182, 2, 2, 1, 0⟩
theorem s5_82_edges : next config 5 s5_82 = [s6_63] := by decide
theorem s5_82_safe : Safe 8 5 s5_82 := by
  apply safe_succ 7 5 s5_82 [s6_63] (by decide) s5_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_63_safe
def s5_83 : State := ⟨[1,4,66,210], 1645529665728147588878024865997410256586863830663685524097667350, 2, 2, 1, 0⟩
theorem s5_83_edges : next config 5 s5_83 = [s6_64] := by decide
theorem s5_83_safe : Safe 8 5 s5_83 := by
  apply safe_succ 7 5 s5_83 [s6_64] (by decide) s5_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_64_safe
def s5_84 : State := ⟨[1,4,66,210], 27973577474460502716656777188955856128786508989651833843043336470, 2, 2, 1, 0⟩
theorem s5_84_edges : next config 5 s5_84 = [s6_65] := by decide
theorem s5_84_safe : Safe 8 5 s5_84 := by
  apply safe_succ 7 5 s5_84 [s6_65] (by decide) s5_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_65_safe
def s5_85 : State := ⟨[1,4,66,210], 27973602582867444263357531786915018336310637680800963337675407638, 2, 2, 1, 0⟩
theorem s5_85_edges : next config 5 s5_85 = [s6_66] := by decide
theorem s5_85_safe : Safe 8 5 s5_85 := by
  apply safe_succ 7 5 s5_85 [s6_66] (by decide) s5_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_66_safe
def s5_86 : State := ⟨[1,4,67,128], 340282366920938463629395304099449213214, 3, 3, 0, 0⟩
theorem s5_86_edges : next config 5 s5_86 = [s6_750, s6_30, s6_33, s6_62, s6_31, s6_34, s6_37, s6_50] := by decide
theorem s5_86_safe : Safe 8 5 s5_86 := by
  apply safe_succ 7 5 s5_86 [s6_750, s6_30, s6_33, s6_62, s6_31, s6_34, s6_37, s6_50] (by decide) s5_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_750_safe
  · subst z; exact s6_30_safe
  · subst z; exact s6_33_safe
  · subst z; exact s6_62_safe
  · subst z; exact s6_31_safe
  · subst z; exact s6_34_safe
  · subst z; exact s6_37_safe
  · subst z; exact s6_50_safe
def s5_87 : State := ⟨[1,4,67,129], 1020847100762815390593038007110404739350, 2, 2, 1, 0⟩
theorem s5_87_edges : next config 5 s5_87 = [s6_40] := by decide
theorem s5_87_safe : Safe 8 5 s5_87 := by
  apply safe_succ 7 5 s5_87 [s6_40] (by decide) s5_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_40_safe
def s5_88 : State := ⟨[1,4,67,129], 1020847100762815390629931495257823842582, 2, 2, 1, 0⟩
theorem s5_88_edges : next config 5 s5_88 = [s6_41] := by decide
theorem s5_88_safe : Safe 8 5 s5_88 := by
  apply safe_succ 7 5 s5_88 [s6_41] (by decide) s5_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_41_safe
def s5_89 : State := ⟨[1,4,67,130], 1701411834604692317519787221973941162262, 2, 2, 1, 0⟩
theorem s5_89_edges : next config 5 s5_89 = [s6_46, s6_51] := by decide
theorem s5_89_safe : Safe 8 5 s5_89 := by
  apply safe_succ 7 5 s5_89 [s6_46, s6_51] (by decide) s5_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_46_safe
  · subst z; exact s6_51_safe
def s5_90 : State := ⟨[1,4,67,130], 1701411834604692317556680710121360265494, 2, 2, 1, 0⟩
theorem s5_90_edges : next config 5 s5_90 = [s6_47, s6_52] := by decide
theorem s5_90_safe : Safe 8 5 s5_90 := by
  apply safe_succ 7 5 s5_90 [s6_47, s6_52] (by decide) s5_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_47_safe
  · subst z; exact s6_52_safe
def s5_91 : State := ⟨[1,4,67,132], 5784800237655953879080282511155159699734, 2, 2, 1, 0⟩
theorem s5_91_edges : next config 5 s5_91 = [] := by decide
theorem s5_91_safe : Safe 8 5 s5_91 := by
  apply safe_succ 7 5 s5_91 [] (by decide) s5_91_edges
  simp
def s5_92 : State := ⟨[1,4,67,132], 5784800237655953879117175999302578802966, 2, 2, 1, 0⟩
theorem s5_92_edges : next config 5 s5_92 = [] := by decide
theorem s5_92_safe : Safe 8 5 s5_92 := by
  apply safe_succ 7 5 s5_92 [] (by decide) s5_92_edges
  simp
def s5_93 : State := ⟨[1,4,67,136], 87452568298681185110290188294779530449174, 2, 2, 1, 0⟩
theorem s5_93_edges : next config 5 s5_93 = [] := by decide
theorem s5_93_safe : Safe 8 5 s5_93 := by
  apply safe_succ 7 5 s5_93 [] (by decide) s5_93_edges
  simp
def s5_94 : State := ⟨[1,4,67,136], 87452568298681185110327081782926949552406, 2, 2, 1, 0⟩
theorem s5_94_edges : next config 5 s5_94 = [] := by decide
theorem s5_94_safe : Safe 8 5 s5_94 := by
  apply safe_succ 7 5 s5_94 [] (by decide) s5_94_edges
  simp
def s5_95 : State := ⟨[1,4,67,136], 1481249143206845131456272580335302124568854, 2, 2, 1, 0⟩
theorem s5_95_edges : next config 5 s5_95 = [] := by decide
theorem s5_95_safe : Safe 8 5 s5_95 := by
  apply safe_succ 7 5 s5_95 [] (by decide) s5_95_edges
  simp
def s5_96 : State := ⟨[1,4,67,136], 1481249143206845131456309473823449543672086, 2, 2, 1, 0⟩
theorem s5_96_edges : next config 5 s5_96 = [] := by decide
theorem s5_96_safe : Safe 8 5 s5_96 := by
  apply safe_succ 7 5 s5_96 [] (by decide) s5_96_edges
  simp
def s5_97 : State := ⟨[1,4,67,140], 1394136857275084884809648680832769462440214, 2, 2, 1, 0⟩
theorem s5_97_edges : next config 5 s5_97 = [] := by decide
theorem s5_97_safe : Safe 8 5 s5_97 := by
  apply safe_succ 7 5 s5_97 [] (by decide) s5_97_edges
  simp
def s5_98 : State := ⟨[1,4,67,140], 1394136857275084884809685574320916881543446, 2, 2, 1, 0⟩
theorem s5_98_edges : next config 5 s5_98 = [] := by decide
theorem s5_98_safe : Safe 8 5 s5_98 := by
  apply safe_succ 7 5 s5_98 [] (by decide) s5_98_edges
  simp
def s5_99 : State := ⟨[1,4,67,140], 1399581375145819900225025781063530334716190, 1, 1, 1, 0⟩
theorem s5_99_edges : next config 5 s5_99 = [] := by decide
theorem s5_99_safe : Safe 8 5 s5_99 := by
  apply safe_succ 7 5 s5_99 [] (by decide) s5_99_edges
  simp
def s5_100 : State := ⟨[1,4,67,140], 1481249143206845131456235686847154705465630, 1, 1, 1, 0⟩
theorem s5_100_edges : next config 5 s5_100 = [] := by decide
theorem s5_100_safe : Safe 8 5 s5_100 := by
  apply safe_succ 7 5 s5_100 [] (by decide) s5_100_edges
  simp
def s5_101 : State := ⟨[1,4,67,144], 22301085480897544079999384561440608374296854, 2, 2, 1, 0⟩
theorem s5_101_edges : next config 5 s5_101 = [s6_42, s6_48, s6_57] := by decide
theorem s5_101_safe : Safe 8 5 s5_101 := by
  apply safe_succ 7 5 s5_101 [s6_42, s6_48, s6_57] (by decide) s5_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_42_safe
  · subst z; exact s6_48_safe
  · subst z; exact s6_57_safe
def s5_102 : State := ⟨[1,4,67,144], 22301085480897544079999421454928755793400086, 2, 2, 1, 0⟩
theorem s5_102_edges : next config 5 s5_102 = [s6_43, s6_49, s6_58] := by decide
theorem s5_102_safe : Safe 8 5 s5_102 := by
  apply safe_succ 7 5 s5_102 [s6_43, s6_49, s6_58] (by decide) s5_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_43_safe
  · subst z; exact s6_49_safe
  · subst z; exact s6_58_safe
def s5_103 : State := ⟨[1,4,67,145], 44601830679428167221535102834088969880404246, 1, 1, 1, 0⟩
theorem s5_103_edges : next config 5 s5_103 = [s6_414] := by decide
theorem s5_103_safe : Safe 8 5 s5_103 := by
  apply safe_succ 7 5 s5_103 [s6_414] (by decide) s5_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_414_safe
def s5_104 : State := ⟨[1,4,67,145], 44601830679428167221535139727577117299507478, 1, 1, 1, 0⟩
theorem s5_104_edges : next config 5 s5_104 = [s6_415] := by decide
theorem s5_104_safe : Safe 8 5 s5_104 := by
  apply safe_succ 7 5 s5_104 [s6_415] (by decide) s5_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_415_safe
def s5_105 : State := ⟨[1,4,67,145], 44602511244162009098461992689815685997592862, 1, 1, 1, 0⟩
theorem s5_105_edges : next config 5 s5_105 = [s6_416] := by decide
theorem s5_105_safe : Safe 8 5 s5_105 := by
  apply safe_succ 7 5 s5_105 [s6_416] (by decide) s5_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_416_safe
def s5_106 : State := ⟨[1,4,67,145], 66902575877958790363070784213249183967150366, 1, 1, 1, 0⟩
theorem s5_106_edges : next config 5 s5_106 = [s6_417] := by decide
theorem s5_106_safe : Safe 8 5 s5_106 := by
  apply safe_succ 7 5 s5_106 [s6_417] (by decide) s5_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_417_safe
def s5_107 : State := ⟨[1,4,67,145], 1645504557321206042221871758435309295345806723633805342153965846, 0, 0, 1, 0⟩
theorem s5_107_edges : next config 5 s5_107 = [s6_418] := by decide
theorem s5_107_safe : Safe 8 5 s5_107 := by
  apply safe_succ 7 5 s5_107 [s6_418] (by decide) s5_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_418_safe
def s5_108 : State := ⟨[1,4,67,145], 1645529665728147588922626356394471502869935414782934836786037014, 0, 0, 1, 0⟩
theorem s5_108_edges : next config 5 s5_108 = [s6_419] := by decide
theorem s5_108_safe : Safe 8 5 s5_108 := by
  apply safe_succ 7 5 s5_108 [s6_419] (by decide) s5_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_419_safe
def s5_109 : State := ⟨[1,4,67,145], 2056880696651507552760614054074646921591490616255224013152911638, 0, 0, 1, 0⟩
theorem s5_109_edges : next config 5 s5_109 = [s6_420] := by decide
theorem s5_109_safe : Safe 8 5 s5_109 := by
  apply safe_succ 7 5 s5_109 [s6_420] (by decide) s5_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_420_safe
def s5_110 : State := ⟨[1,4,67,146], 89204682205957097258460355984327272545976606, 1, 1, 1, 0⟩
theorem s5_110_edges : next config 5 s5_110 = [s6_421] := by decide
theorem s5_110_safe : Safe 8 5 s5_110 := by
  apply safe_succ 7 5 s5_110 [s6_421] (by decide) s5_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_421_safe
def s5_111 : State := ⟨[1,4,67,146], 111504066275020036646142220758545906979111198, 1, 1, 1, 0⟩
theorem s5_111_edges : next config 5 s5_111 = [s6_422] := by decide
theorem s5_111_safe : Safe 8 5 s5_111 := by
  apply safe_succ 7 5 s5_111 [s6_422] (by decide) s5_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_422_safe
def s5_112 : State := ⟨[1,4,67,160], 1461501637671185285124623296382571811902800859414, 2, 2, 1, 0⟩
theorem s5_112_edges : next config 5 s5_112 = [s6_53, s6_59] := by decide
theorem s5_112_safe : Safe 8 5 s5_112 := by
  apply safe_succ 7 5 s5_112 [s6_53, s6_59] (by decide) s5_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_53_safe
  · subst z; exact s6_59_safe
def s5_113 : State := ⟨[1,4,67,160], 1461501637671185285124623296419465300050219962646, 2, 2, 1, 0⟩
theorem s5_113_edges : next config 5 s5_113 = [s6_54, s6_60] := by decide
theorem s5_113_safe : Safe 8 5 s5_113 := by
  apply safe_succ 7 5 s5_113 [s6_54, s6_60] (by decide) s5_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_54_safe
  · subst z; exact s6_60_safe
def s5_114 : State := ⟨[1,4,67,162], 5846006551025023507419431648348025812450252226846, 1, 1, 1, 0⟩
theorem s5_114_edges : next config 5 s5_114 = [s6_423] := by decide
theorem s5_114_safe : Safe 8 5 s5_114 := by
  apply safe_succ 7 5 s5_114 [s6_423] (by decide) s5_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_423_safe
def s5_115 : State := ⟨[1,4,67,162], 7307508186994796957939362627210810402379111923998, 1, 1, 1, 0⟩
theorem s5_115_edges : next config 5 s5_115 = [s6_424] := by decide
theorem s5_115_safe : Safe 8 5 s5_115 := by
  apply safe_succ 7 5 s5_115 [s6_424] (by decide) s5_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_424_safe
def s5_116 : State := ⟨[1,4,67,163], 11692013101709764647917924833066656320801055244574, 1, 1, 1, 0⟩
theorem s5_116_edges : next config 5 s5_116 = [s6_425, s6_55] := by decide
theorem s5_116_safe : Safe 8 5 s5_116 := by
  apply safe_succ 7 5 s5_116 [s6_425, s6_55] (by decide) s5_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_425_safe
  · subst z; exact s6_55_safe
def s5_117 : State := ⟨[1,4,67,163], 13153514736318408630754101958075942481002842095902, 1, 1, 1, 0⟩
theorem s5_117_edges : next config 5 s5_117 = [s6_426, s6_56] := by decide
theorem s5_117_safe : Safe 8 5 s5_117 := by
  apply safe_succ 7 5 s5_117 [s6_426, s6_56] (by decide) s5_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_426_safe
  · subst z; exact s6_56_safe
def s5_118 : State := ⟨[1,4,67,176], 95780971326419139128294233276893671644123656091664670, 1, 1, 1, 0⟩
theorem s5_118_edges : next config 5 s5_118 = [s6_427] := by decide
theorem s5_118_safe : Safe 8 5 s5_118 := by
  apply safe_succ 7 5 s5_118 [s6_427] (by decide) s5_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_427_safe
def s5_119 : State := ⟨[1,4,67,176], 95782432805755724832681813820190669654494950518227230, 1, 1, 1, 0⟩
theorem s5_119_edges : next config 5 s5_119 = [s6_428] := by decide
theorem s5_119_safe : Safe 8 5 s5_119 := by
  apply safe_succ 7 5 s5_119 [s6_428] (by decide) s5_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_428_safe
def s5_120 : State := ⟨[1,4,67,192], 6277101735386680764176071790128604879768644236710902829334, 2, 2, 1, 0⟩
theorem s5_120_edges : next config 5 s5_120 = [] := by decide
theorem s5_120_safe : Safe 8 5 s5_120 := by
  apply safe_succ 7 5 s5_120 [] (by decide) s5_120_edges
  simp
def s5_121 : State := ⟨[1,4,67,192], 6277101735386680764176071790128604879805537724858321932566, 2, 2, 1, 0⟩
theorem s5_121_edges : next config 5 s5_121 = [] := by decide
theorem s5_121_safe : Safe 8 5 s5_121 := by
  apply safe_succ 7 5 s5_121 [] (by decide) s5_121_edges
  simp
def s5_122 : State := ⟨[1,4,67,193], 12554203470773361528011861213336271295870999681174937342230, 2, 2, 1, 0⟩
theorem s5_122_edges : next config 5 s5_122 = [] := by decide
theorem s5_122_safe : Safe 8 5 s5_122 := by
  apply safe_succ 7 5 s5_122 [] (by decide) s5_122_edges
  simp
def s5_123 : State := ⟨[1,4,67,194], 25108406941546723055683440059751604128112604058250425471254, 2, 2, 1, 0⟩
theorem s5_123_edges : next config 5 s5_123 = [s6_64] := by decide
theorem s5_123_safe : Safe 8 5 s5_123 := by
  apply safe_succ 7 5 s5_123 [s6_64] (by decide) s5_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_64_safe
def s5_124 : State := ⟨[1,4,67,195], 50216813883093446111026597752582269792485132347959144419606, 2, 2, 1, 0⟩
theorem s5_124_edges : next config 5 s5_124 = [] := by decide
theorem s5_124_safe : Safe 8 5 s5_124 := by
  apply safe_succ 7 5 s5_124 [] (by decide) s5_124_edges
  simp
def s5_125 : State := ⟨[1,4,67,195], 50216813883093446111026597752582269792522025836106563522838, 2, 2, 1, 0⟩
theorem s5_125_edges : next config 5 s5_125 = [] := by decide
theorem s5_125_safe : Safe 8 5 s5_125 := by
  apply safe_succ 7 5 s5_125 [] (by decide) s5_125_edges
  simp
def s5_126 : State := ⟨[1,4,67,214], 27973577474460502716656777188955856128786509137225786432719749398, 0, 0, 1, 0⟩
theorem s5_126_edges : next config 5 s5_126 = [] := by decide
theorem s5_126_safe : Safe 8 5 s5_126 := by
  apply safe_succ 7 5 s5_126 [] (by decide) s5_126_edges
  simp
def s5_127 : State := ⟨[1,4,67,214], 27973602582867444263357531786915018336310637828374915927351820566, 0, 0, 1, 0⟩
theorem s5_127_edges : next config 5 s5_127 = [] := by decide
theorem s5_127_safe : Safe 8 5 s5_127 := by
  apply safe_succ 7 5 s5_127 [] (by decide) s5_127_edges
  simp
def s5_128 : State := ⟨[1,4,80,145], 44602511244162009099670770935477725495890198, 2, 2, 1, 0⟩
theorem s5_128_edges : next config 5 s5_128 = [s6_73] := by decide
theorem s5_128_safe : Safe 8 5 s5_128 := by
  apply safe_succ 7 5 s5_128 [s6_73] (by decide) s5_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_73_safe
def s5_129 : State := ⟨[1,4,80,145], 66902575877958790364279562458911223465447702, 2, 2, 1, 0⟩
theorem s5_129_edges : next config 5 s5_129 = [s6_77] := by decide
theorem s5_129_safe : Safe 8 5 s5_129 := by
  apply safe_succ 7 5 s5_129 [s6_77] (by decide) s5_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_77_safe
def s5_130 : State := ⟨[1,4,80,210], 1645504557321206042154970883969185109676262126772975729368961302, 2, 2, 1, 0⟩
theorem s5_130_edges : next config 5 s5_130 = [] := by decide
theorem s5_130_safe : Safe 8 5 s5_130 := by
  apply safe_succ 7 5 s5_130 [] (by decide) s5_130_edges
  simp
def s5_131 : State := ⟨[1,4,80,210], 2056880696651507552693711818479055052168092239682940968133267734, 2, 2, 1, 0⟩
theorem s5_131_edges : next config 5 s5_131 = [] := by decide
theorem s5_131_safe : Safe 8 5 s5_131 := by
  apply safe_succ 7 5 s5_131 [] (by decide) s5_131_edges
  simp
def s5_132 : State := ⟨[1,4,80,210], 27973577474460502716634477804886793189400035976910253542946701590, 2, 2, 1, 0⟩
theorem s5_132_edges : next config 5 s5_132 = [] := by decide
theorem s5_132_safe : Safe 8 5 s5_132 := by
  apply safe_succ 7 5 s5_132 [] (by decide) s5_132_edges
  simp
def s5_133 : State := ⟨[1,4,80,210], 28384953613790804227173218739396663131891866089820218781711008022, 2, 2, 1, 0⟩
theorem s5_133_edges : next config 5 s5_133 = [] := by decide
theorem s5_133_safe : Safe 8 5 s5_133 := by
  apply safe_succ 7 5 s5_133 [] (by decide) s5_133_edges
  simp
def s5_134 : State := ⟨[1,4,82,129], 1020847100762820226185636001184846254358, 2, 2, 1, 0⟩
theorem s5_134_edges : next config 5 s5_134 = [s6_72] := by decide
theorem s5_134_safe : Safe 8 5 s5_134 := by
  apply safe_succ 7 5 s5_134 [s6_72] (by decide) s5_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_72_safe
def s5_135 : State := ⟨[1,4,82,129], 1020847100762821435037668639519182754070, 2, 2, 1, 0⟩
theorem s5_135_edges : next config 5 s5_135 = [s6_73] := by decide
theorem s5_135_safe : Safe 8 5 s5_135 := by
  apply safe_succ 7 5 s5_135 [s6_73] (by decide) s5_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_73_safe
def s5_136 : State := ⟨[1,4,82,129], 1020847100762897597438091337452027445526, 2, 2, 1, 0⟩
theorem s5_136_edges : next config 5 s5_136 = [s6_74] := by decide
theorem s5_136_safe : Safe 8 5 s5_136 := by
  apply safe_succ 7 5 s5_136 [s6_74] (by decide) s5_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_74_safe
def s5_137 : State := ⟨[1,4,82,129], 1020847100762898806290123975786363945238, 2, 2, 1, 0⟩
theorem s5_137_edges : next config 5 s5_137 = [s6_75] := by decide
theorem s5_137_safe : Safe 8 5 s5_137 := by
  apply safe_succ 7 5 s5_137 [s6_75] (by decide) s5_137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_75_safe
def s5_138 : State := ⟨[1,4,82,130], 1701411834604697153112385216048382677270, 2, 2, 1, 0⟩
theorem s5_138_edges : next config 5 s5_138 = [] := by decide
theorem s5_138_safe : Safe 8 5 s5_138 := by
  apply safe_succ 7 5 s5_138 [] (by decide) s5_138_edges
  simp
def s5_139 : State := ⟨[1,4,82,130], 1701411834604698361964417854382719176982, 2, 2, 1, 0⟩
theorem s5_139_edges : next config 5 s5_139 = [] := by decide
theorem s5_139_safe : Safe 8 5 s5_139 := by
  apply safe_succ 7 5 s5_139 [] (by decide) s5_139_edges
  simp
def s5_140 : State := ⟨[1,4,82,130], 1701411834604774524364840552315563868438, 2, 2, 1, 0⟩
theorem s5_140_edges : next config 5 s5_140 = [] := by decide
theorem s5_140_safe : Safe 8 5 s5_140 := by
  apply safe_succ 7 5 s5_140 [] (by decide) s5_140_edges
  simp
def s5_141 : State := ⟨[1,4,82,130], 1701411834604775733216873190649900368150, 2, 2, 1, 0⟩
theorem s5_141_edges : next config 5 s5_141 = [] := by decide
theorem s5_141_safe : Safe 8 5 s5_141 := by
  apply safe_succ 7 5 s5_141 [] (by decide) s5_141_edges
  simp
def s5_142 : State := ⟨[1,4,82,132], 5784800237655958714672880505229601214742, 2, 2, 1, 0⟩
theorem s5_142_edges : next config 5 s5_142 = [] := by decide
theorem s5_142_safe : Safe 8 5 s5_142 := by
  apply safe_succ 7 5 s5_142 [] (by decide) s5_142_edges
  simp
def s5_143 : State := ⟨[1,4,82,132], 5784800237655959923524913143563937714454, 2, 2, 1, 0⟩
theorem s5_143_edges : next config 5 s5_143 = [] := by decide
theorem s5_143_safe : Safe 8 5 s5_143 := by
  apply safe_succ 7 5 s5_143 [] (by decide) s5_143_edges
  simp
def s5_144 : State := ⟨[1,4,82,132], 5784800237656036085925335841496782405910, 2, 2, 1, 0⟩
theorem s5_144_edges : next config 5 s5_144 = [] := by decide
theorem s5_144_safe : Safe 8 5 s5_144 := by
  apply safe_succ 7 5 s5_144 [] (by decide) s5_144_edges
  simp
def s5_145 : State := ⟨[1,4,82,132], 5784800237656037294777368479831118905622, 2, 2, 1, 0⟩
theorem s5_145_edges : next config 5 s5_145 = [] := by decide
theorem s5_145_safe : Safe 8 5 s5_145 := by
  apply safe_succ 7 5 s5_145 [] (by decide) s5_145_edges
  simp
def s5_146 : State := ⟨[1,4,82,136], 87452568298681189945882786288853971964182, 2, 2, 1, 0⟩
theorem s5_146_edges : next config 5 s5_146 = [] := by decide
theorem s5_146_safe : Safe 8 5 s5_146 := by
  apply safe_succ 7 5 s5_146 [] (by decide) s5_146_edges
  simp
def s5_147 : State := ⟨[1,4,82,136], 87452568298681191154734818927188308463894, 2, 2, 1, 0⟩
theorem s5_147_edges : next config 5 s5_147 = [] := by decide
theorem s5_147_safe : Safe 8 5 s5_147 := by
  apply safe_succ 7 5 s5_147 [] (by decide) s5_147_edges
  simp
def s5_148 : State := ⟨[1,4,82,136], 87452568298681267317135241625121153155350, 2, 2, 1, 0⟩
theorem s5_148_edges : next config 5 s5_148 = [] := by decide
theorem s5_148_safe : Safe 8 5 s5_148 := by
  apply safe_succ 7 5 s5_148 [] (by decide) s5_148_edges
  simp
def s5_149 : State := ⟨[1,4,82,136], 87452568298681268525987274263455489655062, 2, 2, 1, 0⟩
theorem s5_149_edges : next config 5 s5_149 = [] := by decide
theorem s5_149_safe : Safe 8 5 s5_149 := by
  apply safe_succ 7 5 s5_149 [] (by decide) s5_149_edges
  simp
def s5_150 : State := ⟨[1,4,82,136], 1481249143206845136291865178329376566083862, 2, 2, 1, 0⟩
theorem s5_150_edges : next config 5 s5_150 = [] := by decide
theorem s5_150_safe : Safe 8 5 s5_150 := by
  apply safe_succ 7 5 s5_150 [] (by decide) s5_150_edges
  simp
def s5_151 : State := ⟨[1,4,82,136], 1481249143206845137500717210967710902583574, 2, 2, 1, 0⟩
theorem s5_151_edges : next config 5 s5_151 = [] := by decide
theorem s5_151_safe : Safe 8 5 s5_151 := by
  apply safe_succ 7 5 s5_151 [] (by decide) s5_151_edges
  simp
def s5_152 : State := ⟨[1,4,82,140], 1394136857275084889645241278826843903955222, 2, 2, 1, 0⟩
theorem s5_152_edges : next config 5 s5_152 = [] := by decide
theorem s5_152_safe : Safe 8 5 s5_152 := by
  apply safe_succ 7 5 s5_152 [] (by decide) s5_152_edges
  simp
def s5_153 : State := ⟨[1,4,82,140], 1394136857275084890854093311465178240454934, 2, 2, 1, 0⟩
theorem s5_153_edges : next config 5 s5_153 = [] := by decide
theorem s5_153_safe : Safe 8 5 s5_153 := by
  apply safe_succ 7 5 s5_153 [] (by decide) s5_153_edges
  simp
def s5_154 : State := ⟨[1,4,82,144], 22301085480897544084834977159434682815811862, 2, 2, 1, 0⟩
theorem s5_154_edges : next config 5 s5_154 = [s6_76] := by decide
theorem s5_154_safe : Safe 8 5 s5_154 := by
  apply safe_succ 7 5 s5_154 [s6_76] (by decide) s5_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_76_safe
def s5_155 : State := ⟨[1,4,82,144], 22301085480897544086043829192073017152311574, 2, 2, 1, 0⟩
theorem s5_155_edges : next config 5 s5_155 = [s6_77] := by decide
theorem s5_155_safe : Safe 8 5 s5_155 := by
  apply safe_succ 7 5 s5_155 [s6_77] (by decide) s5_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_77_safe
def s5_156 : State := ⟨[1,4,82,144], 22301085480897544162206229614770949997003030, 2, 2, 1, 0⟩
theorem s5_156_edges : next config 5 s5_156 = [s6_78] := by decide
theorem s5_156_safe : Safe 8 5 s5_156 := by
  apply safe_succ 7 5 s5_156 [s6_78] (by decide) s5_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_78_safe
def s5_157 : State := ⟨[1,4,82,144], 22301085480897544163415081647409284333502742, 2, 2, 1, 0⟩
theorem s5_157_edges : next config 5 s5_157 = [s6_79] := by decide
theorem s5_157_safe : Safe 8 5 s5_157 := by
  apply safe_succ 7 5 s5_157 [s6_79] (by decide) s5_157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_79_safe
def s5_158 : State := ⟨[1,4,82,145], 44601830679428167226370695432083044321919254, 1, 1, 1, 0⟩
theorem s5_158_edges : next config 5 s5_158 = [s6_552, s6_429, s6_80] := by decide
theorem s5_158_safe : Safe 8 5 s5_158 := by
  apply safe_succ 7 5 s5_158 [s6_552, s6_429, s6_80] (by decide) s5_158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_552_safe
  · subst z; exact s6_429_safe
  · subst z; exact s6_80_safe
def s5_159 : State := ⟨[1,4,82,145], 44601830679428167227579547464721378658418966, 1, 1, 1, 0⟩
theorem s5_159_edges : next config 5 s5_159 = [s6_553, s6_430, s6_81] := by decide
theorem s5_159_safe : Safe 8 5 s5_159 := by
  apply safe_succ 7 5 s5_159 [s6_553, s6_430, s6_81] (by decide) s5_159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_553_safe
  · subst z; exact s6_430_safe
  · subst z; exact s6_81_safe
def s5_160 : State := ⟨[1,4,82,160], 1461501637671185285124628131975169805977242374422, 2, 2, 1, 0⟩
theorem s5_160_edges : next config 5 s5_160 = [] := by decide
theorem s5_160_safe : Safe 8 5 s5_160 := by
  apply safe_succ 7 5 s5_160 [] (by decide) s5_160_edges
  simp
def s5_161 : State := ⟨[1,4,82,160], 1461501637671185285124629340827202444311578874134, 2, 2, 1, 0⟩
theorem s5_161_edges : next config 5 s5_161 = [] := by decide
theorem s5_161_safe : Safe 8 5 s5_161 := by
  apply safe_succ 7 5 s5_161 [] (by decide) s5_161_edges
  simp
def s5_162 : State := ⟨[1,4,82,160], 1461501637671185285124705503227625142244423565590, 2, 2, 1, 0⟩
theorem s5_162_edges : next config 5 s5_162 = [] := by decide
theorem s5_162_safe : Safe 8 5 s5_162 := by
  apply safe_succ 7 5 s5_162 [] (by decide) s5_162_edges
  simp
def s5_163 : State := ⟨[1,4,82,160], 1461501637671185285124706712079657780578760065302, 2, 2, 1, 0⟩
theorem s5_163_edges : next config 5 s5_163 = [] := by decide
theorem s5_163_safe : Safe 8 5 s5_163 := by
  apply safe_succ 7 5 s5_163 [] (by decide) s5_163_edges
  simp
def s5_164 : State := ⟨[1,4,82,192], 6277101735386680764176071790128609715361242230785344344342, 2, 2, 1, 0⟩
theorem s5_164_edges : next config 5 s5_164 = [] := by decide
theorem s5_164_safe : Safe 8 5 s5_164 := by
  apply safe_succ 7 5 s5_164 [] (by decide) s5_164_edges
  simp
def s5_165 : State := ⟨[1,4,82,192], 6277101735386680764176071790128610924213274869119680844054, 2, 2, 1, 0⟩
theorem s5_165_edges : next config 5 s5_165 = [] := by decide
theorem s5_165_safe : Safe 8 5 s5_165 := by
  apply safe_succ 7 5 s5_165 [] (by decide) s5_165_edges
  simp
def s5_166 : State := ⟨[1,4,82,192], 6277101735386680764176071790128687086613697567052525535510, 2, 2, 1, 0⟩
theorem s5_166_edges : next config 5 s5_166 = [] := by decide
theorem s5_166_safe : Safe 8 5 s5_166 := by
  apply safe_succ 7 5 s5_166 [] (by decide) s5_166_edges
  simp
def s5_167 : State := ⟨[1,4,82,192], 6277101735386680764176071790128688295465730205386862035222, 2, 2, 1, 0⟩
theorem s5_167_edges : next config 5 s5_167 = [] := by decide
theorem s5_167_safe : Safe 8 5 s5_167 := by
  apply safe_succ 7 5 s5_167 [] (by decide) s5_167_edges
  simp
def s5_168 : State := ⟨[1,4,82,194], 25108406941546723055683440059751608963668308564177447883030, 2, 2, 1, 0⟩
theorem s5_168_edges : next config 5 s5_168 = [] := by decide
theorem s5_168_safe : Safe 8 5 s5_168 := by
  apply safe_succ 7 5 s5_168 [] (by decide) s5_168_edges
  simp
def s5_169 : State := ⟨[1,4,82,194], 25108406941546723055683440059751686334920763900444629074198, 2, 2, 1, 0⟩
theorem s5_169_edges : next config 5 s5_169 = [] := by decide
theorem s5_169_safe : Safe 8 5 s5_169 := by
  apply safe_succ 7 5 s5_169 [] (by decide) s5_169_edges
  simp
def s5_170 : State := ⟨[1,4,82,208], 411376139330301510538742635921704547190192077327819621483483414, 2, 2, 1, 0⟩
theorem s5_170_edges : next config 5 s5_170 = [] := by decide
theorem s5_170_safe : Safe 8 5 s5_170 := by
  apply safe_succ 7 5 s5_170 [] (by decide) s5_170_edges
  simp
def s5_171 : State := ⟨[1,4,82,208], 411376139330301510538742635921704547267563329783155888664674582, 2, 2, 1, 0⟩
theorem s5_171_edges : next config 5 s5_171 = [] := by decide
theorem s5_171_safe : Safe 8 5 s5_171 := by
  apply safe_succ 7 5 s5_171 [] (by decide) s5_171_edges
  simp
def s5_172 : State := ⟨[1,4,82,210], 1645504557321206042154969522839717425926035124520366184658440470, 2, 2, 1, 0⟩
theorem s5_172_edges : next config 5 s5_172 = [] := by decide
theorem s5_172_safe : Safe 8 5 s5_172 := by
  apply safe_succ 7 5 s5_172 [] (by decide) s5_172_edges
  simp
def s5_173 : State := ⟨[1,4,82,210], 1645504557321206042154969522839717425927243976553004518994940182, 2, 2, 1, 0⟩
theorem s5_173_edges : next config 5 s5_173 = [] := by decide
theorem s5_173_safe : Safe 8 5 s5_173 := by
  apply safe_succ 7 5 s5_173 [] (by decide) s5_173_edges
  simp
def s5_174 : State := ⟨[1,4,82,210], 1645504557321206042154969522839717426003406376975702451839631638, 2, 2, 1, 0⟩
theorem s5_174_edges : next config 5 s5_174 = [] := by decide
theorem s5_174_safe : Safe 8 5 s5_174 := by
  apply safe_succ 7 5 s5_174 [] (by decide) s5_174_edges
  simp
def s5_175 : State := ⟨[1,4,82,210], 1645504557321206042154969522839717426004615229008340786176131350, 2, 2, 1, 0⟩
theorem s5_175_edges : next config 5 s5_175 = [] := by decide
theorem s5_175_safe : Safe 8 5 s5_175 := by
  apply safe_succ 7 5 s5_175 [] (by decide) s5_175_edges
  simp
def s5_176 : State := ⟨[1,4,82,210], 27973577474460502716634476443757325505649808974657643998236180758, 2, 2, 1, 0⟩
theorem s5_176_edges : next config 5 s5_176 = [] := by decide
theorem s5_176_safe : Safe 8 5 s5_176 := by
  apply safe_succ 7 5 s5_176 [] (by decide) s5_176_edges
  simp
def s5_177 : State := ⟨[1,4,82,210], 27973577474460502716634476443757325505651017826690282332572680470, 2, 2, 1, 0⟩
theorem s5_177_edges : next config 5 s5_177 = [] := by decide
theorem s5_177_safe : Safe 8 5 s5_177 := by
  apply safe_succ 7 5 s5_177 [] (by decide) s5_177_edges
  simp
def s5_178 : State := ⟨[1,4,82,214], 26328072917139296674479507261199975000744444361479400402068766998, 2, 2, 1, 0⟩
theorem s5_178_edges : next config 5 s5_178 = [] := by decide
theorem s5_178_safe : Safe 8 5 s5_178 := by
  apply safe_succ 7 5 s5_178 [] (by decide) s5_178_edges
  simp
def s5_179 : State := ⟨[1,4,82,214], 26328072917139296674479507261199975000745653213512038736405266710, 2, 2, 1, 0⟩
theorem s5_179_edges : next config 5 s5_179 = [] := by decide
theorem s5_179_safe : Safe 8 5 s5_179 := by
  apply safe_succ 7 5 s5_179 [] (by decide) s5_179_edges
  simp
def s5_180 : State := ⟨[1,4,86,145], 44602511244162009180668874636634175039406358, 0, 0, 1, 0⟩
theorem s5_180_edges : next config 5 s5_180 = [] := by decide
theorem s5_180_safe : Safe 8 5 s5_180 := by
  apply safe_succ 7 5 s5_180 [] (by decide) s5_180_edges
  simp
def s5_181 : State := ⟨[1,4,86,145], 44602511244162009181877726669272509375906070, 0, 0, 1, 0⟩
theorem s5_181_edges : next config 5 s5_181 = [] := by decide
theorem s5_181_safe : Safe 8 5 s5_181 := by
  apply safe_succ 7 5 s5_181 [] (by decide) s5_181_edges
  simp
def s5_182 : State := ⟨[1,4,86,145], 66902575877958790445277666160067673008963862, 0, 0, 1, 0⟩
theorem s5_182_edges : next config 5 s5_182 = [] := by decide
theorem s5_182_safe : Safe 8 5 s5_182 := by
  apply safe_succ 7 5 s5_182 [] (by decide) s5_182_edges
  simp
def s5_183 : State := ⟨[1,4,86,145], 66902575877958790446486518192706007345463574, 0, 0, 1, 0⟩
theorem s5_183_edges : next config 5 s5_183 = [] := by decide
theorem s5_183_safe : Safe 8 5 s5_183 := by
  apply safe_succ 7 5 s5_183 [] (by decide) s5_183_edges
  simp
def s5_184 : State := ⟨[1,4,96,128], 340282367000166625996085689103316750622, 3, 3, 0, 0⟩
theorem s5_184_edges : next config 5 s5_184 = [s6_770, s6_200, s6_82, s6_98, s6_180, s6_88, s6_104, s6_118, s6_130] := by decide
theorem s5_184_safe : Safe 8 5 s5_184 := by
  apply safe_succ 7 5 s5_184 [s6_770, s6_200, s6_82, s6_98, s6_180, s6_88, s6_104, s6_118, s6_130] (by decide) s5_184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_770_safe
  · subst z; exact s6_200_safe
  · subst z; exact s6_82_safe
  · subst z; exact s6_98_safe
  · subst z; exact s6_180_safe
  · subst z; exact s6_88_safe
  · subst z; exact s6_104_safe
  · subst z; exact s6_118_safe
  · subst z; exact s6_130_safe
def s5_185 : State := ⟨[1,4,96,128], 340282367000166625996085689111906685206, 3, 3, 0, 0⟩
theorem s5_185_edges : next config 5 s5_185 = [s6_773, s6_201, s6_83, s6_99, s6_181, s6_89, s6_105, s6_119, s6_131] := by decide
theorem s5_185_safe : Safe 8 5 s5_185 := by
  apply safe_succ 7 5 s5_185 [s6_773, s6_201, s6_83, s6_99, s6_181, s6_89, s6_105, s6_119, s6_131] (by decide) s5_185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_773_safe
  · subst z; exact s6_201_safe
  · subst z; exact s6_83_safe
  · subst z; exact s6_99_safe
  · subst z; exact s6_181_safe
  · subst z; exact s6_89_safe
  · subst z; exact s6_105_safe
  · subst z; exact s6_119_safe
  · subst z; exact s6_131_safe
def s5_186 : State := ⟨[1,4,96,128], 340282367000166626032979177250735853846, 3, 3, 0, 0⟩
theorem s5_186_edges : next config 5 s5_186 = [s6_775, s6_202, s6_84, s6_100, s6_182, s6_90, s6_106, s6_120, s6_132] := by decide
theorem s5_186_safe : Safe 8 5 s5_186 := by
  apply safe_succ 7 5 s5_186 [s6_775, s6_202, s6_84, s6_100, s6_182, s6_90, s6_106, s6_120, s6_132] (by decide) s5_186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_775_safe
  · subst z; exact s6_202_safe
  · subst z; exact s6_84_safe
  · subst z; exact s6_100_safe
  · subst z; exact s6_182_safe
  · subst z; exact s6_90_safe
  · subst z; exact s6_106_safe
  · subst z; exact s6_120_safe
  · subst z; exact s6_132_safe
def s5_187 : State := ⟨[1,4,96,128], 340282367158622951024614364290404651286, 3, 3, 0, 0⟩
theorem s5_187_edges : next config 5 s5_187 = [s6_777, s6_203, s6_85, s6_101, s6_183, s6_91, s6_107, s6_121, s6_133] := by decide
theorem s5_187_safe : Safe 8 5 s5_187 := by
  apply safe_succ 7 5 s5_187 [s6_777, s6_203, s6_85, s6_101, s6_183, s6_91, s6_107, s6_121, s6_133] (by decide) s5_187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_777_safe
  · subst z; exact s6_203_safe
  · subst z; exact s6_85_safe
  · subst z; exact s6_101_safe
  · subst z; exact s6_183_safe
  · subst z; exact s6_91_safe
  · subst z; exact s6_107_safe
  · subst z; exact s6_121_safe
  · subst z; exact s6_133_safe
def s5_188 : State := ⟨[1,4,96,128], 340282368267817226224315090600019951902, 3, 3, 0, 0⟩
theorem s5_188_edges : next config 5 s5_188 = [s6_779, s6_204, s6_86, s6_102, s6_184, s6_92, s6_108, s6_122, s6_134] := by decide
theorem s5_188_safe : Safe 8 5 s5_188 := by
  apply safe_succ 7 5 s5_188 [s6_779, s6_204, s6_86, s6_102, s6_184, s6_92, s6_108, s6_122, s6_134] (by decide) s5_188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_779_safe
  · subst z; exact s6_204_safe
  · subst z; exact s6_86_safe
  · subst z; exact s6_102_safe
  · subst z; exact s6_184_safe
  · subst z; exact s6_92_safe
  · subst z; exact s6_108_safe
  · subst z; exact s6_122_safe
  · subst z; exact s6_134_safe
def s5_189 : State := ⟨[1,4,96,128], 340282368267817226261208578747439055126, 3, 3, 0, 0⟩
theorem s5_189_edges : next config 5 s5_189 = [s6_780, s6_205, s6_87, s6_103, s6_185, s6_93, s6_109, s6_123, s6_135] := by decide
theorem s5_189_safe : Safe 8 5 s5_189 := by
  apply safe_succ 7 5 s5_189 [s6_780, s6_205, s6_87, s6_103, s6_185, s6_93, s6_109, s6_123, s6_135] (by decide) s5_189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_780_safe
  · subst z; exact s6_205_safe
  · subst z; exact s6_87_safe
  · subst z; exact s6_103_safe
  · subst z; exact s6_185_safe
  · subst z; exact s6_93_safe
  · subst z; exact s6_109_safe
  · subst z; exact s6_123_safe
  · subst z; exact s6_135_safe
def s5_190 : State := ⟨[1,4,96,131], 3743106036209551260629831763420998865174, 2, 2, 1, 0⟩
theorem s5_190_edges : next config 5 s5_190 = [s6_208, s6_140] := by decide
theorem s5_190_safe : Safe 8 5 s5_190 := by
  apply safe_succ 7 5 s5_190 [s6_208, s6_140] (by decide) s5_190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_208_safe
  · subst z; exact s6_140_safe
def s5_191 : State := ⟨[1,4,96,131], 3743106037477201860858061164917702066454, 2, 2, 1, 0⟩
theorem s5_191_edges : next config 5 s5_191 = [s6_209] := by decide
theorem s5_191_safe : Safe 8 5 s5_191 := by
  apply safe_succ 7 5 s5_191 [s6_209] (by decide) s5_191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_209_safe
def s5_192 : State := ⟨[1,4,96,131], 4423670770051428187556580978284535288086, 2, 2, 1, 0⟩
theorem s5_192_edges : next config 5 s5_192 = [s6_211, s6_141] := by decide
theorem s5_192_safe : Safe 8 5 s5_192 := by
  apply safe_succ 7 5 s5_192 [s6_211, s6_141] (by decide) s5_192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_211_safe
  · subst z; exact s6_141_safe
def s5_193 : State := ⟨[1,4,96,131], 4423670771319078787784810379781238489366, 2, 2, 1, 0⟩
theorem s5_193_edges : next config 5 s5_193 = [s6_212] := by decide
theorem s5_193_safe : Safe 8 5 s5_193 := by
  apply safe_succ 7 5 s5_193 [s6_212] (by decide) s5_193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_212_safe
def s5_194 : State := ⟨[1,4,96,140], 1399581375145899128387392471448534202253598, 1, 1, 1, 0⟩
theorem s5_194_edges : next config 5 s5_194 = [s6_214] := by decide
theorem s5_194_safe : Safe 8 5 s5_194 := by
  apply safe_succ 7 5 s5_194 [s6_214] (by decide) s5_194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_214_safe
def s5_195 : State := ⟨[1,4,96,140], 1399581375145899128387392471448542792188182, 1, 1, 1, 0⟩
theorem s5_195_edges : next config 5 s5_195 = [s6_215] := by decide
theorem s5_195_safe : Safe 8 5 s5_195 := by
  apply safe_succ 7 5 s5_195 [s6_215] (by decide) s5_195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_215_safe
def s5_196 : State := ⟨[1,4,96,140], 1399581375145899128387429364936681621356822, 1, 1, 1, 0⟩
theorem s5_196_edges : next config 5 s5_196 = [s6_216] := by decide
theorem s5_196_safe : Safe 8 5 s5_196 := by
  apply safe_succ 7 5 s5_196 [s6_216] (by decide) s5_196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_216_safe
def s5_197 : State := ⟨[1,4,96,140], 1399581375146057584712421000123721290154262, 1, 1, 1, 0⟩
theorem s5_197_edges : next config 5 s5_197 = [s6_217] := by decide
theorem s5_197_safe : Safe 8 5 s5_197 := by
  apply safe_succ 7 5 s5_197 [s6_217] (by decide) s5_197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_217_safe
def s5_198 : State := ⟨[1,4,96,140], 1481249143206924359618602377232158573003038, 1, 1, 1, 0⟩
theorem s5_198_edges : next config 5 s5_198 = [s6_218] := by decide
theorem s5_198_safe : Safe 8 5 s5_198 := by
  apply safe_succ 7 5 s5_198 [s6_218] (by decide) s5_198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_218_safe
def s5_199 : State := ⟨[1,4,96,140], 1481249143206924359618602377232167162937622, 1, 1, 1, 0⟩
theorem s5_199_edges : next config 5 s5_199 = [s6_219] := by decide
theorem s5_199_safe : Safe 8 5 s5_199 := by
  apply safe_succ 7 5 s5_199 [s6_219] (by decide) s5_199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_219_safe
def s5_200 : State := ⟨[1,4,96,140], 1481249143206924359618639270720305992106262, 1, 1, 1, 0⟩
theorem s5_200_edges : next config 5 s5_200 = [s6_220] := by decide
theorem s5_200_safe : Safe 8 5 s5_200 := by
  apply safe_succ 7 5 s5_200 [s6_220] (by decide) s5_200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_220_safe
def s5_201 : State := ⟨[1,4,96,140], 1481249143207082815943630905907345660903702, 1, 1, 1, 0⟩
theorem s5_201_edges : next config 5 s5_201 = [s6_221] := by decide
theorem s5_201_safe : Safe 8 5 s5_201 := by
  apply safe_succ 7 5 s5_201 [s6_221] (by decide) s5_201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_221_safe
def s5_202 : State := ⟨[1,4,96,145], 44602511244162088326624359380200689865130270, 1, 1, 1, 0⟩
theorem s5_202_edges : next config 5 s5_202 = [s6_554, s6_431, s6_196, s6_404, s6_222] := by decide
theorem s5_202_safe : Safe 8 5 s5_202 := by
  apply safe_succ 7 5 s5_202 [s6_554, s6_431, s6_196, s6_404, s6_222] (by decide) s5_202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_554_safe
  · subst z; exact s6_431_safe
  · subst z; exact s6_196_safe
  · subst z; exact s6_404_safe
  · subst z; exact s6_222_safe
def s5_203 : State := ⟨[1,4,96,145], 44602511244162088326624359380200689865130774, 1, 1, 1, 0⟩
theorem s5_203_edges : next config 5 s5_203 = [s6_223] := by decide
theorem s5_203_safe : Safe 8 5 s5_203 := by
  apply safe_succ 7 5 s5_203 [s6_223] (by decide) s5_203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_223_safe
def s5_204 : State := ⟨[1,4,96,145], 44602511244162088326624359380200689865134358, 2, 2, 1, 0⟩
theorem s5_204_edges : next config 5 s5_204 = [s6_1335, s6_650, s6_995, s6_192, s6_405, s6_224, s6_371] := by decide
theorem s5_204_safe : Safe 8 5 s5_204 := by
  apply safe_succ 7 5 s5_204 [s6_1335, s6_650, s6_995, s6_192, s6_405, s6_224, s6_371] (by decide) s5_204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1335_safe
  · subst z; exact s6_650_safe
  · subst z; exact s6_995_safe
  · subst z; exact s6_192_safe
  · subst z; exact s6_405_safe
  · subst z; exact s6_224_safe
  · subst z; exact s6_371_safe
def s5_205 : State := ⟨[1,4,96,145], 44602511244162088326624359380200698455064854, 1, 1, 1, 0⟩
theorem s5_205_edges : next config 5 s5_205 = [s6_432, s6_225] := by decide
theorem s5_205_safe : Safe 8 5 s5_205 := by
  apply safe_succ 7 5 s5_205 [s6_432, s6_225] (by decide) s5_205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_432_safe
  · subst z; exact s6_225_safe
def s5_206 : State := ⟨[1,4,96,145], 44602511244162088326624396273688837284233494, 1, 1, 1, 0⟩
theorem s5_206_edges : next config 5 s5_206 = [s6_555, s6_433, s6_197, s6_406, s6_226] := by decide
theorem s5_206_safe : Safe 8 5 s5_206 := by
  apply safe_succ 7 5 s5_206 [s6_555, s6_433, s6_197, s6_406, s6_226] (by decide) s5_206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_555_safe
  · subst z; exact s6_433_safe
  · subst z; exact s6_197_safe
  · subst z; exact s6_406_safe
  · subst z; exact s6_226_safe
def s5_207 : State := ⟨[1,4,96,145], 44602511244162088326624654528105869217956118, 2, 2, 1, 0⟩
theorem s5_207_edges : next config 5 s5_207 = [s6_227] := by decide
theorem s5_207_safe : Safe 8 5 s5_207 := by
  apply safe_succ 7 5 s5_207 [s6_227] (by decide) s5_207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_227_safe
def s5_208 : State := ⟨[1,4,96,145], 44602511244162246782949387908875876953030934, 1, 1, 1, 0⟩
theorem s5_208_edges : next config 5 s5_208 = [s6_434, s6_228] := by decide
theorem s5_208_safe : Safe 8 5 s5_208 := by
  apply safe_succ 7 5 s5_208 [s6_434, s6_228] (by decide) s5_208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_434_safe
  · subst z; exact s6_228_safe
def s5_209 : State := ⟨[1,4,96,145], 44602511244163355977224587609602186568335638, 2, 2, 1, 0⟩
theorem s5_209_edges : next config 5 s5_209 = [s6_651, s6_229] := by decide
theorem s5_209_safe : Safe 8 5 s5_209 := by
  apply safe_succ 7 5 s5_209 [s6_651, s6_229] (by decide) s5_209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_651_safe
  · subst z; exact s6_229_safe
def s5_210 : State := ⟨[1,4,96,145], 66902575877958869591233150903634187834687774, 1, 1, 1, 0⟩
theorem s5_210_edges : next config 5 s5_210 = [s6_556, s6_435, s6_198, s6_407, s6_231] := by decide
theorem s5_210_safe : Safe 8 5 s5_210 := by
  apply safe_succ 7 5 s5_210 [s6_556, s6_435, s6_198, s6_407, s6_231] (by decide) s5_210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_556_safe
  · subst z; exact s6_435_safe
  · subst z; exact s6_198_safe
  · subst z; exact s6_407_safe
  · subst z; exact s6_231_safe
def s5_211 : State := ⟨[1,4,96,145], 66902575877958869591233150903634187834688278, 1, 1, 1, 0⟩
theorem s5_211_edges : next config 5 s5_211 = [s6_232] := by decide
theorem s5_211_safe : Safe 8 5 s5_211 := by
  apply safe_succ 7 5 s5_211 [s6_232] (by decide) s5_211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_232_safe
def s5_212 : State := ⟨[1,4,96,145], 66902575877958869591233150903634187834691862, 2, 2, 1, 0⟩
theorem s5_212_edges : next config 5 s5_212 = [s6_1336, s6_652, s6_996, s6_193, s6_408, s6_233, s6_372] := by decide
theorem s5_212_safe : Safe 8 5 s5_212 := by
  apply safe_succ 7 5 s5_212 [s6_1336, s6_652, s6_996, s6_193, s6_408, s6_233, s6_372] (by decide) s5_212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1336_safe
  · subst z; exact s6_652_safe
  · subst z; exact s6_996_safe
  · subst z; exact s6_193_safe
  · subst z; exact s6_408_safe
  · subst z; exact s6_233_safe
  · subst z; exact s6_372_safe
def s5_213 : State := ⟨[1,4,96,145], 66902575877958869591233150903634196424622358, 1, 1, 1, 0⟩
theorem s5_213_edges : next config 5 s5_213 = [s6_436, s6_234] := by decide
theorem s5_213_safe : Safe 8 5 s5_213 := by
  apply safe_succ 7 5 s5_213 [s6_436, s6_234] (by decide) s5_213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_436_safe
  · subst z; exact s6_234_safe
def s5_214 : State := ⟨[1,4,96,145], 66902575877958869591233187797122335253790998, 1, 1, 1, 0⟩
theorem s5_214_edges : next config 5 s5_214 = [s6_557, s6_437, s6_199, s6_409, s6_235] := by decide
theorem s5_214_safe : Safe 8 5 s5_214 := by
  apply safe_succ 7 5 s5_214 [s6_557, s6_437, s6_199, s6_409, s6_235] (by decide) s5_214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_557_safe
  · subst z; exact s6_437_safe
  · subst z; exact s6_199_safe
  · subst z; exact s6_409_safe
  · subst z; exact s6_235_safe
def s5_215 : State := ⟨[1,4,96,145], 66902575877958869591233446051539367187513622, 2, 2, 1, 0⟩
theorem s5_215_edges : next config 5 s5_215 = [s6_236] := by decide
theorem s5_215_safe : Safe 8 5 s5_215 := by
  apply safe_succ 7 5 s5_215 [s6_236] (by decide) s5_215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_236_safe
def s5_216 : State := ⟨[1,4,96,145], 66902575877959028047558179432309374922588438, 1, 1, 1, 0⟩
theorem s5_216_edges : next config 5 s5_216 = [s6_438, s6_237] := by decide
theorem s5_216_safe : Safe 8 5 s5_216 := by
  apply safe_succ 7 5 s5_216 [s6_438, s6_237] (by decide) s5_216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_438_safe
  · subst z; exact s6_237_safe
def s5_217 : State := ⟨[1,4,96,145], 66902575877960137241833379133035684537893142, 2, 2, 1, 0⟩
theorem s5_217_edges : next config 5 s5_217 = [s6_653, s6_238] := by decide
theorem s5_217_safe : Safe 8 5 s5_217 := by
  apply safe_succ 7 5 s5_217 [s6_653, s6_238] (by decide) s5_217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_653_safe
  · subst z; exact s6_238_safe
def s5_218 : State := ⟨[1,4,96,146], 89204682205957176486622722674712276413514014, 1, 1, 1, 0⟩
theorem s5_218_edges : next config 5 s5_218 = [s6_439, s6_240] := by decide
theorem s5_218_safe : Safe 8 5 s5_218 := by
  apply safe_succ 7 5 s5_218 [s6_439, s6_240] (by decide) s5_218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_439_safe
  · subst z; exact s6_240_safe
def s5_219 : State := ⟨[1,4,96,146], 89204682205957176486622722674712276413518102, 2, 2, 1, 0⟩
theorem s5_219_edges : next config 5 s5_219 = [s6_654, s6_241] := by decide
theorem s5_219_safe : Safe 8 5 s5_219 := by
  apply safe_succ 7 5 s5_219 [s6_654, s6_241] (by decide) s5_219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_654_safe
  · subst z; exact s6_241_safe
def s5_220 : State := ⟨[1,4,96,146], 89204682205957176486622759568200423832617238, 1, 1, 1, 0⟩
theorem s5_220_edges : next config 5 s5_220 = [s6_440, s6_242] := by decide
theorem s5_220_safe : Safe 8 5 s5_220 := by
  apply safe_succ 7 5 s5_220 [s6_440, s6_242] (by decide) s5_220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_440_safe
  · subst z; exact s6_242_safe
def s5_221 : State := ⟨[1,4,96,146], 89204682205957176486623017822617455766339862, 2, 2, 1, 0⟩
theorem s5_221_edges : next config 5 s5_221 = [s6_243] := by decide
theorem s5_221_safe : Safe 8 5 s5_221 := by
  apply safe_succ 7 5 s5_221 [s6_243] (by decide) s5_221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_243_safe
def s5_222 : State := ⟨[1,4,96,146], 89204682205958444137222950904113773116719382, 2, 2, 1, 0⟩
theorem s5_222_edges : next config 5 s5_222 = [s6_244] := by decide
theorem s5_222_safe : Safe 8 5 s5_222 := by
  apply safe_succ 7 5 s5_222 [s6_244] (by decide) s5_222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_244_safe
def s5_223 : State := ⟨[1,4,96,146], 89207404464892543994330429671571730559205654, 1, 1, 1, 0⟩
theorem s5_223_edges : next config 5 s5_223 = [s6_441, s6_246] := by decide
theorem s5_223_safe : Safe 8 5 s5_223 := by
  apply safe_succ 7 5 s5_223 [s6_441, s6_246] (by decide) s5_223_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_441_safe
  · subst z; exact s6_246_safe
def s5_224 : State := ⟨[1,4,96,146], 111504066275020115874304587448930910846648606, 1, 1, 1, 0⟩
theorem s5_224_edges : next config 5 s5_224 = [s6_442, s6_247] := by decide
theorem s5_224_safe : Safe 8 5 s5_224 := by
  apply safe_succ 7 5 s5_224 [s6_442, s6_247] (by decide) s5_224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_442_safe
  · subst z; exact s6_247_safe
def s5_225 : State := ⟨[1,4,96,146], 111504066275020115874304587448930910846652694, 2, 2, 1, 0⟩
theorem s5_225_edges : next config 5 s5_225 = [s6_655, s6_248] := by decide
theorem s5_225_safe : Safe 8 5 s5_225 := by
  apply safe_succ 7 5 s5_225 [s6_655, s6_248] (by decide) s5_225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_655_safe
  · subst z; exact s6_248_safe
def s5_226 : State := ⟨[1,4,96,146], 111504066275020115874304624342419058265751830, 1, 1, 1, 0⟩
theorem s5_226_edges : next config 5 s5_226 = [s6_443, s6_249] := by decide
theorem s5_226_safe : Safe 8 5 s5_226 := by
  apply safe_succ 7 5 s5_226 [s6_443, s6_249] (by decide) s5_226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_443_safe
  · subst z; exact s6_249_safe
def s5_227 : State := ⟨[1,4,96,146], 111504066275020115874304882596836090199474454, 2, 2, 1, 0⟩
theorem s5_227_edges : next config 5 s5_227 = [s6_250] := by decide
theorem s5_227_safe : Safe 8 5 s5_227 := by
  apply safe_succ 7 5 s5_227 [s6_250] (by decide) s5_227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_250_safe
def s5_228 : State := ⟨[1,4,96,146], 111504066275021383524904815678332407549853974, 2, 2, 1, 0⟩
theorem s5_228_edges : next config 5 s5_228 = [s6_251] := by decide
theorem s5_228_safe : Safe 8 5 s5_228 := by
  apply safe_succ 7 5 s5_228 [s6_251] (by decide) s5_228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_251_safe
def s5_229 : State := ⟨[1,4,96,146], 1516452374911917057544908692124207412796260630, 2, 2, 1, 0⟩
theorem s5_229_edges : next config 5 s5_229 = [s6_253] := by decide
theorem s5_229_safe : Safe 8 5 s5_229 := by
  apply safe_succ 7 5 s5_229 [s6_253] (by decide) s5_229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_253_safe
def s5_230 : State := ⟨[1,4,96,146], 1538751758980979996932590556898426047229395222, 2, 2, 1, 0⟩
theorem s5_230_edges : next config 5 s5_230 = [s6_254] := by decide
theorem s5_230_safe : Safe 8 5 s5_230 := by
  apply safe_succ 7 5 s5_230 [s6_254] (by decide) s5_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_254_safe
def s5_231 : State := ⟨[1,4,96,161], 2923003275682652937249413218355400943278718259478, 2, 2, 1, 0⟩
theorem s5_231_edges : next config 5 s5_231 = [s6_255, s6_142] := by decide
theorem s5_231_safe : Safe 8 5 s5_231 := by
  apply safe_succ 7 5 s5_231 [s6_255, s6_142] (by decide) s5_231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_255_safe
  · subst z; exact s6_142_safe
def s5_232 : State := ⟨[1,4,96,161], 4384504912332991121611221124144934748071114379542, 2, 2, 1, 0⟩
theorem s5_232_edges : next config 5 s5_232 = [s6_256, s6_143] := by decide
theorem s5_232_safe : Safe 8 5 s5_232 := by
  apply safe_succ 7 5 s5_232 [s6_256, s6_143] (by decide) s5_232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_256_safe
  · subst z; exact s6_143_safe
def s5_233 : State := ⟨[1,4,96,162], 5846006551025023507498659810714716197454119764254, 1, 1, 1, 0⟩
theorem s5_233_edges : next config 5 s5_233 = [s6_444, s6_257] := by decide
theorem s5_233_safe : Safe 8 5 s5_233 := by
  apply safe_succ 7 5 s5_233 [s6_444, s6_257] (by decide) s5_233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_444_safe
  · subst z; exact s6_257_safe
def s5_234 : State := ⟨[1,4,96,162], 5846006551025023507498659810714716197454119764758, 1, 1, 1, 0⟩
theorem s5_234_edges : next config 5 s5_234 = [s6_258] := by decide
theorem s5_234_safe : Safe 8 5 s5_234 := by
  apply safe_succ 7 5 s5_234 [s6_258] (by decide) s5_234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_258_safe
def s5_235 : State := ⟨[1,4,96,162], 5846006551025023507498659810714716197454119768342, 2, 2, 1, 0⟩
theorem s5_235_edges : next config 5 s5_235 = [s6_1337, s6_1419, s6_656, s6_194, s6_392, s6_259, s6_144, s6_164] := by decide
theorem s5_235_safe : Safe 8 5 s5_235 := by
  apply safe_succ 7 5 s5_235 [s6_1337, s6_1419, s6_656, s6_194, s6_392, s6_259, s6_144, s6_164] (by decide) s5_235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1337_safe
  · subst z; exact s6_1419_safe
  · subst z; exact s6_656_safe
  · subst z; exact s6_194_safe
  · subst z; exact s6_392_safe
  · subst z; exact s6_259_safe
  · subst z; exact s6_144_safe
  · subst z; exact s6_164_safe
def s5_236 : State := ⟨[1,4,96,162], 5846006551025023507498659810751609685601538867478, 1, 1, 1, 0⟩
theorem s5_236_edges : next config 5 s5_236 = [s6_445, s6_260] := by decide
theorem s5_236_safe : Safe 8 5 s5_236 := by
  apply safe_succ 7 5 s5_236 [s6_445, s6_260] (by decide) s5_236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_445_safe
  · subst z; exact s6_260_safe
def s5_237 : State := ⟨[1,4,96,162], 5846006551025023507657116135743244872641207664918, 1, 1, 1, 0⟩
theorem s5_237_edges : next config 5 s5_237 = [s6_446, s6_261] := by decide
theorem s5_237_safe : Safe 8 5 s5_237 := by
  apply safe_succ 7 5 s5_237 [s6_446, s6_261] (by decide) s5_237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_446_safe
  · subst z; exact s6_261_safe
def s5_238 : State := ⟨[1,4,96,162], 5846006551025023508766310410942945598950822969622, 2, 2, 1, 0⟩
theorem s5_238_edges : next config 5 s5_238 = [s6_262] := by decide
theorem s5_238_safe : Safe 8 5 s5_238 := by
  apply safe_succ 7 5 s5_238 [s6_262] (by decide) s5_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_262_safe
def s5_239 : State := ⟨[1,4,96,162], 5846006553747282442866167518421713056908265455894, 1, 1, 1, 0⟩
theorem s5_239_edges : next config 5 s5_239 = [s6_447, s6_264] := by decide
theorem s5_239_safe : Safe 8 5 s5_239 := by
  apply safe_succ 7 5 s5_239 [s6_447, s6_264] (by decide) s5_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_447_safe
  · subst z; exact s6_264_safe
def s5_240 : State := ⟨[1,4,96,162], 7307508186994796958018590789577500787382979461406, 1, 1, 1, 0⟩
theorem s5_240_edges : next config 5 s5_240 = [s6_448, s6_265] := by decide
theorem s5_240_safe : Safe 8 5 s5_240 := by
  apply safe_succ 7 5 s5_240 [s6_448, s6_265] (by decide) s5_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_448_safe
  · subst z; exact s6_265_safe
def s5_241 : State := ⟨[1,4,96,162], 7307508186994796958018590789577500787382979461910, 1, 1, 1, 0⟩
theorem s5_241_edges : next config 5 s5_241 = [s6_266] := by decide
theorem s5_241_safe : Safe 8 5 s5_241 := by
  apply safe_succ 7 5 s5_241 [s6_266] (by decide) s5_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_266_safe
def s5_242 : State := ⟨[1,4,96,162], 7307508186994796958018590789577500787382979465494, 2, 2, 1, 0⟩
theorem s5_242_edges : next config 5 s5_242 = [s6_1338, s6_1420, s6_657, s6_195, s6_393, s6_267, s6_145, s6_165] := by decide
theorem s5_242_safe : Safe 8 5 s5_242 := by
  apply safe_succ 7 5 s5_242 [s6_1338, s6_1420, s6_657, s6_195, s6_393, s6_267, s6_145, s6_165] (by decide) s5_242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1338_safe
  · subst z; exact s6_1420_safe
  · subst z; exact s6_657_safe
  · subst z; exact s6_195_safe
  · subst z; exact s6_393_safe
  · subst z; exact s6_267_safe
  · subst z; exact s6_145_safe
  · subst z; exact s6_165_safe
def s5_243 : State := ⟨[1,4,96,162], 7307508186994796958018590789614394275530398564630, 1, 1, 1, 0⟩
theorem s5_243_edges : next config 5 s5_243 = [s6_449, s6_268] := by decide
theorem s5_243_safe : Safe 8 5 s5_243 := by
  apply safe_succ 7 5 s5_243 [s6_449, s6_268] (by decide) s5_243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_449_safe
  · subst z; exact s6_268_safe
def s5_244 : State := ⟨[1,4,96,162], 7307508186994796958177047114606029462570067362070, 1, 1, 1, 0⟩
theorem s5_244_edges : next config 5 s5_244 = [s6_450, s6_269] := by decide
theorem s5_244_safe : Safe 8 5 s5_244 := by
  apply safe_succ 7 5 s5_244 [s6_450, s6_269] (by decide) s5_244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_450_safe
  · subst z; exact s6_269_safe
def s5_245 : State := ⟨[1,4,96,162], 7307508186994796959286241389805730188879682666774, 2, 2, 1, 0⟩
theorem s5_245_edges : next config 5 s5_245 = [s6_270] := by decide
theorem s5_245_safe : Safe 8 5 s5_245 := by
  apply safe_succ 7 5 s5_245 [s6_270] (by decide) s5_245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_270_safe
def s5_246 : State := ⟨[1,4,96,162], 17538019649672246853128138472444980354701580108054, 1, 1, 1, 0⟩
theorem s5_246_edges : next config 5 s5_246 = [s6_451, s6_272] := by decide
theorem s5_246_safe : Safe 8 5 s5_246 := by
  apply safe_succ 7 5 s5_246 [s6_451, s6_272] (by decide) s5_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_451_safe
  · subst z; exact s6_272_safe
def s5_247 : State := ⟨[1,4,96,162], 18999521285642020303648069451307764944630439805206, 1, 1, 1, 0⟩
theorem s5_247_edges : next config 5 s5_247 = [s6_452, s6_273] := by decide
theorem s5_247_safe : Safe 8 5 s5_247 := by
  apply safe_succ 7 5 s5_247 [s6_452, s6_273] (by decide) s5_247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_452_safe
  · subst z; exact s6_273_safe
def s5_248 : State := ⟨[1,4,96,163], 11692013100348635180313399141579848276086439870742, 1, 1, 1, 0⟩
theorem s5_248_edges : next config 5 s5_248 = [s6_453, s6_274, s6_150] := by decide
theorem s5_248_safe : Safe 8 5 s5_248 := by
  apply safe_succ 7 5 s5_248 [s6_453, s6_274, s6_150] (by decide) s5_248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_453_safe
  · subst z; exact s6_274_safe
  · subst z; exact s6_150_safe
def s5_249 : State := ⟨[1,4,96,163], 11692013101709764647997152995433346705804922781982, 1, 1, 1, 0⟩
theorem s5_249_edges : next config 5 s5_249 = [s6_454, s6_275, s6_151] := by decide
theorem s5_249_safe : Safe 8 5 s5_249 := by
  apply safe_succ 7 5 s5_249 [s6_454, s6_275, s6_151] (by decide) s5_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_454_safe
  · subst z; exact s6_275_safe
  · subst z; exact s6_151_safe
def s5_250 : State := ⟨[1,4,96,163], 13153514736318408630833330120442632866006709633310, 1, 1, 1, 0⟩
theorem s5_250_edges : next config 5 s5_250 = [s6_455, s6_276, s6_152] := by decide
theorem s5_250_safe : Safe 8 5 s5_250 := by
  apply safe_succ 7 5 s5_250 [s6_455, s6_276, s6_152] (by decide) s5_250_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_455_safe
  · subst z; exact s6_276_safe
  · subst z; exact s6_152_safe
def s5_251 : State := ⟨[1,4,96,163], 14615016373649311549037014953158915885671232110870, 1, 1, 1, 0⟩
theorem s5_251_edges : next config 5 s5_251 = [s6_456, s6_277, s6_153] := by decide
theorem s5_251_safe : Safe 8 5 s5_251 := by
  apply safe_succ 7 5 s5_251 [s6_456, s6_277, s6_153] (by decide) s5_251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_456_safe
  · subst z; exact s6_277_safe
  · subst z; exact s6_153_safe
def s5_252 : State := ⟨[1,4,96,171], 3004847366356079505862985567325307720176018307219734, 0, 0, 1, 0⟩
theorem s5_252_edges : next config 5 s5_252 = [s6_278] := by decide
theorem s5_252_safe : Safe 8 5 s5_252 := by
  apply safe_succ 7 5 s5_252 [s6_278] (by decide) s5_252_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_278_safe
def s5_253 : State := ⟨[1,4,96,171], 3004847366356760070596827444252234469390881843642646, 0, 0, 1, 0⟩
theorem s5_253_edges : next config 5 s5_253 = [s6_279] := by decide
theorem s5_253_safe : Safe 8 5 s5_253 := by
  apply safe_succ 7 5 s5_253 [s6_279] (by decide) s5_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_279_safe
def s5_254 : State := ⟨[1,4,96,171], 3007770369628019052764025429283033289355876026614038, 0, 0, 1, 0⟩
theorem s5_254_edges : next config 5 s5_254 = [s6_280] := by decide
theorem s5_254_safe : Safe 8 5 s5_254 := by
  apply safe_succ 7 5 s5_254 [s6_280] (by decide) s5_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_280_safe
def s5_255 : State := ⟨[1,4,96,171], 3009231871264669390948387237188822823160668422734102, 0, 0, 1, 0⟩
theorem s5_255_edges : next config 5 s5_255 = [s6_281] := by decide
theorem s5_255_safe : Safe 8 5 s5_255 := by
  apply safe_succ 7 5 s5_255 [s6_281] (by decide) s5_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_281_safe
def s5_256 : State := ⟨[1,4,96,171], 3010693372903361423334274675875392604610051428122902, 0, 0, 1, 0⟩
theorem s5_256_edges : next config 5 s5_256 = [s6_282] := by decide
theorem s5_256_safe : Safe 8 5 s5_256 := by
  apply safe_succ 7 5 s5_256 [s6_282] (by decide) s5_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_282_safe
def s5_257 : State := ⟨[1,4,96,171], 3012154874539331196784794606854255389199980287820054, 0, 0, 1, 0⟩
theorem s5_257_edges : next config 5 s5_257 = [s6_283] := by decide
theorem s5_257_safe : Safe 8 5 s5_257 := by
  apply safe_succ 7 5 s5_257 [s6_283] (by decide) s5_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_283_safe
def s5_258 : State := ⟨[1,4,96,171], 4495579036431558788229218465915136152580478891786518, 0, 0, 1, 0⟩
theorem s5_258_edges : next config 5 s5_258 = [s6_284] := by decide
theorem s5_258_safe : Safe 8 5 s5_258 := by
  apply safe_succ 7 5 s5_258 [s6_284] (by decide) s5_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_284_safe
def s5_259 : State := ⟨[1,4,96,171], 4497040538067528561679738396893998937170407751483670, 0, 0, 1, 0⟩
theorem s5_259_edges : next config 5 s5_259 = [s6_285] := by decide
theorem s5_259_safe : Safe 8 5 s5_259 := by
  apply safe_succ 7 5 s5_259 [s6_285] (by decide) s5_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_285_safe
def s5_260 : State := ⟨[1,4,96,176], 95780971326419139128294312505056038334508659959202078, 1, 1, 1, 0⟩
theorem s5_260_edges : next config 5 s5_260 = [s6_457, s6_286] := by decide
theorem s5_260_safe : Safe 8 5 s5_260 := by
  apply safe_succ 7 5 s5_260 [s6_457, s6_286] (by decide) s5_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_457_safe
  · subst z; exact s6_286_safe
def s5_261 : State := ⟨[1,4,96,176], 95780971326419139128294312505056038334508659959206166, 2, 2, 1, 0⟩
theorem s5_261_edges : next config 5 s5_261 = [s6_660, s6_287] := by decide
theorem s5_261_safe : Safe 8 5 s5_261 := by
  apply safe_succ 7 5 s5_261 [s6_660, s6_287] (by decide) s5_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_660_safe
  · subst z; exact s6_287_safe
def s5_262 : State := ⟨[1,4,96,176], 95780971326419139128294312505056075227996807378305302, 1, 1, 1, 0⟩
theorem s5_262_edges : next config 5 s5_262 = [s6_458, s6_288] := by decide
theorem s5_262_safe : Safe 8 5 s5_262 := by
  apply safe_succ 7 5 s5_262 [s6_458, s6_288] (by decide) s5_262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_458_safe
  · subst z; exact s6_288_safe
def s5_263 : State := ⟨[1,4,96,176], 95780971326419139128295580155656266563910156662407446, 2, 2, 1, 0⟩
theorem s5_263_edges : next config 5 s5_263 = [s6_289] := by decide
theorem s5_263_safe : Safe 8 5 s5_263 := by
  apply safe_succ 7 5 s5_263 [s6_289] (by decide) s5_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_289_safe
def s5_264 : State := ⟨[1,4,96,176], 95782432805755724832681893048353036344879954385764638, 1, 1, 1, 0⟩
theorem s5_264_edges : next config 5 s5_264 = [s6_459, s6_291] := by decide
theorem s5_264_safe : Safe 8 5 s5_264 := by
  apply safe_succ 7 5 s5_264 [s6_459, s6_291] (by decide) s5_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_459_safe
  · subst z; exact s6_291_safe
def s5_265 : State := ⟨[1,4,96,176], 95782432805755724832681893048353036344879954385768726, 2, 2, 1, 0⟩
theorem s5_265_edges : next config 5 s5_265 = [s6_661, s6_292] := by decide
theorem s5_265_safe : Safe 8 5 s5_265 := by
  apply safe_succ 7 5 s5_265 [s6_661, s6_292] (by decide) s5_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_661_safe
  · subst z; exact s6_292_safe
def s5_266 : State := ⟨[1,4,96,176], 95782432805755724832681893048353073238368101804867862, 1, 1, 1, 0⟩
theorem s5_266_edges : next config 5 s5_266 = [s6_460, s6_293] := by decide
theorem s5_266_safe : Safe 8 5 s5_266 := by
  apply safe_succ 7 5 s5_266 [s6_460, s6_293] (by decide) s5_266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_460_safe
  · subst z; exact s6_293_safe
def s5_267 : State := ⟨[1,4,96,176], 95782432805755724832683160698953264574281451088970006, 2, 2, 1, 0⟩
theorem s5_267_edges : next config 5 s5_267 = [s6_294] := by decide
theorem s5_267_safe : Safe 8 5 s5_267 := by
  apply safe_succ 7 5 s5_267 [s6_294] (by decide) s5_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_294_safe
def s5_268 : State := ⟨[1,4,96,193], 12554203470773361528692425947257376385127545792894922199318, 2, 2, 1, 0⟩
theorem s5_268_edges : next config 5 s5_268 = [s6_304] := by decide
theorem s5_268_safe : Safe 8 5 s5_268 := by
  apply safe_succ 7 5 s5_268 [s6_304] (by decide) s5_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_304_safe
def s5_269 : State := ⟨[1,4,96,193], 12554203470773361528692425948525026985355775194391625400598, 2, 2, 1, 0⟩
theorem s5_269_edges : next config 5 s5_269 = [s6_305] := by decide
theorem s5_269_safe : Safe 8 5 s5_269 := by
  apply safe_succ 7 5 s5_269 [s6_305] (by decide) s5_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_305_safe
def s5_270 : State := ⟨[1,4,96,193], 18831305206160042291847650636623165874303152022495420289302, 2, 2, 1, 0⟩
theorem s5_270_edges : next config 5 s5_270 = [s6_307] := by decide
theorem s5_270_safe : Safe 8 5 s5_270 := by
  apply safe_succ 7 5 s5_270 [s6_307] (by decide) s5_270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_307_safe
def s5_271 : State := ⟨[1,4,96,193], 18831305206160042291847650637890816474531381423992123490582, 2, 2, 1, 0⟩
theorem s5_271_edges : next config 5 s5_271 = [s6_308] := by decide
theorem s5_271_safe : Safe 8 5 s5_271 := by
  apply safe_succ 7 5 s5_271 [s6_308] (by decide) s5_271_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_308_safe
def s5_272 : State := ⟨[1,4,96,194], 25108406941546723057044569527514586144259005896686527648022, 2, 2, 1, 0⟩
theorem s5_272_edges : next config 5 s5_272 = [s6_379, s6_310, s6_373, s6_138, s6_168] := by decide
theorem s5_272_safe : Safe 8 5 s5_272 := by
  apply safe_succ 7 5 s5_272 [s6_379, s6_310, s6_373, s6_138, s6_168] (by decide) s5_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_379_safe
  · subst z; exact s6_310_safe
  · subst z; exact s6_373_safe
  · subst z; exact s6_138_safe
  · subst z; exact s6_168_safe
def s5_273 : State := ⟨[1,4,96,194], 25108406941546723057044569528782236744487235298183230849302, 2, 2, 1, 0⟩
theorem s5_273_edges : next config 5 s5_273 = [s6_311] := by decide
theorem s5_273_safe : Safe 8 5 s5_273 := by
  apply safe_succ 7 5 s5_273 [s6_311] (by decide) s5_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_311_safe
def s5_274 : State := ⟨[1,4,96,194], 31385508676933403819519229483038498706507862911423489315094, 2, 2, 1, 0⟩
theorem s5_274_edges : next config 5 s5_274 = [s6_380, s6_313, s6_374, s6_139, s6_169] := by decide
theorem s5_274_safe : Safe 8 5 s5_274 := by
  apply safe_succ 7 5 s5_274 [s6_380, s6_313, s6_374, s6_139, s6_169] (by decide) s5_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_380_safe
  · subst z; exact s6_313_safe
  · subst z; exact s6_374_safe
  · subst z; exact s6_139_safe
  · subst z; exact s6_169_safe
def s5_275 : State := ⟨[1,4,96,194], 31385508676933403819519229484306149306736092312920192516374, 2, 2, 1, 0⟩
theorem s5_275_edges : next config 5 s5_275 = [s6_314] := by decide
theorem s5_275_safe : Safe 8 5 s5_275 := by
  apply safe_succ 7 5 s5_275 [s6_314] (by decide) s5_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_314_safe
def s5_276 : State := ⟨[1,4,96,208], 411376139330301510561043381120235249553845680766732430659883286, 2, 2, 1, 0⟩
theorem s5_276_edges : next config 5 s5_276 = [s6_316, s6_170] := by decide
theorem s5_276_safe : Safe 8 5 s5_276 := by
  apply safe_succ 7 5 s5_276 [s6_316, s6_170] (by decide) s5_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_316_safe
  · subst z; exact s6_170_safe
def s5_277 : State := ⟨[1,4,96,208], 411382416432036897219506471711127834078726064849528533188415766, 2, 2, 1, 0⟩
theorem s5_277_edges : next config 5 s5_277 = [s6_318, s6_171] := by decide
theorem s5_277_safe : Safe 8 5 s5_277 := by
  apply safe_succ 7 5 s5_277 [s6_318, s6_171] (by decide) s5_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_318_safe
  · subst z; exact s6_171_safe
def s5_278 : State := ⟨[1,4,96,214], 26328072917139296675995959295829525137268682542261485226374005014, 0, 0, 1, 0⟩
theorem s5_278_edges : next config 5 s5_278 = [s6_320] := by decide
theorem s5_278_safe : Safe 8 5 s5_278 := by
  apply safe_succ 7 5 s5_278 [s6_320] (by decide) s5_278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_320_safe
def s5_279 : State := ⟨[1,4,96,214], 26328072917139296676018258679898588076656364407035703860807139606, 0, 0, 1, 0⟩
theorem s5_279_edges : next config 5 s5_279 = [s6_321] := by decide
theorem s5_279_safe : Safe 8 5 s5_279 := by
  apply safe_succ 7 5 s5_279 [s6_321] (by decide) s5_279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_321_safe
def s5_280 : State := ⟨[1,4,96,214], 27973577474460502716723680785680915761193132438445569953339867414, 0, 0, 1, 0⟩
theorem s5_280_edges : next config 5 s5_280 = [s6_322] := by decide
theorem s5_280_safe : Safe 8 5 s5_280 := by
  apply safe_succ 7 5 s5_280 [s6_322] (by decide) s5_280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_322_safe
def s5_281 : State := ⟨[1,4,96,214], 27973577474460502716745980169749978700580814303219788587773002006, 0, 0, 1, 0⟩
theorem s5_281_edges : next config 5 s5_281 = [s6_323] := by decide
theorem s5_281_safe : Safe 8 5 s5_281 := by
  apply safe_succ 7 5 s5_281 [s6_323] (by decide) s5_281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_323_safe
def s5_282 : State := ⟨[1,4,96,214], 27973602582867444263357533148044486099292653974776754363453997334, 0, 0, 1, 0⟩
theorem s5_282_edges : next config 5 s5_282 = [s6_324] := by decide
theorem s5_282_safe : Safe 8 5 s5_282 := by
  apply safe_succ 7 5 s5_282 [s6_324] (by decide) s5_282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_324_safe
def s5_283 : State := ⟨[1,4,96,214], 27973608859969179650038295622704441623205216223633769100415664406, 0, 0, 1, 0⟩
theorem s5_283_edges : next config 5 s5_283 = [s6_325] := by decide
theorem s5_283_safe : Safe 8 5 s5_283 := by
  apply safe_succ 7 5 s5_283 [s6_325] (by decide) s5_283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_325_safe
def s5_284 : State := ⟨[1,4,96,214], 28384953613790804227195519484595193834260355396537590107586232598, 0, 0, 1, 0⟩
theorem s5_284_edges : next config 5 s5_284 = [s6_326] := by decide
theorem s5_284_safe : Safe 8 5 s5_284 := by
  apply safe_succ 7 5 s5_284 [s6_326] (by decide) s5_284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_326_safe
def s5_285 : State := ⟨[1,4,96,214], 28384959890892539613853982575186086418785235780620386210114765078, 0, 0, 1, 0⟩
theorem s5_285_edges : next config 5 s5_285 = [s6_327] := by decide
theorem s5_285_safe : Safe 8 5 s5_285 := by
  apply safe_succ 7 5 s5_285 [s6_327] (by decide) s5_285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_327_safe
def s5_286 : State := ⟨[1,4,96,225], 53919893334301279589334030175060108448116332398003979866174073671958, 2, 2, 1, 0⟩
theorem s5_286_edges : next config 5 s5_286 = [s6_328] := by decide
theorem s5_286_safe : Safe 8 5 s5_286 := by
  apply safe_succ 7 5 s5_286 [s6_328] (by decide) s5_286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_328_safe
def s5_287 : State := ⟨[1,4,96,225], 80879840001451919384001045261399174387911599893617803132414147498262, 2, 2, 1, 0⟩
theorem s5_287_edges : next config 5 s5_287 = [s6_329] := by decide
theorem s5_287_safe : Safe 8 5 s5_287 := by
  apply safe_succ 7 5 s5_287 [s6_329] (by decide) s5_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_329_safe
def s5_288 : State := ⟨[1,4,96,228], 431359146674410236714672241398098891015929492802059239105669372117278, 1, 1, 1, 0⟩
theorem s5_288_edges : next config 5 s5_288 = [s6_330] := by decide
theorem s5_288_safe : Safe 8 5 s5_288 := by
  apply safe_succ 7 5 s5_288 [s6_330] (by decide) s5_288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_330_safe
def s5_289 : State := ⟨[1,4,96,228], 431359146674410236714672241398098891015929492802096132593816791220502, 1, 1, 1, 0⟩
theorem s5_289_edges : next config 5 s5_289 = [s6_331] := by decide
theorem s5_289_safe : Safe 8 5 s5_289 := by
  apply safe_succ 7 5 s5_289 [s6_331] (by decide) s5_289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_331_safe
def s5_290 : State := ⟨[1,4,96,228], 458319093341560876509339256479674003818831621809185817867864690983198, 1, 1, 1, 0⟩
theorem s5_290_edges : next config 5 s5_290 = [s6_332] := by decide
theorem s5_290_safe : Safe 8 5 s5_290 := by
  apply safe_succ 7 5 s5_290 [s6_332] (by decide) s5_290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_332_safe
def s5_291 : State := ⟨[1,4,96,228], 458319093341560876509339256479674003818831621809222711356012110086422, 1, 1, 1, 0⟩
theorem s5_291_edges : next config 5 s5_291 = [s6_333] := by decide
theorem s5_291_safe : Safe 8 5 s5_291 := by
  apply safe_succ 7 5 s5_291 [s6_333] (by decide) s5_291_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_333_safe
def s5_292 : State := ⟨[1,4,96,240], 1766847064778384329583297500765219601308381520183780672479943666115350806, 2, 2, 1, 0⟩
theorem s5_292_edges : next config 5 s5_292 = [s6_338] := by decide
theorem s5_292_safe : Safe 8 5 s5_292 := by
  apply safe_succ 7 5 s5_292 [s6_338] (by decide) s5_292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_338_safe
def s5_293 : State := ⟨[1,4,96,240], 1766874024725051480223092167758005875740524534186667494779776408219619606, 2, 2, 1, 0⟩
theorem s5_293_edges : next config 5 s5_293 = [s6_339] := by decide
theorem s5_293_safe : Safe 8 5 s5_293 := by
  apply safe_succ 7 5 s5_293 [s6_339] (by decide) s5_293_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_339_safe
def s5_294 : State := ⟨[1,4,97,129], 1020847101000499877951363579153941074198, 2, 2, 1, 0⟩
theorem s5_294_edges : next config 5 s5_294 = [s6_192] := by decide
theorem s5_294_safe : Safe 8 5 s5_294 := by
  apply safe_succ 7 5 s5_294 [s6_192] (by decide) s5_294_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_192_safe
def s5_295 : State := ⟨[1,4,97,130], 1701411834842376804878112794017477497110, 2, 2, 1, 0⟩
theorem s5_295_edges : next config 5 s5_295 = [s6_194] := by decide
theorem s5_295_safe : Safe 8 5 s5_295 := by
  apply safe_succ 7 5 s5_295 [s6_194] (by decide) s5_295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_194_safe
def s5_296 : State := ⟨[1,4,97,132], 5784800237893638366438608083198696034582, 2, 2, 1, 0⟩
theorem s5_296_edges : next config 5 s5_296 = [] := by decide
theorem s5_296_safe : Safe 8 5 s5_296 := by
  apply safe_succ 7 5 s5_296 [] (by decide) s5_296_edges
  simp
def s5_297 : State := ⟨[1,4,97,136], 87452568298918869597648513866823066784022, 2, 2, 1, 0⟩
theorem s5_297_edges : next config 5 s5_297 = [] := by decide
theorem s5_297_safe : Safe 8 5 s5_297 := by
  apply safe_succ 7 5 s5_297 [] (by decide) s5_297_edges
  simp
def s5_298 : State := ⟨[1,4,97,136], 1481249143207082815943630905907345660903702, 2, 2, 1, 0⟩
theorem s5_298_edges : next config 5 s5_298 = [] := by decide
theorem s5_298_safe : Safe 8 5 s5_298 := by
  apply safe_succ 7 5 s5_298 [] (by decide) s5_298_edges
  simp
def s5_299 : State := ⟨[1,4,97,140], 1394136857275322569297007006404812998775062, 2, 2, 1, 0⟩
theorem s5_299_edges : next config 5 s5_299 = [] := by decide
theorem s5_299_safe : Safe 8 5 s5_299 := by
  apply safe_succ 7 5 s5_299 [] (by decide) s5_299_edges
  simp
def s5_300 : State := ⟨[1,4,97,144], 22301085480897781764486742887012651910631702, 2, 2, 1, 0⟩
theorem s5_300_edges : next config 5 s5_300 = [s6_193] := by decide
theorem s5_300_safe : Safe 8 5 s5_300 := by
  apply safe_succ 7 5 s5_300 [s6_193] (by decide) s5_300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_193_safe
def s5_301 : State := ⟨[1,4,97,145], 44601830679428404906022461159661013416739094, 1, 1, 1, 0⟩
theorem s5_301_edges : next config 5 s5_301 = [s6_461] := by decide
theorem s5_301_safe : Safe 8 5 s5_301 := by
  apply safe_succ 7 5 s5_301 [s6_461] (by decide) s5_301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_461_safe
def s5_302 : State := ⟨[1,4,97,160], 1461501637671185285362307783740897383946337194262, 2, 2, 1, 0⟩
theorem s5_302_edges : next config 5 s5_302 = [s6_195] := by decide
theorem s5_302_safe : Safe 8 5 s5_302 := by
  apply safe_succ 7 5 s5_302 [s6_195] (by decide) s5_302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_195_safe
def s5_303 : State := ⟨[1,4,97,192], 6277101735386680764176071790366289367126969808754439164182, 2, 2, 1, 0⟩
theorem s5_303_edges : next config 5 s5_303 = [] := by decide
theorem s5_303_safe : Safe 8 5 s5_303 := by
  apply safe_succ 7 5 s5_303 [] (by decide) s5_303_edges
  simp
def s5_304 : State := ⟨[1,4,97,224], 26959946667150639794667015087359913040795767373565186845394014900502, 2, 2, 1, 0⟩
theorem s5_304_edges : next config 5 s5_304 = [] := by decide
theorem s5_304_safe : Safe 8 5 s5_304 := by
  apply safe_succ 7 5 s5_304 [] (by decide) s5_304_edges
  simp
def s5_305 : State := ⟨[1,4,97,225], 53919893334301279589334030174379543714432911796105759326497625149718, 2, 2, 1, 0⟩
theorem s5_305_edges : next config 5 s5_305 = [] := by decide
theorem s5_305_safe : Safe 8 5 s5_305 := by
  apply safe_succ 7 5 s5_305 [] (by decide) s5_305_edges
  simp
def s5_306 : State := ⟨[1,4,100,129], 1020847102109694153151064305463556374814, 1, 1, 1, 0⟩
theorem s5_306_edges : next config 5 s5_306 = [s6_196] := by decide
theorem s5_306_safe : Safe 8 5 s5_306 := by
  apply safe_succ 7 5 s5_306 [s6_196] (by decide) s5_306_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_196_safe
def s5_307 : State := ⟨[1,4,100,129], 1020847102109694153187957793610975478038, 1, 1, 1, 0⟩
theorem s5_307_edges : next config 5 s5_307 = [s6_197] := by decide
theorem s5_307_safe : Safe 8 5 s5_307 := by
  apply safe_succ 7 5 s5_307 [s6_197] (by decide) s5_307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_197_safe
def s5_308 : State := ⟨[1,4,100,130], 1701411835951571080077813520327092797726, 1, 1, 1, 0⟩
theorem s5_308_edges : next config 5 s5_308 = [] := by decide
theorem s5_308_safe : Safe 8 5 s5_308 := by
  apply safe_succ 7 5 s5_308 [] (by decide) s5_308_edges
  simp
def s5_309 : State := ⟨[1,4,100,130], 1701411835951571080114707008474511900950, 1, 1, 1, 0⟩
theorem s5_309_edges : next config 5 s5_309 = [] := by decide
theorem s5_309_safe : Safe 8 5 s5_309 := by
  apply safe_succ 7 5 s5_309 [] (by decide) s5_309_edges
  simp
def s5_310 : State := ⟨[1,4,100,130], 4423670771319078787784810379781238489366, 1, 1, 1, 0⟩
theorem s5_310_edges : next config 5 s5_310 = [] := by decide
theorem s5_310_safe : Safe 8 5 s5_310 := by
  apply safe_succ 7 5 s5_310 [] (by decide) s5_310_edges
  simp
def s5_311 : State := ⟨[1,4,100,131], 3062541303635324933931311950054165643550, 1, 1, 1, 0⟩
theorem s5_311_edges : next config 5 s5_311 = [] := by decide
theorem s5_311_safe : Safe 8 5 s5_311 := by
  apply safe_succ 7 5 s5_311 [] (by decide) s5_311_edges
  simp
def s5_312 : State := ⟨[1,4,100,132], 5784800239002832641638308809508311335198, 1, 1, 1, 0⟩
theorem s5_312_edges : next config 5 s5_312 = [] := by decide
theorem s5_312_safe : Safe 8 5 s5_312 := by
  apply safe_succ 7 5 s5_312 [] (by decide) s5_312_edges
  simp
def s5_313 : State := ⟨[1,4,100,132], 5784800239002832641675202297655730438422, 1, 1, 1, 0⟩
theorem s5_313_edges : next config 5 s5_313 = [] := by decide
theorem s5_313_safe : Safe 8 5 s5_313 := by
  apply safe_succ 7 5 s5_313 [] (by decide) s5_313_edges
  simp
def s5_314 : State := ⟨[1,4,100,136], 87452568300028063872848214593132682084638, 1, 1, 1, 0⟩
theorem s5_314_edges : next config 5 s5_314 = [] := by decide
theorem s5_314_safe : Safe 8 5 s5_314 := by
  apply safe_succ 7 5 s5_314 [] (by decide) s5_314_edges
  simp
def s5_315 : State := ⟨[1,4,100,136], 87452568300028063872885108081280101187862, 1, 1, 1, 0⟩
theorem s5_315_edges : next config 5 s5_315 = [] := by decide
theorem s5_315_safe : Safe 8 5 s5_315 := by
  apply safe_succ 7 5 s5_315 [] (by decide) s5_315_edges
  simp
def s5_316 : State := ⟨[1,4,100,144], 22301085480898890958761942587738961525932318, 1, 1, 1, 0⟩
theorem s5_316_edges : next config 5 s5_316 = [s6_198] := by decide
theorem s5_316_safe : Safe 8 5 s5_316 := by
  apply safe_succ 7 5 s5_316 [s6_198] (by decide) s5_316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_198_safe
def s5_317 : State := ⟨[1,4,100,144], 22301085480898890958761979481227108945035542, 1, 1, 1, 0⟩
theorem s5_317_edges : next config 5 s5_317 = [s6_199] := by decide
theorem s5_317_safe : Safe 8 5 s5_317 := by
  apply safe_succ 7 5 s5_317 [s6_199] (by decide) s5_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_199_safe
def s5_318 : State := ⟨[1,4,100,145], 44601830679429514100297660860387323032043798, 1, 1, 1, 0⟩
theorem s5_318_edges : next config 5 s5_318 = [s6_662] := by decide
theorem s5_318_safe : Safe 8 5 s5_318 := by
  apply safe_succ 7 5 s5_318 [s6_662] (by decide) s5_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_662_safe
def s5_319 : State := ⟨[1,4,100,160], 1461501637671185286471502058940598110255952494878, 1, 1, 1, 0⟩
theorem s5_319_edges : next config 5 s5_319 = [] := by decide
theorem s5_319_safe : Safe 8 5 s5_319 := by
  apply safe_succ 7 5 s5_319 [] (by decide) s5_319_edges
  simp
def s5_320 : State := ⟨[1,4,100,160], 1461501637671185286471502058977491598403371598102, 1, 1, 1, 0⟩
theorem s5_320_edges : next config 5 s5_320 = [] := by decide
theorem s5_320_safe : Safe 8 5 s5_320 := by
  apply safe_succ 7 5 s5_320 [] (by decide) s5_320_edges
  simp
def s5_321 : State := ⟨[1,4,100,192], 6277101735386680764176071791475483642326670535064054464798, 1, 1, 1, 0⟩
theorem s5_321_edges : next config 5 s5_321 = [] := by decide
theorem s5_321_safe : Safe 8 5 s5_321 := by
  apply safe_succ 7 5 s5_321 [] (by decide) s5_321_edges
  simp
def s5_322 : State := ⟨[1,4,100,192], 6277101735386680764176071791475483642363564023211473568022, 1, 1, 1, 0⟩
theorem s5_322_edges : next config 5 s5_322 = [] := by decide
theorem s5_322_safe : Safe 8 5 s5_322 := by
  apply safe_succ 7 5 s5_322 [] (by decide) s5_322_edges
  simp
def s5_323 : State := ⟨[1,4,100,192], 18831305206160042291847650637890816474531381423992123490582, 1, 1, 1, 0⟩
theorem s5_323_edges : next config 5 s5_323 = [] := by decide
theorem s5_323_safe : Safe 8 5 s5_323 := by
  apply safe_succ 7 5 s5_323 [] (by decide) s5_323_edges
  simp
def s5_324 : State := ⟨[1,4,100,193], 12554203470773361528011861214683150058465919467675508080918, 1, 1, 1, 0⟩
theorem s5_324_edges : next config 5 s5_324 = [] := by decide
theorem s5_324_safe : Safe 8 5 s5_324 := by
  apply safe_succ 7 5 s5_324 [] (by decide) s5_324_edges
  simp
def s5_325 : State := ⟨[1,4,100,224], 26959946667150639794667015087359913041904961648764887571703630201118, 1, 1, 1, 0⟩
theorem s5_325_edges : next config 5 s5_325 = [] := by decide
theorem s5_325_safe : Safe 8 5 s5_325 := by
  apply safe_succ 7 5 s5_325 [] (by decide) s5_325_edges
  simp
def s5_326 : State := ⟨[1,4,100,224], 26959946667150639794667015087359913041904961648801781059851049304342, 1, 1, 1, 0⟩
theorem s5_326_edges : next config 5 s5_326 = [] := by decide
theorem s5_326_safe : Safe 8 5 s5_326 := by
  apply safe_succ 7 5 s5_326 [] (by decide) s5_326_edges
  simp
def s5_327 : State := ⟨[1,4,100,228], 431359146674410236714672241392654373146462127986873474788257783939358, 1, 1, 1, 0⟩
theorem s5_327_edges : next config 5 s5_327 = [] := by decide
theorem s5_327_safe : Safe 8 5 s5_327 := by
  apply safe_succ 7 5 s5_327 [] (by decide) s5_327_edges
  simp
def s5_328 : State := ⟨[1,4,100,228], 431359146674410236714672241392654373146462127986910368276405203042582, 1, 1, 1, 0⟩
theorem s5_328_edges : next config 5 s5_328 = [] := by decide
theorem s5_328_safe : Safe 8 5 s5_328 := by
  apply safe_succ 7 5 s5_328 [] (by decide) s5_328_edges
  simp
def s5_329 : State := ⟨[1,4,104,129], 1020847121124453156574505327914104455454, 1, 1, 1, 0⟩
theorem s5_329_edges : next config 5 s5_329 = [s6_583, s6_462, s6_340, s6_222] := by decide
theorem s5_329_safe : Safe 8 5 s5_329 := by
  apply safe_succ 7 5 s5_329 [s6_583, s6_462, s6_340, s6_222] (by decide) s5_329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_583_safe
  · subst z; exact s6_462_safe
  · subst z; exact s6_340_safe
  · subst z; exact s6_222_safe
def s5_330 : State := ⟨[1,4,104,129], 1020847121124453156574505327914104455958, 1, 1, 1, 0⟩
theorem s5_330_edges : next config 5 s5_330 = [s6_223] := by decide
theorem s5_330_safe : Safe 8 5 s5_330 := by
  apply safe_succ 7 5 s5_330 [s6_223] (by decide) s5_330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_223_safe
def s5_331 : State := ⟨[1,4,104,129], 1020847121124453156574505327914104459542, 2, 2, 1, 0⟩
theorem s5_331_edges : next config 5 s5_331 = [s6_663, s6_999, s6_208, s6_224, s6_255] := by decide
theorem s5_331_safe : Safe 8 5 s5_331 := by
  apply safe_succ 7 5 s5_331 [s6_663, s6_999, s6_208, s6_224, s6_255] (by decide) s5_331_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_663_safe
  · subst z; exact s6_999_safe
  · subst z; exact s6_208_safe
  · subst z; exact s6_224_safe
  · subst z; exact s6_255_safe
def s5_332 : State := ⟨[1,4,104,129], 1020847121124453156574505327922694390038, 1, 1, 1, 0⟩
theorem s5_332_edges : next config 5 s5_332 = [s6_463, s6_225] := by decide
theorem s5_332_safe : Safe 8 5 s5_332 := by
  apply safe_succ 7 5 s5_332 [s6_463, s6_225] (by decide) s5_332_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_463_safe
  · subst z; exact s6_225_safe
def s5_333 : State := ⟨[1,4,104,129], 1020847121124453156611398816061523558678, 1, 1, 1, 0⟩
theorem s5_333_edges : next config 5 s5_333 = [s6_584, s6_464, s6_341, s6_226] := by decide
theorem s5_333_safe : Safe 8 5 s5_333 := by
  apply safe_succ 7 5 s5_333 [s6_584, s6_464, s6_341, s6_226] (by decide) s5_333_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_584_safe
  · subst z; exact s6_464_safe
  · subst z; exact s6_341_safe
  · subst z; exact s6_226_safe
def s5_334 : State := ⟨[1,4,104,129], 1020847121124453156869653233093457281302, 2, 2, 1, 0⟩
theorem s5_334_edges : next config 5 s5_334 = [s6_227] := by decide
theorem s5_334_safe : Safe 8 5 s5_334 := by
  apply safe_succ 7 5 s5_334 [s6_227] (by decide) s5_334_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_227_safe
def s5_335 : State := ⟨[1,4,104,129], 1020847121282909481603034003101192356118, 1, 1, 1, 0⟩
theorem s5_335_edges : next config 5 s5_335 = [s6_465, s6_228] := by decide
theorem s5_335_safe : Safe 8 5 s5_335 := by
  apply safe_succ 7 5 s5_335 [s6_465, s6_228] (by decide) s5_335_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_465_safe
  · subst z; exact s6_228_safe
def s5_336 : State := ⟨[1,4,104,129], 1020847122392103756802734729410807660822, 2, 2, 1, 0⟩
theorem s5_336_edges : next config 5 s5_336 = [s6_664, s6_209, s6_229] := by decide
theorem s5_336_safe : Safe 8 5 s5_336 := by
  apply safe_succ 7 5 s5_336 [s6_664, s6_209, s6_229] (by decide) s5_336_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_664_safe
  · subst z; exact s6_209_safe
  · subst z; exact s6_229_safe
def s5_337 : State := ⟨[1,4,104,129], 1020847445643006815001232111070125031702, 2, 2, 1, 0⟩
theorem s5_337_edges : next config 5 s5_337 = [s6_665, s6_210, s6_230] := by decide
theorem s5_337_safe : Safe 8 5 s5_337 := by
  apply safe_succ 7 5 s5_337 [s6_665, s6_210, s6_230] (by decide) s5_337_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_665_safe
  · subst z; exact s6_210_safe
  · subst z; exact s6_230_safe
def s5_338 : State := ⟨[1,4,104,130], 1701411854966330083501254542777640878366, 1, 1, 1, 0⟩
theorem s5_338_edges : next config 5 s5_338 = [s6_585, s6_466, s6_342, s6_240, s6_257] := by decide
theorem s5_338_safe : Safe 8 5 s5_338 := by
  apply safe_succ 7 5 s5_338 [s6_585, s6_466, s6_342, s6_240, s6_257] (by decide) s5_338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_585_safe
  · subst z; exact s6_466_safe
  · subst z; exact s6_342_safe
  · subst z; exact s6_240_safe
  · subst z; exact s6_257_safe
def s5_339 : State := ⟨[1,4,104,130], 1701411854966330083501254542777640878870, 1, 1, 1, 0⟩
theorem s5_339_edges : next config 5 s5_339 = [s6_258] := by decide
theorem s5_339_safe : Safe 8 5 s5_339 := by
  apply safe_succ 7 5 s5_339 [s6_258] (by decide) s5_339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_258_safe
def s5_340 : State := ⟨[1,4,104,130], 1701411854966330083501254542777640882454, 2, 2, 1, 0⟩
theorem s5_340_edges : next config 5 s5_340 = [s6_1396, s6_666, s6_1000, s6_211, s6_241, s6_259] := by decide
theorem s5_340_safe : Safe 8 5 s5_340 := by
  apply safe_succ 7 5 s5_340 [s6_1396, s6_666, s6_1000, s6_211, s6_241, s6_259] (by decide) s5_340_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1396_safe
  · subst z; exact s6_666_safe
  · subst z; exact s6_1000_safe
  · subst z; exact s6_211_safe
  · subst z; exact s6_241_safe
  · subst z; exact s6_259_safe
def s5_341 : State := ⟨[1,4,104,130], 1701411854966330083501254542786230812950, 1, 1, 1, 0⟩
theorem s5_341_edges : next config 5 s5_341 = [s6_467] := by decide
theorem s5_341_safe : Safe 8 5 s5_341 := by
  apply safe_succ 7 5 s5_341 [s6_467] (by decide) s5_341_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_467_safe
def s5_342 : State := ⟨[1,4,104,130], 1701411854966330083538148030925059981590, 1, 1, 1, 0⟩
theorem s5_342_edges : next config 5 s5_342 = [s6_586, s6_468, s6_343, s6_242, s6_260] := by decide
theorem s5_342_safe : Safe 8 5 s5_342 := by
  apply safe_succ 7 5 s5_342 [s6_586, s6_468, s6_343, s6_242, s6_260] (by decide) s5_342_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_586_safe
  · subst z; exact s6_468_safe
  · subst z; exact s6_343_safe
  · subst z; exact s6_242_safe
  · subst z; exact s6_260_safe
def s5_343 : State := ⟨[1,4,104,130], 1701411854966330083796402447956993704214, 2, 2, 1, 0⟩
theorem s5_343_edges : next config 5 s5_343 = [s6_243] := by decide
theorem s5_343_safe : Safe 8 5 s5_343 := by
  apply safe_succ 7 5 s5_343 [s6_243] (by decide) s5_343_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_243_safe
def s5_344 : State := ⟨[1,4,104,130], 1701411855124786408529783217964728779030, 1, 1, 1, 0⟩
theorem s5_344_edges : next config 5 s5_344 = [s6_469, s6_261] := by decide
theorem s5_344_safe : Safe 8 5 s5_344 := by
  apply safe_succ 7 5 s5_344 [s6_469, s6_261] (by decide) s5_344_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_469_safe
  · subst z; exact s6_261_safe
def s5_345 : State := ⟨[1,4,104,130], 1701411856233980683729483944274344083734, 2, 2, 1, 0⟩
theorem s5_345_edges : next config 5 s5_345 = [s6_1397, s6_667, s6_212, s6_244, s6_262] := by decide
theorem s5_345_safe : Safe 8 5 s5_345 := by
  apply safe_succ 7 5 s5_345 [s6_1397, s6_667, s6_212, s6_244, s6_262] (by decide) s5_345_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1397_safe
  · subst z; exact s6_667_safe
  · subst z; exact s6_212_safe
  · subst z; exact s6_244_safe
  · subst z; exact s6_262_safe
def s5_346 : State := ⟨[1,4,104,130], 1701412179484883741927981325933661454614, 2, 2, 1, 0⟩
theorem s5_346_edges : next config 5 s5_346 = [s6_1398, s6_668, s6_213, s6_245, s6_263] := by decide
theorem s5_346_safe : Safe 8 5 s5_346 := by
  apply safe_succ 7 5 s5_346 [s6_1398, s6_668, s6_213, s6_245, s6_263] (by decide) s5_346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1398_safe
  · subst z; exact s6_668_safe
  · subst z; exact s6_213_safe
  · subst z; exact s6_245_safe
  · subst z; exact s6_263_safe
def s5_347 : State := ⟨[1,4,104,130], 4423670790333837791208251402231786570006, 1, 1, 1, 0⟩
theorem s5_347_edges : next config 5 s5_347 = [s6_587, s6_470, s6_344, s6_246, s6_264] := by decide
theorem s5_347_safe : Safe 8 5 s5_347 := by
  apply safe_succ 7 5 s5_347 [s6_587, s6_470, s6_344, s6_246, s6_264] (by decide) s5_347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_587_safe
  · subst z; exact s6_470_safe
  · subst z; exact s6_344_safe
  · subst z; exact s6_246_safe
  · subst z; exact s6_264_safe
def s5_348 : State := ⟨[1,4,104,131], 3062541322650083937354752972504713724190, 1, 1, 1, 0⟩
theorem s5_348_edges : next config 5 s5_348 = [s6_588, s6_471, s6_345, s6_275] := by decide
theorem s5_348_safe : Safe 8 5 s5_348 := by
  apply safe_succ 7 5 s5_348 [s6_588, s6_471, s6_345, s6_275] (by decide) s5_348_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_588_safe
  · subst z; exact s6_471_safe
  · subst z; exact s6_345_safe
  · subst z; exact s6_275_safe
def s5_349 : State := ⟨[1,4,104,132], 5784800258017591645061749831958859415838, 1, 1, 1, 0⟩
theorem s5_349_edges : next config 5 s5_349 = [s6_589, s6_472, s6_346, s6_401, s6_334, s6_214] := by decide
theorem s5_349_safe : Safe 8 5 s5_349 := by
  apply safe_succ 7 5 s5_349 [s6_589, s6_472, s6_346, s6_401, s6_334, s6_214] (by decide) s5_349_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_589_safe
  · subst z; exact s6_472_safe
  · subst z; exact s6_346_safe
  · subst z; exact s6_401_safe
  · subst z; exact s6_334_safe
  · subst z; exact s6_214_safe
def s5_350 : State := ⟨[1,4,104,132], 5784800258017591645061749831958859416342, 1, 1, 1, 0⟩
theorem s5_350_edges : next config 5 s5_350 = [] := by decide
theorem s5_350_safe : Safe 8 5 s5_350 := by
  apply safe_succ 7 5 s5_350 [] (by decide) s5_350_edges
  simp
def s5_351 : State := ⟨[1,4,104,132], 5784800258017591645061749831958859419926, 2, 2, 1, 0⟩
theorem s5_351_edges : next config 5 s5_351 = [s6_672, s6_1001] := by decide
theorem s5_351_safe : Safe 8 5 s5_351 := by
  apply safe_succ 7 5 s5_351 [s6_672, s6_1001] (by decide) s5_351_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_672_safe
  · subst z; exact s6_1001_safe
def s5_352 : State := ⟨[1,4,104,132], 5784800258017591645061749831967449350422, 1, 1, 1, 0⟩
theorem s5_352_edges : next config 5 s5_352 = [s6_473, s6_215] := by decide
theorem s5_352_safe : Safe 8 5 s5_352 := by
  apply safe_succ 7 5 s5_352 [s6_473, s6_215] (by decide) s5_352_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_473_safe
  · subst z; exact s6_215_safe
def s5_353 : State := ⟨[1,4,104,132], 5784800258017591645098643320106278519062, 1, 1, 1, 0⟩
theorem s5_353_edges : next config 5 s5_353 = [s6_590, s6_474, s6_347, s6_402, s6_335, s6_216] := by decide
theorem s5_353_safe : Safe 8 5 s5_353 := by
  apply safe_succ 7 5 s5_353 [s6_590, s6_474, s6_347, s6_402, s6_335, s6_216] (by decide) s5_353_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_590_safe
  · subst z; exact s6_474_safe
  · subst z; exact s6_347_safe
  · subst z; exact s6_402_safe
  · subst z; exact s6_335_safe
  · subst z; exact s6_216_safe
def s5_354 : State := ⟨[1,4,104,132], 5784800258017591645356897737138212241686, 2, 2, 1, 0⟩
theorem s5_354_edges : next config 5 s5_354 = [] := by decide
theorem s5_354_safe : Safe 8 5 s5_354 := by
  apply safe_succ 7 5 s5_354 [] (by decide) s5_354_edges
  simp
def s5_355 : State := ⟨[1,4,104,132], 5784800258176047970090278507145947316502, 1, 1, 1, 0⟩
theorem s5_355_edges : next config 5 s5_355 = [s6_475, s6_217] := by decide
theorem s5_355_safe : Safe 8 5 s5_355 := by
  apply safe_succ 7 5 s5_355 [s6_475, s6_217] (by decide) s5_355_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_475_safe
  · subst z; exact s6_217_safe
def s5_356 : State := ⟨[1,4,104,132], 5784800259285242245289979233455562621206, 2, 2, 1, 0⟩
theorem s5_356_edges : next config 5 s5_356 = [s6_673] := by decide
theorem s5_356_safe : Safe 8 5 s5_356 := by
  apply safe_succ 7 5 s5_356 [s6_673] (by decide) s5_356_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_673_safe
def s5_357 : State := ⟨[1,4,104,132], 5784800582536145303488476615114879992086, 2, 2, 1, 0⟩
theorem s5_357_edges : next config 5 s5_357 = [s6_674] := by decide
theorem s5_357_safe : Safe 8 5 s5_357 := by
  apply safe_succ 7 5 s5_357 [s6_674] (by decide) s5_357_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_674_safe
def s5_358 : State := ⟨[1,4,104,136], 87452568319042822876271655615583230165278, 1, 1, 1, 0⟩
theorem s5_358_edges : next config 5 s5_358 = [s6_591, s6_615, s6_476, s6_348, s6_218] := by decide
theorem s5_358_safe : Safe 8 5 s5_358 := by
  apply safe_succ 7 5 s5_358 [s6_591, s6_615, s6_476, s6_348, s6_218] (by decide) s5_358_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_591_safe
  · subst z; exact s6_615_safe
  · subst z; exact s6_476_safe
  · subst z; exact s6_348_safe
  · subst z; exact s6_218_safe
def s5_359 : State := ⟨[1,4,104,136], 87452568319042822876271655615583230165782, 1, 1, 1, 0⟩
theorem s5_359_edges : next config 5 s5_359 = [] := by decide
theorem s5_359_safe : Safe 8 5 s5_359 := by
  apply safe_succ 7 5 s5_359 [] (by decide) s5_359_edges
  simp
def s5_360 : State := ⟨[1,4,104,136], 87452568319042822876271655615583230169366, 2, 2, 1, 0⟩
theorem s5_360_edges : next config 5 s5_360 = [s6_675, s6_1002] := by decide
theorem s5_360_safe : Safe 8 5 s5_360 := by
  apply safe_succ 7 5 s5_360 [s6_675, s6_1002] (by decide) s5_360_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_675_safe
  · subst z; exact s6_1002_safe
def s5_361 : State := ⟨[1,4,104,136], 87452568319042822876271655615591820099862, 1, 1, 1, 0⟩
theorem s5_361_edges : next config 5 s5_361 = [s6_616, s6_477, s6_219] := by decide
theorem s5_361_safe : Safe 8 5 s5_361 := by
  apply safe_succ 7 5 s5_361 [s6_616, s6_477, s6_219] (by decide) s5_361_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_616_safe
  · subst z; exact s6_477_safe
  · subst z; exact s6_219_safe
def s5_362 : State := ⟨[1,4,104,136], 87452568319042822876308549103730649268502, 1, 1, 1, 0⟩
theorem s5_362_edges : next config 5 s5_362 = [s6_592, s6_617, s6_478, s6_349, s6_220] := by decide
theorem s5_362_safe : Safe 8 5 s5_362 := by
  apply safe_succ 7 5 s5_362 [s6_592, s6_617, s6_478, s6_349, s6_220] (by decide) s5_362_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_592_safe
  · subst z; exact s6_617_safe
  · subst z; exact s6_478_safe
  · subst z; exact s6_349_safe
  · subst z; exact s6_220_safe
def s5_363 : State := ⟨[1,4,104,136], 87452568319042822876566803520762582991126, 2, 2, 1, 0⟩
theorem s5_363_edges : next config 5 s5_363 = [] := by decide
theorem s5_363_safe : Safe 8 5 s5_363 := by
  apply safe_succ 7 5 s5_363 [] (by decide) s5_363_edges
  simp
def s5_364 : State := ⟨[1,4,104,136], 87452568319201279201300184290770318065942, 1, 1, 1, 0⟩
theorem s5_364_edges : next config 5 s5_364 = [s6_618, s6_479, s6_221] := by decide
theorem s5_364_safe : Safe 8 5 s5_364 := by
  apply safe_succ 7 5 s5_364 [s6_618, s6_479, s6_221] (by decide) s5_364_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_618_safe
  · subst z; exact s6_479_safe
  · subst z; exact s6_221_safe
def s5_365 : State := ⟨[1,4,104,136], 87452568320310473476499885017079933370646, 2, 2, 1, 0⟩
theorem s5_365_edges : next config 5 s5_365 = [s6_676] := by decide
theorem s5_365_safe : Safe 8 5 s5_365 := by
  apply safe_succ 7 5 s5_365 [s6_676] (by decide) s5_365_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_676_safe
def s5_366 : State := ⟨[1,4,104,136], 87452568643561376534698382398739250741526, 2, 2, 1, 0⟩
theorem s5_366_edges : next config 5 s5_366 = [s6_677] := by decide
theorem s5_366_safe : Safe 8 5 s5_366 := by
  apply safe_succ 7 5 s5_366 [s6_677] (by decide) s5_366_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_677_safe
def s5_367 : State := ⟨[1,4,104,136], 261677140182563316169519454620648554430742, 1, 1, 1, 0⟩
theorem s5_367_edges : next config 5 s5_367 = [] := by decide
theorem s5_367_safe : Safe 8 5 s5_367 := by
  apply safe_succ 7 5 s5_367 [] (by decide) s5_367_edges
  simp
def s5_368 : State := ⟨[1,4,104,136], 1481249143227206769222254047656105824289046, 2, 2, 1, 0⟩
theorem s5_368_edges : next config 5 s5_368 = [s6_678, s6_1003] := by decide
theorem s5_368_safe : Safe 8 5 s5_368 := by
  apply safe_succ 7 5 s5_368 [s6_678, s6_1003] (by decide) s5_368_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_678_safe
  · subst z; exact s6_1003_safe
def s5_369 : State := ⟨[1,4,104,137], 174564854250803069522895555118115892298518, 1, 1, 1, 0⟩
theorem s5_369_edges : next config 5 s5_369 = [] := by decide
theorem s5_369_safe : Safe 8 5 s5_369 := by
  apply safe_succ 7 5 s5_369 [] (by decide) s5_369_edges
  simp
def s5_370 : State := ⟨[1,4,104,140], 1394136857295446522575630148153573162160406, 2, 2, 1, 0⟩
theorem s5_370_edges : next config 5 s5_370 = [s6_679, s6_1004] := by decide
theorem s5_370_safe : Safe 8 5 s5_370 := by
  apply safe_succ 7 5 s5_370 [s6_679, s6_1004] (by decide) s5_370_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_679_safe
  · subst z; exact s6_1004_safe
def s5_371 : State := ⟨[1,4,104,144], 22301085480917905717765366028761412074012958, 1, 1, 1, 0⟩
theorem s5_371_edges : next config 5 s5_371 = [s6_593, s6_484, s6_350, s6_231, s6_247, s6_286] := by decide
theorem s5_371_safe : Safe 8 5 s5_371 := by
  apply safe_succ 7 5 s5_371 [s6_593, s6_484, s6_350, s6_231, s6_247, s6_286] (by decide) s5_371_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_593_safe
  · subst z; exact s6_484_safe
  · subst z; exact s6_350_safe
  · subst z; exact s6_231_safe
  · subst z; exact s6_247_safe
  · subst z; exact s6_286_safe
def s5_372 : State := ⟨[1,4,104,144], 22301085480917905717765366028761412074013462, 1, 1, 1, 0⟩
theorem s5_372_edges : next config 5 s5_372 = [s6_232] := by decide
theorem s5_372_safe : Safe 8 5 s5_372 := by
  apply safe_succ 7 5 s5_372 [s6_232] (by decide) s5_372_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_232_safe
def s5_373 : State := ⟨[1,4,104,144], 22301085480917905717765366028761412074017046, 2, 2, 1, 0⟩
theorem s5_373_edges : next config 5 s5_373 = [s6_680, s6_1005, s6_233, s6_248, s6_287] := by decide
theorem s5_373_safe : Safe 8 5 s5_373 := by
  apply safe_succ 7 5 s5_373 [s6_680, s6_1005, s6_233, s6_248, s6_287] (by decide) s5_373_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_680_safe
  · subst z; exact s6_1005_safe
  · subst z; exact s6_233_safe
  · subst z; exact s6_248_safe
  · subst z; exact s6_287_safe
def s5_374 : State := ⟨[1,4,104,144], 22301085480917905717765366028761420663947542, 1, 1, 1, 0⟩
theorem s5_374_edges : next config 5 s5_374 = [s6_485, s6_234] := by decide
theorem s5_374_safe : Safe 8 5 s5_374 := by
  apply safe_succ 7 5 s5_374 [s6_485, s6_234] (by decide) s5_374_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_485_safe
  · subst z; exact s6_234_safe
def s5_375 : State := ⟨[1,4,104,144], 22301085480917905717765402922249559493116182, 1, 1, 1, 0⟩
theorem s5_375_edges : next config 5 s5_375 = [s6_594, s6_486, s6_351, s6_235, s6_249, s6_288] := by decide
theorem s5_375_safe : Safe 8 5 s5_375 := by
  apply safe_succ 7 5 s5_375 [s6_594, s6_486, s6_351, s6_235, s6_249, s6_288] (by decide) s5_375_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_594_safe
  · subst z; exact s6_486_safe
  · subst z; exact s6_351_safe
  · subst z; exact s6_235_safe
  · subst z; exact s6_249_safe
  · subst z; exact s6_288_safe
def s5_376 : State := ⟨[1,4,104,144], 22301085480917905717765661176666591426838806, 2, 2, 1, 0⟩
theorem s5_376_edges : next config 5 s5_376 = [s6_236, s6_250] := by decide
theorem s5_376_safe : Safe 8 5 s5_376 := by
  apply safe_succ 7 5 s5_376 [s6_236, s6_250] (by decide) s5_376_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_236_safe
  · subst z; exact s6_250_safe
def s5_377 : State := ⟨[1,4,104,144], 22301085480918064174090394557436599161913622, 1, 1, 1, 0⟩
theorem s5_377_edges : next config 5 s5_377 = [s6_487, s6_237] := by decide
theorem s5_377_safe : Safe 8 5 s5_377 := by
  apply safe_succ 7 5 s5_377 [s6_487, s6_237] (by decide) s5_377_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_487_safe
  · subst z; exact s6_237_safe
def s5_378 : State := ⟨[1,4,104,144], 22301085480919173368365594258162908777218326, 2, 2, 1, 0⟩
theorem s5_378_edges : next config 5 s5_378 = [s6_681, s6_238, s6_251, s6_289] := by decide
theorem s5_378_safe : Safe 8 5 s5_378 := by
  apply safe_succ 7 5 s5_378 [s6_681, s6_238, s6_251, s6_289] (by decide) s5_378_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_681_safe
  · subst z; exact s6_238_safe
  · subst z; exact s6_251_safe
  · subst z; exact s6_289_safe
def s5_379 : State := ⟨[1,4,104,144], 22301085481242424271423792755544568094589206, 2, 2, 1, 0⟩
theorem s5_379_edges : next config 5 s5_379 = [s6_682, s6_239, s6_252, s6_290] := by decide
theorem s5_379_safe : Safe 8 5 s5_379 := by
  apply safe_succ 7 5 s5_379 [s6_682, s6_239, s6_252, s6_290] (by decide) s5_379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_682_safe
  · subst z; exact s6_239_safe
  · subst z; exact s6_252_safe
  · subst z; exact s6_290_safe
def s5_380 : State := ⟨[1,4,104,145], 44601830679448528859301084301409773580124438, 1, 1, 1, 0⟩
theorem s5_380_edges : next config 5 s5_380 = [s6_683, s6_739, s6_1006, s6_595, s6_488, s6_352, s6_410, s6_375] := by decide
theorem s5_380_safe : Safe 8 5 s5_380 := by
  apply safe_succ 7 5 s5_380 [s6_683, s6_739, s6_1006, s6_595, s6_488, s6_352, s6_410, s6_375] (by decide) s5_380_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_683_safe
  · subst z; exact s6_739_safe
  · subst z; exact s6_1006_safe
  · subst z; exact s6_595_safe
  · subst z; exact s6_488_safe
  · subst z; exact s6_352_safe
  · subst z; exact s6_410_safe
  · subst z; exact s6_375_safe
def s5_381 : State := ⟨[1,4,104,150], 1516452374911937339954512343794631360047546646, 0, 0, 1, 0⟩
theorem s5_381_edges : next config 5 s5_381 = [] := by decide
theorem s5_381_safe : Safe 8 5 s5_381 := by
  apply safe_succ 7 5 s5_381 [] (by decide) s5_381_edges
  simp
def s5_382 : State := ⟨[1,4,104,150], 1538751758981000279342194208568849994480681238, 0, 0, 1, 0⟩
theorem s5_382_edges : next config 5 s5_382 = [] := by decide
theorem s5_382_safe : Safe 8 5 s5_382 := by
  apply safe_succ 7 5 s5_382 [] (by decide) s5_382_edges
  simp
def s5_383 : State := ⟨[1,4,104,160], 1461501637671185305486261062364039132706500575518, 1, 1, 1, 0⟩
theorem s5_383_edges : next config 5 s5_383 = [s6_596, s6_489, s6_353, s6_265, s6_291] := by decide
theorem s5_383_safe : Safe 8 5 s5_383 := by
  apply safe_succ 7 5 s5_383 [s6_596, s6_489, s6_353, s6_265, s6_291] (by decide) s5_383_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_596_safe
  · subst z; exact s6_489_safe
  · subst z; exact s6_353_safe
  · subst z; exact s6_265_safe
  · subst z; exact s6_291_safe
def s5_384 : State := ⟨[1,4,104,160], 1461501637671185305486261062364039132706500576022, 1, 1, 1, 0⟩
theorem s5_384_edges : next config 5 s5_384 = [s6_266] := by decide
theorem s5_384_safe : Safe 8 5 s5_384 := by
  apply safe_succ 7 5 s5_384 [s6_266] (by decide) s5_384_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_266_safe
def s5_385 : State := ⟨[1,4,104,160], 1461501637671185305486261062364039132706500579606, 2, 2, 1, 0⟩
theorem s5_385_edges : next config 5 s5_385 = [s6_1413, s6_686, s6_1007, s6_256, s6_267, s6_292] := by decide
theorem s5_385_safe : Safe 8 5 s5_385 := by
  apply safe_succ 7 5 s5_385 [s6_1413, s6_686, s6_1007, s6_256, s6_267, s6_292] (by decide) s5_385_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1413_safe
  · subst z; exact s6_686_safe
  · subst z; exact s6_1007_safe
  · subst z; exact s6_256_safe
  · subst z; exact s6_267_safe
  · subst z; exact s6_292_safe
def s5_386 : State := ⟨[1,4,104,160], 1461501637671185305486261062364039132715090510102, 1, 1, 1, 0⟩
theorem s5_386_edges : next config 5 s5_386 = [s6_490] := by decide
theorem s5_386_safe : Safe 8 5 s5_386 := by
  apply safe_succ 7 5 s5_386 [s6_490] (by decide) s5_386_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_490_safe
def s5_387 : State := ⟨[1,4,104,160], 1461501637671185305486261062400932620853919678742, 1, 1, 1, 0⟩
theorem s5_387_edges : next config 5 s5_387 = [s6_597, s6_491, s6_354, s6_268, s6_293] := by decide
theorem s5_387_safe : Safe 8 5 s5_387 := by
  apply safe_succ 7 5 s5_387 [s6_597, s6_491, s6_354, s6_268, s6_293] (by decide) s5_387_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_597_safe
  · subst z; exact s6_491_safe
  · subst z; exact s6_354_safe
  · subst z; exact s6_268_safe
  · subst z; exact s6_293_safe
def s5_388 : State := ⟨[1,4,104,160], 1461501637671185305486261062659187037885853401366, 2, 2, 1, 0⟩
theorem s5_388_edges : next config 5 s5_388 = [] := by decide
theorem s5_388_safe : Safe 8 5 s5_388 := by
  apply safe_succ 7 5 s5_388 [] (by decide) s5_388_edges
  simp
def s5_389 : State := ⟨[1,4,104,160], 1461501637671185305644717387392567807893588476182, 1, 1, 1, 0⟩
theorem s5_389_edges : next config 5 s5_389 = [s6_492, s6_269] := by decide
theorem s5_389_safe : Safe 8 5 s5_389 := by
  apply safe_succ 7 5 s5_389 [s6_492, s6_269] (by decide) s5_389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_492_safe
  · subst z; exact s6_269_safe
def s5_390 : State := ⟨[1,4,104,160], 1461501637671185306753911662592268534203203780886, 2, 2, 1, 0⟩
theorem s5_390_edges : next config 5 s5_390 = [s6_687, s6_270, s6_294] := by decide
theorem s5_390_safe : Safe 8 5 s5_390 := by
  apply safe_succ 7 5 s5_390 [s6_687, s6_270, s6_294] (by decide) s5_390_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_687_safe
  · subst z; exact s6_270_safe
  · subst z; exact s6_294_safe
def s5_391 : State := ⟨[1,4,104,160], 1461501637671185630004814720790765915862521151766, 2, 2, 1, 0⟩
theorem s5_391_edges : next config 5 s5_391 = [s6_688, s6_271, s6_295] := by decide
theorem s5_391_safe : Safe 8 5 s5_391 := by
  apply safe_succ 7 5 s5_391 [s6_688, s6_271, s6_295] (by decide) s5_391_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_688_safe
  · subst z; exact s6_271_safe
  · subst z; exact s6_295_safe
def s5_392 : State := ⟨[1,4,104,160], 4384504912332991141893630727796605172018365661462, 1, 1, 1, 0⟩
theorem s5_392_edges : next config 5 s5_392 = [s6_493] := by decide
theorem s5_392_safe : Safe 8 5 s5_392 := by
  apply safe_succ 7 5 s5_392 [s6_493] (by decide) s5_392_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_493_safe
def s5_393 : State := ⟨[1,4,104,161], 2923003275002088223689945895080322152371023053078, 1, 1, 1, 0⟩
theorem s5_393_edges : next config 5 s5_393 = [s6_494, s6_277] := by decide
theorem s5_393_safe : Safe 8 5 s5_393 := by
  apply safe_succ 7 5 s5_393 [s6_494, s6_277] (by decide) s5_393_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_494_safe
  · subst z; exact s6_277_safe
def s5_394 : State := ⟨[1,4,104,162], 25108406947392729606368181220611735078775808399257509101846, 0, 0, 1, 0⟩
theorem s5_394_edges : next config 5 s5_394 = [s6_495] := by decide
theorem s5_394_safe : Safe 8 5 s5_394 := by
  apply safe_succ 7 5 s5_394 [s6_495] (by decide) s5_394_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_495_safe
def s5_395 : State := ⟨[1,4,104,162], 31385508682779410368842841176135647641024665413994470768918, 0, 0, 1, 0⟩
theorem s5_395_edges : next config 5 s5_395 = [s6_496] := by decide
theorem s5_395_safe : Safe 8 5 s5_395 := by
  apply safe_succ 7 5 s5_395 [s6_496] (by decide) s5_395_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_496_safe
def s5_396 : State := ⟨[1,4,104,163], 11692013102390329402121439526011766344615710490902, 0, 0, 1, 0⟩
theorem s5_396_edges : next config 5 s5_396 = [s6_497, s6_278] := by decide
theorem s5_396_safe : Safe 8 5 s5_396 := by
  apply safe_succ 7 5 s5_396 [s6_497, s6_278] (by decide) s5_396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_497_safe
  · subst z; exact s6_278_safe
def s5_397 : State := ⟨[1,4,104,163], 11692013103070894135963316452938515559479246913814, 0, 0, 1, 0⟩
theorem s5_397_edges : next config 5 s5_397 = [s6_498, s6_279] := by decide
theorem s5_397_safe : Safe 8 5 s5_397 := by
  apply safe_succ 7 5 s5_397 [s6_498, s6_279] (by decide) s5_397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_498_safe
  · subst z; exact s6_279_safe
def s5_398 : State := ⟨[1,4,104,163], 14615016374329876303161301483737335524473429885206, 0, 0, 1, 0⟩
theorem s5_398_edges : next config 5 s5_398 = [s6_499, s6_280] := by decide
theorem s5_398_safe : Safe 8 5 s5_398 := by
  apply safe_succ 7 5 s5_398 [s6_499, s6_280] (by decide) s5_398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_499_safe
  · subst z; exact s6_280_safe
def s5_399 : State := ⟨[1,4,104,163], 16076518010980214487523109389526869329265826005270, 0, 0, 1, 0⟩
theorem s5_399_edges : next config 5 s5_399 = [s6_500, s6_281] := by decide
theorem s5_399_safe : Safe 8 5 s5_399 := by
  apply safe_succ 7 5 s5_399 [s6_500, s6_281] (by decide) s5_399_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_500_safe
  · subst z; exact s6_281_safe
def s5_400 : State := ⟨[1,4,104,163], 17538019649672246873410548076096650778648831394070, 0, 0, 1, 0⟩
theorem s5_400_edges : next config 5 s5_400 = [s6_501, s6_282] := by decide
theorem s5_400_safe : Safe 8 5 s5_400 := by
  apply safe_succ 7 5 s5_400 [s6_501, s6_282] (by decide) s5_400_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_501_safe
  · subst z; exact s6_282_safe
def s5_401 : State := ⟨[1,4,104,163], 18999521285642020323930479054959435368577691091222, 0, 0, 1, 0⟩
theorem s5_401_edges : next config 5 s5_401 = [s6_502, s6_283] := by decide
theorem s5_401_safe : Safe 8 5 s5_401 := by
  apply safe_succ 7 5 s5_401 [s6_502, s6_283] (by decide) s5_401_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_502_safe
  · subst z; exact s6_283_safe
def s5_402 : State := ⟨[1,4,104,170], 1502423683177869611768354338115840198749076295057686, 0, 0, 1, 0⟩
theorem s5_402_edges : next config 5 s5_402 = [s6_1439, s6_284] := by decide
theorem s5_402_safe : Safe 8 5 s5_402 := by
  apply safe_succ 7 5 s5_402 [s6_1439, s6_284] (by decide) s5_402_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1439_safe
  · subst z; exact s6_284_safe
def s5_403 : State := ⟨[1,4,104,170], 1503885184813839385218874269094702983339005154754838, 0, 0, 1, 0⟩
theorem s5_403_edges : next config 5 s5_403 = [s6_1440, s6_285] := by decide
theorem s5_403_safe : Safe 8 5 s5_403 := by
  apply safe_succ 7 5 s5_403 [s6_1440, s6_285] (by decide) s5_403_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1440_safe
  · subst z; exact s6_285_safe
def s5_404 : State := ⟨[1,4,104,170], 25108408438124399683889157788370264449384488448308702937366, 0, 0, 1, 0⟩
theorem s5_404_edges : next config 5 s5_404 = [s6_296] := by decide
theorem s5_404_safe : Safe 8 5 s5_404 := by
  apply safe_succ 7 5 s5_404 [s6_296] (by decide) s5_404_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_296_safe
def s5_405 : State := ⟨[1,4,104,170], 31385510173511080446363817743894177011633345463045664604438, 0, 0, 1, 0⟩
theorem s5_405_edges : next config 5 s5_405 = [s6_297] := by decide
theorem s5_405_safe : Safe 8 5 s5_405 := by
  apply safe_succ 7 5 s5_405 [s6_297] (by decide) s5_405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_297_safe
def s5_406 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645750111557514602545438, 1, 1, 1, 0⟩
theorem s5_406_edges : next config 5 s5_406 = [s6_598, s6_503, s6_355] := by decide
theorem s5_406_safe : Safe 8 5 s5_406 := by
  apply safe_succ 7 5 s5_406 [s6_598, s6_503, s6_355] (by decide) s5_406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_598_safe
  · subst z; exact s6_503_safe
  · subst z; exact s6_355_safe
def s5_407 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645750111557514602545942, 1, 1, 1, 0⟩
theorem s5_407_edges : next config 5 s5_407 = [] := by decide
theorem s5_407_safe : Safe 8 5 s5_407 := by
  apply safe_succ 7 5 s5_407 [] (by decide) s5_407_edges
  simp
def s5_408 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645750111557514602549526, 2, 2, 1, 0⟩
theorem s5_408_edges : next config 5 s5_408 = [s6_1441, s6_691, s6_1011, s6_307, s6_313, s6_318] := by decide
theorem s5_408_safe : Safe 8 5 s5_408 := by
  apply safe_succ 7 5 s5_408 [s6_1441, s6_691, s6_1011, s6_307, s6_313, s6_318] (by decide) s5_408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1441_safe
  · subst z; exact s6_691_safe
  · subst z; exact s6_1011_safe
  · subst z; exact s6_307_safe
  · subst z; exact s6_313_safe
  · subst z; exact s6_318_safe
def s5_409 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645750111557523192480022, 1, 1, 1, 0⟩
theorem s5_409_edges : next config 5 s5_409 = [s6_504] := by decide
theorem s5_409_safe : Safe 8 5 s5_409 := by
  apply safe_succ 7 5 s5_409 [s6_504] (by decide) s5_409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_504_safe
def s5_410 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645787005045662021648662, 1, 1, 1, 0⟩
theorem s5_410_edges : next config 5 s5_410 = [s6_599, s6_505, s6_356] := by decide
theorem s5_410_safe : Safe 8 5 s5_410 := by
  apply safe_succ 7 5 s5_410 [s6_599, s6_505, s6_356] (by decide) s5_410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_599_safe
  · subst z; exact s6_505_safe
  · subst z; exact s6_356_safe
def s5_411 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242646045259462693955371286, 2, 2, 1, 0⟩
theorem s5_411_edges : next config 5 s5_411 = [] := by decide
theorem s5_411_safe : Safe 8 5 s5_411 := by
  apply safe_succ 7 5 s5_411 [] (by decide) s5_411_edges
  simp
def s5_412 : State := ⟨[1,4,104,192], 6277101735386680764176071810648698970778640232701690446102, 1, 1, 1, 0⟩
theorem s5_412_edges : next config 5 s5_412 = [s6_506] := by decide
theorem s5_412_safe : Safe 8 5 s5_412 := by
  apply safe_succ 7 5 s5_412 [s6_506] (by decide) s5_412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_506_safe
def s5_413 : State := ⟨[1,4,104,192], 6277101735386680764176071811757893245978340959011305750806, 2, 2, 1, 0⟩
theorem s5_413_edges : next config 5 s5_413 = [s6_1442, s6_692, s6_308, s6_314] := by decide
theorem s5_413_safe : Safe 8 5 s5_413 := by
  apply safe_succ 7 5 s5_413 [s6_1442, s6_692, s6_308, s6_314] (by decide) s5_413_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1442_safe
  · subst z; exact s6_692_safe
  · subst z; exact s6_308_safe
  · subst z; exact s6_314_safe
def s5_414 : State := ⟨[1,4,104,192], 6277101735386680764176072135008796304176838340670623121686, 2, 2, 1, 0⟩
theorem s5_414_edges : next config 5 s5_414 = [s6_1443, s6_693, s6_309, s6_315, s6_319] := by decide
theorem s5_414_safe : Safe 8 5 s5_414 := by
  apply safe_succ 7 5 s5_414 [s6_1443, s6_693, s6_309, s6_315, s6_319] (by decide) s5_414_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1443_safe
  · subst z; exact s6_693_safe
  · subst z; exact s6_309_safe
  · subst z; exact s6_315_safe
  · subst z; exact s6_319_safe
def s5_415 : State := ⟨[1,4,104,192], 18831305206160042291847650656905575477954822446442671571222, 1, 1, 1, 0⟩
theorem s5_415_edges : next config 5 s5_415 = [s6_600, s6_507, s6_357] := by decide
theorem s5_415_safe : Safe 8 5 s5_415 := by
  apply safe_succ 7 5 s5_415 [s6_600, s6_507, s6_357] (by decide) s5_415_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_600_safe
  · subst z; exact s6_507_safe
  · subst z; exact s6_357_safe
def s5_416 : State := ⟨[1,4,104,192], 106710729501573572985548702581812905303387798668939154751766, 2, 2, 1, 0⟩
theorem s5_416_edges : next config 5 s5_416 = [] := by decide
theorem s5_416_safe : Safe 8 5 s5_416 := by
  apply safe_succ 7 5 s5_416 [] (by decide) s5_416_edges
  simp
def s5_417 : State := ⟨[1,4,104,193], 12554203470773361528011861233697909061889360490126056161558, 1, 1, 1, 0⟩
theorem s5_417_edges : next config 5 s5_417 = [s6_601, s6_508, s6_358] := by decide
theorem s5_417_safe : Safe 8 5 s5_417 := by
  apply safe_succ 7 5 s5_417 [s6_601, s6_508, s6_358] (by decide) s5_417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_601_safe
  · subst z; exact s6_508_safe
  · subst z; exact s6_358_safe
def s5_418 : State := ⟨[1,4,104,194], 25108406947392729606368181220611735078775808399257509101846, 0, 0, 1, 0⟩
theorem s5_418_edges : next config 5 s5_418 = [s6_509] := by decide
theorem s5_418_safe : Safe 8 5 s5_418 := by
  apply safe_succ 7 5 s5_418 [s6_509] (by decide) s5_418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_509_safe
def s5_419 : State := ⟨[1,4,104,194], 25108406948854231242337954671131666057638592989186368798998, 0, 0, 1, 0⟩
theorem s5_419_edges : next config 5 s5_419 = [s6_510] := by decide
theorem s5_419_safe : Safe 8 5 s5_419 := by
  apply safe_succ 7 5 s5_419 [s6_510] (by decide) s5_419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_510_safe
def s5_420 : State := ⟨[1,4,104,196], 100433627766186892221712913158605238887580591129654473064726, 2, 2, 1, 0⟩
theorem s5_420_edges : next config 5 s5_420 = [] := by decide
theorem s5_420_safe : Safe 8 5 s5_420 := by
  apply safe_succ 7 5 s5_420 [] (by decide) s5_420_edges
  simp
def s5_421 : State := ⟨[1,4,104,210], 1645504557321206042244173864763327963878962239978716087013409046, 0, 0, 1, 0⟩
theorem s5_421_edges : next config 5 s5_421 = [s6_602, s6_626, s6_511, s6_359, s6_385, s6_322, s6_298] := by decide
theorem s5_421_safe : Safe 8 5 s5_421 := by
  apply safe_succ 7 5 s5_421 [s6_602, s6_626, s6_511, s6_359, s6_385, s6_322, s6_298] (by decide) s5_421_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_602_safe
  · subst z; exact s6_626_safe
  · subst z; exact s6_511_safe
  · subst z; exact s6_359_safe
  · subst z; exact s6_385_safe
  · subst z; exact s6_322_safe
  · subst z; exact s6_298_safe
def s5_422 : State := ⟨[1,4,104,210], 1645504557321206042266473248832390903266644104752934721446543638, 0, 0, 1, 0⟩
theorem s5_422_edges : next config 5 s5_422 = [s6_603, s6_627, s6_512, s6_360, s6_386, s6_323, s6_299] := by decide
theorem s5_422_safe : Safe 8 5 s5_422 := by
  apply safe_succ 7 5 s5_422 [s6_603, s6_627, s6_512, s6_360, s6_386, s6_323, s6_299] (by decide) s5_422_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_603_safe
  · subst z; exact s6_627_safe
  · subst z; exact s6_512_safe
  · subst z; exact s6_360_safe
  · subst z; exact s6_386_safe
  · subst z; exact s6_323_safe
  · subst z; exact s6_299_safe
def s5_423 : State := ⟨[1,4,104,210], 1645529665728147588878026227126898301978483776309900497127538966, 0, 0, 1, 0⟩
theorem s5_423_edges : next config 5 s5_423 = [s6_604, s6_628, s6_513, s6_361, s6_387, s6_324, s6_300] := by decide
theorem s5_423_safe : Safe 8 5 s5_423 := by
  apply safe_succ 7 5 s5_423 [s6_604, s6_628, s6_513, s6_361, s6_387, s6_324, s6_300] (by decide) s5_423_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_604_safe
  · subst z; exact s6_628_safe
  · subst z; exact s6_513_safe
  · subst z; exact s6_361_safe
  · subst z; exact s6_387_safe
  · subst z; exact s6_324_safe
  · subst z; exact s6_300_safe
def s5_424 : State := ⟨[1,4,104,210], 1645535942829882975558788701786853825891046025166915234089206038, 0, 0, 1, 0⟩
theorem s5_424_edges : next config 5 s5_424 = [s6_605, s6_629, s6_514, s6_362, s6_388, s6_325, s6_301] := by decide
theorem s5_424_safe : Safe 8 5 s5_424 := by
  apply safe_succ 7 5 s5_424 [s6_605, s6_629, s6_514, s6_362, s6_388, s6_325, s6_301] (by decide) s5_424_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_605_safe
  · subst z; exact s6_629_safe
  · subst z; exact s6_514_safe
  · subst z; exact s6_362_safe
  · subst z; exact s6_388_safe
  · subst z; exact s6_325_safe
  · subst z; exact s6_301_safe
def s5_425 : State := ⟨[1,4,104,210], 2056880696651507552716012563677606036946185198070736241259774230, 0, 0, 1, 0⟩
theorem s5_425_edges : next config 5 s5_425 = [s6_606, s6_630, s6_515, s6_363, s6_389, s6_326, s6_302] := by decide
theorem s5_425_safe : Safe 8 5 s5_425 := by
  apply safe_succ 7 5 s5_425 [s6_606, s6_630, s6_515, s6_363, s6_389, s6_326, s6_302] (by decide) s5_425_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_606_safe
  · subst z; exact s6_630_safe
  · subst z; exact s6_515_safe
  · subst z; exact s6_363_safe
  · subst z; exact s6_389_safe
  · subst z; exact s6_326_safe
  · subst z; exact s6_302_safe
def s5_426 : State := ⟨[1,4,104,210], 2056886973753242939374475654268498621471065582153532343788306710, 0, 0, 1, 0⟩
theorem s5_426_edges : next config 5 s5_426 = [s6_607, s6_631, s6_516, s6_364, s6_390, s6_327, s6_303] := by decide
theorem s5_426_safe : Safe 8 5 s5_426 := by
  apply safe_succ 7 5 s5_426 [s6_607, s6_631, s6_516, s6_364, s6_390, s6_327, s6_303] (by decide) s5_426_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_607_safe
  · subst z; exact s6_631_safe
  · subst z; exact s6_516_safe
  · subst z; exact s6_364_safe
  · subst z; exact s6_390_safe
  · subst z; exact s6_327_safe
  · subst z; exact s6_303_safe
def s5_427 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652188328594154178281758, 1, 1, 1, 0⟩
theorem s5_427_edges : next config 5 s5_427 = [s6_608, s6_632, s6_517, s6_365, s6_332] := by decide
theorem s5_427_safe : Safe 8 5 s5_427 := by
  apply safe_succ 7 5 s5_427 [s6_608, s6_632, s6_517, s6_365, s6_332] (by decide) s5_427_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_608_safe
  · subst z; exact s6_632_safe
  · subst z; exact s6_517_safe
  · subst z; exact s6_365_safe
  · subst z; exact s6_332_safe
def s5_428 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652188328594154178282262, 1, 1, 1, 0⟩
theorem s5_428_edges : next config 5 s5_428 = [] := by decide
theorem s5_428_safe : Safe 8 5 s5_428 := by
  apply safe_succ 7 5 s5_428 [] (by decide) s5_428_edges
  simp
def s5_429 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652188328594154178285846, 2, 2, 1, 0⟩
theorem s5_429_edges : next config 5 s5_429 = [s6_1444, s6_694, s6_1012, s6_329, s6_339] := by decide
theorem s5_429_safe : Safe 8 5 s5_429 := by
  apply safe_succ 7 5 s5_429 [s6_1444, s6_694, s6_1012, s6_329, s6_339] (by decide) s5_429_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1444_safe
  · subst z; exact s6_694_safe
  · subst z; exact s6_1012_safe
  · subst z; exact s6_329_safe
  · subst z; exact s6_339_safe
def s5_430 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652188328594162768216342, 1, 1, 1, 0⟩
theorem s5_430_edges : next config 5 s5_430 = [s6_518] := by decide
theorem s5_430_safe : Safe 8 5 s5_430 := by
  apply safe_succ 7 5 s5_430 [s6_518] (by decide) s5_430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_518_safe
def s5_431 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652225222082301597384982, 1, 1, 1, 0⟩
theorem s5_431_edges : next config 5 s5_431 = [s6_609, s6_633, s6_519, s6_366, s6_333] := by decide
theorem s5_431_safe : Safe 8 5 s5_431 := by
  apply safe_succ 7 5 s5_431 [s6_609, s6_633, s6_519, s6_366, s6_333] (by decide) s5_431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_609_safe
  · subst z; exact s6_633_safe
  · subst z; exact s6_519_safe
  · subst z; exact s6_366_safe
  · subst z; exact s6_333_safe
def s5_432 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652483476499333531107606, 2, 2, 1, 0⟩
theorem s5_432_edges : next config 5 s5_432 = [] := by decide
theorem s5_432_safe : Safe 8 5 s5_432 := by
  apply safe_succ 7 5 s5_432 [] (by decide) s5_432_edges
  simp
def s5_433 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913061078176977216857269341266182422, 1, 1, 1, 0⟩
theorem s5_433_edges : next config 5 s5_433 = [s6_520] := by decide
theorem s5_433_safe : Safe 8 5 s5_433 := by
  apply safe_succ 7 5 s5_433 [s6_520] (by decide) s5_433_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_520_safe
def s5_434 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913062187371252416557995650881487126, 2, 2, 1, 0⟩
theorem s5_434_edges : next config 5 s5_434 = [s6_695] := by decide
theorem s5_434_safe : Safe 8 5 s5_434 := by
  apply safe_succ 7 5 s5_434 [s6_695] (by decide) s5_434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_695_safe
def s5_435 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913385438274310615055377310198858006, 2, 2, 1, 0⟩
theorem s5_435_edges : next config 5 s5_435 = [s6_696] := by decide
theorem s5_435_safe : Safe 8 5 s5_435 := by
  apply safe_succ 7 5 s5_435 [s6_696] (by decide) s5_435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_696_safe
def s5_436 : State := ⟨[1,4,104,224], 80879840001451919384001045261399174408194009497269473556361398780182, 1, 1, 1, 0⟩
theorem s5_436_edges : next config 5 s5_436 = [s6_521] := by decide
theorem s5_436_safe : Safe 8 5 s5_436 := by
  apply safe_succ 7 5 s5_436 [s6_521] (by decide) s5_436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_521_safe
def s5_437 : State := ⟨[1,4,104,224], 458319093341560876509339256479674003839114031412837488291811942269206, 2, 2, 1, 0⟩
theorem s5_437_edges : next config 5 s5_437 = [s6_697] := by decide
theorem s5_437_safe : Safe 8 5 s5_437 := by
  apply safe_succ 7 5 s5_437 [s6_697] (by decide) s5_437_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_697_safe
def s5_438 : State := ⟨[1,4,104,225], 53919893334301279589334030174379543734715321399757429750444876431638, 1, 1, 1, 0⟩
theorem s5_438_edges : next config 5 s5_438 = [s6_522] := by decide
theorem s5_438_safe : Safe 8 5 s5_438 := by
  apply safe_succ 7 5 s5_438 [s6_522] (by decide) s5_438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_522_safe
def s5_439 : State := ⟨[1,4,104,228], 431359146674410236714672241392654373166744537590525145212205035225366, 2, 2, 1, 0⟩
theorem s5_439_edges : next config 5 s5_439 = [s6_698] := by decide
theorem s5_439_safe : Safe 8 5 s5_439 := by
  apply safe_succ 7 5 s5_439 [s6_698] (by decide) s5_439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_698_safe
def s5_440 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791831838, 1, 1, 1, 0⟩
theorem s5_440_edges : next config 5 s5_440 = [s6_610, s6_634, s6_523, s6_367, s6_336] := by decide
theorem s5_440_safe : Safe 8 5 s5_440 := by
  apply safe_succ 7 5 s5_440 [s6_610, s6_634, s6_523, s6_367, s6_336] (by decide) s5_440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_610_safe
  · subst z; exact s6_634_safe
  · subst z; exact s6_523_safe
  · subst z; exact s6_367_safe
  · subst z; exact s6_336_safe
def s5_441 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791832342, 1, 1, 1, 0⟩
theorem s5_441_edges : next config 5 s5_441 = [] := by decide
theorem s5_441_safe : Safe 8 5 s5_441 := by
  apply safe_succ 7 5 s5_441 [] (by decide) s5_441_edges
  simp
def s5_442 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791835926, 2, 2, 1, 0⟩
theorem s5_442_edges : next config 5 s5_442 = [s6_699, s6_1013] := by decide
theorem s5_442_safe : Safe 8 5 s5_442 := by
  apply safe_succ 7 5 s5_442 [s6_699, s6_1013] (by decide) s5_442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_699_safe
  · subst z; exact s6_1013_safe
def s5_443 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400034311275583381766422, 1, 1, 1, 0⟩
theorem s5_443_edges : next config 5 s5_443 = [s6_524] := by decide
theorem s5_443_safe : Safe 8 5 s5_443 := by
  apply safe_succ 7 5 s5_443 [s6_524] (by decide) s5_443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_524_safe
def s5_444 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400071204763722210935062, 1, 1, 1, 0⟩
theorem s5_444_edges : next config 5 s5_444 = [s6_611, s6_635, s6_525, s6_368, s6_337] := by decide
theorem s5_444_safe : Safe 8 5 s5_444 := by
  apply safe_succ 7 5 s5_444 [s6_611, s6_635, s6_525, s6_368, s6_337] (by decide) s5_444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_611_safe
  · subst z; exact s6_635_safe
  · subst z; exact s6_525_safe
  · subst z; exact s6_368_safe
  · subst z; exact s6_337_safe
def s5_445 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400329459180754144657686, 2, 2, 1, 0⟩
theorem s5_445_edges : next config 5 s5_445 = [] := by decide
theorem s5_445_safe : Safe 8 5 s5_445 := by
  apply safe_succ 7 5 s5_445 [] (by decide) s5_445_edges
  simp
def s5_446 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838550004725062839950761879732502, 1, 1, 1, 0⟩
theorem s5_446_edges : next config 5 s5_446 = [s6_526] := by decide
theorem s5_446_safe : Safe 8 5 s5_446 := by
  apply safe_succ 7 5 s5_446 [s6_526] (by decide) s5_446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_526_safe
def s5_447 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734839659199000262540677071495037206, 2, 2, 1, 0⟩
theorem s5_447_edges : next config 5 s5_447 = [s6_700] := by decide
theorem s5_447_safe : Safe 8 5 s5_447 := by
  apply safe_succ 7 5 s5_447 [s6_700] (by decide) s5_447_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_700_safe
def s5_448 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365735162910102058461038058730812408086, 2, 2, 1, 0⟩
theorem s5_448_edges : next config 5 s5_448 = [s6_701] := by decide
theorem s5_448_safe : Safe 8 5 s5_448 := by
  apply safe_succ 7 5 s5_448 [s6_701] (by decide) s5_448_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_701_safe
def s5_449 : State := ⟨[1,4,104,232], 117329687895439584386390849658709772974056135103126219193875962372620566, 2, 2, 1, 0⟩
theorem s5_449_edges : next config 5 s5_449 = [s6_702] := by decide
theorem s5_449_safe : Safe 8 5 s5_449 := by
  apply safe_succ 7 5 s5_449 [s6_702] (by decide) s5_449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_702_safe
def s5_450 : State := ⟨[1,4,104,236], 110427941548649020598956093796432747521929544684614259365496594169397526, 2, 2, 1, 0⟩
theorem s5_450_edges : next config 5 s5_450 = [s6_703] := by decide
theorem s5_450_safe : Safe 8 5 s5_450 := by
  apply safe_succ 7 5 s5_450 [s6_703] (by decide) s5_450_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_703_safe
def s5_451 : State := ⟨[1,4,108,128], 340282711801129888074482896206588608798, 1, 1, 0, 0⟩
theorem s5_451_edges : next config 5 s5_451 = [s6_796, s6_340, s6_346, s6_369, s6_342, s6_348, s6_350, s6_353] := by decide
theorem s5_451_safe : Safe 8 5 s5_451 := by
  apply safe_succ 7 5 s5_451 [s6_796, s6_340, s6_346, s6_369, s6_342, s6_348, s6_350, s6_353] (by decide) s5_451_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_796_safe
  · subst z; exact s6_340_safe
  · subst z; exact s6_346_safe
  · subst z; exact s6_369_safe
  · subst z; exact s6_342_safe
  · subst z; exact s6_348_safe
  · subst z; exact s6_350_safe
  · subst z; exact s6_353_safe
def s5_452 : State := ⟨[1,4,108,128], 340282711801129888111376384354007712022, 1, 1, 0, 0⟩
theorem s5_452_edges : next config 5 s5_452 = [s6_798, s6_341, s6_347, s6_370, s6_343, s6_349, s6_351, s6_354] := by decide
theorem s5_452_safe : Safe 8 5 s5_452 := by
  apply safe_succ 7 5 s5_452 [s6_798, s6_341, s6_347, s6_370, s6_343, s6_349, s6_351, s6_354] (by decide) s5_452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_798_safe
  · subst z; exact s6_341_safe
  · subst z; exact s6_347_safe
  · subst z; exact s6_370_safe
  · subst z; exact s6_343_safe
  · subst z; exact s6_349_safe
  · subst z; exact s6_351_safe
  · subst z; exact s6_354_safe
def s5_453 : State := ⟨[1,4,108,131], 3743106381010514522708228970524270723350, 0, 0, 1, 0⟩
theorem s5_453_edges : next config 5 s5_453 = [] := by decide
theorem s5_453_safe : Safe 8 5 s5_453 := by
  apply safe_succ 7 5 s5_453 [] (by decide) s5_453_edges
  simp
def s5_454 : State := ⟨[1,4,108,131], 4423671114852391449634978185387807146262, 0, 0, 1, 0⟩
theorem s5_454_edges : next config 5 s5_454 = [] := by decide
theorem s5_454_safe : Safe 8 5 s5_454 := by
  apply safe_succ 7 5 s5_454 [] (by decide) s5_454_edges
  simp
def s5_455 : State := ⟨[1,4,108,145], 44602511244506889289886437777407793136992534, 0, 0, 1, 0⟩
theorem s5_455_edges : next config 5 s5_455 = [s6_704] := by decide
theorem s5_455_safe : Safe 8 5 s5_455 := by
  apply safe_succ 7 5 s5_455 [s6_704] (by decide) s5_455_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_704_safe
def s5_456 : State := ⟨[1,4,108,145], 66902575878303670554495229300841291106550038, 0, 0, 1, 0⟩
theorem s5_456_edges : next config 5 s5_456 = [s6_705] := by decide
theorem s5_456_safe : Safe 8 5 s5_456 := by
  apply safe_succ 7 5 s5_456 [s6_705] (by decide) s5_456_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_705_safe
def s5_457 : State := ⟨[1,4,108,146], 89204682206301977449884801071919379685376278, 0, 0, 1, 0⟩
theorem s5_457_edges : next config 5 s5_457 = [] := by decide
theorem s5_457_safe : Safe 8 5 s5_457 := by
  apply safe_succ 7 5 s5_457 [] (by decide) s5_457_edges
  simp
def s5_458 : State := ⟨[1,4,108,146], 111504066275364916837566665846138014118510870, 0, 0, 1, 0⟩
theorem s5_458_edges : next config 5 s5_458 = [] := by decide
theorem s5_458_safe : Safe 8 5 s5_458 := by
  apply safe_succ 7 5 s5_458 [] (by decide) s5_458_edges
  simp
def s5_459 : State := ⟨[1,4,108,162], 5846006551025023852299623072793113404557391626518, 0, 0, 1, 0⟩
theorem s5_459_edges : next config 5 s5_459 = [] := by decide
theorem s5_459_safe : Safe 8 5 s5_459 := by
  apply safe_succ 7 5 s5_459 [] (by decide) s5_459_edges
  simp
def s5_460 : State := ⟨[1,4,108,162], 7307508186994797302819554051655897994486251323670, 0, 0, 1, 0⟩
theorem s5_460_edges : next config 5 s5_460 = [] := by decide
theorem s5_460_safe : Safe 8 5 s5_460 := by
  apply safe_succ 7 5 s5_460 [] (by decide) s5_460_edges
  simp
def s5_461 : State := ⟨[1,4,108,176], 95780971326419139128639113468318116731715763231064342, 0, 0, 1, 0⟩
theorem s5_461_edges : next config 5 s5_461 = [] := by decide
theorem s5_461_safe : Safe 8 5 s5_461 := by
  apply safe_succ 7 5 s5_461 [] (by decide) s5_461_edges
  simp
def s5_462 : State := ⟨[1,4,108,176], 95782432805755724833026694011615114742087057657626902, 0, 0, 1, 0⟩
theorem s5_462_edges : next config 5 s5_462 = [] := by decide
theorem s5_462_safe : Safe 8 5 s5_462 := by
  apply safe_succ 7 5 s5_462 [] (by decide) s5_462_edges
  simp
def s5_463 : State := ⟨[1,4,108,193], 12554203470773361528692426292058339647205942999998194057494, 0, 0, 1, 0⟩
theorem s5_463_edges : next config 5 s5_463 = [] := by decide
theorem s5_463_safe : Safe 8 5 s5_463 := by
  apply safe_succ 7 5 s5_463 [] (by decide) s5_463_edges
  simp
def s5_464 : State := ⟨[1,4,108,193], 18831305206160042291847650981424129136381549229598692147478, 0, 0, 1, 0⟩
theorem s5_464_edges : next config 5 s5_464 = [] := by decide
theorem s5_464_safe : Safe 8 5 s5_464 := by
  apply safe_succ 7 5 s5_464 [] (by decide) s5_464_edges
  simp
def s5_465 : State := ⟨[1,4,108,194], 25108406941546723057044569872315549406337403103789799506198, 0, 0, 1, 0⟩
theorem s5_465_edges : next config 5 s5_465 = [s6_361] := by decide
theorem s5_465_safe : Safe 8 5 s5_465 := by
  apply safe_succ 7 5 s5_465 [s6_361] (by decide) s5_465_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_361_safe
def s5_466 : State := ⟨[1,4,108,194], 31385508676933403819519229827839461968586260118526761173270, 0, 0, 1, 0⟩
theorem s5_466_edges : next config 5 s5_466 = [s6_362] := by decide
theorem s5_466_safe : Safe 8 5 s5_466 := by
  apply safe_succ 7 5 s5_466 [s6_362] (by decide) s5_466_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_362_safe
def s5_467 : State := ⟨[1,4,108,208], 411376139330301510561043381120580050517107759163939533931741462, 0, 0, 1, 0⟩
theorem s5_467_edges : next config 5 s5_467 = [s6_363] := by decide
theorem s5_467_safe : Safe 8 5 s5_467 := by
  apply safe_succ 7 5 s5_467 [s6_363] (by decide) s5_467_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_363_safe
def s5_468 : State := ⟨[1,4,108,208], 411382416432036897219506471711472635041988143246735636460273942, 0, 0, 1, 0⟩
theorem s5_468_edges : next config 5 s5_468 = [s6_364] := by decide
theorem s5_468_safe : Safe 8 5 s5_468 := by
  apply safe_succ 7 5 s5_468 [s6_364] (by decide) s5_468_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_364_safe
def s5_469 : State := ⟨[1,4,112,129], 1020852293138902087750463434463182393622, 2, 2, 1, 0⟩
theorem s5_469_edges : next config 5 s5_469 = [s6_371] := by decide
theorem s5_469_safe : Safe 8 5 s5_469 := by
  apply safe_succ 7 5 s5_469 [s6_371] (by decide) s5_469_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_371_safe
def s5_470 : State := ⟨[1,4,112,130], 1701417026980779014677212649326718816534, 2, 2, 1, 0⟩
theorem s5_470_edges : next config 5 s5_470 = [] := by decide
theorem s5_470_safe : Safe 8 5 s5_470 := by
  apply safe_succ 7 5 s5_470 [] (by decide) s5_470_edges
  simp
def s5_471 : State := ⟨[1,4,112,132], 5784805430032040576237707938507937354006, 2, 2, 1, 0⟩
theorem s5_471_edges : next config 5 s5_471 = [] := by decide
theorem s5_471_safe : Safe 8 5 s5_471 := by
  apply safe_succ 7 5 s5_471 [] (by decide) s5_471_edges
  simp
def s5_472 : State := ⟨[1,4,112,136], 87452573491057271807447613722132308103446, 2, 2, 1, 0⟩
theorem s5_472_edges : next config 5 s5_472 = [] := by decide
theorem s5_472_safe : Safe 8 5 s5_472 := by
  apply safe_succ 7 5 s5_472 [] (by decide) s5_472_edges
  simp
def s5_473 : State := ⟨[1,4,112,136], 1481249148399221218153430005762654902223126, 2, 2, 1, 0⟩
theorem s5_473_edges : next config 5 s5_473 = [] := by decide
theorem s5_473_safe : Safe 8 5 s5_473 := by
  apply safe_succ 7 5 s5_473 [] (by decide) s5_473_edges
  simp
def s5_474 : State := ⟨[1,4,112,140], 1394136862467460971506806106260122240094486, 2, 2, 1, 0⟩
theorem s5_474_edges : next config 5 s5_474 = [] := by decide
theorem s5_474_safe : Safe 8 5 s5_474 := by
  apply safe_succ 7 5 s5_474 [] (by decide) s5_474_edges
  simp
def s5_475 : State := ⟨[1,4,112,144], 22301085486089920166696541986867961151951126, 2, 2, 1, 0⟩
theorem s5_475_edges : next config 5 s5_475 = [s6_372] := by decide
theorem s5_475_safe : Safe 8 5 s5_475 := by
  apply safe_succ 7 5 s5_475 [s6_372] (by decide) s5_475_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_372_safe
def s5_476 : State := ⟨[1,4,112,145], 44601830684620543308232260259516322658058518, 1, 1, 1, 0⟩
theorem s5_476_edges : next config 5 s5_476 = [s6_527] := by decide
theorem s5_476_safe : Safe 8 5 s5_476 := by
  apply safe_succ 7 5 s5_476 [s6_527] (by decide) s5_476_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_527_safe
def s5_477 : State := ⟨[1,4,112,160], 1461501637671190477500709993539997239255578513686, 2, 2, 1, 0⟩
theorem s5_477_edges : next config 5 s5_477 = [] := by decide
theorem s5_477_safe : Safe 8 5 s5_477 := by
  apply safe_succ 7 5 s5_477 [] (by decide) s5_477_edges
  simp
def s5_478 : State := ⟨[1,4,112,192], 6277101735386680764176076982504691576926069664063680483606, 2, 2, 1, 0⟩
theorem s5_478_edges : next config 5 s5_478 = [s6_374] := by decide
theorem s5_478_safe : Safe 8 5 s5_478 := by
  apply safe_succ 7 5 s5_478 [s6_374] (by decide) s5_478_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_374_safe
def s5_479 : State := ⟨[1,4,112,224], 26959946667150639794667015087359918232934169583364286700703256219926, 2, 2, 1, 0⟩
theorem s5_479_edges : next config 5 s5_479 = [] := by decide
theorem s5_479_safe : Safe 8 5 s5_479 := by
  apply safe_succ 7 5 s5_479 [] (by decide) s5_479_edges
  simp
def s5_480 : State := ⟨[1,4,112,240], 1766847064778384329583297500742918856115043193900779781835825800938590486, 2, 2, 1, 0⟩
theorem s5_480_edges : next config 5 s5_480 = [] := by decide
theorem s5_480_safe : Safe 8 5 s5_480 := by
  apply safe_succ 7 5 s5_480 [] (by decide) s5_480_edges
  simp
def s5_481 : State := ⟨[1,4,113,145], 44601830689812840166767087888046818987278614, 1, 1, 1, 0⟩
theorem s5_481_edges : next config 5 s5_481 = [s6_706, s6_528] := by decide
theorem s5_481_safe : Safe 8 5 s5_481 := by
  apply safe_succ 7 5 s5_481 [s6_706, s6_528] (by decide) s5_481_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_706_safe
  · subst z; exact s6_528_safe
def s5_482 : State := ⟨[1,4,120,145], 44602512573410366521143883954431697396760854, 0, 0, 1, 0⟩
theorem s5_482_edges : next config 5 s5_482 = [] := by decide
theorem s5_482_safe : Safe 8 5 s5_482 := by
  apply safe_succ 7 5 s5_482 [] (by decide) s5_482_edges
  simp
def s5_483 : State := ⟨[1,4,120,145], 66902577207207147785752675477865195366318358, 0, 0, 1, 0⟩
theorem s5_483_edges : next config 5 s5_483 = [] := by decide
theorem s5_483_safe : Safe 8 5 s5_483 := by
  apply safe_succ 7 5 s5_483 [] (by decide) s5_483_edges
  simp
def s5_484 : State := ⟨[1,4,120,194], 25108406941546723057045898775792780663783580127694059274518, 0, 0, 1, 0⟩
theorem s5_484_edges : next config 5 s5_484 = [s6_381, s6_376] := by decide
theorem s5_484_safe : Safe 8 5 s5_484 := by
  apply safe_succ 7 5 s5_484 [s6_381, s6_376] (by decide) s5_484_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_381_safe
  · subst z; exact s6_376_safe
def s5_485 : State := ⟨[1,4,120,194], 31385508676933403819520558731316693226032437142431020941590, 0, 0, 1, 0⟩
theorem s5_485_edges : next config 5 s5_485 = [s6_383, s6_377] := by decide
theorem s5_485_safe : Safe 8 5 s5_485 := by
  apply safe_succ 7 5 s5_485 [s6_383, s6_377] (by decide) s5_485_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_383_safe
  · subst z; exact s6_377_safe
def s5_486 : State := ⟨[1,4,170,194], 25108408438124399683889157788370264449384488448308702937366, 0, 0, 1, 0⟩
theorem s5_486_edges : next config 5 s5_486 = [s6_382] := by decide
theorem s5_486_safe : Safe 8 5 s5_486 := by
  apply safe_succ 7 5 s5_486 [s6_382] (by decide) s5_486_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_382_safe
def s5_487 : State := ⟨[1,4,170,194], 31385510173511080446363817743894177011633345463045664604438, 0, 0, 1, 0⟩
theorem s5_487_edges : next config 5 s5_487 = [s6_384] := by decide
theorem s5_487_safe : Safe 8 5 s5_487 := by
  apply safe_succ 7 5 s5_487 [s6_384] (by decide) s5_487_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_384_safe
def s5_488 : State := ⟨[1,4,193,145], 12554203470773406130182823008424431294049826752024390209814, 2, 2, 1, 0⟩
theorem s5_488_edges : next config 5 s5_488 = [] := by decide
theorem s5_488_safe : Safe 8 5 s5_488 := by
  apply safe_succ 7 5 s5_488 [] (by decide) s5_488_edges
  simp
def s5_489 : State := ⟨[1,4,194,104], 25108406947392729606368181220611735078775808399257509101846, 0, 0, 1, 0⟩
theorem s5_489_edges : next config 5 s5_489 = [s6_529] := by decide
theorem s5_489_safe : Safe 8 5 s5_489 := by
  apply safe_succ 7 5 s5_489 [s6_529] (by decide) s5_489_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_529_safe
def s5_490 : State := ⟨[1,4,194,146], 25108406941546812260025363649927924124617832152539007619350, 2, 2, 1, 0⟩
theorem s5_490_edges : next config 5 s5_490 = [] := by decide
theorem s5_490_safe : Safe 8 5 s5_490 := by
  apply safe_succ 7 5 s5_490 [] (by decide) s5_490_edges
  simp
def s5_491 : State := ⟨[1,4,194,162], 25108406947392729606368181200250097312609873637716713869590, 2, 2, 1, 0⟩
theorem s5_491_edges : next config 5 s5_491 = [s6_138, s6_391] := by decide
theorem s5_491_safe : Safe 8 5 s5_491 := by
  apply safe_succ 7 5 s5_491 [s6_138, s6_391] (by decide) s5_491_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_138_safe
  · subst z; exact s6_391_safe
def s5_492 : State := ⟨[1,4,208,145], 411376139330301510605644871517296416608754603047691560127893782, 2, 2, 1, 0⟩
theorem s5_492_edges : next config 5 s5_492 = [s6_397] := by decide
theorem s5_492_safe : Safe 8 5 s5_492 := by
  apply safe_succ 7 5 s5_492 [s6_397] (by decide) s5_492_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_397_safe
def s5_493 : State := ⟨[1,4,209,145], 822752278660603021122087102522837261589829777932653027995488534, 2, 2, 1, 0⟩
theorem s5_493_edges : next config 5 s5_493 = [] := by decide
theorem s5_493_safe : Safe 8 5 s5_493 := by
  apply safe_succ 7 5 s5_493 [] (by decide) s5_493_edges
  simp
def s5_494 : State := ⟨[1,4,209,145], 822752278660603021144387167156634042854438569456086525965046038, 2, 2, 1, 0⟩
theorem s5_494_edges : next config 5 s5_494 = [] := by decide
theorem s5_494_safe : Safe 8 5 s5_494 := by
  apply safe_succ 7 5 s5_494 [] (by decide) s5_494_edges
  simp
def s5_495 : State := ⟨[1,4,210,130], 1645504557321206042154970883969185109676262126772975729368961302, 2, 2, 1, 0⟩
theorem s5_495_edges : next config 5 s5_495 = [] := by decide
theorem s5_495_safe : Safe 8 5 s5_495 := by
  apply safe_succ 7 5 s5_495 [] (by decide) s5_495_edges
  simp
def s5_496 : State := ⟨[1,4,210,130], 1645529665728147588878026227126877940340717610375138956332306710, 2, 2, 1, 0⟩
theorem s5_496_edges : next config 5 s5_496 = [] := by decide
theorem s5_496_safe : Safe 8 5 s5_496 := by
  apply safe_succ 7 5 s5_496 [] (by decide) s5_496_edges
  simp
def s5_497 : State := ⟨[1,4,210,130], 27973577474460502716634477804886793189400035976910253542946701590, 2, 2, 1, 0⟩
theorem s5_497_edges : next config 5 s5_497 = [] := by decide
theorem s5_497_safe : Safe 8 5 s5_497 := by
  apply safe_succ 7 5 s5_497 [] (by decide) s5_497_edges
  simp
def s5_498 : State := ⟨[1,4,210,130], 27973602582867444263357533148044486020064491460512416769910046998, 2, 2, 1, 0⟩
theorem s5_498_edges : next config 5 s5_498 = [] := by decide
theorem s5_498_safe : Safe 8 5 s5_498 := by
  apply safe_succ 7 5 s5_498 [] (by decide) s5_498_edges
  simp
def s5_499 : State := ⟨[1,4,210,144], 1645504557321206042177270268038248049062735139514556029465596182, 2, 2, 1, 0⟩
theorem s5_499_edges : next config 5 s5_499 = [s6_396] := by decide
theorem s5_499_safe : Safe 8 5 s5_499 := by
  apply safe_succ 7 5 s5_499 [s6_396] (by decide) s5_499_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_396_safe
def s5_500 : State := ⟨[1,4,210,144], 2056880696651507552716012563677585675308419032135974700464541974, 2, 2, 1, 0⟩
theorem s5_500_edges : next config 5 s5_500 = [s6_397] := by decide
theorem s5_500_safe : Safe 8 5 s5_500 := by
  apply safe_succ 7 5 s5_500 [s6_397] (by decide) s5_500_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_397_safe
def s5_501 : State := ⟨[1,4,210,144], 27973577474460502716656777188955856128786508989651833843043336470, 2, 2, 1, 0⟩
theorem s5_501_edges : next config 5 s5_501 = [s6_398] := by decide
theorem s5_501_safe : Safe 8 5 s5_501 := by
  apply safe_succ 7 5 s5_501 [s6_398] (by decide) s5_501_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_398_safe
def s5_502 : State := ⟨[1,4,210,144], 28384953613790804227195519484595193755032192882273252514042282262, 2, 2, 1, 0⟩
theorem s5_502_edges : next config 5 s5_502 = [s6_399] := by decide
theorem s5_502_safe : Safe 8 5 s5_502 := by
  apply safe_succ 7 5 s5_502 [s6_399] (by decide) s5_502_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_399_safe
def s5_503 : State := ⟨[1,4,210,146], 1645504557321206042244173864763307602241196074043954546218176790, 2, 2, 1, 0⟩
theorem s5_503_edges : next config 5 s5_503 = [] := by decide
theorem s5_503_safe : Safe 8 5 s5_503 := by
  apply safe_succ 7 5 s5_503 [] (by decide) s5_503_edges
  simp
def s5_504 : State := ⟨[1,4,210,146], 1645504557321206042266473248832370541628877938818173180651311382, 2, 2, 1, 0⟩
theorem s5_504_edges : next config 5 s5_504 = [] := by decide
theorem s5_504_safe : Safe 8 5 s5_504 := by
  apply safe_succ 7 5 s5_504 [] (by decide) s5_504_edges
  simp
def s5_505 : State := ⟨[1,4,210,146], 27973577474460502716723680785680915681964969924181232359795917078, 2, 2, 1, 0⟩
theorem s5_505_edges : next config 5 s5_505 = [] := by decide
theorem s5_505_safe : Safe 8 5 s5_505 := by
  apply safe_succ 7 5 s5_505 [] (by decide) s5_505_edges
  simp
def s5_506 : State := ⟨[1,4,210,146], 27973577474460502716745980169749978621352651788955450994229051670, 2, 2, 1, 0⟩
theorem s5_506_edges : next config 5 s5_506 = [] := by decide
theorem s5_506_safe : Safe 8 5 s5_506 := by
  apply safe_succ 7 5 s5_506 [] (by decide) s5_506_edges
  simp
def s5_507 : State := ⟨[1,4,214,145], 27973577474460502716701378679352917375069580426197130566055297302, 0, 0, 1, 0⟩
theorem s5_507_edges : next config 5 s5_507 = [] := by decide
theorem s5_507_safe : Safe 8 5 s5_507 := by
  apply safe_succ 7 5 s5_507 [] (by decide) s5_507_edges
  simp
def s5_508 : State := ⟨[1,4,214,145], 28384953613790804227240120974992255001315264318818549237054243094, 0, 0, 1, 0⟩
theorem s5_508_edges : next config 5 s5_508 = [] := by decide
theorem s5_508_safe : Safe 8 5 s5_508 := by
  apply safe_succ 7 5 s5_508 [] (by decide) s5_508_edges
  simp
def s5_509 : State := ⟨[1,4,214,146], 26328072917139296675995959295829525058040520027997147632830054678, 2, 2, 1, 0⟩
theorem s5_509_edges : next config 5 s5_509 = [] := by decide
theorem s5_509_safe : Safe 8 5 s5_509 := by
  apply safe_succ 7 5 s5_509 [] (by decide) s5_509_edges
  simp
def s5_510 : State := ⟨[1,4,214,146], 26328072917139296676018258679898587997428201892771366267263189270, 2, 2, 1, 0⟩
theorem s5_510_edges : next config 5 s5_510 = [] := by decide
theorem s5_510_safe : Safe 8 5 s5_510 := by
  apply safe_succ 7 5 s5_510 [] (by decide) s5_510_edges
  simp
def s5_511 : State := ⟨[1,4,225,129], 53919893334301279589334030175060108448116332398003979866174073671958, 2, 2, 1, 0⟩
theorem s5_511_edges : next config 5 s5_511 = [s6_400] := by decide
theorem s5_511_safe : Safe 8 5 s5_511 := by
  apply safe_succ 7 5 s5_511 [s6_400] (by decide) s5_511_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_400_safe
def s5_512 : State := ⟨[1,4,228,132], 431359146674410236714672241398098891015929492802059239105669372117278, 1, 1, 1, 0⟩
theorem s5_512_edges : next config 5 s5_512 = [] := by decide
theorem s5_512_safe : Safe 8 5 s5_512 := by
  apply safe_succ 7 5 s5_512 [] (by decide) s5_512_edges
  simp
def s5_513 : State := ⟨[1,4,228,132], 431359146674410236714672241398098891015929492802096132593816791220502, 1, 1, 1, 0⟩
theorem s5_513_edges : next config 5 s5_513 = [] := by decide
theorem s5_513_safe : Safe 8 5 s5_513 := by
  apply safe_succ 7 5 s5_513 [] (by decide) s5_513_edges
  simp
def s5_514 : State := ⟨[1,4,240,144], 1766847064778384329583297500765219601308381520183780672479943666115350806, 2, 2, 1, 0⟩
theorem s5_514_edges : next config 5 s5_514 = [s6_403] := by decide
theorem s5_514_safe : Safe 8 5 s5_514 := by
  apply safe_succ 7 5 s5_514 [s6_403] (by decide) s5_514_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_403_safe
def s5_515 : State := ⟨[1,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914077974, 1, 1, 1, 0⟩
theorem s5_515_edges : next config 5 s5_515 = [s6_707, s6_530] := by decide
theorem s5_515_safe : Safe 8 5 s5_515 := by
  apply safe_succ 7 5 s5_515 [s6_707, s6_530] (by decide) s5_515_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_707_safe
  · subst z; exact s6_530_safe
def s5_516 : State := ⟨[1,4,248,145], 452312848583266388373324160190254042627713856752159290081705245665996636438, 0, 0, 1, 0⟩
theorem s5_516_edges : next config 5 s5_516 = [] := by decide
theorem s5_516_safe : Safe 8 5 s5_516 := by
  apply safe_succ 7 5 s5_516 [] (by decide) s5_516_edges
  simp
def s5_517 : State := ⟨[1,4,249,145], 904625697166532776746648320380418882614915937571053134569312999698937741590, 0, 0, 1, 0⟩
theorem s5_517_edges : next config 5 s5_517 = [s6_708] := by decide
theorem s5_517_safe : Safe 8 5 s5_517 := by
  apply safe_succ 7 5 s5_517 [s6_708] (by decide) s5_517_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_708_safe
def s5_518 : State := ⟨[1,4,249,145], 904625697166532776746648320380441182679549734352317743360836433196907299094, 0, 0, 1, 0⟩
theorem s5_518_edges : next config 5 s5_518 = [s6_709] := by decide
theorem s5_518_safe : Safe 8 5 s5_518 := by
  apply safe_succ 7 5 s5_518 [s6_709] (by decide) s5_518_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_709_safe
def s5_519 : State := ⟨[1,12,64,145], 44602511244162009098461845115863096321184030, 3, 1, 1, 0⟩
theorem s5_519_edges : next config 5 s5_519 = [s6_0, s6_431] := by decide
theorem s5_519_safe : Safe 8 5 s5_519 := by
  apply safe_succ 7 5 s5_519 [s6_0, s6_431] (by decide) s5_519_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_0_safe
  · subst z; exact s6_431_safe
def s5_520 : State := ⟨[1,12,64,145], 44602511244162009098461845115863104911118614, 3, 1, 1, 0⟩
theorem s5_520_edges : next config 5 s5_520 = [s6_1, s6_432] := by decide
theorem s5_520_safe : Safe 8 5 s5_520 := by
  apply safe_succ 7 5 s5_520 [s6_1, s6_432] (by decide) s5_520_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1_safe
  · subst z; exact s6_432_safe
def s5_521 : State := ⟨[1,12,64,145], 44602511244162009098461882009351243740287254, 3, 1, 1, 0⟩
theorem s5_521_edges : next config 5 s5_521 = [s6_2, s6_433] := by decide
theorem s5_521_safe : Safe 8 5 s5_521 := by
  apply safe_succ 7 5 s5_521 [s6_2, s6_433] (by decide) s5_521_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_2_safe
  · subst z; exact s6_433_safe
def s5_522 : State := ⟨[1,12,64,145], 66902575877958790363070636639296594290741534, 3, 1, 1, 0⟩
theorem s5_522_edges : next config 5 s5_522 = [s6_3, s6_435] := by decide
theorem s5_522_safe : Safe 8 5 s5_522 := by
  apply safe_succ 7 5 s5_522 [s6_3, s6_435] (by decide) s5_522_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_3_safe
  · subst z; exact s6_435_safe
def s5_523 : State := ⟨[1,12,64,145], 66902575877958790363070636639296602880676118, 3, 1, 1, 0⟩
theorem s5_523_edges : next config 5 s5_523 = [s6_4, s6_436] := by decide
theorem s5_523_safe : Safe 8 5 s5_523 := by
  apply safe_succ 7 5 s5_523 [s6_4, s6_436] (by decide) s5_523_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_4_safe
  · subst z; exact s6_436_safe
def s5_524 : State := ⟨[1,12,64,145], 66902575877958790363070673532784741709844758, 3, 1, 1, 0⟩
theorem s5_524_edges : next config 5 s5_524 = [s6_5, s6_437] := by decide
theorem s5_524_safe : Safe 8 5 s5_524 := by
  apply safe_succ 7 5 s5_524 [s6_5, s6_437] (by decide) s5_524_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_5_safe
  · subst z; exact s6_437_safe
def s5_525 : State := ⟨[1,12,64,146], 89204682205957097258460208410374682869567774, 3, 1, 1, 0⟩
theorem s5_525_edges : next config 5 s5_525 = [s6_6, s6_439] := by decide
theorem s5_525_safe : Safe 8 5 s5_525 := by
  apply safe_succ 7 5 s5_525 [s6_6, s6_439] (by decide) s5_525_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_6_safe
  · subst z; exact s6_439_safe
def s5_526 : State := ⟨[1,12,64,146], 89204682205957097258460245303862830288670998, 3, 1, 1, 0⟩
theorem s5_526_edges : next config 5 s5_526 = [s6_7, s6_440] := by decide
theorem s5_526_safe : Safe 8 5 s5_526 := by
  apply safe_succ 7 5 s5_526 [s6_7, s6_440] (by decide) s5_526_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_7_safe
  · subst z; exact s6_440_safe
def s5_527 : State := ⟨[1,12,64,146], 89207404464892464766167915407234137015259414, 3, 1, 1, 0⟩
theorem s5_527_edges : next config 5 s5_527 = [s6_8, s6_441] := by decide
theorem s5_527_safe : Safe 8 5 s5_527 := by
  apply safe_succ 7 5 s5_527 [s6_8, s6_441] (by decide) s5_527_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_8_safe
  · subst z; exact s6_441_safe
def s5_528 : State := ⟨[1,12,64,146], 111504066275020036646142073184593317302702366, 3, 1, 1, 0⟩
theorem s5_528_edges : next config 5 s5_528 = [s6_9, s6_442] := by decide
theorem s5_528_safe : Safe 8 5 s5_528 := by
  apply safe_succ 7 5 s5_528 [s6_9, s6_442] (by decide) s5_528_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_9_safe
  · subst z; exact s6_442_safe
def s5_529 : State := ⟨[1,12,64,146], 111504066275020036646142110078081464721805590, 3, 1, 1, 0⟩
theorem s5_529_edges : next config 5 s5_529 = [s6_10, s6_443] := by decide
theorem s5_529_safe : Safe 8 5 s5_529 := by
  apply safe_succ 7 5 s5_529 [s6_10, s6_443] (by decide) s5_529_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_10_safe
  · subst z; exact s6_443_safe
def s5_530 : State := ⟨[1,12,64,162], 5846006551025023507419431648200451859860575818014, 3, 1, 1, 0⟩
theorem s5_530_edges : next config 5 s5_530 = [s6_11, s6_444] := by decide
theorem s5_530_safe : Safe 8 5 s5_530 := by
  apply safe_succ 7 5 s5_530 [s6_11, s6_444] (by decide) s5_530_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_11_safe
  · subst z; exact s6_444_safe
def s5_531 : State := ⟨[1,12,64,162], 5846006551025023507419431648237345348007994921238, 3, 1, 1, 0⟩
theorem s5_531_edges : next config 5 s5_531 = [s6_12, s6_445] := by decide
theorem s5_531_safe : Safe 8 5 s5_531 := by
  apply safe_succ 7 5 s5_531 [s6_12, s6_445] (by decide) s5_531_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_12_safe
  · subst z; exact s6_445_safe
def s5_532 : State := ⟨[1,12,64,162], 5846006553747282442786939355907448719314721509654, 3, 1, 1, 0⟩
theorem s5_532_edges : next config 5 s5_532 = [s6_13, s6_447] := by decide
theorem s5_532_safe : Safe 8 5 s5_532 := by
  apply safe_succ 7 5 s5_532 [s6_13, s6_447] (by decide) s5_532_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_13_safe
  · subst z; exact s6_447_safe
def s5_533 : State := ⟨[1,12,64,162], 7307508186994796957939362627063236449789435515166, 3, 1, 1, 0⟩
theorem s5_533_edges : next config 5 s5_533 = [s6_14, s6_448] := by decide
theorem s5_533_safe : Safe 8 5 s5_533 := by
  apply safe_succ 7 5 s5_533 [s6_14, s6_448] (by decide) s5_533_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_14_safe
  · subst z; exact s6_448_safe
def s5_534 : State := ⟨[1,12,64,162], 7307508186994796957939362627100129937936854618390, 3, 1, 1, 0⟩
theorem s5_534_edges : next config 5 s5_534 = [s6_15, s6_449] := by decide
theorem s5_534_safe : Safe 8 5 s5_534 := by
  apply safe_succ 7 5 s5_534 [s6_15, s6_449] (by decide) s5_534_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_15_safe
  · subst z; exact s6_449_safe
def s5_535 : State := ⟨[1,12,64,162], 17538019649672246853048910309930716017108036161814, 3, 1, 1, 0⟩
theorem s5_535_edges : next config 5 s5_535 = [s6_16, s6_451] := by decide
theorem s5_535_safe : Safe 8 5 s5_535 := by
  apply safe_succ 7 5 s5_535 [s6_16, s6_451] (by decide) s5_535_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_16_safe
  · subst z; exact s6_451_safe
def s5_536 : State := ⟨[1,12,64,162], 18999521285642020303568841288793500607036895858966, 3, 1, 1, 0⟩
theorem s5_536_edges : next config 5 s5_536 = [s6_17, s6_452] := by decide
theorem s5_536_safe : Safe 8 5 s5_536 := by
  apply safe_succ 7 5 s5_536 [s6_17, s6_452] (by decide) s5_536_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_17_safe
  · subst z; exact s6_452_safe
def s5_537 : State := ⟨[1,12,64,163], 11692013100348635180234170979065583938492895924502, 3, 1, 1, 0⟩
theorem s5_537_edges : next config 5 s5_537 = [s6_18, s6_453] := by decide
theorem s5_537_safe : Safe 8 5 s5_537 := by
  apply safe_succ 7 5 s5_537 [s6_18, s6_453] (by decide) s5_537_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_18_safe
  · subst z; exact s6_453_safe
def s5_538 : State := ⟨[1,12,64,163], 11692013101709764647917924832919082368211378835742, 3, 1, 1, 0⟩
theorem s5_538_edges : next config 5 s5_538 = [s6_19, s6_454] := by decide
theorem s5_538_safe : Safe 8 5 s5_538 := by
  apply safe_succ 7 5 s5_538 [s6_19, s6_454] (by decide) s5_538_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_19_safe
  · subst z; exact s6_454_safe
def s5_539 : State := ⟨[1,12,64,163], 13153514736318408630754101957928368528413165687070, 3, 1, 1, 0⟩
theorem s5_539_edges : next config 5 s5_539 = [s6_20, s6_455] := by decide
theorem s5_539_safe : Safe 8 5 s5_539 := by
  apply safe_succ 7 5 s5_539 [s6_20, s6_455] (by decide) s5_539_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_20_safe
  · subst z; exact s6_455_safe
def s5_540 : State := ⟨[1,12,64,163], 14615016373649311548957786790644651548077688164630, 3, 1, 1, 0⟩
theorem s5_540_edges : next config 5 s5_540 = [s6_21, s6_456] := by decide
theorem s5_540_safe : Safe 8 5 s5_540 := by
  apply safe_succ 7 5 s5_540 [s6_21, s6_456] (by decide) s5_540_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_21_safe
  · subst z; exact s6_456_safe
def s5_541 : State := ⟨[1,12,64,176], 95780971326419139128294233276893524070171066415255838, 3, 1, 1, 0⟩
theorem s5_541_edges : next config 5 s5_541 = [s6_22, s6_457] := by decide
theorem s5_541_safe : Safe 8 5 s5_541 := by
  apply safe_succ 7 5 s5_541 [s6_22, s6_457] (by decide) s5_541_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_22_safe
  · subst z; exact s6_457_safe
def s5_542 : State := ⟨[1,12,64,176], 95780971326419139128294233276893560963659213834359062, 3, 1, 1, 0⟩
theorem s5_542_edges : next config 5 s5_542 = [s6_23, s6_458] := by decide
theorem s5_542_safe : Safe 8 5 s5_542 := by
  apply safe_succ 7 5 s5_542 [s6_23, s6_458] (by decide) s5_542_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_23_safe
  · subst z; exact s6_458_safe
def s5_543 : State := ⟨[1,12,64,176], 95782432805755724832681813820190522080542360841818398, 3, 1, 1, 0⟩
theorem s5_543_edges : next config 5 s5_543 = [s6_24, s6_459] := by decide
theorem s5_543_safe : Safe 8 5 s5_543 := by
  apply safe_succ 7 5 s5_543 [s6_24, s6_459] (by decide) s5_543_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_24_safe
  · subst z; exact s6_459_safe
def s5_544 : State := ⟨[1,12,64,176], 95782432805755724832681813820190558974030508260921622, 3, 1, 1, 0⟩
theorem s5_544_edges : next config 5 s5_544 = [s6_25, s6_460] := by decide
theorem s5_544_safe : Safe 8 5 s5_544 := by
  apply safe_succ 7 5 s5_544 [s6_25, s6_460] (by decide) s5_544_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_25_safe
  · subst z; exact s6_460_safe
def s5_545 : State := ⟨[1,12,65,145], 44601830679428167221534955260136380203995414, 3, 1, 1, 0⟩
theorem s5_545_edges : next config 5 s5_545 = [s6_26, s6_414] := by decide
theorem s5_545_safe : Safe 8 5 s5_545 := by
  apply safe_succ 7 5 s5_545 [s6_26, s6_414] (by decide) s5_545_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_26_safe
  · subst z; exact s6_414_safe
def s5_546 : State := ⟨[1,12,66,145], 44601830679428167221534992153624527623098646, 3, 1, 1, 0⟩
theorem s5_546_edges : next config 5 s5_546 = [s6_28, s6_415, s6_429] := by decide
theorem s5_546_safe : Safe 8 5 s5_546 := by
  apply safe_succ 7 5 s5_546 [s6_28, s6_415, s6_429] (by decide) s5_546_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_28_safe
  · subst z; exact s6_415_safe
  · subst z; exact s6_429_safe
def s5_547 : State := ⟨[1,12,67,129], 1020847100762815390556144518962985636126, 3, 1, 1, 0⟩
theorem s5_547_edges : next config 5 s5_547 = [s6_30, s6_416] := by decide
theorem s5_547_safe : Safe 8 5 s5_547 := by
  apply safe_succ 7 5 s5_547 [s6_30, s6_416] (by decide) s5_547_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_30_safe
  · subst z; exact s6_416_safe
def s5_548 : State := ⟨[1,12,67,130], 1701411834604692317482893733826522059038, 3, 1, 1, 0⟩
theorem s5_548_edges : next config 5 s5_548 = [s6_31, s6_421, s6_423] := by decide
theorem s5_548_safe : Safe 8 5 s5_548 := by
  apply safe_succ 7 5 s5_548 [s6_31, s6_421, s6_423] (by decide) s5_548_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_31_safe
  · subst z; exact s6_421_safe
  · subst z; exact s6_423_safe
def s5_549 : State := ⟨[1,12,67,131], 3062541302288446171336392163553594904862, 3, 1, 1, 0⟩
theorem s5_549_edges : next config 5 s5_549 = [s6_32, s6_425] := by decide
theorem s5_549_safe : Safe 8 5 s5_549 := by
  apply safe_succ 7 5 s5_549 [s6_32, s6_425] (by decide) s5_549_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_32_safe
  · subst z; exact s6_425_safe
def s5_550 : State := ⟨[1,12,67,132], 5784800237655953879043389023007740596510, 3, 1, 1, 0⟩
theorem s5_550_edges : next config 5 s5_550 = [s6_33] := by decide
theorem s5_550_safe : Safe 8 5 s5_550 := by
  apply safe_succ 7 5 s5_550 [s6_33] (by decide) s5_550_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_33_safe
def s5_551 : State := ⟨[1,12,67,136], 87452568298681185110253294806632111345950, 3, 1, 1, 0⟩
theorem s5_551_edges : next config 5 s5_551 = [s6_34] := by decide
theorem s5_551_safe : Safe 8 5 s5_551 := by
  apply safe_succ 7 5 s5_551 [s6_34] (by decide) s5_551_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_34_safe
def s5_552 : State := ⟨[1,12,67,140], 1394136857275084884809611787344622043336990, 3, 1, 1, 0⟩
theorem s5_552_edges : next config 5 s5_552 = [s6_36] := by decide
theorem s5_552_safe : Safe 8 5 s5_552 := by
  apply safe_succ 7 5 s5_552 [s6_36] (by decide) s5_552_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_36_safe
def s5_553 : State := ⟨[1,12,67,144], 22301085480897544079999347667952460955193630, 3, 1, 1, 0⟩
theorem s5_553_edges : next config 5 s5_553 = [s6_37, s6_417, s6_422, s6_427] := by decide
theorem s5_553_safe : Safe 8 5 s5_553 := by
  apply safe_succ 7 5 s5_553 [s6_37, s6_417, s6_422, s6_427] (by decide) s5_553_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_37_safe
  · subst z; exact s6_417_safe
  · subst z; exact s6_422_safe
  · subst z; exact s6_427_safe
def s5_554 : State := ⟨[1,12,67,145], 44602511244162009098462029583303833416700182, 2, 0, 1, 0⟩
theorem s5_554_edges : next config 5 s5_554 = [s6_40] := by decide
theorem s5_554_safe : Safe 8 5 s5_554 := by
  apply safe_succ 7 5 s5_554 [s6_40] (by decide) s5_554_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_40_safe
def s5_555 : State := ⟨[1,12,67,145], 44602511244162009098462066476791980835803414, 2, 0, 1, 0⟩
theorem s5_555_edges : next config 5 s5_555 = [s6_41] := by decide
theorem s5_555_safe : Safe 8 5 s5_555 := by
  apply safe_succ 7 5 s5_555 [s6_41] (by decide) s5_555_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_41_safe
def s5_556 : State := ⟨[1,12,67,145], 66902575877958790363070821106737331386257686, 2, 0, 1, 0⟩
theorem s5_556_edges : next config 5 s5_556 = [s6_42] := by decide
theorem s5_556_safe : Safe 8 5 s5_556 := by
  apply safe_succ 7 5 s5_556 [s6_42] (by decide) s5_556_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_42_safe
def s5_557 : State := ⟨[1,12,67,145], 66902575877958790363070858000225478805360918, 2, 0, 1, 0⟩
theorem s5_557_edges : next config 5 s5_557 = [s6_43] := by decide
theorem s5_557_safe : Safe 8 5 s5_557 := by
  apply safe_succ 7 5 s5_557 [s6_43] (by decide) s5_557_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_43_safe
def s5_558 : State := ⟨[1,12,67,146], 89204682205957097258460392877815419965083926, 2, 0, 1, 0⟩
theorem s5_558_edges : next config 5 s5_558 = [s6_46] := by decide
theorem s5_558_safe : Safe 8 5 s5_558 := by
  apply safe_succ 7 5 s5_558 [s6_46] (by decide) s5_558_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_46_safe
def s5_559 : State := ⟨[1,12,67,146], 89204682205957097258460429771303567384187158, 2, 0, 1, 0⟩
theorem s5_559_edges : next config 5 s5_559 = [s6_47] := by decide
theorem s5_559_safe : Safe 8 5 s5_559 := by
  apply safe_succ 7 5 s5_559 [s6_47] (by decide) s5_559_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_47_safe
def s5_560 : State := ⟨[1,12,67,146], 111504066275020036646142257652034054398218518, 2, 0, 1, 0⟩
theorem s5_560_edges : next config 5 s5_560 = [s6_48] := by decide
theorem s5_560_safe : Safe 8 5 s5_560 := by
  apply safe_succ 7 5 s5_560 [s6_48] (by decide) s5_560_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_48_safe
def s5_561 : State := ⟨[1,12,67,146], 111504066275020036646142294545522201817321750, 2, 0, 1, 0⟩
theorem s5_561_edges : next config 5 s5_561 = [s6_49] := by decide
theorem s5_561_safe : Safe 8 5 s5_561 := by
  apply safe_succ 7 5 s5_561 [s6_49] (by decide) s5_561_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_49_safe
def s5_562 : State := ⟨[1,12,67,160], 1461501637671185285124623296345678323755381756190, 3, 1, 1, 0⟩
theorem s5_562_edges : next config 5 s5_562 = [s6_50, s6_424, s6_428] := by decide
theorem s5_562_safe : Safe 8 5 s5_562 := by
  apply safe_succ 7 5 s5_562 [s6_50, s6_424, s6_428] (by decide) s5_562_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_50_safe
  · subst z; exact s6_424_safe
  · subst z; exact s6_428_safe
def s5_563 : State := ⟨[1,12,67,162], 5846006551025023507419431648384919300597671334166, 2, 0, 1, 0⟩
theorem s5_563_edges : next config 5 s5_563 = [s6_51] := by decide
theorem s5_563_safe : Safe 8 5 s5_563 := by
  apply safe_succ 7 5 s5_563 [s6_51] (by decide) s5_563_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_51_safe
def s5_564 : State := ⟨[1,12,67,162], 5846006551025023507419431648421812788745090437398, 2, 0, 1, 0⟩
theorem s5_564_edges : next config 5 s5_564 = [s6_52] := by decide
theorem s5_564_safe : Safe 8 5 s5_564 := by
  apply safe_succ 7 5 s5_564 [s6_52] (by decide) s5_564_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_52_safe
def s5_565 : State := ⟨[1,12,67,162], 7307508186994796957939362627247703890526531031318, 2, 0, 1, 0⟩
theorem s5_565_edges : next config 5 s5_565 = [s6_53] := by decide
theorem s5_565_safe : Safe 8 5 s5_565 := by
  apply safe_succ 7 5 s5_565 [s6_53] (by decide) s5_565_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_53_safe
def s5_566 : State := ⟨[1,12,67,162], 7307508186994796957939362627284597378673950134550, 2, 0, 1, 0⟩
theorem s5_566_edges : next config 5 s5_566 = [s6_54] := by decide
theorem s5_566_safe : Safe 8 5 s5_566 := by
  apply safe_succ 7 5 s5_566 [s6_54] (by decide) s5_566_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_54_safe
def s5_567 : State := ⟨[1,12,67,176], 95780971326419139128294233276893708537611803510771990, 2, 0, 1, 0⟩
theorem s5_567_edges : next config 5 s5_567 = [s6_57] := by decide
theorem s5_567_safe : Safe 8 5 s5_567 := by
  apply safe_succ 7 5 s5_567 [s6_57] (by decide) s5_567_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_57_safe
def s5_568 : State := ⟨[1,12,67,176], 95780971326419139128294233276893745431099950929875222, 2, 0, 1, 0⟩
theorem s5_568_edges : next config 5 s5_568 = [s6_58] := by decide
theorem s5_568_safe : Safe 8 5 s5_568 := by
  apply safe_succ 7 5 s5_568 [s6_58] (by decide) s5_568_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_58_safe
def s5_569 : State := ⟨[1,12,67,176], 95782432805755724832681813820190706547983097937334550, 2, 0, 1, 0⟩
theorem s5_569_edges : next config 5 s5_569 = [s6_59] := by decide
theorem s5_569_safe : Safe 8 5 s5_569 := by
  apply safe_succ 7 5 s5_569 [s6_59] (by decide) s5_569_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_59_safe
def s5_570 : State := ⟨[1,12,67,176], 95782432805755724832681813820190743441471245356437782, 2, 0, 1, 0⟩
theorem s5_570_edges : next config 5 s5_570 = [s6_60] := by decide
theorem s5_570_safe : Safe 8 5 s5_570 := by
  apply safe_succ 7 5 s5_570 [s6_60] (by decide) s5_570_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_60_safe
def s5_571 : State := ⟨[1,12,67,192], 6277101735386680764176071790128604879731750748563483726110, 3, 1, 1, 0⟩
theorem s5_571_edges : next config 5 s5_571 = [s6_61] := by decide
theorem s5_571_safe : Safe 8 5 s5_571 := by
  apply safe_succ 7 5 s5_571 [s6_61] (by decide) s5_571_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_61_safe
def s5_572 : State := ⟨[1,12,67,195], 50216813883093446111026597752582269792448238859811725316382, 3, 1, 1, 0⟩
theorem s5_572_edges : next config 5 s5_572 = [s6_62] := by decide
theorem s5_572_safe : Safe 8 5 s5_572 := by
  apply safe_succ 7 5 s5_572 [s6_62] (by decide) s5_572_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_62_safe
def s5_573 : State := ⟨[1,12,67,210], 1645504557321206042177270268038248049062735287088508619142009110, 2, 0, 1, 0⟩
theorem s5_573_edges : next config 5 s5_573 = [s6_63, s6_418] := by decide
theorem s5_573_safe : Safe 8 5 s5_573 := by
  apply safe_succ 7 5 s5_573 [s6_63, s6_418] (by decide) s5_573_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_63_safe
  · subst z; exact s6_418_safe
def s5_574 : State := ⟨[1,12,67,210], 1645529665728147588878024865997410256586863978237638113774080278, 2, 0, 1, 0⟩
theorem s5_574_edges : next config 5 s5_574 = [s6_64, s6_419] := by decide
theorem s5_574_safe : Safe 8 5 s5_574 := by
  apply safe_succ 7 5 s5_574 [s6_64, s6_419] (by decide) s5_574_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_64_safe
  · subst z; exact s6_419_safe
def s5_575 : State := ⟨[1,12,80,145], 44601830679428167222743844186262861959598358, 3, 1, 1, 0⟩
theorem s5_575_edges : next config 5 s5_575 = [s6_68, s6_430] := by decide
theorem s5_575_safe : Safe 8 5 s5_575 := by
  apply safe_succ 7 5 s5_575 [s6_68, s6_430] (by decide) s5_575_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_68_safe
  · subst z; exact s6_430_safe
def s5_576 : State := ⟨[1,12,81,145], 44601830679428167223952770005877491134304534, 3, 1, 1, 0⟩
theorem s5_576_edges : next config 5 s5_576 = [s6_70] := by decide
theorem s5_576_safe : Safe 8 5 s5_576 := by
  apply safe_succ 7 5 s5_576 [s6_70] (by decide) s5_576_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_70_safe
def s5_577 : State := ⟨[1,12,82,145], 44602511244162009103297622181297907858215190, 2, 0, 1, 0⟩
theorem s5_577_edges : next config 5 s5_577 = [s6_72] := by decide
theorem s5_577_safe : Safe 8 5 s5_577 := by
  apply safe_succ 7 5 s5_577 [s6_72] (by decide) s5_577_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_72_safe
def s5_578 : State := ⟨[1,12,82,145], 44602511244162009104506474213936242194714902, 2, 0, 1, 0⟩
theorem s5_578_edges : next config 5 s5_578 = [s6_73] := by decide
theorem s5_578_safe : Safe 8 5 s5_578 := by
  apply safe_succ 7 5 s5_578 [s6_73] (by decide) s5_578_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_73_safe
def s5_579 : State := ⟨[1,12,82,145], 66902575877958790367906413704731405827772694, 2, 0, 1, 0⟩
theorem s5_579_edges : next config 5 s5_579 = [s6_76] := by decide
theorem s5_579_safe : Safe 8 5 s5_579 := by
  apply safe_succ 7 5 s5_579 [s6_76] (by decide) s5_579_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_76_safe
def s5_580 : State := ⟨[1,12,82,145], 66902575877958790369115265737369740164272406, 2, 0, 1, 0⟩
theorem s5_580_edges : next config 5 s5_580 = [s6_77] := by decide
theorem s5_580_safe : Safe 8 5 s5_580 := by
  apply safe_succ 7 5 s5_580 [s6_77] (by decide) s5_580_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_77_safe
def s5_581 : State := ⟨[1,12,96,129], 1020847100842043552922834903966853173534, 3, 1, 1, 0⟩
theorem s5_581_edges : next config 5 s5_581 = [s6_82, s6_462, s6_431] := by decide
theorem s5_581_safe : Safe 8 5 s5_581 := by
  apply safe_succ 7 5 s5_581 [s6_82, s6_462, s6_431] (by decide) s5_581_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_82_safe
  · subst z; exact s6_462_safe
  · subst z; exact s6_431_safe
def s5_582 : State := ⟨[1,12,96,129], 1020847100842043552922834903975443108118, 3, 1, 1, 0⟩
theorem s5_582_edges : next config 5 s5_582 = [s6_83, s6_463, s6_432] := by decide
theorem s5_582_safe : Safe 8 5 s5_582 := by
  apply safe_succ 7 5 s5_582 [s6_83, s6_463, s6_432] (by decide) s5_582_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_83_safe
  · subst z; exact s6_463_safe
  · subst z; exact s6_432_safe
def s5_583 : State := ⟨[1,12,96,129], 1020847100842043552959728392114272276758, 3, 1, 1, 0⟩
theorem s5_583_edges : next config 5 s5_583 = [s6_84, s6_464, s6_433] := by decide
theorem s5_583_safe : Safe 8 5 s5_583 := by
  apply safe_succ 7 5 s5_583 [s6_84, s6_464, s6_433] (by decide) s5_583_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_84_safe
  · subst z; exact s6_464_safe
  · subst z; exact s6_433_safe
def s5_584 : State := ⟨[1,12,96,129], 1020847101000499877951363579153941074198, 3, 1, 1, 0⟩
theorem s5_584_edges : next config 5 s5_584 = [s6_85, s6_465, s6_434] := by decide
theorem s5_584_safe : Safe 8 5 s5_584 := by
  apply safe_succ 7 5 s5_584 [s6_85, s6_465, s6_434] (by decide) s5_584_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_85_safe
  · subst z; exact s6_465_safe
  · subst z; exact s6_434_safe
def s5_585 : State := ⟨[1,12,96,130], 1701411834683920479849584118830389596446, 3, 1, 1, 0⟩
theorem s5_585_edges : next config 5 s5_585 = [s6_88, s6_466, s6_439, s6_444] := by decide
theorem s5_585_safe : Safe 8 5 s5_585 := by
  apply safe_succ 7 5 s5_585 [s6_88, s6_466, s6_439, s6_444] (by decide) s5_585_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_88_safe
  · subst z; exact s6_466_safe
  · subst z; exact s6_439_safe
  · subst z; exact s6_444_safe
def s5_586 : State := ⟨[1,12,96,130], 1701411834683920479849584118838979531030, 3, 1, 1, 0⟩
theorem s5_586_edges : next config 5 s5_586 = [s6_89, s6_467] := by decide
theorem s5_586_safe : Safe 8 5 s5_586 := by
  apply safe_succ 7 5 s5_586 [s6_89, s6_467] (by decide) s5_586_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_89_safe
  · subst z; exact s6_467_safe
def s5_587 : State := ⟨[1,12,96,130], 1701411834683920479886477606977808699670, 3, 1, 1, 0⟩
theorem s5_587_edges : next config 5 s5_587 = [s6_90, s6_468, s6_440, s6_445] := by decide
theorem s5_587_safe : Safe 8 5 s5_587 := by
  apply safe_succ 7 5 s5_587 [s6_90, s6_468, s6_440, s6_445] (by decide) s5_587_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_90_safe
  · subst z; exact s6_468_safe
  · subst z; exact s6_440_safe
  · subst z; exact s6_445_safe
def s5_588 : State := ⟨[1,12,96,130], 1701411834842376804878112794017477497110, 3, 1, 1, 0⟩
theorem s5_588_edges : next config 5 s5_588 = [s6_91, s6_469, s6_446] := by decide
theorem s5_588_safe : Safe 8 5 s5_588 := by
  apply safe_succ 7 5 s5_588 [s6_91, s6_469, s6_446] (by decide) s5_588_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_91_safe
  · subst z; exact s6_469_safe
  · subst z; exact s6_446_safe
def s5_589 : State := ⟨[1,12,96,130], 4423670770051428187556580978284535288086, 3, 1, 1, 0⟩
theorem s5_589_edges : next config 5 s5_589 = [s6_94, s6_470, s6_441, s6_447] := by decide
theorem s5_589_safe : Safe 8 5 s5_589 := by
  apply safe_succ 7 5 s5_589 [s6_94, s6_470, s6_441, s6_447] (by decide) s5_589_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_94_safe
  · subst z; exact s6_470_safe
  · subst z; exact s6_441_safe
  · subst z; exact s6_447_safe
def s5_590 : State := ⟨[1,12,96,131], 3062541302367674333703082548557462442270, 3, 1, 1, 0⟩
theorem s5_590_edges : next config 5 s5_590 = [s6_96, s6_471, s6_454] := by decide
theorem s5_590_safe : Safe 8 5 s5_590 := by
  apply safe_succ 7 5 s5_590 [s6_96, s6_471, s6_454] (by decide) s5_590_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_96_safe
  · subst z; exact s6_471_safe
  · subst z; exact s6_454_safe
def s5_591 : State := ⟨[1,12,96,132], 5784800237735182041410079408011608133918, 3, 1, 1, 0⟩
theorem s5_591_edges : next config 5 s5_591 = [s6_98, s6_472] := by decide
theorem s5_591_safe : Safe 8 5 s5_591 := by
  apply safe_succ 7 5 s5_591 [s6_98, s6_472] (by decide) s5_591_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_98_safe
  · subst z; exact s6_472_safe
def s5_592 : State := ⟨[1,12,96,132], 5784800237735182041410079408020198068502, 3, 1, 1, 0⟩
theorem s5_592_edges : next config 5 s5_592 = [s6_99, s6_473] := by decide
theorem s5_592_safe : Safe 8 5 s5_592 := by
  apply safe_succ 7 5 s5_592 [s6_99, s6_473] (by decide) s5_592_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_99_safe
  · subst z; exact s6_473_safe
def s5_593 : State := ⟨[1,12,96,132], 5784800237735182041446972896159027237142, 3, 1, 1, 0⟩
theorem s5_593_edges : next config 5 s5_593 = [s6_100, s6_474] := by decide
theorem s5_593_safe : Safe 8 5 s5_593 := by
  apply safe_succ 7 5 s5_593 [s6_100, s6_474] (by decide) s5_593_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_100_safe
  · subst z; exact s6_474_safe
def s5_594 : State := ⟨[1,12,96,132], 5784800237893638366438608083198696034582, 3, 1, 1, 0⟩
theorem s5_594_edges : next config 5 s5_594 = [s6_101, s6_475] := by decide
theorem s5_594_safe : Safe 8 5 s5_594 := by
  apply safe_succ 7 5 s5_594 [s6_101, s6_475] (by decide) s5_594_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_101_safe
  · subst z; exact s6_475_safe
def s5_595 : State := ⟨[1,12,96,136], 87452568298760413272619985191635978883358, 3, 1, 1, 0⟩
theorem s5_595_edges : next config 5 s5_595 = [s6_104, s6_476] := by decide
theorem s5_595_safe : Safe 8 5 s5_595 := by
  apply safe_succ 7 5 s5_595 [s6_104, s6_476] (by decide) s5_595_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_104_safe
  · subst z; exact s6_476_safe
def s5_596 : State := ⟨[1,12,96,136], 87452568298760413272619985191644568817942, 3, 1, 1, 0⟩
theorem s5_596_edges : next config 5 s5_596 = [s6_105, s6_477] := by decide
theorem s5_596_safe : Safe 8 5 s5_596 := by
  apply safe_succ 7 5 s5_596 [s6_105, s6_477] (by decide) s5_596_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_105_safe
  · subst z; exact s6_477_safe
def s5_597 : State := ⟨[1,12,96,136], 87452568298760413272656878679783397986582, 3, 1, 1, 0⟩
theorem s5_597_edges : next config 5 s5_597 = [s6_106, s6_478] := by decide
theorem s5_597_safe : Safe 8 5 s5_597 := by
  apply safe_succ 7 5 s5_597 [s6_106, s6_478] (by decide) s5_597_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_106_safe
  · subst z; exact s6_478_safe
def s5_598 : State := ⟨[1,12,96,136], 87452568298918869597648513866823066784022, 3, 1, 1, 0⟩
theorem s5_598_edges : next config 5 s5_598 = [s6_107, s6_479] := by decide
theorem s5_598_safe : Safe 8 5 s5_598 := by
  apply safe_succ 7 5 s5_598 [s6_107, s6_479] (by decide) s5_598_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_107_safe
  · subst z; exact s6_479_safe
def s5_599 : State := ⟨[1,12,96,140], 1394136857275164112971978477729625910874398, 3, 1, 1, 0⟩
theorem s5_599_edges : next config 5 s5_599 = [s6_114, s6_480] := by decide
theorem s5_599_safe : Safe 8 5 s5_599 := by
  apply safe_succ 7 5 s5_599 [s6_114, s6_480] (by decide) s5_599_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_114_safe
  · subst z; exact s6_480_safe
def s5_600 : State := ⟨[1,12,96,140], 1394136857275164112971978477729634500808982, 3, 1, 1, 0⟩
theorem s5_600_edges : next config 5 s5_600 = [s6_115, s6_481] := by decide
theorem s5_600_safe : Safe 8 5 s5_600 := by
  apply safe_succ 7 5 s5_600 [s6_115, s6_481] (by decide) s5_600_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_115_safe
  · subst z; exact s6_481_safe
def s5_601 : State := ⟨[1,12,96,140], 1394136857275164112972015371217773329977622, 3, 1, 1, 0⟩
theorem s5_601_edges : next config 5 s5_601 = [s6_116, s6_482] := by decide
theorem s5_601_safe : Safe 8 5 s5_601 := by
  apply safe_succ 7 5 s5_601 [s6_116, s6_482] (by decide) s5_601_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_116_safe
  · subst z; exact s6_482_safe
def s5_602 : State := ⟨[1,12,96,140], 1394136857275322569297007006404812998775062, 3, 1, 1, 0⟩
theorem s5_602_edges : next config 5 s5_602 = [s6_117, s6_483] := by decide
theorem s5_602_safe : Safe 8 5 s5_602 := by
  apply safe_succ 7 5 s5_602 [s6_117, s6_483] (by decide) s5_602_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_117_safe
  · subst z; exact s6_483_safe
def s5_603 : State := ⟨[1,12,96,144], 22301085480897623308161714358337464822731038, 3, 1, 1, 0⟩
theorem s5_603_edges : next config 5 s5_603 = [s6_118, s6_484, s6_435, s6_442, s6_457] := by decide
theorem s5_603_safe : Safe 8 5 s5_603 := by
  apply safe_succ 7 5 s5_603 [s6_118, s6_484, s6_435, s6_442, s6_457] (by decide) s5_603_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_118_safe
  · subst z; exact s6_484_safe
  · subst z; exact s6_435_safe
  · subst z; exact s6_442_safe
  · subst z; exact s6_457_safe
def s5_604 : State := ⟨[1,12,96,144], 22301085480897623308161714358337473412665622, 3, 1, 1, 0⟩
theorem s5_604_edges : next config 5 s5_604 = [s6_119, s6_485, s6_436] := by decide
theorem s5_604_safe : Safe 8 5 s5_604 := by
  apply safe_succ 7 5 s5_604 [s6_119, s6_485, s6_436] (by decide) s5_604_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_119_safe
  · subst z; exact s6_485_safe
  · subst z; exact s6_436_safe
def s5_605 : State := ⟨[1,12,96,144], 22301085480897623308161751251825612241834262, 3, 1, 1, 0⟩
theorem s5_605_edges : next config 5 s5_605 = [s6_120, s6_486, s6_437, s6_443, s6_458] := by decide
theorem s5_605_safe : Safe 8 5 s5_605 := by
  apply safe_succ 7 5 s5_605 [s6_120, s6_486, s6_437, s6_443, s6_458] (by decide) s5_605_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_120_safe
  · subst z; exact s6_486_safe
  · subst z; exact s6_437_safe
  · subst z; exact s6_443_safe
  · subst z; exact s6_458_safe
def s5_606 : State := ⟨[1,12,96,144], 22301085480897781764486742887012651910631702, 3, 1, 1, 0⟩
theorem s5_606_edges : next config 5 s5_606 = [s6_121, s6_487, s6_438] := by decide
theorem s5_606_safe : Safe 8 5 s5_606 := by
  apply safe_succ 7 5 s5_606 [s6_121, s6_487, s6_438] (by decide) s5_606_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_121_safe
  · subst z; exact s6_487_safe
  · subst z; exact s6_438_safe
def s5_607 : State := ⟨[1,12,96,145], 44601830679428246449697432630985826328842518, 3, 1, 1, 0⟩
theorem s5_607_edges : next config 5 s5_607 = [s6_1352, s6_713, s6_1014, s6_124, s6_461, s6_530, s6_488, s6_527] := by decide
theorem s5_607_safe : Safe 8 5 s5_607 := by
  apply safe_succ 7 5 s5_607 [s6_1352, s6_713, s6_1014, s6_124, s6_461, s6_530, s6_488, s6_527] (by decide) s5_607_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1352_safe
  · subst z; exact s6_713_safe
  · subst z; exact s6_1014_safe
  · subst z; exact s6_124_safe
  · subst z; exact s6_461_safe
  · subst z; exact s6_530_safe
  · subst z; exact s6_488_safe
  · subst z; exact s6_527_safe
def s5_608 : State := ⟨[1,12,96,160], 1461501637671185285203851458712368708759249293598, 3, 1, 1, 0⟩
theorem s5_608_edges : next config 5 s5_608 = [s6_130, s6_489, s6_448, s6_459] := by decide
theorem s5_608_safe : Safe 8 5 s5_608 := by
  apply safe_succ 7 5 s5_608 [s6_130, s6_489, s6_448, s6_459] (by decide) s5_608_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_130_safe
  · subst z; exact s6_489_safe
  · subst z; exact s6_448_safe
  · subst z; exact s6_459_safe
def s5_609 : State := ⟨[1,12,96,160], 1461501637671185285203851458712368708767839228182, 3, 1, 1, 0⟩
theorem s5_609_edges : next config 5 s5_609 = [s6_131, s6_490] := by decide
theorem s5_609_safe : Safe 8 5 s5_609 := by
  apply safe_succ 7 5 s5_609 [s6_131, s6_490] (by decide) s5_609_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_131_safe
  · subst z; exact s6_490_safe
def s5_610 : State := ⟨[1,12,96,160], 1461501637671185285203851458749262196906668396822, 3, 1, 1, 0⟩
theorem s5_610_edges : next config 5 s5_610 = [s6_132, s6_491, s6_449, s6_460] := by decide
theorem s5_610_safe : Safe 8 5 s5_610 := by
  apply safe_succ 7 5 s5_610 [s6_132, s6_491, s6_449, s6_460] (by decide) s5_610_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_132_safe
  · subst z; exact s6_491_safe
  · subst z; exact s6_449_safe
  · subst z; exact s6_460_safe
def s5_611 : State := ⟨[1,12,96,160], 1461501637671185285362307783740897383946337194262, 3, 1, 1, 0⟩
theorem s5_611_edges : next config 5 s5_611 = [s6_133, s6_492, s6_450] := by decide
theorem s5_611_safe : Safe 8 5 s5_611 := by
  apply safe_succ 7 5 s5_611 [s6_133, s6_492, s6_450] (by decide) s5_611_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_133_safe
  · subst z; exact s6_492_safe
  · subst z; exact s6_450_safe
def s5_612 : State := ⟨[1,12,96,160], 4384504912332991121611221124144934748071114379542, 3, 1, 1, 0⟩
theorem s5_612_edges : next config 5 s5_612 = [s6_136, s6_493] := by decide
theorem s5_612_safe : Safe 8 5 s5_612 := by
  apply safe_succ 7 5 s5_612 [s6_136, s6_493] (by decide) s5_612_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_136_safe
  · subst z; exact s6_493_safe
def s5_613 : State := ⟨[1,12,96,161], 2923003275002088203407536291428651728423771771158, 3, 1, 1, 0⟩
theorem s5_613_edges : next config 5 s5_613 = [s6_137, s6_494, s6_456] := by decide
theorem s5_613_safe : Safe 8 5 s5_613 := by
  apply safe_succ 7 5 s5_613 [s6_137, s6_494, s6_456] (by decide) s5_613_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_137_safe
  · subst z; exact s6_494_safe
  · subst z; exact s6_456_safe
def s5_614 : State := ⟨[1,12,96,162], 25108406947392729606368181200329325475124137975310257819926, 2, 0, 1, 0⟩
theorem s5_614_edges : next config 5 s5_614 = [s6_138, s6_495] := by decide
theorem s5_614_safe : Safe 8 5 s5_614 := by
  apply safe_succ 7 5 s5_614 [s6_138, s6_495] (by decide) s5_614_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_138_safe
  · subst z; exact s6_495_safe
def s5_615 : State := ⟨[1,12,96,162], 31385508682779410368842841155853238037372994990047219486998, 2, 0, 1, 0⟩
theorem s5_615_edges : next config 5 s5_615 = [s6_139, s6_496] := by decide
theorem s5_615_safe : Safe 8 5 s5_615 := by
  apply safe_succ 7 5 s5_615 [s6_139, s6_496] (by decide) s5_615_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_139_safe
  · subst z; exact s6_496_safe
def s5_616 : State := ⟨[1,12,96,163], 11692013102390329381839029922360095920668459208982, 2, 0, 1, 0⟩
theorem s5_616_edges : next config 5 s5_616 = [s6_140, s6_497] := by decide
theorem s5_616_safe : Safe 8 5 s5_616 := by
  apply safe_succ 7 5 s5_616 [s6_140, s6_497] (by decide) s5_616_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_140_safe
  · subst z; exact s6_497_safe
def s5_617 : State := ⟨[1,12,96,163], 11692013103070894115680906849286845135531995631894, 2, 0, 1, 0⟩
theorem s5_617_edges : next config 5 s5_617 = [s6_141, s6_498] := by decide
theorem s5_617_safe : Safe 8 5 s5_617 := by
  apply safe_succ 7 5 s5_617 [s6_141, s6_498] (by decide) s5_617_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_141_safe
  · subst z; exact s6_498_safe
def s5_618 : State := ⟨[1,12,96,163], 14615016374329876282878891880085665100526178603286, 2, 0, 1, 0⟩
theorem s5_618_edges : next config 5 s5_618 = [s6_142, s6_499] := by decide
theorem s5_618_safe : Safe 8 5 s5_618 := by
  apply safe_succ 7 5 s5_618 [s6_142, s6_499] (by decide) s5_618_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_142_safe
  · subst z; exact s6_499_safe
def s5_619 : State := ⟨[1,12,96,163], 16076518010980214467240699785875198905318574723350, 2, 0, 1, 0⟩
theorem s5_619_edges : next config 5 s5_619 = [s6_143, s6_500] := by decide
theorem s5_619_safe : Safe 8 5 s5_619 := by
  apply safe_succ 7 5 s5_619 [s6_143, s6_500] (by decide) s5_619_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_143_safe
  · subst z; exact s6_500_safe
def s5_620 : State := ⟨[1,12,96,163], 17538019649672246853128138472444980354701580112150, 2, 0, 1, 0⟩
theorem s5_620_edges : next config 5 s5_620 = [s6_144, s6_501] := by decide
theorem s5_620_safe : Safe 8 5 s5_620 := by
  apply safe_succ 7 5 s5_620 [s6_144, s6_501] (by decide) s5_620_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_144_safe
  · subst z; exact s6_501_safe
def s5_621 : State := ⟨[1,12,96,163], 18999521285642020303648069451307764944630439809302, 2, 0, 1, 0⟩
theorem s5_621_edges : next config 5 s5_621 = [s6_145, s6_502] := by decide
theorem s5_621_safe : Safe 8 5 s5_621 := by
  apply safe_succ 7 5 s5_621 [s6_145, s6_502] (by decide) s5_621_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_145_safe
  · subst z; exact s6_502_safe
def s5_622 : State := ⟨[1,12,96,192], 6277101735386680764176071790207833042098441133567351263518, 3, 1, 1, 0⟩
theorem s5_622_edges : next config 5 s5_622 = [s6_154, s6_503] := by decide
theorem s5_622_safe : Safe 8 5 s5_622 := by
  apply safe_succ 7 5 s5_622 [s6_154, s6_503] (by decide) s5_622_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_154_safe
  · subst z; exact s6_503_safe
def s5_623 : State := ⟨[1,12,96,192], 6277101735386680764176071790207833042098441133575941198102, 3, 1, 1, 0⟩
theorem s5_623_edges : next config 5 s5_623 = [s6_155, s6_504] := by decide
theorem s5_623_safe : Safe 8 5 s5_623 := by
  apply safe_succ 7 5 s5_623 [s6_155, s6_504] (by decide) s5_623_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_155_safe
  · subst z; exact s6_504_safe
def s5_624 : State := ⟨[1,12,96,192], 6277101735386680764176071790207833042135334621714770366742, 3, 1, 1, 0⟩
theorem s5_624_edges : next config 5 s5_624 = [s6_156, s6_505] := by decide
theorem s5_624_safe : Safe 8 5 s5_624 := by
  apply safe_succ 7 5 s5_624 [s6_156, s6_505] (by decide) s5_624_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_156_safe
  · subst z; exact s6_505_safe
def s5_625 : State := ⟨[1,12,96,192], 6277101735386680764176071790366289367126969808754439164182, 3, 1, 1, 0⟩
theorem s5_625_edges : next config 5 s5_625 = [s6_157, s6_506] := by decide
theorem s5_625_safe : Safe 8 5 s5_625 := by
  apply safe_succ 7 5 s5_625 [s6_157, s6_506] (by decide) s5_625_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_157_safe
  · subst z; exact s6_506_safe
def s5_626 : State := ⟨[1,12,96,192], 18831305206160042291847650636623165874303152022495420289302, 3, 1, 1, 0⟩
theorem s5_626_edges : next config 5 s5_626 = [s6_160, s6_507] := by decide
theorem s5_626_safe : Safe 8 5 s5_626 := by
  apply safe_succ 7 5 s5_626 [s6_160, s6_507] (by decide) s5_626_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_160_safe
  · subst z; exact s6_507_safe
def s5_627 : State := ⟨[1,12,96,193], 12554203470773361528011861213415499458237690066178804879638, 3, 1, 1, 0⟩
theorem s5_627_edges : next config 5 s5_627 = [s6_162, s6_508] := by decide
theorem s5_627_safe : Safe 8 5 s5_627 := by
  apply safe_succ 7 5 s5_627 [s6_162, s6_508] (by decide) s5_627_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_162_safe
  · subst z; exact s6_508_safe
def s5_628 : State := ⟨[1,12,96,194], 25108406947392729606368181200329325475124137975310257819926, 2, 0, 1, 0⟩
theorem s5_628_edges : next config 5 s5_628 = [s6_164, s6_509] := by decide
theorem s5_628_safe : Safe 8 5 s5_628 := by
  apply safe_succ 7 5 s5_628 [s6_164, s6_509] (by decide) s5_628_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_164_safe
  · subst z; exact s6_509_safe
def s5_629 : State := ⟨[1,12,96,194], 25108406948854231242337954650849256453986922565239117517078, 2, 0, 1, 0⟩
theorem s5_629_edges : next config 5 s5_629 = [s6_165, s6_510] := by decide
theorem s5_629_safe : Safe 8 5 s5_629 := by
  apply safe_succ 7 5 s5_629 [s6_165, s6_510] (by decide) s5_629_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_165_safe
  · subst z; exact s6_510_safe
def s5_630 : State := ⟨[1,12,96,210], 1645504557321206042244173864763307681469358588308292139762127126, 2, 0, 1, 0⟩
theorem s5_630_edges : next config 5 s5_630 = [s6_166, s6_511] := by decide
theorem s5_630_safe : Safe 8 5 s5_630 := by
  apply safe_succ 7 5 s5_630 [s6_166, s6_511] (by decide) s5_630_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_166_safe
  · subst z; exact s6_511_safe
def s5_631 : State := ⟨[1,12,96,210], 1645504557321206042266473248832370620857040453082510774195261718, 2, 0, 1, 0⟩
theorem s5_631_edges : next config 5 s5_631 = [s6_167, s6_512] := by decide
theorem s5_631_safe : Safe 8 5 s5_631 := by
  apply safe_succ 7 5 s5_631 [s6_167, s6_512] (by decide) s5_631_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_167_safe
  · subst z; exact s6_512_safe
def s5_632 : State := ⟨[1,12,96,210], 1645529665728147588878026227126878019568880124639476549876257046, 2, 0, 1, 0⟩
theorem s5_632_edges : next config 5 s5_632 = [s6_168, s6_513] := by decide
theorem s5_632_safe : Safe 8 5 s5_632 := by
  apply safe_succ 7 5 s5_632 [s6_168, s6_513] (by decide) s5_632_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_168_safe
  · subst z; exact s6_513_safe
def s5_633 : State := ⟨[1,12,96,210], 1645535942829882975558788701786833543481442373496491286837924118, 2, 0, 1, 0⟩
theorem s5_633_edges : next config 5 s5_633 = [s6_169, s6_514] := by decide
theorem s5_633_safe : Safe 8 5 s5_633 := by
  apply safe_succ 7 5 s5_633 [s6_169, s6_514] (by decide) s5_633_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_169_safe
  · subst z; exact s6_514_safe
def s5_634 : State := ⟨[1,12,96,210], 2056880696651507552716012563677585754536581546400312294008492310, 2, 0, 1, 0⟩
theorem s5_634_edges : next config 5 s5_634 = [s6_170, s6_515] := by decide
theorem s5_634_safe : Safe 8 5 s5_634 := by
  apply safe_succ 7 5 s5_634 [s6_170, s6_515] (by decide) s5_634_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_170_safe
  · subst z; exact s6_515_safe
def s5_635 : State := ⟨[1,12,96,210], 2056886973753242939374475654268478339061461930483108396537024790, 2, 0, 1, 0⟩
theorem s5_635_edges : next config 5 s5_635 = [s6_171, s6_516] := by decide
theorem s5_635_safe : Safe 8 5 s5_635 := by
  apply safe_succ 7 5 s5_635 [s6_171, s6_516] (by decide) s5_635_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_171_safe
  · subst z; exact s6_516_safe
def s5_636 : State := ⟨[1,12,96,224], 26959946667150639794667015087359913040637311048536658170206926999838, 3, 1, 1, 0⟩
theorem s5_636_edges : next config 5 s5_636 = [s6_180, s6_517] := by decide
theorem s5_636_safe : Safe 8 5 s5_636 := by
  apply safe_succ 7 5 s5_636 [s6_180, s6_517] (by decide) s5_636_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_180_safe
  · subst z; exact s6_517_safe
def s5_637 : State := ⟨[1,12,96,224], 26959946667150639794667015087359913040637311048536658170215516934422, 3, 1, 1, 0⟩
theorem s5_637_edges : next config 5 s5_637 = [s6_181, s6_518] := by decide
theorem s5_637_safe : Safe 8 5 s5_637 := by
  apply safe_succ 7 5 s5_637 [s6_181, s6_518] (by decide) s5_637_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_181_safe
  · subst z; exact s6_518_safe
def s5_638 : State := ⟨[1,12,96,224], 26959946667150639794667015087359913040637311048573551658354346103062, 3, 1, 1, 0⟩
theorem s5_638_edges : next config 5 s5_638 = [s6_182, s6_519] := by decide
theorem s5_638_safe : Safe 8 5 s5_638 := by
  apply safe_succ 7 5 s5_638 [s6_182, s6_519] (by decide) s5_638_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_182_safe
  · subst z; exact s6_519_safe
def s5_639 : State := ⟨[1,12,96,224], 26959946667150639794667015087359913040795767373565186845394014900502, 3, 1, 1, 0⟩
theorem s5_639_edges : next config 5 s5_639 = [s6_183, s6_520] := by decide
theorem s5_639_safe : Safe 8 5 s5_639 := by
  apply safe_succ 7 5 s5_639 [s6_183, s6_520] (by decide) s5_639_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_183_safe
  · subst z; exact s6_520_safe
def s5_640 : State := ⟨[1,12,96,224], 80879840001451919384001045261399174387911599893617803132414147498262, 3, 1, 1, 0⟩
theorem s5_640_edges : next config 5 s5_640 = [s6_186, s6_521] := by decide
theorem s5_640_safe : Safe 8 5 s5_640 := by
  apply safe_succ 7 5 s5_640 [s6_186, s6_521] (by decide) s5_640_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_186_safe
  · subst z; exact s6_521_safe
def s5_641 : State := ⟨[1,12,96,225], 53919893334301279589334030174379543714432911796105759326497625149718, 3, 1, 1, 0⟩
theorem s5_641_edges : next config 5 s5_641 = [s6_189, s6_522] := by decide
theorem s5_641_safe : Safe 8 5 s5_641 := by
  apply safe_succ 7 5 s5_641 [s6_189, s6_522] (by decide) s5_641_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_189_safe
  · subst z; exact s6_522_safe
def s5_642 : State := ⟨[1,12,97,145], 44602511244162246782949387908875876953035030, 2, 0, 1, 0⟩
theorem s5_642_edges : next config 5 s5_642 = [s6_192] := by decide
theorem s5_642_safe : Safe 8 5 s5_642 := by
  apply safe_succ 7 5 s5_642 [s6_192] (by decide) s5_642_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_192_safe
def s5_643 : State := ⟨[1,12,97,145], 66902575877959028047558179432309374922592534, 2, 0, 1, 0⟩
theorem s5_643_edges : next config 5 s5_643 = [s6_193] := by decide
theorem s5_643_safe : Safe 8 5 s5_643 := by
  apply safe_succ 7 5 s5_643 [s6_193] (by decide) s5_643_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_193_safe
def s5_644 : State := ⟨[1,12,97,162], 5846006551025023507657116135743244872641207669014, 2, 0, 1, 0⟩
theorem s5_644_edges : next config 5 s5_644 = [s6_194] := by decide
theorem s5_644_safe : Safe 8 5 s5_644 := by
  apply safe_succ 7 5 s5_644 [s6_194] (by decide) s5_644_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_194_safe
def s5_645 : State := ⟨[1,12,97,162], 7307508186994796958177047114606029462570067366166, 2, 0, 1, 0⟩
theorem s5_645_edges : next config 5 s5_645 = [s6_195] := by decide
theorem s5_645_safe : Safe 8 5 s5_645 := by
  apply safe_succ 7 5 s5_645 [s6_195] (by decide) s5_645_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_195_safe
def s5_646 : State := ⟨[1,12,104,128], 340282387282576229647756113050568036638, 3, 1, 0, 0⟩
theorem s5_646_edges : next config 5 s5_646 = [s6_835, s6_200, s6_462, s6_480, s6_523, s6_466, s6_476, s6_484, s6_489] := by decide
theorem s5_646_safe : Safe 8 5 s5_646 := by
  apply safe_succ 7 5 s5_646 [s6_835, s6_200, s6_462, s6_480, s6_523, s6_466, s6_476, s6_484, s6_489] (by decide) s5_646_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_835_safe
  · subst z; exact s6_200_safe
  · subst z; exact s6_462_safe
  · subst z; exact s6_480_safe
  · subst z; exact s6_523_safe
  · subst z; exact s6_466_safe
  · subst z; exact s6_476_safe
  · subst z; exact s6_484_safe
  · subst z; exact s6_489_safe
def s5_647 : State := ⟨[1,12,104,128], 340282387282576229647756113059157971222, 3, 1, 0, 0⟩
theorem s5_647_edges : next config 5 s5_647 = [s6_837, s6_201, s6_463, s6_481, s6_524, s6_467, s6_477, s6_485, s6_490] := by decide
theorem s5_647_safe : Safe 8 5 s5_647 := by
  apply safe_succ 7 5 s5_647 [s6_837, s6_201, s6_463, s6_481, s6_524, s6_467, s6_477, s6_485, s6_490] (by decide) s5_647_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_837_safe
  · subst z; exact s6_201_safe
  · subst z; exact s6_463_safe
  · subst z; exact s6_481_safe
  · subst z; exact s6_524_safe
  · subst z; exact s6_467_safe
  · subst z; exact s6_477_safe
  · subst z; exact s6_485_safe
  · subst z; exact s6_490_safe
def s5_648 : State := ⟨[1,12,104,128], 340282387282576229684649601197987139862, 3, 1, 0, 0⟩
theorem s5_648_edges : next config 5 s5_648 = [s6_838, s6_202, s6_464, s6_482, s6_525, s6_468, s6_478, s6_486, s6_491] := by decide
theorem s5_648_safe : Safe 8 5 s5_648 := by
  apply safe_succ 7 5 s5_648 [s6_838, s6_202, s6_464, s6_482, s6_525, s6_468, s6_478, s6_486, s6_491] (by decide) s5_648_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_838_safe
  · subst z; exact s6_202_safe
  · subst z; exact s6_464_safe
  · subst z; exact s6_482_safe
  · subst z; exact s6_525_safe
  · subst z; exact s6_468_safe
  · subst z; exact s6_478_safe
  · subst z; exact s6_486_safe
  · subst z; exact s6_491_safe
def s5_649 : State := ⟨[1,12,104,128], 340282387441032554676284788237655937302, 3, 1, 0, 0⟩
theorem s5_649_edges : next config 5 s5_649 = [s6_839, s6_203, s6_465, s6_483, s6_526, s6_469, s6_479, s6_487, s6_492] := by decide
theorem s5_649_safe : Safe 8 5 s5_649 := by
  apply safe_succ 7 5 s5_649 [s6_839, s6_203, s6_465, s6_483, s6_526, s6_469, s6_479, s6_487, s6_492] (by decide) s5_649_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_839_safe
  · subst z; exact s6_203_safe
  · subst z; exact s6_465_safe
  · subst z; exact s6_483_safe
  · subst z; exact s6_526_safe
  · subst z; exact s6_469_safe
  · subst z; exact s6_479_safe
  · subst z; exact s6_487_safe
  · subst z; exact s6_492_safe
def s5_650 : State := ⟨[1,12,104,131], 3743106056491960864281502187368250151190, 2, 0, 1, 0⟩
theorem s5_650_edges : next config 5 s5_650 = [s6_208, s6_497] := by decide
theorem s5_650_safe : Safe 8 5 s5_650 := by
  apply safe_succ 7 5 s5_650 [s6_208, s6_497] (by decide) s5_650_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_208_safe
  · subst z; exact s6_497_safe
def s5_651 : State := ⟨[1,12,104,131], 4423670790333837791208251402231786574102, 2, 0, 1, 0⟩
theorem s5_651_edges : next config 5 s5_651 = [s6_211, s6_498] := by decide
theorem s5_651_safe : Safe 8 5 s5_651 := by
  apply safe_succ 7 5 s5_651 [s6_211, s6_498] (by decide) s5_651_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_211_safe
  · subst z; exact s6_498_safe
def s5_652 : State := ⟨[1,12,104,145], 44602511244182370736228011050624637116420374, 2, 0, 1, 0⟩
theorem s5_652_edges : next config 5 s5_652 = [s6_716, s6_1015, s6_224] := by decide
theorem s5_652_safe : Safe 8 5 s5_652 := by
  apply safe_succ 7 5 s5_652 [s6_716, s6_1015, s6_224] (by decide) s5_652_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_716_safe
  · subst z; exact s6_1015_safe
  · subst z; exact s6_224_safe
def s5_653 : State := ⟨[1,12,104,145], 66902575877979152000836802574058135085977878, 2, 0, 1, 0⟩
theorem s5_653_edges : next config 5 s5_653 = [s6_717, s6_1016, s6_233] := by decide
theorem s5_653_safe : Safe 8 5 s5_653 := by
  apply safe_succ 7 5 s5_653 [s6_717, s6_1016, s6_233] (by decide) s5_653_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_717_safe
  · subst z; exact s6_1016_safe
  · subst z; exact s6_233_safe
def s5_654 : State := ⟨[1,12,104,146], 89204682205977458896226374345136223664804118, 2, 0, 1, 0⟩
theorem s5_654_edges : next config 5 s5_654 = [s6_718, s6_241] := by decide
theorem s5_654_safe : Safe 8 5 s5_654 := by
  apply safe_succ 7 5 s5_654 [s6_718, s6_241] (by decide) s5_654_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_718_safe
  · subst z; exact s6_241_safe
def s5_655 : State := ⟨[1,12,104,146], 111504066275040398283908239119354858097938710, 2, 0, 1, 0⟩
theorem s5_655_edges : next config 5 s5_655 = [s6_719, s6_248] := by decide
theorem s5_655_safe : Safe 8 5 s5_655 := by
  apply safe_succ 7 5 s5_655 [s6_719, s6_248] (by decide) s5_655_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_719_safe
  · subst z; exact s6_248_safe
def s5_656 : State := ⟨[1,12,104,161], 2923003275682652957531822822007071367225969545494, 2, 0, 1, 0⟩
theorem s5_656_edges : next config 5 s5_656 = [s6_255, s6_499] := by decide
theorem s5_656_safe : Safe 8 5 s5_656 := by
  apply safe_succ 7 5 s5_656 [s6_255, s6_499] (by decide) s5_656_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_255_safe
  · subst z; exact s6_499_safe
def s5_657 : State := ⟨[1,12,104,161], 4384504912332991141893630727796605172018365665558, 2, 0, 1, 0⟩
theorem s5_657_edges : next config 5 s5_657 = [s6_256, s6_500] := by decide
theorem s5_657_safe : Safe 8 5 s5_657 := by
  apply safe_succ 7 5 s5_657 [s6_256, s6_500] (by decide) s5_657_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_256_safe
  · subst z; exact s6_500_safe
def s5_658 : State := ⟨[1,12,104,162], 5846006551025023527781069414366386621401371054358, 2, 0, 1, 0⟩
theorem s5_658_edges : next config 5 s5_658 = [s6_1425, s6_720, s6_259, s6_501] := by decide
theorem s5_658_safe : Safe 8 5 s5_658 := by
  apply safe_succ 7 5 s5_658 [s6_1425, s6_720, s6_259, s6_501] (by decide) s5_658_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1425_safe
  · subst z; exact s6_720_safe
  · subst z; exact s6_259_safe
  · subst z; exact s6_501_safe
def s5_659 : State := ⟨[1,12,104,162], 7307508186994796978301000393229171211330230751510, 2, 0, 1, 0⟩
theorem s5_659_edges : next config 5 s5_659 = [s6_1426, s6_721, s6_267, s6_502] := by decide
theorem s5_659_safe : Safe 8 5 s5_659 := by
  apply safe_succ 7 5 s5_659 [s6_1426, s6_721, s6_267, s6_502] (by decide) s5_659_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1426_safe
  · subst z; exact s6_721_safe
  · subst z; exact s6_267_safe
  · subst z; exact s6_502_safe
def s5_660 : State := ⟨[1,12,104,176], 95780971326419139128314594914659690004932607210492182, 2, 0, 1, 0⟩
theorem s5_660_edges : next config 5 s5_660 = [s6_724, s6_287] := by decide
theorem s5_660_safe : Safe 8 5 s5_660 := by
  apply safe_succ 7 5 s5_660 [s6_724, s6_287] (by decide) s5_660_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_724_safe
  · subst z; exact s6_287_safe
def s5_661 : State := ⟨[1,12,104,176], 95782432805755724832702175457956688015303901637054742, 2, 0, 1, 0⟩
theorem s5_661_edges : next config 5 s5_661 = [s6_725, s6_292] := by decide
theorem s5_661_safe : Safe 8 5 s5_661 := by
  apply safe_succ 7 5 s5_661 [s6_725, s6_292] (by decide) s5_661_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_725_safe
  · subst z; exact s6_292_safe
def s5_662 : State := ⟨[1,12,104,193], 12554203470773361528692425967539785988779216216842173485334, 2, 0, 1, 0⟩
theorem s5_662_edges : next config 5 s5_662 = [s6_304] := by decide
theorem s5_662_safe : Safe 8 5 s5_662 := by
  apply safe_succ 7 5 s5_662 [s6_304] (by decide) s5_662_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_304_safe
def s5_663 : State := ⟨[1,12,104,193], 18831305206160042291847650656905575477954822446442671575318, 2, 0, 1, 0⟩
theorem s5_663_edges : next config 5 s5_663 = [s6_307] := by decide
theorem s5_663_safe : Safe 8 5 s5_663 := by
  apply safe_succ 7 5 s5_663 [s6_307] (by decide) s5_663_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_307_safe
def s5_664 : State := ⟨[1,12,104,194], 25108406941546723057044569547796995747910676320633778934038, 2, 0, 1, 0⟩
theorem s5_664_edges : next config 5 s5_664 = [s6_310, s6_513] := by decide
theorem s5_664_safe : Safe 8 5 s5_664 := by
  apply safe_succ 7 5 s5_664 [s6_310, s6_513] (by decide) s5_664_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_310_safe
  · subst z; exact s6_513_safe
def s5_665 : State := ⟨[1,12,104,194], 31385508676933403819519229503320908310159533335370740601110, 2, 0, 1, 0⟩
theorem s5_665_edges : next config 5 s5_665 = [s6_313, s6_514] := by decide
theorem s5_665_safe : Safe 8 5 s5_665 := by
  apply safe_succ 7 5 s5_665 [s6_313, s6_514] (by decide) s5_665_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_313_safe
  · subst z; exact s6_514_safe
def s5_666 : State := ⟨[1,12,104,208], 411376139330301510561043381120255531963449332437156377911169302, 2, 0, 1, 0⟩
theorem s5_666_edges : next config 5 s5_666 = [s6_316, s6_515] := by decide
theorem s5_666_safe : Safe 8 5 s5_666 := by
  apply safe_succ 7 5 s5_666 [s6_316, s6_515] (by decide) s5_666_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_316_safe
  · subst z; exact s6_515_safe
def s5_667 : State := ⟨[1,12,104,208], 411382416432036897219506471711148116488329716519952480439701782, 2, 0, 1, 0⟩
theorem s5_667_edges : next config 5 s5_667 = [s6_318, s6_516] := by decide
theorem s5_667_safe : Safe 8 5 s5_667 := by
  apply safe_succ 7 5 s5_667 [s6_318, s6_516] (by decide) s5_667_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_318_safe
  · subst z; exact s6_516_safe
def s5_668 : State := ⟨[1,12,104,225], 53919893334301279589334030175060108468398742001655650290121324957974, 2, 0, 1, 0⟩
theorem s5_668_edges : next config 5 s5_668 = [s6_328] := by decide
theorem s5_668_safe : Safe 8 5 s5_668 := by
  apply safe_succ 7 5 s5_668 [s6_328] (by decide) s5_668_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_328_safe
def s5_669 : State := ⟨[1,12,104,225], 80879840001451919384001045261399174408194009497269473556361398784278, 2, 0, 1, 0⟩
theorem s5_669_edges : next config 5 s5_669 = [s6_329] := by decide
theorem s5_669_safe : Safe 8 5 s5_669 := by
  apply safe_succ 7 5 s5_669 [s6_329] (by decide) s5_669_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_329_safe
def s5_670 : State := ⟨[1,12,104,240], 1766847064778384329583297500765219601308401802593384324150367613366636822, 2, 0, 1, 0⟩
theorem s5_670_edges : next config 5 s5_670 = [s6_338] := by decide
theorem s5_670_safe : Safe 8 5 s5_670 := by
  apply safe_succ 7 5 s5_670 [s6_338] (by decide) s5_670_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_338_safe
def s5_671 : State := ⟨[1,12,104,240], 1766874024725051480223092167758005875740544816596271146450200355470905622, 2, 0, 1, 0⟩
theorem s5_671_edges : next config 5 s5_671 = [s6_339] := by decide
theorem s5_671_safe : Safe 8 5 s5_671 := by
  apply safe_succ 7 5 s5_671 [s6_339] (by decide) s5_671_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_339_safe
def s5_672 : State := ⟨[1,12,112,145], 44602511249354385185159187008731186194354454, 2, 0, 1, 0⟩
theorem s5_672_edges : next config 5 s5_672 = [s6_371] := by decide
theorem s5_672_safe : Safe 8 5 s5_672 := by
  apply safe_succ 7 5 s5_672 [s6_371] (by decide) s5_672_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_371_safe
def s5_673 : State := ⟨[1,12,112,145], 66902575883151166449767978532164684163911958, 2, 0, 1, 0⟩
theorem s5_673_edges : next config 5 s5_673 = [s6_372] := by decide
theorem s5_673_safe : Safe 8 5 s5_673 := by
  apply safe_succ 7 5 s5_673 [s6_372] (by decide) s5_673_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_372_safe
def s5_674 : State := ⟨[1,12,112,194], 25108406941546723057044574719811444679086634427182856868118, 2, 0, 1, 0⟩
theorem s5_674_edges : next config 5 s5_674 = [s6_373] := by decide
theorem s5_674_safe : Safe 8 5 s5_674 := by
  apply safe_succ 7 5 s5_674 [s6_373] (by decide) s5_674_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_373_safe
def s5_675 : State := ⟨[1,12,112,194], 31385508676933403819519234675335357241335491441919818535190, 2, 0, 1, 0⟩
theorem s5_675_edges : next config 5 s5_675 = [s6_374] := by decide
theorem s5_675_safe : Safe 8 5 s5_675 := by
  apply safe_succ 7 5 s5_675 [s6_374] (by decide) s5_675_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_374_safe
def s5_676 : State := ⟨[1,12,162,194], 25108406947392729606368181200329325475124137975310257819926, 2, 0, 1, 0⟩
theorem s5_676_edges : next config 5 s5_676 = [s6_379] := by decide
theorem s5_676_safe : Safe 8 5 s5_676 := by
  apply safe_succ 7 5 s5_676 [s6_379] (by decide) s5_676_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_379_safe
def s5_677 : State := ⟨[1,12,162,194], 31385508682779410368842841155853238037372994990047219486998, 2, 0, 1, 0⟩
theorem s5_677_edges : next config 5 s5_677 = [s6_380] := by decide
theorem s5_677_safe : Safe 8 5 s5_677 := by
  apply safe_succ 7 5 s5_677 [s6_380] (by decide) s5_677_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_380_safe
def s5_678 : State := ⟨[1,12,194,96], 25108406947392729606368181200329325475124137975310257819926, 2, 0, 1, 0⟩
theorem s5_678_edges : next config 5 s5_678 = [s6_391, s6_529] := by decide
theorem s5_678_safe : Safe 8 5 s5_678 := by
  apply safe_succ 7 5 s5_678 [s6_391, s6_529] (by decide) s5_678_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_391_safe
  · subst z; exact s6_529_safe
def s5_679 : State := ⟨[1,12,194,162], 25108406947392729606368181200329325475124137975310257819926, 2, 0, 1, 0⟩
theorem s5_679_edges : next config 5 s5_679 = [s6_392] := by decide
theorem s5_679_safe : Safe 8 5 s5_679 := by
  apply safe_succ 7 5 s5_679 [s6_392] (by decide) s5_679_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_392_safe
def s5_680 : State := ⟨[1,12,194,162], 25108406948854231242337954650849256453986922565239117517078, 2, 0, 1, 0⟩
theorem s5_680_edges : next config 5 s5_680 = [s6_393] := by decide
theorem s5_680_safe : Safe 8 5 s5_680 := by
  apply safe_succ 7 5 s5_680 [s6_393] (by decide) s5_680_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_393_safe
def s5_681 : State := ⟨[1,12,209,145], 822752278660603021122086421958103419712902851183438164459196694, 3, 1, 1, 0⟩
theorem s5_681_edges : next config 5 s5_681 = [s6_394] := by decide
theorem s5_681_safe : Safe 8 5 s5_681 := by
  apply safe_succ 7 5 s5_681 [s6_394] (by decide) s5_681_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_394_safe
def s5_682 : State := ⟨[1,12,210,145], 1645504557321206042221871758435309295345806576059852752477557014, 2, 0, 1, 0⟩
theorem s5_682_edges : next config 5 s5_682 = [s6_396, s6_418] := by decide
theorem s5_682_safe : Safe 8 5 s5_682 := by
  apply safe_succ 7 5 s5_682 [s6_396, s6_418] (by decide) s5_682_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_396_safe
  · subst z; exact s6_418_safe
def s5_683 : State := ⟨[1,12,210,145], 2056880696651507552760614054074646921591490468681271423476502806, 2, 0, 1, 0⟩
theorem s5_683_edges : next config 5 s5_683 = [s6_397, s6_420] := by decide
theorem s5_683_safe : Safe 8 5 s5_683 := by
  apply safe_succ 7 5 s5_683 [s6_397, s6_420] (by decide) s5_683_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_397_safe
  · subst z; exact s6_420_safe
def s5_684 : State := ⟨[1,12,225,145], 53919893334301279589334074776550505509362615469440525162897085632790, 2, 0, 1, 0⟩
theorem s5_684_edges : next config 5 s5_684 = [s6_400] := by decide
theorem s5_684_safe : Safe 8 5 s5_684 := by
  apply safe_succ 7 5 s5_684 [s6_400] (by decide) s5_684_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_400_safe
def s5_685 : State := ⟨[1,12,240,145], 1766847064778384329583297500809821091705442766466852109025240389127311638, 2, 0, 1, 0⟩
theorem s5_685_edges : next config 5 s5_685 = [s6_403] := by decide
theorem s5_685_safe : Safe 8 5 s5_685 := by
  apply safe_succ 7 5 s5_685 [s6_403] (by decide) s5_685_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_403_safe
def s5_686 : State := ⟨[1,12,241,145], 3533694129556768659166595001530439542899129882077862275623413092450373910, 2, 0, 1, 0⟩
theorem s5_686_edges : next config 5 s5_686 = [s6_726, s6_405] := by decide
theorem s5_686_safe : Safe 8 5 s5_686 := by
  apply safe_succ 7 5 s5_686 [s6_726, s6_405] (by decide) s5_686_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_726_safe
  · subst z; exact s6_405_safe
def s5_687 : State := ⟨[1,12,241,145], 3533694129556768659166595001552739607532926663342471067146846590419931414, 2, 0, 1, 0⟩
theorem s5_687_edges : next config 5 s5_687 = [s6_727, s6_408] := by decide
theorem s5_687_safe : Safe 8 5 s5_687 := by
  apply safe_succ 7 5 s5_687 [s6_727, s6_408] (by decide) s5_687_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_727_safe
  · subst z; exact s6_408_safe
def s5_688 : State := ⟨[1,21,65,145], 44601830679428167221534955260136380206088470, 3, 1, 1, 0⟩
theorem s5_688_edges : next config 5 s5_688 = [s6_544, s6_533] := by decide
theorem s5_688_safe : Safe 8 5 s5_688 := by
  apply safe_succ 7 5 s5_688 [s6_544, s6_533] (by decide) s5_688_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_544_safe
  · subst z; exact s6_533_safe
def s5_689 : State := ⟨[1,21,66,145], 44601830679428167221534992153624527625191702, 3, 1, 1, 0⟩
theorem s5_689_edges : next config 5 s5_689 = [s6_545, s6_534, s6_535] := by decide
theorem s5_689_safe : Safe 8 5 s5_689 := by
  apply safe_succ 7 5 s5_689 [s6_545, s6_534, s6_535] (by decide) s5_689_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_545_safe
  · subst z; exact s6_534_safe
  · subst z; exact s6_535_safe
def s5_690 : State := ⟨[1,21,68,145], 44601830679428167221535213514553412139811094, 3, 1, 1, 0⟩
theorem s5_690_edges : next config 5 s5_690 = [] := by decide
theorem s5_690_safe : Safe 8 5 s5_690 := by
  apply safe_succ 7 5 s5_690 [] (by decide) s5_690_edges
  simp
def s5_691 : State := ⟨[1,21,80,145], 44601830679428167222743844186262861961691414, 3, 1, 1, 0⟩
theorem s5_691_edges : next config 5 s5_691 = [s6_536] := by decide
theorem s5_691_safe : Safe 8 5 s5_691 := by
  apply safe_succ 7 5 s5_691 [s6_536] (by decide) s5_691_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_536_safe
def s5_692 : State := ⟨[1,21,81,145], 44601830679428167223952770005877491136397590, 3, 1, 1, 0⟩
theorem s5_692_edges : next config 5 s5_692 = [] := by decide
theorem s5_692_safe : Safe 8 5 s5_692 := by
  apply safe_succ 7 5 s5_692 [] (by decide) s5_692_edges
  simp
def s5_693 : State := ⟨[1,21,96,145], 44601830679428246449697432630985826330935574, 3, 1, 1, 0⟩
theorem s5_693_edges : next config 5 s5_693 = [s6_1357, s6_729, s6_742, s6_1019, s6_614, s6_546, s6_547, s6_537, s6_542, s6_543, s6_539, s6_540] := by decide
theorem s5_693_safe : Safe 8 5 s5_693 := by
  apply safe_succ 7 5 s5_693 [s6_1357, s6_729, s6_742, s6_1019, s6_614, s6_546, s6_547, s6_537, s6_542, s6_543, s6_539, s6_540] (by decide) s5_693_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1357_safe
  · subst z; exact s6_729_safe
  · subst z; exact s6_742_safe
  · subst z; exact s6_1019_safe
  · subst z; exact s6_614_safe
  · subst z; exact s6_546_safe
  · subst z; exact s6_547_safe
  · subst z; exact s6_537_safe
  · subst z; exact s6_542_safe
  · subst z; exact s6_543_safe
  · subst z; exact s6_539_safe
  · subst z; exact s6_540_safe
def s5_694 : State := ⟨[1,21,209,145], 822752278660603021122086421958103419712902851183438164461289750, 3, 1, 1, 0⟩
theorem s5_694_edges : next config 5 s5_694 = [] := by decide
theorem s5_694_safe : Safe 8 5 s5_694 := by
  apply safe_succ 7 5 s5_694 [] (by decide) s5_694_edges
  simp
def s5_695 : State := ⟨[1,29,64,145], 44601830679428167221534918366648233323856150, 3, 1, 1, 0⟩
theorem s5_695_edges : next config 5 s5_695 = [s6_1291, s6_731, s6_1020, s6_544, s6_545, s6_546] := by decide
theorem s5_695_safe : Safe 8 5 s5_695 := by
  apply safe_succ 7 5 s5_695 [s6_1291, s6_731, s6_1020, s6_544, s6_545, s6_546] (by decide) s5_695_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1291_safe
  · subst z; exact s6_731_safe
  · subst z; exact s6_1020_safe
  · subst z; exact s6_544_safe
  · subst z; exact s6_545_safe
  · subst z; exact s6_546_safe
def s5_696 : State := ⟨[1,53,64,145], 44601830679428167221534918375655432041726230, 3, 1, 1, 0⟩
theorem s5_696_edges : next config 5 s5_696 = [s6_732, s6_547] := by decide
theorem s5_696_safe : Safe 8 5 s5_696 := by
  apply safe_succ 7 5 s5_696 [s6_732, s6_547] (by decide) s5_696_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_732_safe
  · subst z; exact s6_547_safe
def s5_697 : State := ⟨[1,68,96,145], 44601830679428246449697727778891005681664278, 3, 1, 1, 0⟩
theorem s5_697_edges : next config 5 s5_697 = [s6_549] := by decide
theorem s5_697_safe : Safe 8 5 s5_697 := by
  apply safe_succ 7 5 s5_697 [s6_549] (by decide) s5_697_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_549_safe
def s5_698 : State := ⟨[1,68,96,214], 26328072917139296674568711603123565256210396867959895269344084246, 2, 0, 1, 0⟩
theorem s5_698_edges : next config 5 s5_698 = [s6_550] := by decide
theorem s5_698_safe : Safe 8 5 s5_698 := by
  apply safe_succ 7 5 s5_698 [s6_550] (by decide) s5_698_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_550_safe
def s5_699 : State := ⟨[1,68,96,214], 26328072917139296674591010987192628195598078732734113903777218838, 2, 0, 1, 0⟩
theorem s5_699_edges : next config 5 s5_699 = [s6_551] := by decide
theorem s5_699_safe : Safe 8 5 s5_699 := by
  apply safe_succ 7 5 s5_699 [s6_551] (by decide) s5_699_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_551_safe
def s5_700 : State := ⟨[1,68,104,145], 44602511244182370736228306198529816469242134, 2, 0, 1, 0⟩
theorem s5_700_edges : next config 5 s5_700 = [] := by decide
theorem s5_700_safe : Safe 8 5 s5_700 := by
  apply safe_succ 7 5 s5_700 [] (by decide) s5_700_edges
  simp
def s5_701 : State := ⟨[1,68,104,145], 66902575877979152000837097721963314438799638, 2, 0, 1, 0⟩
theorem s5_701_edges : next config 5 s5_701 = [] := by decide
theorem s5_701_safe : Safe 8 5 s5_701 := by
  apply safe_succ 7 5 s5_701 [] (by decide) s5_701_edges
  simp
def s5_702 : State := ⟨[1,68,104,146], 89204682205977458896226669493041403017625878, 2, 0, 1, 0⟩
theorem s5_702_edges : next config 5 s5_702 = [s6_622, s6_550] := by decide
theorem s5_702_safe : Safe 8 5 s5_702 := by
  apply safe_succ 7 5 s5_702 [s6_622, s6_550] (by decide) s5_702_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_622_safe
  · subst z; exact s6_550_safe
def s5_703 : State := ⟨[1,68,104,146], 111504066275040398283908534267260037450760470, 2, 0, 1, 0⟩
theorem s5_703_edges : next config 5 s5_703 = [s6_623, s6_551] := by decide
theorem s5_703_safe : Safe 8 5 s5_703 := by
  apply safe_succ 7 5 s5_703 [s6_623, s6_551] (by decide) s5_703_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_623_safe
  · subst z; exact s6_551_safe
def s5_704 : State := ⟨[1,86,82,145], 44602511244162009180668874636634175039406358, 2, 0, 1, 0⟩
theorem s5_704_edges : next config 5 s5_704 = [s6_74] := by decide
theorem s5_704_safe : Safe 8 5 s5_704 := by
  apply safe_succ 7 5 s5_704 [s6_74] (by decide) s5_704_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_74_safe
def s5_705 : State := ⟨[1,86,82,145], 44602511244162009181877726669272509375906070, 2, 0, 1, 0⟩
theorem s5_705_edges : next config 5 s5_705 = [s6_75] := by decide
theorem s5_705_safe : Safe 8 5 s5_705 := by
  apply safe_succ 7 5 s5_705 [s6_75] (by decide) s5_705_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_75_safe
def s5_706 : State := ⟨[1,86,82,145], 66902575877958790445277666160067673008963862, 2, 0, 1, 0⟩
theorem s5_706_edges : next config 5 s5_706 = [s6_78] := by decide
theorem s5_706_safe : Safe 8 5 s5_706 := by
  apply safe_succ 7 5 s5_706 [s6_78] (by decide) s5_706_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_78_safe
def s5_707 : State := ⟨[1,86,82,145], 66902575877958790446486518192706007345463574, 2, 0, 1, 0⟩
theorem s5_707_edges : next config 5 s5_707 = [s6_79] := by decide
theorem s5_707_safe : Safe 8 5 s5_707 := by
  apply safe_succ 7 5 s5_707 [s6_79] (by decide) s5_707_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_79_safe
def s5_708 : State := ⟨[1,100,96,129], 1020847102109694153151064305463556374814, 3, 1, 1, 0⟩
theorem s5_708_edges : next config 5 s5_708 = [s6_86, s6_558, s6_554] := by decide
theorem s5_708_safe : Safe 8 5 s5_708 := by
  apply safe_succ 7 5 s5_708 [s6_86, s6_558, s6_554] (by decide) s5_708_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_86_safe
  · subst z; exact s6_558_safe
  · subst z; exact s6_554_safe
def s5_709 : State := ⟨[1,100,96,129], 1020847102109694153187957793610975478038, 3, 1, 1, 0⟩
theorem s5_709_edges : next config 5 s5_709 = [s6_87, s6_559, s6_555] := by decide
theorem s5_709_safe : Safe 8 5 s5_709 := by
  apply safe_succ 7 5 s5_709 [s6_87, s6_559, s6_555] (by decide) s5_709_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_87_safe
  · subst z; exact s6_559_safe
  · subst z; exact s6_555_safe
def s5_710 : State := ⟨[1,100,96,130], 1701411835951571080077813520327092797726, 3, 1, 1, 0⟩
theorem s5_710_edges : next config 5 s5_710 = [s6_92, s6_560] := by decide
theorem s5_710_safe : Safe 8 5 s5_710 := by
  apply safe_succ 7 5 s5_710 [s6_92, s6_560] (by decide) s5_710_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_92_safe
  · subst z; exact s6_560_safe
def s5_711 : State := ⟨[1,100,96,130], 1701411835951571080114707008474511900950, 3, 1, 1, 0⟩
theorem s5_711_edges : next config 5 s5_711 = [s6_93, s6_561] := by decide
theorem s5_711_safe : Safe 8 5 s5_711 := by
  apply safe_succ 7 5 s5_711 [s6_93, s6_561] (by decide) s5_711_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_93_safe
  · subst z; exact s6_561_safe
def s5_712 : State := ⟨[1,100,96,130], 4423670771319078787784810379781238489366, 3, 1, 1, 0⟩
theorem s5_712_edges : next config 5 s5_712 = [s6_95, s6_562] := by decide
theorem s5_712_safe : Safe 8 5 s5_712 := by
  apply safe_succ 7 5 s5_712 [s6_95, s6_562] (by decide) s5_712_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_95_safe
  · subst z; exact s6_562_safe
def s5_713 : State := ⟨[1,100,96,131], 3062541303635324933931311950054165643550, 3, 1, 1, 0⟩
theorem s5_713_edges : next config 5 s5_713 = [s6_97, s6_563] := by decide
theorem s5_713_safe : Safe 8 5 s5_713 := by
  apply safe_succ 7 5 s5_713 [s6_97, s6_563] (by decide) s5_713_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_97_safe
  · subst z; exact s6_563_safe
def s5_714 : State := ⟨[1,100,96,132], 5784800239002832641638308809508311335198, 3, 1, 1, 0⟩
theorem s5_714_edges : next config 5 s5_714 = [s6_102, s6_564] := by decide
theorem s5_714_safe : Safe 8 5 s5_714 := by
  apply safe_succ 7 5 s5_714 [s6_102, s6_564] (by decide) s5_714_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_102_safe
  · subst z; exact s6_564_safe
def s5_715 : State := ⟨[1,100,96,132], 5784800239002832641675202297655730438422, 3, 1, 1, 0⟩
theorem s5_715_edges : next config 5 s5_715 = [s6_103, s6_565] := by decide
theorem s5_715_safe : Safe 8 5 s5_715 := by
  apply safe_succ 7 5 s5_715 [s6_103, s6_565] (by decide) s5_715_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_103_safe
  · subst z; exact s6_565_safe
def s5_716 : State := ⟨[1,100,96,136], 87452568300028063872848214593132682084638, 3, 1, 1, 0⟩
theorem s5_716_edges : next config 5 s5_716 = [s6_108, s6_566] := by decide
theorem s5_716_safe : Safe 8 5 s5_716 := by
  apply safe_succ 7 5 s5_716 [s6_108, s6_566] (by decide) s5_716_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_108_safe
  · subst z; exact s6_566_safe
def s5_717 : State := ⟨[1,100,96,136], 87452568300028063872885108081280101187862, 3, 1, 1, 0⟩
theorem s5_717_edges : next config 5 s5_717 = [s6_109, s6_567] := by decide
theorem s5_717_safe : Safe 8 5 s5_717 := by
  apply safe_succ 7 5 s5_717 [s6_109, s6_567] (by decide) s5_717_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_109_safe
  · subst z; exact s6_567_safe
def s5_718 : State := ⟨[1,100,96,144], 22301085480898890958761942587738961525932318, 3, 1, 1, 0⟩
theorem s5_718_edges : next config 5 s5_718 = [s6_122, s6_568, s6_556] := by decide
theorem s5_718_safe : Safe 8 5 s5_718 := by
  apply safe_succ 7 5 s5_718 [s6_122, s6_568, s6_556] (by decide) s5_718_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_122_safe
  · subst z; exact s6_568_safe
  · subst z; exact s6_556_safe
def s5_719 : State := ⟨[1,100,96,144], 22301085480898890958761979481227108945035542, 3, 1, 1, 0⟩
theorem s5_719_edges : next config 5 s5_719 = [s6_123, s6_569, s6_557] := by decide
theorem s5_719_safe : Safe 8 5 s5_719 := by
  apply safe_succ 7 5 s5_719 [s6_123, s6_569, s6_557] (by decide) s5_719_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_123_safe
  · subst z; exact s6_569_safe
  · subst z; exact s6_557_safe
def s5_720 : State := ⟨[1,100,96,145], 44601830679429514100297660860387323032043798, 3, 1, 1, 0⟩
theorem s5_720_edges : next config 5 s5_720 = [s6_733, s6_127, s6_570] := by decide
theorem s5_720_safe : Safe 8 5 s5_720 := by
  apply safe_succ 7 5 s5_720 [s6_733, s6_127, s6_570] (by decide) s5_720_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_733_safe
  · subst z; exact s6_127_safe
  · subst z; exact s6_570_safe
def s5_721 : State := ⟨[1,100,96,160], 1461501637671185286471502058940598110255952494878, 3, 1, 1, 0⟩
theorem s5_721_edges : next config 5 s5_721 = [s6_134, s6_571] := by decide
theorem s5_721_safe : Safe 8 5 s5_721 := by
  apply safe_succ 7 5 s5_721 [s6_134, s6_571] (by decide) s5_721_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_134_safe
  · subst z; exact s6_571_safe
def s5_722 : State := ⟨[1,100,96,160], 1461501637671185286471502058977491598403371598102, 3, 1, 1, 0⟩
theorem s5_722_edges : next config 5 s5_722 = [s6_135, s6_572] := by decide
theorem s5_722_safe : Safe 8 5 s5_722 := by
  apply safe_succ 7 5 s5_722 [s6_135, s6_572] (by decide) s5_722_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_135_safe
  · subst z; exact s6_572_safe
def s5_723 : State := ⟨[1,100,96,192], 6277101735386680764176071791475483642326670535064054464798, 3, 1, 1, 0⟩
theorem s5_723_edges : next config 5 s5_723 = [s6_158, s6_573] := by decide
theorem s5_723_safe : Safe 8 5 s5_723 := by
  apply safe_succ 7 5 s5_723 [s6_158, s6_573] (by decide) s5_723_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_158_safe
  · subst z; exact s6_573_safe
def s5_724 : State := ⟨[1,100,96,192], 6277101735386680764176071791475483642363564023211473568022, 3, 1, 1, 0⟩
theorem s5_724_edges : next config 5 s5_724 = [s6_159, s6_574] := by decide
theorem s5_724_safe : Safe 8 5 s5_724 := by
  apply safe_succ 7 5 s5_724 [s6_159, s6_574] (by decide) s5_724_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_159_safe
  · subst z; exact s6_574_safe
def s5_725 : State := ⟨[1,100,96,192], 18831305206160042291847650637890816474531381423992123490582, 3, 1, 1, 0⟩
theorem s5_725_edges : next config 5 s5_725 = [s6_161, s6_575] := by decide
theorem s5_725_safe : Safe 8 5 s5_725 := by
  apply safe_succ 7 5 s5_725 [s6_161, s6_575] (by decide) s5_725_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_161_safe
  · subst z; exact s6_575_safe
def s5_726 : State := ⟨[1,100,96,193], 12554203470773361528011861214683150058465919467675508080918, 3, 1, 1, 0⟩
theorem s5_726_edges : next config 5 s5_726 = [s6_163, s6_576] := by decide
theorem s5_726_safe : Safe 8 5 s5_726 := by
  apply safe_succ 7 5 s5_726 [s6_163, s6_576] (by decide) s5_726_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_163_safe
  · subst z; exact s6_576_safe
def s5_727 : State := ⟨[1,100,96,224], 26959946667150639794667015087359913041904961648764887571703630201118, 3, 1, 1, 0⟩
theorem s5_727_edges : next config 5 s5_727 = [s6_184, s6_577] := by decide
theorem s5_727_safe : Safe 8 5 s5_727 := by
  apply safe_succ 7 5 s5_727 [s6_184, s6_577] (by decide) s5_727_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_184_safe
  · subst z; exact s6_577_safe
def s5_728 : State := ⟨[1,100,96,224], 26959946667150639794667015087359913041904961648801781059851049304342, 3, 1, 1, 0⟩
theorem s5_728_edges : next config 5 s5_728 = [s6_185, s6_578] := by decide
theorem s5_728_safe : Safe 8 5 s5_728 := by
  apply safe_succ 7 5 s5_728 [s6_185, s6_578] (by decide) s5_728_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_185_safe
  · subst z; exact s6_578_safe
def s5_729 : State := ⟨[1,100,96,228], 431359146674410236714672241392654373146462127986873474788257783939358, 3, 1, 1, 0⟩
theorem s5_729_edges : next config 5 s5_729 = [s6_190, s6_579] := by decide
theorem s5_729_safe : Safe 8 5 s5_729 := by
  apply safe_succ 7 5 s5_729 [s6_190, s6_579] (by decide) s5_729_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_190_safe
  · subst z; exact s6_579_safe
def s5_730 : State := ⟨[1,100,96,228], 431359146674410236714672241392654373146462127986910368276405203042582, 3, 1, 1, 0⟩
theorem s5_730_edges : next config 5 s5_730 = [s6_191, s6_580] := by decide
theorem s5_730_safe : Safe 8 5 s5_730 := by
  apply safe_succ 7 5 s5_730 [s6_191, s6_580] (by decide) s5_730_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_191_safe
  · subst z; exact s6_580_safe
def s5_731 : State := ⟨[1,100,104,128], 340282388550226829875985514547271237918, 3, 1, 0, 0⟩
theorem s5_731_edges : next config 5 s5_731 = [s6_925, s6_558, s6_579, s6_581, s6_560, s6_566, s6_568, s6_571] := by decide
theorem s5_731_safe : Safe 8 5 s5_731 := by
  apply safe_succ 7 5 s5_731 [s6_925, s6_558, s6_579, s6_581, s6_560, s6_566, s6_568, s6_571] (by decide) s5_731_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_925_safe
  · subst z; exact s6_558_safe
  · subst z; exact s6_579_safe
  · subst z; exact s6_581_safe
  · subst z; exact s6_560_safe
  · subst z; exact s6_566_safe
  · subst z; exact s6_568_safe
  · subst z; exact s6_571_safe
def s5_732 : State := ⟨[1,100,104,128], 340282388550226829912879002694690341142, 3, 1, 0, 0⟩
theorem s5_732_edges : next config 5 s5_732 = [s6_927, s6_559, s6_580, s6_582, s6_561, s6_567, s6_569, s6_572] := by decide
theorem s5_732_safe : Safe 8 5 s5_732 := by
  apply safe_succ 7 5 s5_732 [s6_927, s6_559, s6_580, s6_582, s6_561, s6_567, s6_569, s6_572] (by decide) s5_732_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_927_safe
  · subst z; exact s6_559_safe
  · subst z; exact s6_580_safe
  · subst z; exact s6_582_safe
  · subst z; exact s6_561_safe
  · subst z; exact s6_567_safe
  · subst z; exact s6_569_safe
  · subst z; exact s6_572_safe
def s5_733 : State := ⟨[1,100,104,131], 3743106057759611464509731588864953352470, 2, 0, 1, 0⟩
theorem s5_733_edges : next config 5 s5_733 = [] := by decide
theorem s5_733_safe : Safe 8 5 s5_733 := by
  apply safe_succ 7 5 s5_733 [] (by decide) s5_733_edges
  simp
def s5_734 : State := ⟨[1,100,104,131], 4423670791601488391436480803728489775382, 2, 0, 1, 0⟩
theorem s5_734_edges : next config 5 s5_734 = [] := by decide
theorem s5_734_safe : Safe 8 5 s5_734 := by
  apply safe_succ 7 5 s5_734 [] (by decide) s5_734_edges
  simp
def s5_735 : State := ⟨[1,100,104,145], 44602511244183638386828239280026133819621654, 2, 0, 1, 0⟩
theorem s5_735_edges : next config 5 s5_735 = [s6_734] := by decide
theorem s5_735_safe : Safe 8 5 s5_735 := by
  apply safe_succ 7 5 s5_735 [s6_734] (by decide) s5_735_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_734_safe
def s5_736 : State := ⟨[1,100,104,145], 66902575877980419651437030803459631789179158, 2, 0, 1, 0⟩
theorem s5_736_edges : next config 5 s5_736 = [s6_735] := by decide
theorem s5_736_safe : Safe 8 5 s5_736 := by
  apply safe_succ 7 5 s5_736 [s6_735] (by decide) s5_736_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_735_safe
def s5_737 : State := ⟨[1,100,104,146], 89204682205978726546826602574537720368005398, 2, 0, 1, 0⟩
theorem s5_737_edges : next config 5 s5_737 = [] := by decide
theorem s5_737_safe : Safe 8 5 s5_737 := by
  apply safe_succ 7 5 s5_737 [] (by decide) s5_737_edges
  simp
def s5_738 : State := ⟨[1,100,104,146], 111504066275041665934508467348756354801139990, 2, 0, 1, 0⟩
theorem s5_738_edges : next config 5 s5_738 = [] := by decide
theorem s5_738_safe : Safe 8 5 s5_738 := by
  apply safe_succ 7 5 s5_738 [] (by decide) s5_738_edges
  simp
def s5_739 : State := ⟨[1,100,104,162], 5846006551025023529048720014594616022898074255638, 2, 0, 1, 0⟩
theorem s5_739_edges : next config 5 s5_739 = [] := by decide
theorem s5_739_safe : Safe 8 5 s5_739 := by
  apply safe_succ 7 5 s5_739 [] (by decide) s5_739_edges
  simp
def s5_740 : State := ⟨[1,100,104,162], 7307508186994796979568650993457400612826933952790, 2, 0, 1, 0⟩
theorem s5_740_edges : next config 5 s5_740 = [] := by decide
theorem s5_740_safe : Safe 8 5 s5_740 := by
  apply safe_succ 7 5 s5_740 [] (by decide) s5_740_edges
  simp
def s5_741 : State := ⟨[1,100,104,176], 95780971326419139128315862565259918234334103913693462, 2, 0, 1, 0⟩
theorem s5_741_edges : next config 5 s5_741 = [] := by decide
theorem s5_741_safe : Safe 8 5 s5_741 := by
  apply safe_succ 7 5 s5_741 [] (by decide) s5_741_edges
  simp
def s5_742 : State := ⟨[1,100,104,176], 95782432805755724832703443108556916244705398340256022, 2, 0, 1, 0⟩
theorem s5_742_edges : next config 5 s5_742 = [] := by decide
theorem s5_742_safe : Safe 8 5 s5_742 := by
  apply safe_succ 7 5 s5_742 [] (by decide) s5_742_edges
  simp
def s5_743 : State := ⟨[1,100,104,193], 12554203470773361528692425968807436589007445618338876686614, 2, 0, 1, 0⟩
theorem s5_743_edges : next config 5 s5_743 = [] := by decide
theorem s5_743_safe : Safe 8 5 s5_743 := by
  apply safe_succ 7 5 s5_743 [] (by decide) s5_743_edges
  simp
def s5_744 : State := ⟨[1,100,104,193], 18831305206160042291847650658173226078183051847939374776598, 2, 0, 1, 0⟩
theorem s5_744_edges : next config 5 s5_744 = [] := by decide
theorem s5_744_safe : Safe 8 5 s5_744 := by
  apply safe_succ 7 5 s5_744 [] (by decide) s5_744_edges
  simp
def s5_745 : State := ⟨[1,100,104,194], 25108406941546723057044569549064646348138905722130482135318, 2, 0, 1, 0⟩
theorem s5_745_edges : next config 5 s5_745 = [] := by decide
theorem s5_745_safe : Safe 8 5 s5_745 := by
  apply safe_succ 7 5 s5_745 [] (by decide) s5_745_edges
  simp
def s5_746 : State := ⟨[1,100,104,194], 31385508676933403819519229504588558910387762736867443802390, 2, 0, 1, 0⟩
theorem s5_746_edges : next config 5 s5_746 = [] := by decide
theorem s5_746_safe : Safe 8 5 s5_746 := by
  apply safe_succ 7 5 s5_746 [] (by decide) s5_746_edges
  simp
def s5_747 : State := ⟨[1,108,104,128], 340282711801129888074482896206588608798, 3, 1, 0, 0⟩
theorem s5_747_edges : next config 5 s5_747 = [s6_928, s6_206, s6_583, s6_612, s6_610, s6_585, s6_591, s6_593, s6_596] := by decide
theorem s5_747_safe : Safe 8 5 s5_747 := by
  apply safe_succ 7 5 s5_747 [s6_928, s6_206, s6_583, s6_612, s6_610, s6_585, s6_591, s6_593, s6_596] (by decide) s5_747_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_928_safe
  · subst z; exact s6_206_safe
  · subst z; exact s6_583_safe
  · subst z; exact s6_612_safe
  · subst z; exact s6_610_safe
  · subst z; exact s6_585_safe
  · subst z; exact s6_591_safe
  · subst z; exact s6_593_safe
  · subst z; exact s6_596_safe
def s5_748 : State := ⟨[1,108,104,128], 340282711801129888111376384354007712022, 3, 1, 0, 0⟩
theorem s5_748_edges : next config 5 s5_748 = [s6_930, s6_207, s6_584, s6_613, s6_611, s6_586, s6_592, s6_594, s6_597] := by decide
theorem s5_748_safe : Safe 8 5 s5_748 := by
  apply safe_succ 7 5 s5_748 [s6_930, s6_207, s6_584, s6_613, s6_611, s6_586, s6_592, s6_594, s6_597] (by decide) s5_748_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_930_safe
  · subst z; exact s6_207_safe
  · subst z; exact s6_584_safe
  · subst z; exact s6_613_safe
  · subst z; exact s6_611_safe
  · subst z; exact s6_586_safe
  · subst z; exact s6_592_safe
  · subst z; exact s6_594_safe
  · subst z; exact s6_597_safe
def s5_749 : State := ⟨[1,108,104,131], 3743106381010514522708228970524270723350, 2, 0, 1, 0⟩
theorem s5_749_edges : next config 5 s5_749 = [s6_210] := by decide
theorem s5_749_safe : Safe 8 5 s5_749 := by
  apply safe_succ 7 5 s5_749 [s6_210] (by decide) s5_749_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_210_safe
def s5_750 : State := ⟨[1,108,104,131], 4423671114852391449634978185387807146262, 2, 0, 1, 0⟩
theorem s5_750_edges : next config 5 s5_750 = [s6_213] := by decide
theorem s5_750_safe : Safe 8 5 s5_750 := by
  apply safe_succ 7 5 s5_750 [s6_213] (by decide) s5_750_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_213_safe
def s5_751 : State := ⟨[1,108,104,145], 44602511244506889289886437777407793136992534, 2, 0, 1, 0⟩
theorem s5_751_edges : next config 5 s5_751 = [s6_736, s6_230] := by decide
theorem s5_751_safe : Safe 8 5 s5_751 := by
  apply safe_succ 7 5 s5_751 [s6_736, s6_230] (by decide) s5_751_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_736_safe
  · subst z; exact s6_230_safe
def s5_752 : State := ⟨[1,108,104,145], 66902575878303670554495229300841291106550038, 2, 0, 1, 0⟩
theorem s5_752_edges : next config 5 s5_752 = [s6_737, s6_239] := by decide
theorem s5_752_safe : Safe 8 5 s5_752 := by
  apply safe_succ 7 5 s5_752 [s6_737, s6_239] (by decide) s5_752_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_737_safe
  · subst z; exact s6_239_safe
def s5_753 : State := ⟨[1,108,104,146], 89204682206301977449884801071919379685376278, 2, 0, 1, 0⟩
theorem s5_753_edges : next config 5 s5_753 = [s6_245] := by decide
theorem s5_753_safe : Safe 8 5 s5_753 := by
  apply safe_succ 7 5 s5_753 [s6_245] (by decide) s5_753_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_245_safe
def s5_754 : State := ⟨[1,108,104,146], 111504066275364916837566665846138014118510870, 2, 0, 1, 0⟩
theorem s5_754_edges : next config 5 s5_754 = [s6_252] := by decide
theorem s5_754_safe : Safe 8 5 s5_754 := by
  apply safe_succ 7 5 s5_754 [s6_252] (by decide) s5_754_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_252_safe
def s5_755 : State := ⟨[1,108,104,162], 5846006551025023852299623072793113404557391626518, 2, 0, 1, 0⟩
theorem s5_755_edges : next config 5 s5_755 = [s6_263] := by decide
theorem s5_755_safe : Safe 8 5 s5_755 := by
  apply safe_succ 7 5 s5_755 [s6_263] (by decide) s5_755_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_263_safe
def s5_756 : State := ⟨[1,108,104,162], 7307508186994797302819554051655897994486251323670, 2, 0, 1, 0⟩
theorem s5_756_edges : next config 5 s5_756 = [s6_271] := by decide
theorem s5_756_safe : Safe 8 5 s5_756 := by
  apply safe_succ 7 5 s5_756 [s6_271] (by decide) s5_756_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_271_safe
def s5_757 : State := ⟨[1,108,104,176], 95780971326419139128639113468318116731715763231064342, 2, 0, 1, 0⟩
theorem s5_757_edges : next config 5 s5_757 = [s6_290] := by decide
theorem s5_757_safe : Safe 8 5 s5_757 := by
  apply safe_succ 7 5 s5_757 [s6_290] (by decide) s5_757_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_290_safe
def s5_758 : State := ⟨[1,108,104,176], 95782432805755724833026694011615114742087057657626902, 2, 0, 1, 0⟩
theorem s5_758_edges : next config 5 s5_758 = [s6_295] := by decide
theorem s5_758_safe : Safe 8 5 s5_758 := by
  apply safe_succ 7 5 s5_758 [s6_295] (by decide) s5_758_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_295_safe
def s5_759 : State := ⟨[1,108,104,193], 12554203470773361528692426292058339647205942999998194057494, 2, 0, 1, 0⟩
theorem s5_759_edges : next config 5 s5_759 = [s6_306] := by decide
theorem s5_759_safe : Safe 8 5 s5_759 := by
  apply safe_succ 7 5 s5_759 [s6_306] (by decide) s5_759_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_306_safe
def s5_760 : State := ⟨[1,108,104,193], 18831305206160042291847650981424129136381549229598692147478, 2, 0, 1, 0⟩
theorem s5_760_edges : next config 5 s5_760 = [s6_309] := by decide
theorem s5_760_safe : Safe 8 5 s5_760 := by
  apply safe_succ 7 5 s5_760 [s6_309] (by decide) s5_760_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_309_safe
def s5_761 : State := ⟨[1,108,104,194], 25108406941546723057044569872315549406337403103789799506198, 2, 0, 1, 0⟩
theorem s5_761_edges : next config 5 s5_761 = [s6_312, s6_604] := by decide
theorem s5_761_safe : Safe 8 5 s5_761 := by
  apply safe_succ 7 5 s5_761 [s6_312, s6_604] (by decide) s5_761_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_312_safe
  · subst z; exact s6_604_safe
def s5_762 : State := ⟨[1,108,104,194], 31385508676933403819519229827839461968586260118526761173270, 2, 0, 1, 0⟩
theorem s5_762_edges : next config 5 s5_762 = [s6_315, s6_605] := by decide
theorem s5_762_safe : Safe 8 5 s5_762 := by
  apply safe_succ 7 5 s5_762 [s6_315, s6_605] (by decide) s5_762_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_315_safe
  · subst z; exact s6_605_safe
def s5_763 : State := ⟨[1,108,104,208], 411376139330301510561043381120580050517107759163939533931741462, 2, 0, 1, 0⟩
theorem s5_763_edges : next config 5 s5_763 = [s6_317, s6_606] := by decide
theorem s5_763_safe : Safe 8 5 s5_763 := by
  apply safe_succ 7 5 s5_763 [s6_317, s6_606] (by decide) s5_763_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_317_safe
  · subst z; exact s6_606_safe
def s5_764 : State := ⟨[1,108,104,208], 411382416432036897219506471711472635041988143246735636460273942, 2, 0, 1, 0⟩
theorem s5_764_edges : next config 5 s5_764 = [s6_319, s6_607] := by decide
theorem s5_764_safe : Safe 8 5 s5_764 := by
  apply safe_succ 7 5 s5_764 [s6_319, s6_607] (by decide) s5_764_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_319_safe
  · subst z; exact s6_607_safe
def s5_765 : State := ⟨[1,140,67,136], 1481249143206845131456235686847154705465630, 3, 1, 1, 0⟩
theorem s5_765_edges : next config 5 s5_765 = [s6_35] := by decide
theorem s5_765_safe : Safe 8 5 s5_765 := by
  apply safe_succ 7 5 s5_765 [s6_35] (by decide) s5_765_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_35_safe
def s5_766 : State := ⟨[1,140,96,136], 1481249143206924359618602377232158573003038, 3, 1, 1, 0⟩
theorem s5_766_edges : next config 5 s5_766 = [s6_110, s6_615] := by decide
theorem s5_766_safe : Safe 8 5 s5_766 := by
  apply safe_succ 7 5 s5_766 [s6_110, s6_615] (by decide) s5_766_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_110_safe
  · subst z; exact s6_615_safe
def s5_767 : State := ⟨[1,140,96,136], 1481249143206924359618602377232167162937622, 3, 1, 1, 0⟩
theorem s5_767_edges : next config 5 s5_767 = [s6_111, s6_616] := by decide
theorem s5_767_safe : Safe 8 5 s5_767 := by
  apply safe_succ 7 5 s5_767 [s6_111, s6_616] (by decide) s5_767_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_111_safe
  · subst z; exact s6_616_safe
def s5_768 : State := ⟨[1,140,96,136], 1481249143206924359618639270720305992106262, 3, 1, 1, 0⟩
theorem s5_768_edges : next config 5 s5_768 = [s6_112, s6_617] := by decide
theorem s5_768_safe : Safe 8 5 s5_768 := by
  apply safe_succ 7 5 s5_768 [s6_112, s6_617] (by decide) s5_768_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_112_safe
  · subst z; exact s6_617_safe
def s5_769 : State := ⟨[1,140,96,136], 1481249143207082815943630905907345660903702, 3, 1, 1, 0⟩
theorem s5_769_edges : next config 5 s5_769 = [s6_113, s6_618] := by decide
theorem s5_769_safe : Safe 8 5 s5_769 := by
  apply safe_succ 7 5 s5_769 [s6_113, s6_618] (by decide) s5_769_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_113_safe
  · subst z; exact s6_618_safe
def s5_770 : State := ⟨[1,150,104,146], 1516452374911937339954512343794631360047546646, 2, 0, 1, 0⟩
theorem s5_770_edges : next config 5 s5_770 = [s6_253] := by decide
theorem s5_770_safe : Safe 8 5 s5_770 := by
  apply safe_succ 7 5 s5_770 [s6_253] (by decide) s5_770_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_253_safe
def s5_771 : State := ⟨[1,150,104,146], 1538751758981000279342194208568849994480681238, 2, 0, 1, 0⟩
theorem s5_771_edges : next config 5 s5_771 = [s6_254] := by decide
theorem s5_771_safe : Safe 8 5 s5_771 := by
  apply safe_succ 7 5 s5_771 [s6_254] (by decide) s5_771_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_254_safe
def s5_772 : State := ⟨[1,214,67,210], 27973577474460502716656777188955856128786509137225786432719749398, 2, 0, 1, 0⟩
theorem s5_772_edges : next config 5 s5_772 = [s6_65, s6_619] := by decide
theorem s5_772_safe : Safe 8 5 s5_772 := by
  apply safe_succ 7 5 s5_772 [s6_65, s6_619] (by decide) s5_772_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_65_safe
  · subst z; exact s6_619_safe
def s5_773 : State := ⟨[1,214,67,210], 27973602582867444263357531786915018336310637828374915927351820566, 2, 0, 1, 0⟩
theorem s5_773_edges : next config 5 s5_773 = [s6_66, s6_620] := by decide
theorem s5_773_safe : Safe 8 5 s5_773 := by
  apply safe_succ 7 5 s5_773 [s6_66, s6_620] (by decide) s5_773_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_66_safe
  · subst z; exact s6_620_safe
def s5_774 : State := ⟨[1,214,96,146], 26328072917139296674568711603123565256210396867959895269344084246, 2, 0, 1, 0⟩
theorem s5_774_edges : next config 5 s5_774 = [s6_622] := by decide
theorem s5_774_safe : Safe 8 5 s5_774 := by
  apply safe_succ 7 5 s5_774 [s6_622] (by decide) s5_774_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_622_safe
def s5_775 : State := ⟨[1,214,96,146], 26328072917139296674591010987192628195598078732734113903777218838, 2, 0, 1, 0⟩
theorem s5_775_edges : next config 5 s5_775 = [s6_623] := by decide
theorem s5_775_safe : Safe 8 5 s5_775 := by
  apply safe_succ 7 5 s5_775 [s6_623] (by decide) s5_775_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_623_safe
def s5_776 : State := ⟨[1,214,96,146], 26328072917139296675995959295829525137268682542261485226374005014, 2, 0, 1, 0⟩
theorem s5_776_edges : next config 5 s5_776 = [s6_624] := by decide
theorem s5_776_safe : Safe 8 5 s5_776 := by
  apply safe_succ 7 5 s5_776 [s6_624] (by decide) s5_776_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_624_safe
def s5_777 : State := ⟨[1,214,96,146], 26328072917139296676018258679898588076656364407035703860807139606, 2, 0, 1, 0⟩
theorem s5_777_edges : next config 5 s5_777 = [s6_625] := by decide
theorem s5_777_safe : Safe 8 5 s5_777 := by
  apply safe_succ 7 5 s5_777 [s6_625] (by decide) s5_777_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_625_safe
def s5_778 : State := ⟨[1,214,96,210], 27973577474460502716723680785680915761193132438445569953339867414, 2, 0, 1, 0⟩
theorem s5_778_edges : next config 5 s5_778 = [s6_172, s6_626] := by decide
theorem s5_778_safe : Safe 8 5 s5_778 := by
  apply safe_succ 7 5 s5_778 [s6_172, s6_626] (by decide) s5_778_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_172_safe
  · subst z; exact s6_626_safe
def s5_779 : State := ⟨[1,214,96,210], 27973577474460502716745980169749978700580814303219788587773002006, 2, 0, 1, 0⟩
theorem s5_779_edges : next config 5 s5_779 = [s6_173, s6_627] := by decide
theorem s5_779_safe : Safe 8 5 s5_779 := by
  apply safe_succ 7 5 s5_779 [s6_173, s6_627] (by decide) s5_779_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_173_safe
  · subst z; exact s6_627_safe
def s5_780 : State := ⟨[1,214,96,210], 27973602582867444263357533148044486099292653974776754363453997334, 2, 0, 1, 0⟩
theorem s5_780_edges : next config 5 s5_780 = [s6_174, s6_628] := by decide
theorem s5_780_safe : Safe 8 5 s5_780 := by
  apply safe_succ 7 5 s5_780 [s6_174, s6_628] (by decide) s5_780_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_174_safe
  · subst z; exact s6_628_safe
def s5_781 : State := ⟨[1,214,96,210], 27973608859969179650038295622704441623205216223633769100415664406, 2, 0, 1, 0⟩
theorem s5_781_edges : next config 5 s5_781 = [s6_175, s6_629] := by decide
theorem s5_781_safe : Safe 8 5 s5_781 := by
  apply safe_succ 7 5 s5_781 [s6_175, s6_629] (by decide) s5_781_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_175_safe
  · subst z; exact s6_629_safe
def s5_782 : State := ⟨[1,214,96,210], 28384953613790804227195519484595193834260355396537590107586232598, 2, 0, 1, 0⟩
theorem s5_782_edges : next config 5 s5_782 = [s6_176, s6_630] := by decide
theorem s5_782_safe : Safe 8 5 s5_782 := by
  apply safe_succ 7 5 s5_782 [s6_176, s6_630] (by decide) s5_782_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_176_safe
  · subst z; exact s6_630_safe
def s5_783 : State := ⟨[1,214,96,210], 28384959890892539613853982575186086418785235780620386210114765078, 2, 0, 1, 0⟩
theorem s5_783_edges : next config 5 s5_783 = [s6_177, s6_631] := by decide
theorem s5_783_safe : Safe 8 5 s5_783 := by
  apply safe_succ 7 5 s5_783 [s6_177, s6_631] (by decide) s5_783_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_177_safe
  · subst z; exact s6_631_safe
def s5_784 : State := ⟨[1,214,210,145], 27973577474460502716701378679352917375069580426197130566055297302, 2, 0, 1, 0⟩
theorem s5_784_edges : next config 5 s5_784 = [s6_398, s6_619] := by decide
theorem s5_784_safe : Safe 8 5 s5_784 := by
  apply safe_succ 7 5 s5_784 [s6_398, s6_619] (by decide) s5_784_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_398_safe
  · subst z; exact s6_619_safe
def s5_785 : State := ⟨[1,214,210,145], 28384953613790804227240120974992255001315264318818549237054243094, 2, 0, 1, 0⟩
theorem s5_785_edges : next config 5 s5_785 = [s6_399, s6_621] := by decide
theorem s5_785_safe : Safe 8 5 s5_785 := by
  apply safe_succ 7 5 s5_785 [s6_399, s6_621] (by decide) s5_785_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_399_safe
  · subst z; exact s6_621_safe
def s5_786 : State := ⟨[1,228,96,224], 458319093341560876509339256479674003818831621809185817867864690983198, 3, 1, 1, 0⟩
theorem s5_786_edges : next config 5 s5_786 = [s6_187, s6_632] := by decide
theorem s5_786_safe : Safe 8 5 s5_786 := by
  apply safe_succ 7 5 s5_786 [s6_187, s6_632] (by decide) s5_786_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_187_safe
  · subst z; exact s6_632_safe
def s5_787 : State := ⟨[1,228,96,224], 458319093341560876509339256479674003818831621809222711356012110086422, 3, 1, 1, 0⟩
theorem s5_787_edges : next config 5 s5_787 = [s6_188, s6_633] := by decide
theorem s5_787_safe : Safe 8 5 s5_787 := by
  apply safe_succ 7 5 s5_787 [s6_188, s6_633] (by decide) s5_787_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_188_safe
  · subst z; exact s6_633_safe
def s5_788 : State := ⟨[3,4,64,145], 44602511244162009098461845115863096321184030, 3, 2, 1, 0⟩
theorem s5_788_edges : next config 5 s5_788 = [s6_1401, s6_0, s6_1021, s6_640, s6_650] := by decide
theorem s5_788_safe : Safe 8 5 s5_788 := by
  apply safe_succ 7 5 s5_788 [s6_1401, s6_0, s6_1021, s6_640, s6_650] (by decide) s5_788_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1401_safe
  · subst z; exact s6_0_safe
  · subst z; exact s6_1021_safe
  · subst z; exact s6_640_safe
  · subst z; exact s6_650_safe
def s5_789 : State := ⟨[3,4,64,145], 66902575877958790363070636639296594290741534, 3, 2, 1, 0⟩
theorem s5_789_edges : next config 5 s5_789 = [s6_1402, s6_3, s6_1023, s6_641, s6_652] := by decide
theorem s5_789_safe : Safe 8 5 s5_789 := by
  apply safe_succ 7 5 s5_789 [s6_1402, s6_3, s6_1023, s6_641, s6_652] (by decide) s5_789_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1402_safe
  · subst z; exact s6_3_safe
  · subst z; exact s6_1023_safe
  · subst z; exact s6_641_safe
  · subst z; exact s6_652_safe
def s5_790 : State := ⟨[3,4,64,146], 89204682205957097258460208410374682869567774, 3, 2, 1, 0⟩
theorem s5_790_edges : next config 5 s5_790 = [s6_6, s6_642, s6_654, s6_638] := by decide
theorem s5_790_safe : Safe 8 5 s5_790 := by
  apply safe_succ 7 5 s5_790 [s6_6, s6_642, s6_654, s6_638] (by decide) s5_790_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_6_safe
  · subst z; exact s6_642_safe
  · subst z; exact s6_654_safe
  · subst z; exact s6_638_safe
def s5_791 : State := ⟨[3,4,64,146], 111504066275020036646142073184593317302702366, 3, 2, 1, 0⟩
theorem s5_791_edges : next config 5 s5_791 = [s6_9, s6_643, s6_655, s6_639] := by decide
theorem s5_791_safe : Safe 8 5 s5_791 := by
  apply safe_succ 7 5 s5_791 [s6_9, s6_643, s6_655, s6_639] (by decide) s5_791_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_9_safe
  · subst z; exact s6_643_safe
  · subst z; exact s6_655_safe
  · subst z; exact s6_639_safe
def s5_792 : State := ⟨[3,4,64,162], 5846006551025023507419431648200451859860575818014, 3, 2, 1, 0⟩
theorem s5_792_edges : next config 5 s5_792 = [s6_11, s6_644, s6_656] := by decide
theorem s5_792_safe : Safe 8 5 s5_792 := by
  apply safe_succ 7 5 s5_792 [s6_11, s6_644, s6_656] (by decide) s5_792_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_11_safe
  · subst z; exact s6_644_safe
  · subst z; exact s6_656_safe
def s5_793 : State := ⟨[3,4,64,162], 7307508186994796957939362627063236449789435515166, 3, 2, 1, 0⟩
theorem s5_793_edges : next config 5 s5_793 = [s6_14, s6_645, s6_657] := by decide
theorem s5_793_safe : Safe 8 5 s5_793 := by
  apply safe_succ 7 5 s5_793 [s6_14, s6_645, s6_657] (by decide) s5_793_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_14_safe
  · subst z; exact s6_645_safe
  · subst z; exact s6_657_safe
def s5_794 : State := ⟨[3,4,64,163], 11692013101709764647917924832919082368211378835742, 3, 2, 1, 0⟩
theorem s5_794_edges : next config 5 s5_794 = [s6_19, s6_646, s6_658] := by decide
theorem s5_794_safe : Safe 8 5 s5_794 := by
  apply safe_succ 7 5 s5_794 [s6_19, s6_646, s6_658] (by decide) s5_794_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_19_safe
  · subst z; exact s6_646_safe
  · subst z; exact s6_658_safe
def s5_795 : State := ⟨[3,4,64,163], 13153514736318408630754101957928368528413165687070, 3, 2, 1, 0⟩
theorem s5_795_edges : next config 5 s5_795 = [s6_20, s6_647, s6_659] := by decide
theorem s5_795_safe : Safe 8 5 s5_795 := by
  apply safe_succ 7 5 s5_795 [s6_20, s6_647, s6_659] (by decide) s5_795_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_20_safe
  · subst z; exact s6_647_safe
  · subst z; exact s6_659_safe
def s5_796 : State := ⟨[3,4,64,176], 95780971326419139128294233276893524070171066415255838, 3, 2, 1, 0⟩
theorem s5_796_edges : next config 5 s5_796 = [s6_22, s6_648, s6_660] := by decide
theorem s5_796_safe : Safe 8 5 s5_796 := by
  apply safe_succ 7 5 s5_796 [s6_22, s6_648, s6_660] (by decide) s5_796_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_22_safe
  · subst z; exact s6_648_safe
  · subst z; exact s6_660_safe
def s5_797 : State := ⟨[3,4,64,176], 95782432805755724832681813820190522080542360841818398, 3, 2, 1, 0⟩
theorem s5_797_edges : next config 5 s5_797 = [s6_24, s6_649, s6_661] := by decide
theorem s5_797_safe : Safe 8 5 s5_797 := by
  apply safe_succ 7 5 s5_797 [s6_24, s6_649, s6_661] (by decide) s5_797_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_24_safe
  · subst z; exact s6_649_safe
  · subst z; exact s6_661_safe
def s5_798 : State := ⟨[3,4,67,129], 1020847100762815390556144518962985636126, 3, 2, 1, 0⟩
theorem s5_798_edges : next config 5 s5_798 = [s6_30, s6_1027, s6_640] := by decide
theorem s5_798_safe : Safe 8 5 s5_798 := by
  apply safe_succ 7 5 s5_798 [s6_30, s6_1027, s6_640] (by decide) s5_798_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_30_safe
  · subst z; exact s6_1027_safe
  · subst z; exact s6_640_safe
def s5_799 : State := ⟨[3,4,67,130], 1701411834604692317482893733826522059038, 3, 2, 1, 0⟩
theorem s5_799_edges : next config 5 s5_799 = [s6_31, s6_1028, s6_642, s6_644] := by decide
theorem s5_799_safe : Safe 8 5 s5_799 := by
  apply safe_succ 7 5 s5_799 [s6_31, s6_1028, s6_642, s6_644] (by decide) s5_799_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_31_safe
  · subst z; exact s6_1028_safe
  · subst z; exact s6_642_safe
  · subst z; exact s6_644_safe
def s5_800 : State := ⟨[3,4,67,131], 3062541302288446171336392163553594904862, 3, 2, 1, 0⟩
theorem s5_800_edges : next config 5 s5_800 = [s6_32, s6_1029, s6_646] := by decide
theorem s5_800_safe : Safe 8 5 s5_800 := by
  apply safe_succ 7 5 s5_800 [s6_32, s6_1029, s6_646] (by decide) s5_800_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_32_safe
  · subst z; exact s6_1029_safe
  · subst z; exact s6_646_safe
def s5_801 : State := ⟨[3,4,67,132], 5784800237655953879043389023007740596510, 3, 2, 1, 0⟩
theorem s5_801_edges : next config 5 s5_801 = [s6_33, s6_1030] := by decide
theorem s5_801_safe : Safe 8 5 s5_801 := by
  apply safe_succ 7 5 s5_801 [s6_33, s6_1030] (by decide) s5_801_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_33_safe
  · subst z; exact s6_1030_safe
def s5_802 : State := ⟨[3,4,67,136], 87452568298681185110253294806632111345950, 3, 2, 1, 0⟩
theorem s5_802_edges : next config 5 s5_802 = [s6_34, s6_1031] := by decide
theorem s5_802_safe : Safe 8 5 s5_802 := by
  apply safe_succ 7 5 s5_802 [s6_34, s6_1031] (by decide) s5_802_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_34_safe
  · subst z; exact s6_1031_safe
def s5_803 : State := ⟨[3,4,67,136], 1481249143206845131456235686847154705465630, 3, 2, 1, 0⟩
theorem s5_803_edges : next config 5 s5_803 = [s6_35, s6_1032] := by decide
theorem s5_803_safe : Safe 8 5 s5_803 := by
  apply safe_succ 7 5 s5_803 [s6_35, s6_1032] (by decide) s5_803_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_35_safe
  · subst z; exact s6_1032_safe
def s5_804 : State := ⟨[3,4,67,140], 1394136857275084884809611787344622043336990, 3, 2, 1, 0⟩
theorem s5_804_edges : next config 5 s5_804 = [s6_36, s6_1033] := by decide
theorem s5_804_safe : Safe 8 5 s5_804 := by
  apply safe_succ 7 5 s5_804 [s6_36, s6_1033] (by decide) s5_804_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_36_safe
  · subst z; exact s6_1033_safe
def s5_805 : State := ⟨[3,4,67,144], 22301085480897544079999347667952460955193630, 3, 2, 1, 0⟩
theorem s5_805_edges : next config 5 s5_805 = [s6_37, s6_1038, s6_643, s6_648] := by decide
theorem s5_805_safe : Safe 8 5 s5_805 := by
  apply safe_succ 7 5 s5_805 [s6_37, s6_1038, s6_643, s6_648] (by decide) s5_805_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_37_safe
  · subst z; exact s6_1038_safe
  · subst z; exact s6_643_safe
  · subst z; exact s6_648_safe
def s5_806 : State := ⟨[3,4,67,145], 44601830679428167221535065940600822461301022, 1, 1, 1, 0⟩
theorem s5_806_edges : next config 5 s5_806 = [s6_1403, s6_1039, s6_710] := by decide
theorem s5_806_safe : Safe 8 5 s5_806 := by
  apply safe_succ 7 5 s5_806 [s6_1403, s6_1039, s6_710] (by decide) s5_806_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1403_safe
  · subst z; exact s6_1039_safe
  · subst z; exact s6_710_safe
def s5_807 : State := ⟨[3,4,67,145], 133806172603018343541531792529623995557937438, 1, 0, 1, 0⟩
theorem s5_807_edges : next config 5 s5_807 = [s6_44, s6_711] := by decide
theorem s5_807_safe : Safe 8 5 s5_807 := by
  apply safe_succ 7 5 s5_807 [s6_44, s6_711] (by decide) s5_807_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_44_safe
  · subst z; exact s6_711_safe
def s5_808 : State := ⟨[3,4,67,145], 156105556672081282929213657303842629991072030, 1, 0, 1, 0⟩
theorem s5_808_edges : next config 5 s5_808 = [s6_45, s6_712] := by decide
theorem s5_808_safe : Safe 8 5 s5_808 := by
  apply safe_succ 7 5 s5_808 [s6_45, s6_712] (by decide) s5_808_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_45_safe
  · subst z; exact s6_712_safe
def s5_809 : State := ⟨[3,4,67,160], 1461501637671185285124623296345678323755381756190, 3, 2, 1, 0⟩
theorem s5_809_edges : next config 5 s5_809 = [s6_1414, s6_50, s6_1044, s6_647, s6_645, s6_649] := by decide
theorem s5_809_safe : Safe 8 5 s5_809 := by
  apply safe_succ 7 5 s5_809 [s6_1414, s6_50, s6_1044, s6_647, s6_645, s6_649] (by decide) s5_809_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1414_safe
  · subst z; exact s6_50_safe
  · subst z; exact s6_1044_safe
  · subst z; exact s6_647_safe
  · subst z; exact s6_645_safe
  · subst z; exact s6_649_safe
def s5_810 : State := ⟨[3,4,67,171], 3004847366355398941129064462236014280576150903259422, 1, 0, 1, 0⟩
theorem s5_810_edges : next config 5 s5_810 = [s6_55] := by decide
theorem s5_810_safe : Safe 8 5 s5_810 := by
  apply safe_succ 7 5 s5_810 [s6_55] (by decide) s5_810_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_55_safe
def s5_811 : State := ⟨[3,4,67,171], 3006308867990007585111900639361023566736352690110750, 1, 0, 1, 0⟩
theorem s5_811_edges : next config 5 s5_811 = [s6_56] := by decide
theorem s5_811_safe : Safe 8 5 s5_811 := by
  apply safe_succ 7 5 s5_811 [s6_56] (by decide) s5_811_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_56_safe
def s5_812 : State := ⟨[3,4,67,192], 6277101735386680764176071790128604879731750748563483726110, 3, 2, 1, 0⟩
theorem s5_812_edges : next config 5 s5_812 = [s6_61, s6_1050] := by decide
theorem s5_812_safe : Safe 8 5 s5_812 := by
  apply safe_succ 7 5 s5_812 [s6_61, s6_1050] (by decide) s5_812_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_61_safe
  · subst z; exact s6_1050_safe
def s5_813 : State := ⟨[3,4,67,195], 50216813883093446111026597752582269792448238859811725316382, 3, 2, 1, 0⟩
theorem s5_813_edges : next config 5 s5_813 = [s6_62, s6_1051] := by decide
theorem s5_813_safe : Safe 8 5 s5_813 := by
  apply safe_succ 7 5 s5_813 [s6_62, s6_1051] (by decide) s5_813_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_62_safe
  · subst z; exact s6_1051_safe
def s5_814 : State := ⟨[3,4,96,129], 1020847100842043552922834903966853173534, 3, 2, 1, 0⟩
theorem s5_814_edges : next config 5 s5_814 = [s6_82, s6_1052, s6_663, s6_650] := by decide
theorem s5_814_safe : Safe 8 5 s5_814 := by
  apply safe_succ 7 5 s5_814 [s6_82, s6_1052, s6_663, s6_650] (by decide) s5_814_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_82_safe
  · subst z; exact s6_1052_safe
  · subst z; exact s6_663_safe
  · subst z; exact s6_650_safe
def s5_815 : State := ⟨[3,4,96,129], 1020847102109694153151064305463556374814, 3, 2, 1, 0⟩
theorem s5_815_edges : next config 5 s5_815 = [s6_86, s6_664, s6_651] := by decide
theorem s5_815_safe : Safe 8 5 s5_815 := by
  apply safe_succ 7 5 s5_815 [s6_86, s6_664, s6_651] (by decide) s5_815_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_86_safe
  · subst z; exact s6_664_safe
  · subst z; exact s6_651_safe
def s5_816 : State := ⟨[3,4,96,130], 1701411834683920479849584118830389596446, 3, 2, 1, 0⟩
theorem s5_816_edges : next config 5 s5_816 = [s6_88, s6_1054, s6_666, s6_654, s6_656] := by decide
theorem s5_816_safe : Safe 8 5 s5_816 := by
  apply safe_succ 7 5 s5_816 [s6_88, s6_1054, s6_666, s6_654, s6_656] (by decide) s5_816_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_88_safe
  · subst z; exact s6_1054_safe
  · subst z; exact s6_666_safe
  · subst z; exact s6_654_safe
  · subst z; exact s6_656_safe
def s5_817 : State := ⟨[3,4,96,130], 1701411835951571080077813520327092797726, 3, 2, 1, 0⟩
theorem s5_817_edges : next config 5 s5_817 = [s6_92, s6_667] := by decide
theorem s5_817_safe : Safe 8 5 s5_817 := by
  apply safe_succ 7 5 s5_817 [s6_92, s6_667] (by decide) s5_817_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_92_safe
  · subst z; exact s6_667_safe
def s5_818 : State := ⟨[3,4,96,131], 3062541302367674333703082548557462442270, 3, 2, 1, 0⟩
theorem s5_818_edges : next config 5 s5_818 = [s6_96, s6_1056, s6_669, s6_658] := by decide
theorem s5_818_safe : Safe 8 5 s5_818 := by
  apply safe_succ 7 5 s5_818 [s6_96, s6_1056, s6_669, s6_658] (by decide) s5_818_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_96_safe
  · subst z; exact s6_1056_safe
  · subst z; exact s6_669_safe
  · subst z; exact s6_658_safe
def s5_819 : State := ⟨[3,4,96,131], 3062541303635324933931311950054165643550, 3, 2, 1, 0⟩
theorem s5_819_edges : next config 5 s5_819 = [s6_97, s6_670] := by decide
theorem s5_819_safe : Safe 8 5 s5_819 := by
  apply safe_succ 7 5 s5_819 [s6_97, s6_670] (by decide) s5_819_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_97_safe
  · subst z; exact s6_670_safe
def s5_820 : State := ⟨[3,4,96,132], 5784800237735182041410079408011608133918, 3, 2, 1, 0⟩
theorem s5_820_edges : next config 5 s5_820 = [s6_98, s6_1057, s6_672] := by decide
theorem s5_820_safe : Safe 8 5 s5_820 := by
  apply safe_succ 7 5 s5_820 [s6_98, s6_1057, s6_672] (by decide) s5_820_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_98_safe
  · subst z; exact s6_1057_safe
  · subst z; exact s6_672_safe
def s5_821 : State := ⟨[3,4,96,132], 5784800239002832641638308809508311335198, 3, 2, 1, 0⟩
theorem s5_821_edges : next config 5 s5_821 = [s6_102, s6_673] := by decide
theorem s5_821_safe : Safe 8 5 s5_821 := by
  apply safe_succ 7 5 s5_821 [s6_102, s6_673] (by decide) s5_821_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_102_safe
  · subst z; exact s6_673_safe
def s5_822 : State := ⟨[3,4,96,136], 87452568298760413272619985191635978883358, 3, 2, 1, 0⟩
theorem s5_822_edges : next config 5 s5_822 = [s6_104, s6_1059, s6_675] := by decide
theorem s5_822_safe : Safe 8 5 s5_822 := by
  apply safe_succ 7 5 s5_822 [s6_104, s6_1059, s6_675] (by decide) s5_822_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_104_safe
  · subst z; exact s6_1059_safe
  · subst z; exact s6_675_safe
def s5_823 : State := ⟨[3,4,96,136], 87452568300028063872848214593132682084638, 3, 2, 1, 0⟩
theorem s5_823_edges : next config 5 s5_823 = [s6_108, s6_676] := by decide
theorem s5_823_safe : Safe 8 5 s5_823 := by
  apply safe_succ 7 5 s5_823 [s6_108, s6_676] (by decide) s5_823_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_108_safe
  · subst z; exact s6_676_safe
def s5_824 : State := ⟨[3,4,96,136], 1481249143206924359618602377232158573003038, 3, 2, 1, 0⟩
theorem s5_824_edges : next config 5 s5_824 = [s6_110, s6_1061, s6_678] := by decide
theorem s5_824_safe : Safe 8 5 s5_824 := by
  apply safe_succ 7 5 s5_824 [s6_110, s6_1061, s6_678] (by decide) s5_824_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_110_safe
  · subst z; exact s6_1061_safe
  · subst z; exact s6_678_safe
def s5_825 : State := ⟨[3,4,96,140], 1394136857275164112971978477729625910874398, 3, 2, 1, 0⟩
theorem s5_825_edges : next config 5 s5_825 = [s6_114, s6_1063, s6_679] := by decide
theorem s5_825_safe : Safe 8 5 s5_825 := by
  apply safe_succ 7 5 s5_825 [s6_114, s6_1063, s6_679] (by decide) s5_825_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_114_safe
  · subst z; exact s6_1063_safe
  · subst z; exact s6_679_safe
def s5_826 : State := ⟨[3,4,96,144], 22301085480897623308161714358337464822731038, 3, 2, 1, 0⟩
theorem s5_826_edges : next config 5 s5_826 = [s6_118, s6_1065, s6_680, s6_655, s6_660] := by decide
theorem s5_826_safe : Safe 8 5 s5_826 := by
  apply safe_succ 7 5 s5_826 [s6_118, s6_1065, s6_680, s6_655, s6_660] (by decide) s5_826_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_118_safe
  · subst z; exact s6_1065_safe
  · subst z; exact s6_680_safe
  · subst z; exact s6_655_safe
  · subst z; exact s6_660_safe
def s5_827 : State := ⟨[3,4,96,144], 22301085480898890958761942587738961525932318, 3, 2, 1, 0⟩
theorem s5_827_edges : next config 5 s5_827 = [s6_122, s6_681] := by decide
theorem s5_827_safe : Safe 8 5 s5_827 := by
  apply safe_succ 7 5 s5_827 [s6_122, s6_681] (by decide) s5_827_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_122_safe
  · subst z; exact s6_681_safe
def s5_828 : State := ⟨[3,4,96,145], 44601830679428246449697432630985826328838430, 1, 1, 1, 0⟩
theorem s5_828_edges : next config 5 s5_828 = [s6_1404, s6_1067, s6_733, s6_713, s6_662, s6_707, s6_683] := by decide
theorem s5_828_safe : Safe 8 5 s5_828 := by
  apply safe_succ 7 5 s5_828 [s6_1404, s6_1067, s6_733, s6_713, s6_662, s6_707, s6_683] (by decide) s5_828_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1404_safe
  · subst z; exact s6_1067_safe
  · subst z; exact s6_733_safe
  · subst z; exact s6_713_safe
  · subst z; exact s6_662_safe
  · subst z; exact s6_707_safe
  · subst z; exact s6_683_safe
def s5_829 : State := ⟨[3,4,96,145], 133806172603018422769694159220008999425474846, 1, 0, 1, 0⟩
theorem s5_829_edges : next config 5 s5_829 = [s6_128, s6_714, s6_684] := by decide
theorem s5_829_safe : Safe 8 5 s5_829 := by
  apply safe_succ 7 5 s5_829 [s6_128, s6_714, s6_684] (by decide) s5_829_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_128_safe
  · subst z; exact s6_714_safe
  · subst z; exact s6_684_safe
def s5_830 : State := ⟨[3,4,96,145], 156105556672081362157376023994227633858609438, 1, 0, 1, 0⟩
theorem s5_830_edges : next config 5 s5_830 = [s6_129, s6_715, s6_685] := by decide
theorem s5_830_safe : Safe 8 5 s5_830 := by
  apply safe_succ 7 5 s5_830 [s6_129, s6_715, s6_685] (by decide) s5_830_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_129_safe
  · subst z; exact s6_715_safe
  · subst z; exact s6_685_safe
def s5_831 : State := ⟨[3,4,96,160], 1461501637671185285203851458712368708759249293598, 3, 2, 1, 0⟩
theorem s5_831_edges : next config 5 s5_831 = [s6_1417, s6_130, s6_1069, s6_686, s6_659, s6_657, s6_661] := by decide
theorem s5_831_safe : Safe 8 5 s5_831 := by
  apply safe_succ 7 5 s5_831 [s6_1417, s6_130, s6_1069, s6_686, s6_659, s6_657, s6_661] (by decide) s5_831_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1417_safe
  · subst z; exact s6_130_safe
  · subst z; exact s6_1069_safe
  · subst z; exact s6_686_safe
  · subst z; exact s6_659_safe
  · subst z; exact s6_657_safe
  · subst z; exact s6_661_safe
def s5_832 : State := ⟨[3,4,96,160], 1461501637671185286471502058940598110255952494878, 3, 2, 1, 0⟩
theorem s5_832_edges : next config 5 s5_832 = [s6_134, s6_687] := by decide
theorem s5_832_safe : Safe 8 5 s5_832 := by
  apply safe_succ 7 5 s5_832 [s6_134, s6_687] (by decide) s5_832_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_134_safe
  · subst z; exact s6_687_safe
def s5_833 : State := ⟨[3,4,96,171], 3004847366355398941129143690398380970961154770796830, 1, 0, 1, 0⟩
theorem s5_833_edges : next config 5 s5_833 = [s6_151, s6_689] := by decide
theorem s5_833_safe : Safe 8 5 s5_833 := by
  apply safe_succ 7 5 s5_833 [s6_151, s6_689] (by decide) s5_833_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_151_safe
  · subst z; exact s6_689_safe
def s5_834 : State := ⟨[3,4,96,171], 3006308867990007585111979867523390257121356557648158, 1, 0, 1, 0⟩
theorem s5_834_edges : next config 5 s5_834 = [s6_152, s6_690] := by decide
theorem s5_834_safe : Safe 8 5 s5_834 := by
  apply safe_succ 7 5 s5_834 [s6_152, s6_690] (by decide) s5_834_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_152_safe
  · subst z; exact s6_690_safe
def s5_835 : State := ⟨[3,4,96,192], 6277101735386680764176071790207833042098441133567351263518, 3, 2, 1, 0⟩
theorem s5_835_edges : next config 5 s5_835 = [s6_154, s6_1074, s6_691] := by decide
theorem s5_835_safe : Safe 8 5 s5_835 := by
  apply safe_succ 7 5 s5_835 [s6_154, s6_1074, s6_691] (by decide) s5_835_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_154_safe
  · subst z; exact s6_1074_safe
  · subst z; exact s6_691_safe
def s5_836 : State := ⟨[3,4,96,192], 6277101735386680764176071791475483642326670535064054464798, 3, 2, 1, 0⟩
theorem s5_836_edges : next config 5 s5_836 = [s6_158, s6_692] := by decide
theorem s5_836_safe : Safe 8 5 s5_836 := by
  apply safe_succ 7 5 s5_836 [s6_158, s6_692] (by decide) s5_836_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_158_safe
  · subst z; exact s6_692_safe
def s5_837 : State := ⟨[3,4,96,224], 26959946667150639794667015087359913040637311048536658170206926999838, 3, 2, 1, 0⟩
theorem s5_837_edges : next config 5 s5_837 = [s6_180, s6_1076, s6_694] := by decide
theorem s5_837_safe : Safe 8 5 s5_837 := by
  apply safe_succ 7 5 s5_837 [s6_180, s6_1076, s6_694] (by decide) s5_837_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_180_safe
  · subst z; exact s6_1076_safe
  · subst z; exact s6_694_safe
def s5_838 : State := ⟨[3,4,96,224], 26959946667150639794667015087359913041904961648764887571703630201118, 3, 2, 1, 0⟩
theorem s5_838_edges : next config 5 s5_838 = [s6_184, s6_695] := by decide
theorem s5_838_safe : Safe 8 5 s5_838 := by
  apply safe_succ 7 5 s5_838 [s6_184, s6_695] (by decide) s5_838_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_184_safe
  · subst z; exact s6_695_safe
def s5_839 : State := ⟨[3,4,96,224], 458319093341560876509339256479674003818831621809185817867864690983198, 3, 2, 1, 0⟩
theorem s5_839_edges : next config 5 s5_839 = [s6_187, s6_697] := by decide
theorem s5_839_safe : Safe 8 5 s5_839 := by
  apply safe_succ 7 5 s5_839 [s6_187, s6_697] (by decide) s5_839_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_187_safe
  · subst z; exact s6_697_safe
def s5_840 : State := ⟨[3,4,96,228], 431359146674410236714672241392654373146462127986873474788257783939358, 3, 2, 1, 0⟩
theorem s5_840_edges : next config 5 s5_840 = [s6_190, s6_698] := by decide
theorem s5_840_safe : Safe 8 5 s5_840 := by
  apply safe_succ 7 5 s5_840 [s6_190, s6_698] (by decide) s5_840_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_190_safe
  · subst z; exact s6_698_safe
def s5_841 : State := ⟨[3,4,100,145], 44602511244163355977224587609602186568335646, 1, 0, 1, 0⟩
theorem s5_841_edges : next config 5 s5_841 = [s6_196] := by decide
theorem s5_841_safe : Safe 8 5 s5_841 := by
  apply safe_succ 7 5 s5_841 [s6_196] (by decide) s5_841_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_196_safe
def s5_842 : State := ⟨[3,4,100,145], 66902575877960137241833379133035684537893150, 1, 0, 1, 0⟩
theorem s5_842_edges : next config 5 s5_842 = [s6_198] := by decide
theorem s5_842_safe : Safe 8 5 s5_842 := by
  apply safe_succ 7 5 s5_842 [s6_198] (by decide) s5_842_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_198_safe
def s5_843 : State := ⟨[3,4,104,128], 340282387282576229647756113050568036638, 3, 2, 0, 0⟩
theorem s5_843_edges : next config 5 s5_843 = [s6_200, s6_1078, s6_669, s6_672, s6_699, s6_666, s6_675, s6_680, s6_686] := by decide
theorem s5_843_safe : Safe 8 5 s5_843 := by
  apply safe_succ 7 5 s5_843 [s6_200, s6_1078, s6_669, s6_672, s6_699, s6_666, s6_675, s6_680, s6_686] (by decide) s5_843_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_200_safe
  · subst z; exact s6_1078_safe
  · subst z; exact s6_669_safe
  · subst z; exact s6_672_safe
  · subst z; exact s6_699_safe
  · subst z; exact s6_666_safe
  · subst z; exact s6_675_safe
  · subst z; exact s6_680_safe
  · subst z; exact s6_686_safe
def s5_844 : State := ⟨[3,4,104,128], 340282388550226829875985514547271237918, 3, 2, 0, 0⟩
theorem s5_844_edges : next config 5 s5_844 = [s6_204, s6_670, s6_673, s6_700, s6_667, s6_676, s6_681, s6_687] := by decide
theorem s5_844_safe : Safe 8 5 s5_844 := by
  apply safe_succ 7 5 s5_844 [s6_204, s6_670, s6_673, s6_700, s6_667, s6_676, s6_681, s6_687] (by decide) s5_844_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_204_safe
  · subst z; exact s6_670_safe
  · subst z; exact s6_673_safe
  · subst z; exact s6_700_safe
  · subst z; exact s6_667_safe
  · subst z; exact s6_676_safe
  · subst z; exact s6_681_safe
  · subst z; exact s6_687_safe
def s5_845 : State := ⟨[3,4,104,128], 340282711801129888074482896206588608798, 3, 2, 0, 0⟩
theorem s5_845_edges : next config 5 s5_845 = [s6_206, s6_671, s6_674, s6_701, s6_668, s6_677, s6_682, s6_688] := by decide
theorem s5_845_safe : Safe 8 5 s5_845 := by
  apply safe_succ 7 5 s5_845 [s6_206, s6_671, s6_674, s6_701, s6_668, s6_677, s6_682, s6_688] (by decide) s5_845_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_206_safe
  · subst z; exact s6_671_safe
  · subst z; exact s6_674_safe
  · subst z; exact s6_701_safe
  · subst z; exact s6_668_safe
  · subst z; exact s6_677_safe
  · subst z; exact s6_682_safe
  · subst z; exact s6_688_safe
def s5_846 : State := ⟨[3,4,104,140], 1399581375166181537991044141872481453539614, 1, 0, 1, 0⟩
theorem s5_846_edges : next config 5 s5_846 = [s6_214, s6_1080] := by decide
theorem s5_846_safe : Safe 8 5 s5_846 := by
  apply safe_succ 7 5 s5_846 [s6_214, s6_1080] (by decide) s5_846_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_214_safe
  · subst z; exact s6_1080_safe
def s5_847 : State := ⟨[3,4,104,140], 1481249143227206769222254047656105824289054, 1, 0, 1, 0⟩
theorem s5_847_edges : next config 5 s5_847 = [s6_218, s6_1082] := by decide
theorem s5_847_safe : Safe 8 5 s5_847 := by
  apply safe_succ 7 5 s5_847 [s6_218, s6_1082] (by decide) s5_847_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_218_safe
  · subst z; exact s6_1082_safe
def s5_848 : State := ⟨[3,4,104,145], 44602511244182370736228011050624637116416286, 1, 0, 1, 0⟩
theorem s5_848_edges : next config 5 s5_848 = [s6_1405, s6_222, s6_1084, s6_736, s6_716, s6_704, s6_708] := by decide
theorem s5_848_safe : Safe 8 5 s5_848 := by
  apply safe_succ 7 5 s5_848 [s6_1405, s6_222, s6_1084, s6_736, s6_716, s6_704, s6_708] (by decide) s5_848_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1405_safe
  · subst z; exact s6_222_safe
  · subst z; exact s6_1084_safe
  · subst z; exact s6_736_safe
  · subst z; exact s6_716_safe
  · subst z; exact s6_704_safe
  · subst z; exact s6_708_safe
def s5_849 : State := ⟨[3,4,104,145], 66902575877979152000836802574058135085973790, 1, 0, 1, 0⟩
theorem s5_849_edges : next config 5 s5_849 = [s6_1406, s6_231, s6_1086, s6_737, s6_717, s6_705, s6_709] := by decide
theorem s5_849_safe : Safe 8 5 s5_849 := by
  apply safe_succ 7 5 s5_849 [s6_1406, s6_231, s6_1086, s6_737, s6_717, s6_705, s6_709] (by decide) s5_849_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1406_safe
  · subst z; exact s6_231_safe
  · subst z; exact s6_1086_safe
  · subst z; exact s6_737_safe
  · subst z; exact s6_717_safe
  · subst z; exact s6_705_safe
  · subst z; exact s6_709_safe
def s5_850 : State := ⟨[3,4,104,146], 89204682205977458896226374345136223664800030, 1, 0, 1, 0⟩
theorem s5_850_edges : next config 5 s5_850 = [s6_240, s6_718, s6_684] := by decide
theorem s5_850_safe : Safe 8 5 s5_850 := by
  apply safe_succ 7 5 s5_850 [s6_240, s6_718, s6_684] (by decide) s5_850_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_240_safe
  · subst z; exact s6_718_safe
  · subst z; exact s6_684_safe
def s5_851 : State := ⟨[3,4,104,146], 111504066275040398283908239119354858097934622, 1, 0, 1, 0⟩
theorem s5_851_edges : next config 5 s5_851 = [s6_247, s6_719, s6_685] := by decide
theorem s5_851_safe : Safe 8 5 s5_851 := by
  apply safe_succ 7 5 s5_851 [s6_247, s6_719, s6_685] (by decide) s5_851_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_247_safe
  · subst z; exact s6_719_safe
  · subst z; exact s6_685_safe
def s5_852 : State := ⟨[3,4,104,162], 5846006551025023527781069414366386621401371050270, 1, 0, 1, 0⟩
theorem s5_852_edges : next config 5 s5_852 = [s6_257, s6_720] := by decide
theorem s5_852_safe : Safe 8 5 s5_852 := by
  apply safe_succ 7 5 s5_852 [s6_257, s6_720] (by decide) s5_852_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_257_safe
  · subst z; exact s6_720_safe
def s5_853 : State := ⟨[3,4,104,162], 7307508186994796978301000393229171211330230747422, 1, 0, 1, 0⟩
theorem s5_853_edges : next config 5 s5_853 = [s6_265, s6_721] := by decide
theorem s5_853_safe : Safe 8 5 s5_853 := by
  apply safe_succ 7 5 s5_853 [s6_265, s6_721] (by decide) s5_853_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_265_safe
  · subst z; exact s6_721_safe
def s5_854 : State := ⟨[3,4,104,163], 11692013101709764668279562599085017129752174067998, 1, 0, 1, 0⟩
theorem s5_854_edges : next config 5 s5_854 = [s6_275, s6_722, s6_689] := by decide
theorem s5_854_safe : Safe 8 5 s5_854 := by
  apply safe_succ 7 5 s5_854 [s6_275, s6_722, s6_689] (by decide) s5_854_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_275_safe
  · subst z; exact s6_722_safe
  · subst z; exact s6_689_safe
def s5_855 : State := ⟨[3,4,104,163], 13153514736318408651115739724094303289953960919326, 1, 0, 1, 0⟩
theorem s5_855_edges : next config 5 s5_855 = [s6_276, s6_723, s6_690] := by decide
theorem s5_855_safe : Safe 8 5 s5_855 := by
  apply safe_succ 7 5 s5_855 [s6_276, s6_723, s6_690] (by decide) s5_855_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_276_safe
  · subst z; exact s6_723_safe
  · subst z; exact s6_690_safe
def s5_856 : State := ⟨[3,4,104,176], 95780971326419139128314594914659690004932607210488094, 1, 0, 1, 0⟩
theorem s5_856_edges : next config 5 s5_856 = [s6_286, s6_724] := by decide
theorem s5_856_safe : Safe 8 5 s5_856 := by
  apply safe_succ 7 5 s5_856 [s6_286, s6_724] (by decide) s5_856_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_286_safe
  · subst z; exact s6_724_safe
def s5_857 : State := ⟨[3,4,104,176], 95782432805755724832702175457956688015303901637050654, 1, 0, 1, 0⟩
theorem s5_857_edges : next config 5 s5_857 = [s6_291, s6_725] := by decide
theorem s5_857_safe : Safe 8 5 s5_857 := by
  apply safe_succ 7 5 s5_857 [s6_291, s6_725] (by decide) s5_857_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_291_safe
  · subst z; exact s6_725_safe
def s5_858 : State := ⟨[3,4,104,228], 431359146674410236714672241398098891036211902405710909529616623403294, 1, 0, 1, 0⟩
theorem s5_858_edges : next config 5 s5_858 = [s6_330] := by decide
theorem s5_858_safe : Safe 8 5 s5_858 := by
  apply safe_succ 7 5 s5_858 [s6_330] (by decide) s5_858_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_330_safe
def s5_859 : State := ⟨[3,4,104,228], 458319093341560876509339256479674003839114031412837488291811942269214, 1, 0, 1, 0⟩
theorem s5_859_edges : next config 5 s5_859 = [s6_332] := by decide
theorem s5_859_safe : Safe 8 5 s5_859 := by
  apply safe_succ 7 5 s5_859 [s6_332] (by decide) s5_859_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_332_safe
def s5_860 : State := ⟨[3,4,104,236], 110427941548649020598956093796438192039475761146371246632432346440204574, 1, 0, 1, 0⟩
theorem s5_860_edges : next config 5 s5_860 = [s6_334] := by decide
theorem s5_860_safe : Safe 8 5 s5_860 := by
  apply safe_succ 7 5 s5_860 [s6_334] (by decide) s5_860_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_334_safe
def s5_861 : State := ⟨[3,4,104,236], 117329687895439584386390849658709772974056135103126219193875962372620574, 1, 0, 1, 0⟩
theorem s5_861_edges : next config 5 s5_861 = [s6_336] := by decide
theorem s5_861_safe : Safe 8 5 s5_861 := by
  apply safe_succ 7 5 s5_861 [s6_336] (by decide) s5_861_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_336_safe
def s5_862 : State := ⟨[3,4,108,129], 1020847445643006815001232111070125031710, 1, 0, 1, 0⟩
theorem s5_862_edges : next config 5 s5_862 = [s6_340, s6_704] := by decide
theorem s5_862_safe : Safe 8 5 s5_862 := by
  apply safe_succ 7 5 s5_862 [s6_340, s6_704] (by decide) s5_862_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_340_safe
  · subst z; exact s6_704_safe
def s5_863 : State := ⟨[3,4,108,130], 1701412179484883741927981325933661454622, 1, 0, 1, 0⟩
theorem s5_863_edges : next config 5 s5_863 = [s6_342] := by decide
theorem s5_863_safe : Safe 8 5 s5_863 := by
  apply safe_succ 7 5 s5_863 [s6_342] (by decide) s5_863_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_342_safe
def s5_864 : State := ⟨[3,4,108,131], 3062541647168637595781479755660734300446, 1, 0, 1, 0⟩
theorem s5_864_edges : next config 5 s5_864 = [s6_345] := by decide
theorem s5_864_safe : Safe 8 5 s5_864 := by
  apply safe_succ 7 5 s5_864 [s6_345] (by decide) s5_864_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_345_safe
def s5_865 : State := ⟨[3,4,108,132], 5784800582536145303488476615114879992094, 1, 0, 1, 0⟩
theorem s5_865_edges : next config 5 s5_865 = [s6_346] := by decide
theorem s5_865_safe : Safe 8 5 s5_865 := by
  apply safe_succ 7 5 s5_865 [s6_346] (by decide) s5_865_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_346_safe
def s5_866 : State := ⟨[3,4,108,136], 87452568643561376534698382398739250741534, 1, 0, 1, 0⟩
theorem s5_866_edges : next config 5 s5_866 = [s6_348] := by decide
theorem s5_866_safe : Safe 8 5 s5_866 := by
  apply safe_succ 7 5 s5_866 [s6_348] (by decide) s5_866_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_348_safe
def s5_867 : State := ⟨[3,4,108,144], 22301085481242424271423792755544568094589214, 1, 0, 1, 0⟩
theorem s5_867_edges : next config 5 s5_867 = [s6_350] := by decide
theorem s5_867_safe : Safe 8 5 s5_867 := by
  apply safe_succ 7 5 s5_867 [s6_350] (by decide) s5_867_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_350_safe
def s5_868 : State := ⟨[3,4,108,160], 1461501637671185630004814720790765915862521151774, 1, 0, 1, 0⟩
theorem s5_868_edges : next config 5 s5_868 = [s6_353] := by decide
theorem s5_868_safe : Safe 8 5 s5_868 := by
  apply safe_succ 7 5 s5_868 [s6_353] (by decide) s5_868_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_353_safe
def s5_869 : State := ⟨[3,4,108,192], 6277101735386680764176072135008796304176838340670623121694, 1, 0, 1, 0⟩
theorem s5_869_edges : next config 5 s5_869 = [s6_355] := by decide
theorem s5_869_safe : Safe 8 5 s5_869 := by
  apply safe_succ 7 5 s5_869 [s6_355] (by decide) s5_869_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_355_safe
def s5_870 : State := ⟨[3,4,108,224], 26959946667150639794667015087359913385438274310615055377310198858014, 1, 0, 1, 0⟩
theorem s5_870_edges : next config 5 s5_870 = [s6_365] := by decide
theorem s5_870_safe : Safe 8 5 s5_870 := by
  apply safe_succ 7 5 s5_870 [s6_365] (by decide) s5_870_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_365_safe
def s5_871 : State := ⟨[3,4,108,232], 6901746346790563787434755862277365735162910102058461038058730812408094, 1, 0, 1, 0⟩
theorem s5_871_edges : next config 5 s5_871 = [s6_367] := by decide
theorem s5_871_safe : Safe 8 5 s5_871 := by
  apply safe_succ 7 5 s5_871 [s6_367] (by decide) s5_871_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_367_safe
def s5_872 : State := ⟨[3,4,108,236], 110427941548649020598956093796432747521929544684614259365496594169397534, 1, 0, 1, 0⟩
theorem s5_872_edges : next config 5 s5_872 = [s6_369] := by decide
theorem s5_872_safe : Safe 8 5 s5_872 := by
  apply safe_succ 7 5 s5_872 [s6_369] (by decide) s5_872_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_369_safe
def s5_873 : State := ⟨[3,4,236,132], 110427941548649020598956093796438192039475761146371246632432346440204574, 1, 0, 1, 0⟩
theorem s5_873_edges : next config 5 s5_873 = [s6_401] := by decide
theorem s5_873_safe : Safe 8 5 s5_873 := by
  apply safe_succ 7 5 s5_873 [s6_401] (by decide) s5_873_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_401_safe
def s5_874 : State := ⟨[3,4,241,145], 3533694129556768659166595001530439542899129882077862275623413092450369822, 1, 0, 1, 0⟩
theorem s5_874_edges : next config 5 s5_874 = [s6_404, s6_726] := by decide
theorem s5_874_safe : Safe 8 5 s5_874 := by
  apply safe_succ 7 5 s5_874 [s6_404, s6_726] (by decide) s5_874_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_404_safe
  · subst z; exact s6_726_safe
def s5_875 : State := ⟨[3,4,241,145], 3533694129556768659166595001552739607532926663342471067146846590419927326, 1, 0, 1, 0⟩
theorem s5_875_edges : next config 5 s5_875 = [s6_407, s6_727] := by decide
theorem s5_875_safe : Safe 8 5 s5_875 := by
  apply safe_succ 7 5 s5_875 [s6_407, s6_727] (by decide) s5_875_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_407_safe
  · subst z; exact s6_727_safe
def s5_876 : State := ⟨[3,12,64,145], 44601830679428167221534918366648232784892190, 3, 1, 1, 0⟩
theorem s5_876_edges : next config 5 s5_876 = [s6_1407, s6_1092, s6_636, s6_710, s6_713] := by decide
theorem s5_876_safe : Safe 8 5 s5_876 := by
  apply safe_succ 7 5 s5_876 [s6_1407, s6_1092, s6_636, s6_710, s6_713] (by decide) s5_876_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1407_safe
  · subst z; exact s6_1092_safe
  · subst z; exact s6_636_safe
  · subst z; exact s6_710_safe
  · subst z; exact s6_713_safe
def s5_877 : State := ⟨[3,12,64,145], 133806172603018343541531644955671405881528606, 3, 0, 1, 0⟩
theorem s5_877_edges : next config 5 s5_877 = [s6_412, s6_638, s6_711, s6_714] := by decide
theorem s5_877_safe : Safe 8 5 s5_877 := by
  apply safe_succ 7 5 s5_877 [s6_412, s6_638, s6_711, s6_714] (by decide) s5_877_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_412_safe
  · subst z; exact s6_638_safe
  · subst z; exact s6_711_safe
  · subst z; exact s6_714_safe
def s5_878 : State := ⟨[3,12,64,145], 156105556672081282929213509729890040314663198, 3, 0, 1, 0⟩
theorem s5_878_edges : next config 5 s5_878 = [s6_413, s6_639, s6_712, s6_715] := by decide
theorem s5_878_safe : Safe 8 5 s5_878 := by
  apply safe_succ 7 5 s5_878 [s6_413, s6_639, s6_712, s6_715] (by decide) s5_878_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_413_safe
  · subst z; exact s6_639_safe
  · subst z; exact s6_712_safe
  · subst z; exact s6_715_safe
def s5_879 : State := ⟨[3,12,67,145], 44602511244162009098461992689815685997596958, 3, 0, 1, 0⟩
theorem s5_879_edges : next config 5 s5_879 = [s6_1408, s6_416, s6_1107, s6_640] := by decide
theorem s5_879_safe : Safe 8 5 s5_879 := by
  apply safe_succ 7 5 s5_879 [s6_1408, s6_416, s6_1107, s6_640] (by decide) s5_879_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1408_safe
  · subst z; exact s6_416_safe
  · subst z; exact s6_1107_safe
  · subst z; exact s6_640_safe
def s5_880 : State := ⟨[3,12,67,145], 66902575877958790363070784213249183967154462, 3, 0, 1, 0⟩
theorem s5_880_edges : next config 5 s5_880 = [s6_1409, s6_417, s6_1108, s6_641] := by decide
theorem s5_880_safe : Safe 8 5 s5_880 := by
  apply safe_succ 7 5 s5_880 [s6_1409, s6_417, s6_1108, s6_641] (by decide) s5_880_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1409_safe
  · subst z; exact s6_417_safe
  · subst z; exact s6_1108_safe
  · subst z; exact s6_641_safe
def s5_881 : State := ⟨[3,12,67,146], 89204682205957097258460355984327272545980702, 3, 0, 1, 0⟩
theorem s5_881_edges : next config 5 s5_881 = [s6_421, s6_642, s6_711] := by decide
theorem s5_881_safe : Safe 8 5 s5_881 := by
  apply safe_succ 7 5 s5_881 [s6_421, s6_642, s6_711] (by decide) s5_881_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_421_safe
  · subst z; exact s6_642_safe
  · subst z; exact s6_711_safe
def s5_882 : State := ⟨[3,12,67,146], 111504066275020036646142220758545906979115294, 3, 0, 1, 0⟩
theorem s5_882_edges : next config 5 s5_882 = [s6_422, s6_643, s6_712] := by decide
theorem s5_882_safe : Safe 8 5 s5_882 := by
  apply safe_succ 7 5 s5_882 [s6_422, s6_643, s6_712] (by decide) s5_882_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_422_safe
  · subst z; exact s6_643_safe
  · subst z; exact s6_712_safe
def s5_883 : State := ⟨[3,12,67,162], 5846006551025023507419431648348025812450252230942, 3, 0, 1, 0⟩
theorem s5_883_edges : next config 5 s5_883 = [s6_423, s6_644] := by decide
theorem s5_883_safe : Safe 8 5 s5_883 := by
  apply safe_succ 7 5 s5_883 [s6_423, s6_644] (by decide) s5_883_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_423_safe
  · subst z; exact s6_644_safe
def s5_884 : State := ⟨[3,12,67,162], 7307508186994796957939362627210810402379111928094, 3, 0, 1, 0⟩
theorem s5_884_edges : next config 5 s5_884 = [s6_424, s6_645] := by decide
theorem s5_884_safe : Safe 8 5 s5_884 := by
  apply safe_succ 7 5 s5_884 [s6_424, s6_645] (by decide) s5_884_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_424_safe
  · subst z; exact s6_645_safe
def s5_885 : State := ⟨[3,12,67,163], 11692013101709764647917924833066656320801055248670, 3, 0, 1, 0⟩
theorem s5_885_edges : next config 5 s5_885 = [s6_425, s6_646] := by decide
theorem s5_885_safe : Safe 8 5 s5_885 := by
  apply safe_succ 7 5 s5_885 [s6_425, s6_646] (by decide) s5_885_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_425_safe
  · subst z; exact s6_646_safe
def s5_886 : State := ⟨[3,12,67,163], 13153514736318408630754101958075942481002842099998, 3, 0, 1, 0⟩
theorem s5_886_edges : next config 5 s5_886 = [s6_426, s6_647] := by decide
theorem s5_886_safe : Safe 8 5 s5_886 := by
  apply safe_succ 7 5 s5_886 [s6_426, s6_647] (by decide) s5_886_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_426_safe
  · subst z; exact s6_647_safe
def s5_887 : State := ⟨[3,12,67,176], 95780971326419139128294233276893671644123656091668766, 3, 0, 1, 0⟩
theorem s5_887_edges : next config 5 s5_887 = [s6_427, s6_648] := by decide
theorem s5_887_safe : Safe 8 5 s5_887 := by
  apply safe_succ 7 5 s5_887 [s6_427, s6_648] (by decide) s5_887_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_427_safe
  · subst z; exact s6_648_safe
def s5_888 : State := ⟨[3,12,67,176], 95782432805755724832681813820190669654494950518231326, 3, 0, 1, 0⟩
theorem s5_888_edges : next config 5 s5_888 = [s6_428, s6_649] := by decide
theorem s5_888_safe : Safe 8 5 s5_888 := by
  apply safe_succ 7 5 s5_888 [s6_428, s6_649] (by decide) s5_888_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_428_safe
  · subst z; exact s6_649_safe
def s5_889 : State := ⟨[3,12,96,145], 44602511244162088326624359380200689865134366, 3, 0, 1, 0⟩
theorem s5_889_edges : next config 5 s5_889 = [s6_1410, s6_431, s6_1120, s6_650, s6_726, s6_716] := by decide
theorem s5_889_safe : Safe 8 5 s5_889 := by
  apply safe_succ 7 5 s5_889 [s6_1410, s6_431, s6_1120, s6_650, s6_726, s6_716] (by decide) s5_889_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1410_safe
  · subst z; exact s6_431_safe
  · subst z; exact s6_1120_safe
  · subst z; exact s6_650_safe
  · subst z; exact s6_726_safe
  · subst z; exact s6_716_safe
def s5_890 : State := ⟨[3,12,96,145], 66902575877958869591233150903634187834691870, 3, 0, 1, 0⟩
theorem s5_890_edges : next config 5 s5_890 = [s6_1411, s6_435, s6_1122, s6_652, s6_727, s6_717] := by decide
theorem s5_890_safe : Safe 8 5 s5_890 := by
  apply safe_succ 7 5 s5_890 [s6_1411, s6_435, s6_1122, s6_652, s6_727, s6_717] (by decide) s5_890_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1411_safe
  · subst z; exact s6_435_safe
  · subst z; exact s6_1122_safe
  · subst z; exact s6_652_safe
  · subst z; exact s6_727_safe
  · subst z; exact s6_717_safe
def s5_891 : State := ⟨[3,12,96,146], 89204682205957176486622722674712276413518110, 3, 0, 1, 0⟩
theorem s5_891_edges : next config 5 s5_891 = [s6_439, s6_654, s6_718, s6_714] := by decide
theorem s5_891_safe : Safe 8 5 s5_891 := by
  apply safe_succ 7 5 s5_891 [s6_439, s6_654, s6_718, s6_714] (by decide) s5_891_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_439_safe
  · subst z; exact s6_654_safe
  · subst z; exact s6_718_safe
  · subst z; exact s6_714_safe
def s5_892 : State := ⟨[3,12,96,146], 111504066275020115874304587448930910846652702, 3, 0, 1, 0⟩
theorem s5_892_edges : next config 5 s5_892 = [s6_442, s6_655, s6_719, s6_715] := by decide
theorem s5_892_safe : Safe 8 5 s5_892 := by
  apply safe_succ 7 5 s5_892 [s6_442, s6_655, s6_719, s6_715] (by decide) s5_892_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_442_safe
  · subst z; exact s6_655_safe
  · subst z; exact s6_719_safe
  · subst z; exact s6_715_safe
def s5_893 : State := ⟨[3,12,96,162], 5846006551025023507498659810714716197454119768350, 3, 0, 1, 0⟩
theorem s5_893_edges : next config 5 s5_893 = [s6_444, s6_656, s6_720] := by decide
theorem s5_893_safe : Safe 8 5 s5_893 := by
  apply safe_succ 7 5 s5_893 [s6_444, s6_656, s6_720] (by decide) s5_893_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_444_safe
  · subst z; exact s6_656_safe
  · subst z; exact s6_720_safe
def s5_894 : State := ⟨[3,12,96,162], 7307508186994796958018590789577500787382979465502, 3, 0, 1, 0⟩
theorem s5_894_edges : next config 5 s5_894 = [s6_448, s6_657, s6_721] := by decide
theorem s5_894_safe : Safe 8 5 s5_894 := by
  apply safe_succ 7 5 s5_894 [s6_448, s6_657, s6_721] (by decide) s5_894_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_448_safe
  · subst z; exact s6_657_safe
  · subst z; exact s6_721_safe
def s5_895 : State := ⟨[3,12,96,163], 11692013101709764647997152995433346705804922786078, 3, 0, 1, 0⟩
theorem s5_895_edges : next config 5 s5_895 = [s6_454, s6_658, s6_722] := by decide
theorem s5_895_safe : Safe 8 5 s5_895 := by
  apply safe_succ 7 5 s5_895 [s6_454, s6_658, s6_722] (by decide) s5_895_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_454_safe
  · subst z; exact s6_658_safe
  · subst z; exact s6_722_safe
def s5_896 : State := ⟨[3,12,96,163], 13153514736318408630833330120442632866006709637406, 3, 0, 1, 0⟩
theorem s5_896_edges : next config 5 s5_896 = [s6_455, s6_659, s6_723] := by decide
theorem s5_896_safe : Safe 8 5 s5_896 := by
  apply safe_succ 7 5 s5_896 [s6_455, s6_659, s6_723] (by decide) s5_896_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_455_safe
  · subst z; exact s6_659_safe
  · subst z; exact s6_723_safe
def s5_897 : State := ⟨[3,12,96,176], 95780971326419139128294312505056038334508659959206174, 3, 0, 1, 0⟩
theorem s5_897_edges : next config 5 s5_897 = [s6_457, s6_660, s6_724] := by decide
theorem s5_897_safe : Safe 8 5 s5_897 := by
  apply safe_succ 7 5 s5_897 [s6_457, s6_660, s6_724] (by decide) s5_897_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_457_safe
  · subst z; exact s6_660_safe
  · subst z; exact s6_724_safe
def s5_898 : State := ⟨[3,12,96,176], 95782432805755724832681893048353036344879954385768734, 3, 0, 1, 0⟩
theorem s5_898_edges : next config 5 s5_898 = [s6_459, s6_661, s6_725] := by decide
theorem s5_898_safe : Safe 8 5 s5_898 := by
  apply safe_succ 7 5 s5_898 [s6_459, s6_661, s6_725] (by decide) s5_898_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_459_safe
  · subst z; exact s6_661_safe
  · subst z; exact s6_725_safe
def s5_899 : State := ⟨[3,12,104,129], 1020847121124453156574505327914104459550, 3, 0, 1, 0⟩
theorem s5_899_edges : next config 5 s5_899 = [s6_462, s6_1124, s6_663, s6_716] := by decide
theorem s5_899_safe : Safe 8 5 s5_899 := by
  apply safe_succ 7 5 s5_899 [s6_462, s6_1124, s6_663, s6_716] (by decide) s5_899_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_462_safe
  · subst z; exact s6_1124_safe
  · subst z; exact s6_663_safe
  · subst z; exact s6_716_safe
def s5_900 : State := ⟨[3,12,104,130], 1701411854966330083501254542777640882462, 3, 0, 1, 0⟩
theorem s5_900_edges : next config 5 s5_900 = [s6_466, s6_1126, s6_666, s6_718, s6_720] := by decide
theorem s5_900_safe : Safe 8 5 s5_900 := by
  apply safe_succ 7 5 s5_900 [s6_466, s6_1126, s6_666, s6_718, s6_720] (by decide) s5_900_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_466_safe
  · subst z; exact s6_1126_safe
  · subst z; exact s6_666_safe
  · subst z; exact s6_718_safe
  · subst z; exact s6_720_safe
def s5_901 : State := ⟨[3,12,104,131], 3062541322650083937354752972504713728286, 3, 0, 1, 0⟩
theorem s5_901_edges : next config 5 s5_901 = [s6_471, s6_1128, s6_669, s6_722] := by decide
theorem s5_901_safe : Safe 8 5 s5_901 := by
  apply safe_succ 7 5 s5_901 [s6_471, s6_1128, s6_669, s6_722] (by decide) s5_901_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_471_safe
  · subst z; exact s6_1128_safe
  · subst z; exact s6_669_safe
  · subst z; exact s6_722_safe
def s5_902 : State := ⟨[3,12,104,132], 5784800258017591645061749831958859419934, 3, 0, 1, 0⟩
theorem s5_902_edges : next config 5 s5_902 = [s6_472, s6_1129, s6_672] := by decide
theorem s5_902_safe : Safe 8 5 s5_902 := by
  apply safe_succ 7 5 s5_902 [s6_472, s6_1129, s6_672] (by decide) s5_902_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_472_safe
  · subst z; exact s6_1129_safe
  · subst z; exact s6_672_safe
def s5_903 : State := ⟨[3,12,104,136], 87452568319042822876271655615583230169374, 3, 0, 1, 0⟩
theorem s5_903_edges : next config 5 s5_903 = [s6_476, s6_1131, s6_675] := by decide
theorem s5_903_safe : Safe 8 5 s5_903 := by
  apply safe_succ 7 5 s5_903 [s6_476, s6_1131, s6_675] (by decide) s5_903_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_476_safe
  · subst z; exact s6_1131_safe
  · subst z; exact s6_675_safe
def s5_904 : State := ⟨[3,12,104,140], 1394136857295446522575630148153573162160414, 3, 0, 1, 0⟩
theorem s5_904_edges : next config 5 s5_904 = [s6_480, s6_1133, s6_679] := by decide
theorem s5_904_safe : Safe 8 5 s5_904 := by
  apply safe_succ 7 5 s5_904 [s6_480, s6_1133, s6_679] (by decide) s5_904_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_480_safe
  · subst z; exact s6_1133_safe
  · subst z; exact s6_679_safe
def s5_905 : State := ⟨[3,12,104,144], 22301085480917905717765366028761412074017054, 3, 0, 1, 0⟩
theorem s5_905_edges : next config 5 s5_905 = [s6_484, s6_1135, s6_680, s6_719, s6_724] := by decide
theorem s5_905_safe : Safe 8 5 s5_905 := by
  apply safe_succ 7 5 s5_905 [s6_484, s6_1135, s6_680, s6_719, s6_724] (by decide) s5_905_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_484_safe
  · subst z; exact s6_1135_safe
  · subst z; exact s6_680_safe
  · subst z; exact s6_719_safe
  · subst z; exact s6_724_safe
def s5_906 : State := ⟨[3,12,104,160], 1461501637671185305486261062364039132706500579614, 3, 0, 1, 0⟩
theorem s5_906_edges : next config 5 s5_906 = [s6_1423, s6_489, s6_1137, s6_686, s6_723, s6_721, s6_725] := by decide
theorem s5_906_safe : Safe 8 5 s5_906 := by
  apply safe_succ 7 5 s5_906 [s6_1423, s6_489, s6_1137, s6_686, s6_723, s6_721, s6_725] (by decide) s5_906_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1423_safe
  · subst z; exact s6_489_safe
  · subst z; exact s6_1137_safe
  · subst z; exact s6_686_safe
  · subst z; exact s6_723_safe
  · subst z; exact s6_721_safe
  · subst z; exact s6_725_safe
def s5_907 : State := ⟨[3,12,104,192], 6277101735386680764176071810490242645750111557514602549534, 3, 0, 1, 0⟩
theorem s5_907_edges : next config 5 s5_907 = [s6_503, s6_1142, s6_691] := by decide
theorem s5_907_safe : Safe 8 5 s5_907 := by
  apply safe_succ 7 5 s5_907 [s6_503, s6_1142, s6_691] (by decide) s5_907_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_503_safe
  · subst z; exact s6_1142_safe
  · subst z; exact s6_691_safe
def s5_908 : State := ⟨[3,12,104,224], 26959946667150639794667015087359913060919720652188328594154178285854, 3, 0, 1, 0⟩
theorem s5_908_edges : next config 5 s5_908 = [s6_517, s6_1144, s6_694] := by decide
theorem s5_908_safe : Safe 8 5 s5_908 := by
  apply safe_succ 7 5 s5_908 [s6_517, s6_1144, s6_694] (by decide) s5_908_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_517_safe
  · subst z; exact s6_1144_safe
  · subst z; exact s6_694_safe
def s5_909 : State := ⟨[3,12,104,232], 6901746346790563787434755862277365734838391548400034311275574791835934, 3, 0, 1, 0⟩
theorem s5_909_edges : next config 5 s5_909 = [s6_523, s6_1146, s6_699] := by decide
theorem s5_909_safe : Safe 8 5 s5_909 := by
  apply safe_succ 7 5 s5_909 [s6_523, s6_1146, s6_699] (by decide) s5_909_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_523_safe
  · subst z; exact s6_1146_safe
  · subst z; exact s6_699_safe
def s5_910 : State := ⟨[3,21,64,145], 44601830679428167221534918366648232786985246, 3, 1, 1, 0⟩
theorem s5_910_edges : next config 5 s5_910 = [s6_975, s6_1412, s6_1148, s6_730, s6_731, s6_732, s6_728, s6_729] := by decide
theorem s5_910_safe : Safe 8 5 s5_910 := by
  apply safe_succ 7 5 s5_910 [s6_975, s6_1412, s6_1148, s6_730, s6_731, s6_732, s6_728, s6_729] (by decide) s5_910_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_975_safe
  · subst z; exact s6_1412_safe
  · subst z; exact s6_1148_safe
  · subst z; exact s6_730_safe
  · subst z; exact s6_731_safe
  · subst z; exact s6_732_safe
  · subst z; exact s6_728_safe
  · subst z; exact s6_729_safe
def s5_911 : State := ⟨[3,100,96,145], 44602511244163355977224587609602186568335646, 3, 0, 1, 0⟩
theorem s5_911_edges : next config 5 s5_911 = [s6_554, s6_651, s6_734] := by decide
theorem s5_911_safe : Safe 8 5 s5_911 := by
  apply safe_succ 7 5 s5_911 [s6_554, s6_651, s6_734] (by decide) s5_911_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_554_safe
  · subst z; exact s6_651_safe
  · subst z; exact s6_734_safe
def s5_912 : State := ⟨[3,100,96,145], 66902575877960137241833379133035684537893150, 3, 0, 1, 0⟩
theorem s5_912_edges : next config 5 s5_912 = [s6_556, s6_653, s6_735] := by decide
theorem s5_912_safe : Safe 8 5 s5_912 := by
  apply safe_succ 7 5 s5_912 [s6_556, s6_653, s6_735] (by decide) s5_912_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_556_safe
  · subst z; exact s6_653_safe
  · subst z; exact s6_735_safe
def s5_913 : State := ⟨[3,100,104,129], 1020847122392103756802734729410807660830, 3, 0, 1, 0⟩
theorem s5_913_edges : next config 5 s5_913 = [s6_558, s6_734] := by decide
theorem s5_913_safe : Safe 8 5 s5_913 := by
  apply safe_succ 7 5 s5_913 [s6_558, s6_734] (by decide) s5_913_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_558_safe
  · subst z; exact s6_734_safe
def s5_914 : State := ⟨[3,100,104,130], 1701411856233980683729483944274344083742, 3, 0, 1, 0⟩
theorem s5_914_edges : next config 5 s5_914 = [s6_560] := by decide
theorem s5_914_safe : Safe 8 5 s5_914 := by
  apply safe_succ 7 5 s5_914 [s6_560] (by decide) s5_914_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_560_safe
def s5_915 : State := ⟨[3,100,104,131], 3062541323917734537582982374001416929566, 3, 0, 1, 0⟩
theorem s5_915_edges : next config 5 s5_915 = [s6_563] := by decide
theorem s5_915_safe : Safe 8 5 s5_915 := by
  apply safe_succ 7 5 s5_915 [s6_563] (by decide) s5_915_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_563_safe
def s5_916 : State := ⟨[3,100,104,132], 5784800259285242245289979233455562621214, 3, 0, 1, 0⟩
theorem s5_916_edges : next config 5 s5_916 = [s6_564] := by decide
theorem s5_916_safe : Safe 8 5 s5_916 := by
  apply safe_succ 7 5 s5_916 [s6_564] (by decide) s5_916_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_564_safe
def s5_917 : State := ⟨[3,100,104,136], 87452568320310473476499885017079933370654, 3, 0, 1, 0⟩
theorem s5_917_edges : next config 5 s5_917 = [s6_566] := by decide
theorem s5_917_safe : Safe 8 5 s5_917 := by
  apply safe_succ 7 5 s5_917 [s6_566] (by decide) s5_917_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_566_safe
def s5_918 : State := ⟨[3,100,104,144], 22301085480919173368365594258162908777218334, 3, 0, 1, 0⟩
theorem s5_918_edges : next config 5 s5_918 = [s6_568] := by decide
theorem s5_918_safe : Safe 8 5 s5_918 := by
  apply safe_succ 7 5 s5_918 [s6_568] (by decide) s5_918_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_568_safe
def s5_919 : State := ⟨[3,100,104,160], 1461501637671185306753911662592268534203203780894, 3, 0, 1, 0⟩
theorem s5_919_edges : next config 5 s5_919 = [s6_571] := by decide
theorem s5_919_safe : Safe 8 5 s5_919 := by
  apply safe_succ 7 5 s5_919 [s6_571] (by decide) s5_919_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_571_safe
def s5_920 : State := ⟨[3,100,104,192], 6277101735386680764176071811757893245978340959011305750814, 3, 0, 1, 0⟩
theorem s5_920_edges : next config 5 s5_920 = [s6_573] := by decide
theorem s5_920_safe : Safe 8 5 s5_920 := by
  apply safe_succ 7 5 s5_920 [s6_573] (by decide) s5_920_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_573_safe
def s5_921 : State := ⟨[3,100,104,224], 26959946667150639794667015087359913062187371252416557995650881487134, 3, 0, 1, 0⟩
theorem s5_921_edges : next config 5 s5_921 = [s6_577] := by decide
theorem s5_921_safe : Safe 8 5 s5_921 := by
  apply safe_succ 7 5 s5_921 [s6_577] (by decide) s5_921_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_577_safe
def s5_922 : State := ⟨[3,100,104,228], 431359146674410236714672241392654373166744537590525145212205035225374, 3, 0, 1, 0⟩
theorem s5_922_edges : next config 5 s5_922 = [s6_579] := by decide
theorem s5_922_safe : Safe 8 5 s5_922 := by
  apply safe_succ 7 5 s5_922 [s6_579] (by decide) s5_922_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_579_safe
def s5_923 : State := ⟨[3,100,104,232], 6901746346790563787434755862277365734839659199000262540677071495037214, 3, 0, 1, 0⟩
theorem s5_923_edges : next config 5 s5_923 = [s6_581] := by decide
theorem s5_923_safe : Safe 8 5 s5_923 := by
  apply safe_succ 7 5 s5_923 [s6_581] (by decide) s5_923_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_581_safe
def s5_924 : State := ⟨[3,108,104,129], 1020847445643006815001232111070125031710, 3, 0, 1, 0⟩
theorem s5_924_edges : next config 5 s5_924 = [s6_583, s6_665, s6_736] := by decide
theorem s5_924_safe : Safe 8 5 s5_924 := by
  apply safe_succ 7 5 s5_924 [s6_583, s6_665, s6_736] (by decide) s5_924_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_583_safe
  · subst z; exact s6_665_safe
  · subst z; exact s6_736_safe
def s5_925 : State := ⟨[3,108,104,130], 1701412179484883741927981325933661454622, 3, 0, 1, 0⟩
theorem s5_925_edges : next config 5 s5_925 = [s6_585, s6_668] := by decide
theorem s5_925_safe : Safe 8 5 s5_925 := by
  apply safe_succ 7 5 s5_925 [s6_585, s6_668] (by decide) s5_925_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_585_safe
  · subst z; exact s6_668_safe
def s5_926 : State := ⟨[3,108,104,131], 3062541647168637595781479755660734300446, 3, 0, 1, 0⟩
theorem s5_926_edges : next config 5 s5_926 = [s6_588, s6_671] := by decide
theorem s5_926_safe : Safe 8 5 s5_926 := by
  apply safe_succ 7 5 s5_926 [s6_588, s6_671] (by decide) s5_926_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_588_safe
  · subst z; exact s6_671_safe
def s5_927 : State := ⟨[3,108,104,132], 5784800582536145303488476615114879992094, 3, 0, 1, 0⟩
theorem s5_927_edges : next config 5 s5_927 = [s6_589, s6_674] := by decide
theorem s5_927_safe : Safe 8 5 s5_927 := by
  apply safe_succ 7 5 s5_927 [s6_589, s6_674] (by decide) s5_927_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_589_safe
  · subst z; exact s6_674_safe
def s5_928 : State := ⟨[3,108,104,136], 87452568643561376534698382398739250741534, 3, 0, 1, 0⟩
theorem s5_928_edges : next config 5 s5_928 = [s6_591, s6_677] := by decide
theorem s5_928_safe : Safe 8 5 s5_928 := by
  apply safe_succ 7 5 s5_928 [s6_591, s6_677] (by decide) s5_928_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_591_safe
  · subst z; exact s6_677_safe
def s5_929 : State := ⟨[3,108,104,144], 22301085481242424271423792755544568094589214, 3, 0, 1, 0⟩
theorem s5_929_edges : next config 5 s5_929 = [s6_593, s6_682] := by decide
theorem s5_929_safe : Safe 8 5 s5_929 := by
  apply safe_succ 7 5 s5_929 [s6_593, s6_682] (by decide) s5_929_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_593_safe
  · subst z; exact s6_682_safe
def s5_930 : State := ⟨[3,108,104,160], 1461501637671185630004814720790765915862521151774, 3, 0, 1, 0⟩
theorem s5_930_edges : next config 5 s5_930 = [s6_596, s6_688] := by decide
theorem s5_930_safe : Safe 8 5 s5_930 := by
  apply safe_succ 7 5 s5_930 [s6_596, s6_688] (by decide) s5_930_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_596_safe
  · subst z; exact s6_688_safe
def s5_931 : State := ⟨[3,108,104,192], 6277101735386680764176072135008796304176838340670623121694, 3, 0, 1, 0⟩
theorem s5_931_edges : next config 5 s5_931 = [s6_598, s6_693] := by decide
theorem s5_931_safe : Safe 8 5 s5_931 := by
  apply safe_succ 7 5 s5_931 [s6_598, s6_693] (by decide) s5_931_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_598_safe
  · subst z; exact s6_693_safe
def s5_932 : State := ⟨[3,108,104,224], 26959946667150639794667015087359913385438274310615055377310198858014, 3, 0, 1, 0⟩
theorem s5_932_edges : next config 5 s5_932 = [s6_608, s6_696] := by decide
theorem s5_932_safe : Safe 8 5 s5_932 := by
  apply safe_succ 7 5 s5_932 [s6_608, s6_696] (by decide) s5_932_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_608_safe
  · subst z; exact s6_696_safe
def s5_933 : State := ⟨[3,108,104,232], 6901746346790563787434755862277365735162910102058461038058730812408094, 3, 0, 1, 0⟩
theorem s5_933_edges : next config 5 s5_933 = [s6_610, s6_701] := by decide
theorem s5_933_safe : Safe 8 5 s5_933 := by
  apply safe_succ 7 5 s5_933 [s6_610, s6_701] (by decide) s5_933_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_610_safe
  · subst z; exact s6_701_safe
def s5_934 : State := ⟨[3,108,104,236], 110427941548649020598956093796432747521929544684614259365496594169397534, 3, 0, 1, 0⟩
theorem s5_934_edges : next config 5 s5_934 = [s6_612, s6_703] := by decide
theorem s5_934_safe : Safe 8 5 s5_934 := by
  apply safe_succ 7 5 s5_934 [s6_612, s6_703] (by decide) s5_934_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_612_safe
  · subst z; exact s6_703_safe
def s5_935 : State := ⟨[3,140,104,136], 1481249143227206769222254047656105824289054, 3, 0, 1, 0⟩
theorem s5_935_edges : next config 5 s5_935 = [s6_615, s6_1152, s6_678] := by decide
theorem s5_935_safe : Safe 8 5 s5_935 := by
  apply safe_succ 7 5 s5_935 [s6_615, s6_1152, s6_678] (by decide) s5_935_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_615_safe
  · subst z; exact s6_1152_safe
  · subst z; exact s6_678_safe
def s5_936 : State := ⟨[3,228,104,224], 458319093341560876509339256479674003839114031412837488291811942269214, 3, 0, 1, 0⟩
theorem s5_936_edges : next config 5 s5_936 = [s6_632, s6_697] := by decide
theorem s5_936_safe : Safe 8 5 s5_936 := by
  apply safe_succ 7 5 s5_936 [s6_632, s6_697] (by decide) s5_936_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_632_safe
  · subst z; exact s6_697_safe
def s5_937 : State := ⟨[3,236,104,232], 117329687895439584386390849658709772974056135103126219193875962372620574, 3, 0, 1, 0⟩
theorem s5_937_edges : next config 5 s5_937 = [s6_634, s6_702] := by decide
theorem s5_937_safe : Safe 8 5 s5_937 := by
  apply safe_succ 7 5 s5_937 [s6_634, s6_702] (by decide) s5_937_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_634_safe
  · subst z; exact s6_702_safe
def s5_938 : State := ⟨[9,4,96,145], 44601830679428246449697432630985826328838934, 1, 1, 1, 0⟩
theorem s5_938_edges : next config 5 s5_938 = [s6_739] := by decide
theorem s5_938_safe : Safe 8 5 s5_938 := by
  apply safe_succ 7 5 s5_938 [s6_739] (by decide) s5_938_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_739_safe
def s5_939 : State := ⟨[9,4,96,171], 2999001359804714199988645197213662340452803967779606, 1, 0, 1, 0⟩
theorem s5_939_edges : next config 5 s5_939 = [s6_148, s6_740] := by decide
theorem s5_939_safe : Safe 8 5 s5_939 := by
  apply safe_succ 7 5 s5_939 [s6_148, s6_740] (by decide) s5_939_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_148_safe
  · subst z; exact s6_740_safe
def s5_940 : State := ⟨[9,4,96,171], 3000462861440683973439165128192525125042732827476758, 1, 0, 1, 0⟩
theorem s5_940_edges : next config 5 s5_940 = [s6_149, s6_741] := by decide
theorem s5_940_safe : Safe 8 5 s5_940 := by
  apply safe_succ 7 5 s5_940 [s6_149, s6_741] (by decide) s5_940_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_149_safe
  · subst z; exact s6_741_safe
def s5_941 : State := ⟨[9,4,104,145], 44602511244182370736228011050624637116416790, 1, 0, 1, 0⟩
theorem s5_941_edges : next config 5 s5_941 = [s6_223] := by decide
theorem s5_941_safe : Safe 8 5 s5_941 := by
  apply safe_succ 7 5 s5_941 [s6_223] (by decide) s5_941_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_223_safe
def s5_942 : State := ⟨[9,4,104,145], 66902575877979152000836802574058135085974294, 1, 0, 1, 0⟩
theorem s5_942_edges : next config 5 s5_942 = [s6_232] := by decide
theorem s5_942_safe : Safe 8 5 s5_942 := by
  apply safe_succ 7 5 s5_942 [s6_232] (by decide) s5_942_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_232_safe
def s5_943 : State := ⟨[9,4,104,162], 5846006551025023527781069414366386621401371050774, 1, 0, 1, 0⟩
theorem s5_943_edges : next config 5 s5_943 = [s6_1435, s6_258, s6_740] := by decide
theorem s5_943_safe : Safe 8 5 s5_943 := by
  apply safe_succ 7 5 s5_943 [s6_1435, s6_258, s6_740] (by decide) s5_943_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1435_safe
  · subst z; exact s6_258_safe
  · subst z; exact s6_740_safe
def s5_944 : State := ⟨[9,4,104,162], 7307508186994796978301000393229171211330230747926, 1, 0, 1, 0⟩
theorem s5_944_edges : next config 5 s5_944 = [s6_1436, s6_266, s6_741] := by decide
theorem s5_944_safe : Safe 8 5 s5_944 := by
  apply safe_succ 7 5 s5_944 [s6_1436, s6_266, s6_741] (by decide) s5_944_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1436_safe
  · subst z; exact s6_266_safe
  · subst z; exact s6_741_safe
def s5_945 : State := ⟨[9,21,64,145], 44601830679428167221534918366648232786985750, 3, 1, 1, 0⟩
theorem s5_945_edges : next config 5 s5_945 = [s6_742] := by decide
theorem s5_945_safe : Safe 8 5 s5_945 := by
  apply safe_succ 7 5 s5_945 [s6_742] (by decide) s5_945_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_742_safe
def s5_946 : State := ⟨[17,4,64,128], 340282366920938463481821351509772931358, 3, 3, 0, 0⟩
theorem s5_946_edges : next config 5 s5_946 = [s6_845, s6_770, s6_743] := by decide
theorem s5_946_safe : Safe 8 5 s5_946 := by
  apply safe_succ 7 5 s5_946 [s6_845, s6_770, s6_743] (by decide) s5_946_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_845_safe
  · subst z; exact s6_770_safe
  · subst z; exact s6_743_safe
def s5_947 : State := ⟨[17,4,64,128], 340282366920938463481821351509775024414, 3, 3, 0, 0⟩
theorem s5_947_edges : next config 5 s5_947 = [s6_815, s6_771, s6_744] := by decide
theorem s5_947_safe : Safe 8 5 s5_947 := by
  apply safe_succ 7 5 s5_947 [s6_815, s6_771, s6_744] (by decide) s5_947_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_815_safe
  · subst z; exact s6_771_safe
  · subst z; exact s6_744_safe
def s5_948 : State := ⟨[17,4,64,128], 340282366920938463481821351509775024918, 3, 3, 0, 0⟩
theorem s5_948_edges : next config 5 s5_948 = [s6_772, s6_745] := by decide
theorem s5_948_safe : Safe 8 5 s5_948 := by
  apply safe_succ 7 5 s5_948 [s6_772, s6_745] (by decide) s5_948_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_772_safe
  · subst z; exact s6_745_safe
def s5_949 : State := ⟨[17,4,64,128], 340282366920938463481821351518362865942, 3, 3, 0, 0⟩
theorem s5_949_edges : next config 5 s5_949 = [s6_846, s6_773, s6_746] := by decide
theorem s5_949_safe : Safe 8 5 s5_949 := by
  apply safe_succ 7 5 s5_949 [s6_846, s6_773, s6_746] (by decide) s5_949_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_846_safe
  · subst z; exact s6_773_safe
  · subst z; exact s6_746_safe
def s5_950 : State := ⟨[17,4,64,128], 340282366920938463481821351518364958998, 3, 3, 0, 0⟩
theorem s5_950_edges : next config 5 s5_950 = [s6_816, s6_774, s6_747] := by decide
theorem s5_950_safe : Safe 8 5 s5_950 := by
  apply safe_succ 7 5 s5_950 [s6_816, s6_774, s6_747] (by decide) s5_950_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_816_safe
  · subst z; exact s6_774_safe
  · subst z; exact s6_747_safe
def s5_951 : State := ⟨[17,4,64,128], 340282366920938463518714839657192034582, 3, 3, 0, 0⟩
theorem s5_951_edges : next config 5 s5_951 = [s6_847, s6_775, s6_748] := by decide
theorem s5_951_safe : Safe 8 5 s5_951 := by
  apply safe_succ 7 5 s5_951 [s6_847, s6_775, s6_748] (by decide) s5_951_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_847_safe
  · subst z; exact s6_775_safe
  · subst z; exact s6_748_safe
def s5_952 : State := ⟨[17,4,64,128], 340282366920938463518714839657194127638, 3, 3, 0, 0⟩
theorem s5_952_edges : next config 5 s5_952 = [s6_817, s6_776, s6_749] := by decide
theorem s5_952_safe : Safe 8 5 s5_952 := by
  apply safe_succ 7 5 s5_952 [s6_817, s6_776, s6_749] (by decide) s5_952_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_817_safe
  · subst z; exact s6_776_safe
  · subst z; exact s6_749_safe
def s5_953 : State := ⟨[17,4,65,145], 44601830679428167221534955260136380203995414, 3, 2, 1, 0⟩
theorem s5_953_edges : next config 5 s5_953 = [s6_935, s6_26, s6_848, s6_758] := by decide
theorem s5_953_safe : Safe 8 5 s5_953 := by
  apply safe_succ 7 5 s5_953 [s6_935, s6_26, s6_848, s6_758] (by decide) s5_953_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_935_safe
  · subst z; exact s6_26_safe
  · subst z; exact s6_848_safe
  · subst z; exact s6_758_safe
def s5_954 : State := ⟨[17,4,65,145], 44601830679428167221534955260136380206088470, 3, 2, 1, 0⟩
theorem s5_954_edges : next config 5 s5_954 = [s6_976, s6_27, s6_818, s6_759] := by decide
theorem s5_954_safe : Safe 8 5 s5_954 := by
  apply safe_succ 7 5 s5_954 [s6_976, s6_27, s6_818, s6_759] (by decide) s5_954_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_976_safe
  · subst z; exact s6_27_safe
  · subst z; exact s6_818_safe
  · subst z; exact s6_759_safe
def s5_955 : State := ⟨[17,4,66,145], 44601830679428167221534992153624527623098646, 3, 2, 1, 0⟩
theorem s5_955_edges : next config 5 s5_955 = [s6_936, s6_28, s6_849, s6_762] := by decide
theorem s5_955_safe : Safe 8 5 s5_955 := by
  apply safe_succ 7 5 s5_955 [s6_936, s6_28, s6_849, s6_762] (by decide) s5_955_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_936_safe
  · subst z; exact s6_28_safe
  · subst z; exact s6_849_safe
  · subst z; exact s6_762_safe
def s5_956 : State := ⟨[17,4,66,145], 44601830679428167221534992153624527625191702, 3, 2, 1, 0⟩
theorem s5_956_edges : next config 5 s5_956 = [s6_977, s6_29, s6_819, s6_763] := by decide
theorem s5_956_safe : Safe 8 5 s5_956 := by
  apply safe_succ 7 5 s5_956 [s6_977, s6_29, s6_819, s6_763] (by decide) s5_956_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_977_safe
  · subst z; exact s6_29_safe
  · subst z; exact s6_819_safe
  · subst z; exact s6_763_safe
def s5_957 : State := ⟨[17,4,67,128], 340282366920938463666288792246868447510, 3, 2, 0, 0⟩
theorem s5_957_edges : next config 5 s5_957 = [s6_850, s6_758] := by decide
theorem s5_957_safe : Safe 8 5 s5_957 := by
  apply safe_succ 7 5 s5_957 [s6_850, s6_758] (by decide) s5_957_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_850_safe
  · subst z; exact s6_758_safe
def s5_958 : State := ⟨[17,4,67,128], 340282366920938463666288792246870540566, 3, 2, 0, 0⟩
theorem s5_958_edges : next config 5 s5_958 = [s6_820, s6_759] := by decide
theorem s5_958_safe : Safe 8 5 s5_958 := by
  apply safe_succ 7 5 s5_958 [s6_820, s6_759] (by decide) s5_958_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_820_safe
  · subst z; exact s6_759_safe
def s5_959 : State := ⟨[17,4,67,128], 340282366920938463703182280394287550742, 3, 2, 0, 0⟩
theorem s5_959_edges : next config 5 s5_959 = [s6_851, s6_760] := by decide
theorem s5_959_safe : Safe 8 5 s5_959 := by
  apply safe_succ 7 5 s5_959 [s6_851, s6_760] (by decide) s5_959_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_851_safe
  · subst z; exact s6_760_safe
def s5_960 : State := ⟨[17,4,67,128], 340282366920938463703182280394289643798, 3, 2, 0, 0⟩
theorem s5_960_edges : next config 5 s5_960 = [s6_821, s6_761] := by decide
theorem s5_960_safe : Safe 8 5 s5_960 := by
  apply safe_succ 7 5 s5_960 [s6_821, s6_761] (by decide) s5_960_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_821_safe
  · subst z; exact s6_761_safe
def s5_961 : State := ⟨[17,4,67,145], 44601830679428167221535065940600822461301022, 1, 1, 1, 0⟩
theorem s5_961_edges : next config 5 s5_961 = [s6_937, s6_1303, s6_978, s6_1212, s6_854, s6_822] := by decide
theorem s5_961_safe : Safe 8 5 s5_961 := by
  apply safe_succ 7 5 s5_961 [s6_937, s6_1303, s6_978, s6_1212, s6_854, s6_822] (by decide) s5_961_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_937_safe
  · subst z; exact s6_1303_safe
  · subst z; exact s6_978_safe
  · subst z; exact s6_1212_safe
  · subst z; exact s6_854_safe
  · subst z; exact s6_822_safe
def s5_962 : State := ⟨[17,4,67,145], 44601830679428167226370843006035633998332182, 1, 0, 1, 0⟩
theorem s5_962_edges : next config 5 s5_962 = [s6_938, s6_38, s6_855, s6_823] := by decide
theorem s5_962_safe : Safe 8 5 s5_962 := by
  apply safe_succ 7 5 s5_962 [s6_938, s6_38, s6_855, s6_823] (by decide) s5_962_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_938_safe
  · subst z; exact s6_38_safe
  · subst z; exact s6_855_safe
  · subst z; exact s6_823_safe
def s5_963 : State := ⟨[17,4,67,145], 44601830679428167227579695038673968334831894, 1, 0, 1, 0⟩
theorem s5_963_edges : next config 5 s5_963 = [s6_939, s6_39, s6_856, s6_824] := by decide
theorem s5_963_safe : Safe 8 5 s5_963 := by
  apply safe_succ 7 5 s5_963 [s6_939, s6_39, s6_856, s6_824] (by decide) s5_963_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_939_safe
  · subst z; exact s6_39_safe
  · subst z; exact s6_856_safe
  · subst z; exact s6_824_safe
def s5_964 : State := ⟨[17,4,68,145], 44601830679428167221535213514553412139811094, 3, 2, 1, 0⟩
theorem s5_964_edges : next config 5 s5_964 = [s6_67] := by decide
theorem s5_964_safe : Safe 8 5 s5_964 := by
  apply safe_succ 7 5 s5_964 [s6_67] (by decide) s5_964_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_67_safe
def s5_965 : State := ⟨[17,4,80,145], 44601830679428167222743844186262861959598358, 3, 2, 1, 0⟩
theorem s5_965_edges : next config 5 s5_965 = [s6_940, s6_68, s6_857, s6_764] := by decide
theorem s5_965_safe : Safe 8 5 s5_965 := by
  apply safe_succ 7 5 s5_965 [s6_940, s6_68, s6_857, s6_764] (by decide) s5_965_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_940_safe
  · subst z; exact s6_68_safe
  · subst z; exact s6_857_safe
  · subst z; exact s6_764_safe
def s5_966 : State := ⟨[17,4,80,145], 44601830679428167222743844186262861961691414, 3, 2, 1, 0⟩
theorem s5_966_edges : next config 5 s5_966 = [s6_69, s6_825, s6_765] := by decide
theorem s5_966_safe : Safe 8 5 s5_966 := by
  apply safe_succ 7 5 s5_966 [s6_69, s6_825, s6_765] (by decide) s5_966_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_69_safe
  · subst z; exact s6_825_safe
  · subst z; exact s6_765_safe
def s5_967 : State := ⟨[17,4,81,145], 44601830679428167223952770005877491134304534, 3, 2, 1, 0⟩
theorem s5_967_edges : next config 5 s5_967 = [s6_941, s6_70, s6_858] := by decide
theorem s5_967_safe : Safe 8 5 s5_967 := by
  apply safe_succ 7 5 s5_967 [s6_941, s6_70, s6_858] (by decide) s5_967_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_941_safe
  · subst z; exact s6_70_safe
  · subst z; exact s6_858_safe
def s5_968 : State := ⟨[17,4,81,145], 44601830679428167223952770005877491136397590, 3, 2, 1, 0⟩
theorem s5_968_edges : next config 5 s5_968 = [s6_71, s6_826] := by decide
theorem s5_968_safe : Safe 8 5 s5_968 := by
  apply safe_succ 7 5 s5_968 [s6_71, s6_826] (by decide) s5_968_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_71_safe
  · subst z; exact s6_826_safe
def s5_969 : State := ⟨[17,4,82,128], 340282366920943299258886786321309962518, 3, 2, 0, 0⟩
theorem s5_969_edges : next config 5 s5_969 = [s6_859, s6_752, s6_762] := by decide
theorem s5_969_safe : Safe 8 5 s5_969 := by
  apply safe_succ 7 5 s5_969 [s6_859, s6_752, s6_762] (by decide) s5_969_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_859_safe
  · subst z; exact s6_752_safe
  · subst z; exact s6_762_safe
def s5_970 : State := ⟨[17,4,82,128], 340282366920943299258886786321312055574, 3, 2, 0, 0⟩
theorem s5_970_edges : next config 5 s5_970 = [s6_920, s6_827, s6_753, s6_768, s6_763] := by decide
theorem s5_970_safe : Safe 8 5 s5_970 := by
  apply safe_succ 7 5 s5_970 [s6_920, s6_827, s6_753, s6_768, s6_763] (by decide) s5_970_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_920_safe
  · subst z; exact s6_827_safe
  · subst z; exact s6_753_safe
  · subst z; exact s6_768_safe
  · subst z; exact s6_763_safe
def s5_971 : State := ⟨[17,4,82,128], 340282366920944508110919424655646462230, 3, 2, 0, 0⟩
theorem s5_971_edges : next config 5 s5_971 = [s6_860, s6_754, s6_764] := by decide
theorem s5_971_safe : Safe 8 5 s5_971 := by
  apply safe_succ 7 5 s5_971 [s6_860, s6_754, s6_764] (by decide) s5_971_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_860_safe
  · subst z; exact s6_754_safe
  · subst z; exact s6_764_safe
def s5_972 : State := ⟨[17,4,82,128], 340282366920944508110919424655648555286, 3, 2, 0, 0⟩
theorem s5_972_edges : next config 5 s5_972 = [s6_921, s6_828, s6_755, s6_769, s6_765] := by decide
theorem s5_972_safe : Safe 8 5 s5_972 := by
  apply safe_succ 7 5 s5_972 [s6_921, s6_828, s6_755, s6_769, s6_765] (by decide) s5_972_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_921_safe
  · subst z; exact s6_828_safe
  · subst z; exact s6_755_safe
  · subst z; exact s6_769_safe
  · subst z; exact s6_765_safe
def s5_973 : State := ⟨[17,4,82,128], 340282366921020670511342122588491153686, 3, 2, 0, 0⟩
theorem s5_973_edges : next config 5 s5_973 = [s6_861, s6_756, s6_766] := by decide
theorem s5_973_safe : Safe 8 5 s5_973 := by
  apply safe_succ 7 5 s5_973 [s6_861, s6_756, s6_766] (by decide) s5_973_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_861_safe
  · subst z; exact s6_756_safe
  · subst z; exact s6_766_safe
def s5_974 : State := ⟨[17,4,82,128], 340282366921021879363374760922827653398, 3, 2, 0, 0⟩
theorem s5_974_edges : next config 5 s5_974 = [s6_862, s6_757, s6_767] := by decide
theorem s5_974_safe : Safe 8 5 s5_974 := by
  apply safe_succ 7 5 s5_974 [s6_862, s6_757, s6_767] (by decide) s5_974_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_862_safe
  · subst z; exact s6_757_safe
  · subst z; exact s6_767_safe
def s5_975 : State := ⟨[17,4,86,145], 44601830679428167303741947887419311503114518, 1, 0, 1, 0⟩
theorem s5_975_edges : next config 5 s5_975 = [s6_942, s6_80, s6_863] := by decide
theorem s5_975_safe : Safe 8 5 s5_975 := by
  apply safe_succ 7 5 s5_975 [s6_942, s6_80, s6_863] (by decide) s5_975_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_942_safe
  · subst z; exact s6_80_safe
  · subst z; exact s6_863_safe
def s5_976 : State := ⟨[17,4,86,145], 44601830679428167304950799920057645839614230, 1, 0, 1, 0⟩
theorem s5_976_edges : next config 5 s5_976 = [s6_943, s6_81, s6_864] := by decide
theorem s5_976_safe : Safe 8 5 s5_976 := by
  apply safe_succ 7 5 s5_976 [s6_943, s6_81, s6_864] (by decide) s5_976_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_943_safe
  · subst z; exact s6_81_safe
  · subst z; exact s6_864_safe
def s5_977 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826328838430, 1, 1, 1, 0⟩
theorem s5_977_edges : next config 5 s5_977 = [s6_944, s6_1385, s6_979, s6_1213, s6_865, s6_922, s6_829, s6_801, s6_783, s6_811, s6_786] := by decide
theorem s5_977_safe : Safe 8 5 s5_977 := by
  apply safe_succ 7 5 s5_977 [s6_944, s6_1385, s6_979, s6_1213, s6_865, s6_922, s6_829, s6_801, s6_783, s6_811, s6_786] (by decide) s5_977_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s6_944_safe
  · subst z; exact s6_1385_safe
  · subst z; exact s6_979_safe
  · subst z; exact s6_1213_safe
  · subst z; exact s6_865_safe
  · subst z; exact s6_922_safe
  · subst z; exact s6_829_safe
  · subst z; exact s6_801_safe
  · subst z; exact s6_783_safe
  · subst z; exact s6_811_safe
  · subst z; exact s6_786_safe
def s5_978 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826328838934, 1, 1, 1, 0⟩
theorem s5_978_edges : next config 5 s5_978 = [s6_945, s6_866, s6_787] := by decide
theorem s5_978_safe : Safe 8 5 s5_978 := by
  apply safe_succ 7 5 s5_978 [s6_945, s6_866, s6_787] (by decide) s5_978_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_945_safe
  · subst z; exact s6_866_safe
  · subst z; exact s6_787_safe
def s5_979 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826328842518, 3, 2, 1, 0⟩
theorem s5_979_edges : next config 5 s5_979 = [s6_946, s6_1386, s6_124, s6_1214, s6_867, s6_802, s6_812, s6_788, s6_799] := by decide
theorem s5_979_safe : Safe 8 5 s5_979 := by
  apply safe_succ 7 5 s5_979 [s6_946, s6_1386, s6_124, s6_1214, s6_867, s6_802, s6_812, s6_788, s6_799] (by decide) s5_979_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_946_safe
  · subst z; exact s6_1386_safe
  · subst z; exact s6_124_safe
  · subst z; exact s6_1214_safe
  · subst z; exact s6_867_safe
  · subst z; exact s6_802_safe
  · subst z; exact s6_812_safe
  · subst z; exact s6_788_safe
  · subst z; exact s6_799_safe
def s5_980 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826330935574, 3, 2, 1, 0⟩
theorem s5_980_edges : next config 5 s5_980 = [s6_1387, s6_980, s6_125, s6_1215, s6_923, s6_830, s6_803, s6_784, s6_813, s6_789, s6_800] := by decide
theorem s5_980_safe : Safe 8 5 s5_980 := by
  apply safe_succ 7 5 s5_980 [s6_1387, s6_980, s6_125, s6_1215, s6_923, s6_830, s6_803, s6_784, s6_813, s6_789, s6_800] (by decide) s5_980_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1387_safe
  · subst z; exact s6_980_safe
  · subst z; exact s6_125_safe
  · subst z; exact s6_1215_safe
  · subst z; exact s6_923_safe
  · subst z; exact s6_830_safe
  · subst z; exact s6_803_safe
  · subst z; exact s6_784_safe
  · subst z; exact s6_813_safe
  · subst z; exact s6_789_safe
  · subst z; exact s6_800_safe
def s5_981 : State := ⟨[17,4,96,145], 44601830679428246449697432630985834918773014, 1, 1, 1, 0⟩
theorem s5_981_edges : next config 5 s5_981 = [s6_947, s6_868, s6_831, s6_790] := by decide
theorem s5_981_safe : Safe 8 5 s5_981 := by
  apply safe_succ 7 5 s5_981 [s6_947, s6_868, s6_831, s6_790] (by decide) s5_981_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_947_safe
  · subst z; exact s6_868_safe
  · subst z; exact s6_831_safe
  · subst z; exact s6_790_safe
def s5_982 : State := ⟨[17,4,96,145], 44601830679428246449697469524473973747941654, 1, 1, 1, 0⟩
theorem s5_982_edges : next config 5 s5_982 = [s6_948, s6_1388, s6_981, s6_869, s6_924, s6_832, s6_804, s6_785, s6_814, s6_791] := by decide
theorem s5_982_safe : Safe 8 5 s5_982 := by
  apply safe_succ 7 5 s5_982 [s6_948, s6_1388, s6_981, s6_869, s6_924, s6_832, s6_804, s6_785, s6_814, s6_791] (by decide) s5_982_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s6_948_safe
  · subst z; exact s6_1388_safe
  · subst z; exact s6_981_safe
  · subst z; exact s6_869_safe
  · subst z; exact s6_924_safe
  · subst z; exact s6_832_safe
  · subst z; exact s6_804_safe
  · subst z; exact s6_785_safe
  · subst z; exact s6_814_safe
  · subst z; exact s6_791_safe
def s5_983 : State := ⟨[17,4,96,145], 44601830679428246449697727778891005681664278, 3, 2, 1, 0⟩
theorem s5_983_edges : next config 5 s5_983 = [s6_949, s6_126, s6_870, s6_792] := by decide
theorem s5_983_safe : Safe 8 5 s5_983 := by
  apply safe_succ 7 5 s5_983 [s6_949, s6_126, s6_870, s6_792] (by decide) s5_983_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_949_safe
  · subst z; exact s6_126_safe
  · subst z; exact s6_870_safe
  · subst z; exact s6_792_safe
def s5_984 : State := ⟨[17,4,96,145], 44601830679428404906022461159661013416739094, 1, 1, 1, 0⟩
theorem s5_984_edges : next config 5 s5_984 = [s6_950, s6_871, s6_833, s6_793] := by decide
theorem s5_984_safe : Safe 8 5 s5_984 := by
  apply safe_succ 7 5 s5_984 [s6_950, s6_871, s6_833, s6_793] (by decide) s5_984_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_950_safe
  · subst z; exact s6_871_safe
  · subst z; exact s6_833_safe
  · subst z; exact s6_793_safe
def s5_985 : State := ⟨[17,4,96,145], 44601830679429514100297660860387323032043798, 3, 2, 1, 0⟩
theorem s5_985_edges : next config 5 s5_985 = [s6_951, s6_127, s6_872, s6_794] := by decide
theorem s5_985_safe : Safe 8 5 s5_985 := by
  apply safe_succ 7 5 s5_985 [s6_951, s6_127, s6_872, s6_794] (by decide) s5_985_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_951_safe
  · subst z; exact s6_127_safe
  · subst z; exact s6_872_safe
  · subst z; exact s6_794_safe
def s5_986 : State := ⟨[17,4,97,128], 340282367158622951024614364290404782358, 3, 2, 0, 0⟩
theorem s5_986_edges : next config 5 s5_986 = [s6_873, s6_781] := by decide
theorem s5_986_safe : Safe 8 5 s5_986 := by
  apply safe_succ 7 5 s5_986 [s6_873, s6_781] (by decide) s5_986_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_873_safe
  · subst z; exact s6_781_safe
def s5_987 : State := ⟨[17,4,97,128], 340282367158622951024614364290406875414, 3, 2, 0, 0⟩
theorem s5_987_edges : next config 5 s5_987 = [s6_834, s6_782] := by decide
theorem s5_987_safe : Safe 8 5 s5_987 := by
  apply safe_succ 7 5 s5_987 [s6_834, s6_782] (by decide) s5_987_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_834_safe
  · subst z; exact s6_782_safe
def s5_988 : State := ⟨[17,4,100,128], 340282368267817226224315090600020082974, 1, 1, 0, 0⟩
theorem s5_988_edges : next config 5 s5_988 = [s6_874, s6_783] := by decide
theorem s5_988_safe : Safe 8 5 s5_988 := by
  apply safe_succ 7 5 s5_988 [s6_874, s6_783] (by decide) s5_988_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_874_safe
  · subst z; exact s6_783_safe
def s5_989 : State := ⟨[17,4,100,128], 340282368267817226224315090600022180118, 3, 2, 0, 0⟩
theorem s5_989_edges : next config 5 s5_989 = [s6_784] := by decide
theorem s5_989_safe : Safe 8 5 s5_989 := by
  apply safe_succ 7 5 s5_989 [s6_784] (by decide) s5_989_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_784_safe
def s5_990 : State := ⟨[17,4,100,128], 340282368267817226261208578747439186198, 1, 1, 0, 0⟩
theorem s5_990_edges : next config 5 s5_990 = [s6_875, s6_785] := by decide
theorem s5_990_safe : Safe 8 5 s5_990 := by
  apply safe_succ 7 5 s5_990 [s6_875, s6_785] (by decide) s5_990_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_875_safe
  · subst z; exact s6_785_safe
def s5_991 : State := ⟨[17,4,104,128], 340282387282576229647756113050568163614, 1, 1, 0, 0⟩
theorem s5_991_edges : next config 5 s5_991 = [s6_876, s6_928, s6_835, s6_807, s6_796, s6_786] := by decide
theorem s5_991_safe : Safe 8 5 s5_991 := by
  apply safe_succ 7 5 s5_991 [s6_876, s6_928, s6_835, s6_807, s6_796, s6_786] (by decide) s5_991_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_876_safe
  · subst z; exact s6_928_safe
  · subst z; exact s6_835_safe
  · subst z; exact s6_807_safe
  · subst z; exact s6_796_safe
  · subst z; exact s6_786_safe
def s5_992 : State := ⟨[17,4,104,128], 340282387282576229647756113050568164118, 1, 1, 0, 0⟩
theorem s5_992_edges : next config 5 s5_992 = [s6_877, s6_787] := by decide
theorem s5_992_safe : Safe 8 5 s5_992 := by
  apply safe_succ 7 5 s5_992 [s6_877, s6_787] (by decide) s5_992_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_877_safe
  · subst z; exact s6_787_safe
def s5_993 : State := ⟨[17,4,104,128], 340282387282576229647756113050568167702, 3, 2, 0, 0⟩
theorem s5_993_edges : next config 5 s5_993 = [s6_878, s6_788] := by decide
theorem s5_993_safe : Safe 8 5 s5_993 := by
  apply safe_succ 7 5 s5_993 [s6_878, s6_788] (by decide) s5_993_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_878_safe
  · subst z; exact s6_788_safe
def s5_994 : State := ⟨[17,4,104,128], 340282387282576229647756113050570260758, 3, 2, 0, 0⟩
theorem s5_994_edges : next config 5 s5_994 = [s6_929, s6_836, s6_808, s6_797, s6_806, s6_789] := by decide
theorem s5_994_safe : Safe 8 5 s5_994 := by
  apply safe_succ 7 5 s5_994 [s6_929, s6_836, s6_808, s6_797, s6_806, s6_789] (by decide) s5_994_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_929_safe
  · subst z; exact s6_836_safe
  · subst z; exact s6_808_safe
  · subst z; exact s6_797_safe
  · subst z; exact s6_806_safe
  · subst z; exact s6_789_safe
def s5_995 : State := ⟨[17,4,104,128], 340282387282576229647756113059158098198, 1, 1, 0, 0⟩
theorem s5_995_edges : next config 5 s5_995 = [s6_879, s6_837, s6_790] := by decide
theorem s5_995_safe : Safe 8 5 s5_995 := by
  apply safe_succ 7 5 s5_995 [s6_879, s6_837, s6_790] (by decide) s5_995_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_879_safe
  · subst z; exact s6_837_safe
  · subst z; exact s6_790_safe
def s5_996 : State := ⟨[17,4,104,128], 340282387282576229684649601197987266838, 1, 1, 0, 0⟩
theorem s5_996_edges : next config 5 s5_996 = [s6_880, s6_930, s6_838, s6_809, s6_798, s6_791] := by decide
theorem s5_996_safe : Safe 8 5 s5_996 := by
  apply safe_succ 7 5 s5_996 [s6_880, s6_930, s6_838, s6_809, s6_798, s6_791] (by decide) s5_996_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_880_safe
  · subst z; exact s6_930_safe
  · subst z; exact s6_838_safe
  · subst z; exact s6_809_safe
  · subst z; exact s6_798_safe
  · subst z; exact s6_791_safe
def s5_997 : State := ⟨[17,4,104,128], 340282387282576229942904018229920989462, 3, 2, 0, 0⟩
theorem s5_997_edges : next config 5 s5_997 = [s6_881, s6_792] := by decide
theorem s5_997_safe : Safe 8 5 s5_997 := by
  apply safe_succ 7 5 s5_997 [s6_881, s6_792] (by decide) s5_997_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_881_safe
  · subst z; exact s6_792_safe
def s5_998 : State := ⟨[17,4,104,128], 340282387441032554676284788237656064278, 1, 1, 0, 0⟩
theorem s5_998_edges : next config 5 s5_998 = [s6_882, s6_839, s6_793] := by decide
theorem s5_998_safe : Safe 8 5 s5_998 := by
  apply safe_succ 7 5 s5_998 [s6_882, s6_839, s6_793] (by decide) s5_998_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_882_safe
  · subst z; exact s6_839_safe
  · subst z; exact s6_793_safe
def s5_999 : State := ⟨[17,4,104,128], 340282388550226829875985514547271368982, 3, 2, 0, 0⟩
theorem s5_999_edges : next config 5 s5_999 = [s6_883, s6_794] := by decide
theorem s5_999_safe : Safe 8 5 s5_999 := by
  apply safe_succ 7 5 s5_999 [s6_883, s6_794] (by decide) s5_999_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_883_safe
  · subst z; exact s6_794_safe
def s5_1000 : State := ⟨[17,4,104,128], 340282711801129888074482896206588739862, 3, 2, 0, 0⟩
theorem s5_1000_edges : next config 5 s5_1000 = [s6_884, s6_795] := by decide
theorem s5_1000_safe : Safe 8 5 s5_1000 := by
  apply safe_succ 7 5 s5_1000 [s6_884, s6_795] (by decide) s5_1000_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_884_safe
  · subst z; exact s6_795_safe
def s5_1001 : State := ⟨[17,4,108,145], 44601830679773047412959511028192929600700694, 1, 0, 1, 0⟩
theorem s5_1001_edges : next config 5 s5_1001 = [s6_952, s6_352, s6_885] := by decide
theorem s5_1001_safe : Safe 8 5 s5_1001 := by
  apply safe_succ 7 5 s5_1001 [s6_952, s6_352, s6_885] (by decide) s5_1001_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_952_safe
  · subst z; exact s6_352_safe
  · subst z; exact s6_885_safe
def s5_1002 : State := ⟨[17,4,112,128], 340287559297025160823714219599646101782, 3, 2, 0, 0⟩
theorem s5_1002_edges : next config 5 s5_1002 = [s6_886, s6_799] := by decide
theorem s5_1002_safe : Safe 8 5 s5_1002 := by
  apply safe_succ 7 5 s5_1002 [s6_886, s6_799] (by decide) s5_1002_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_886_safe
  · subst z; exact s6_799_safe
def s5_1003 : State := ⟨[17,4,112,128], 340287559297025160823714219599648194838, 3, 2, 0, 0⟩
theorem s5_1003_edges : next config 5 s5_1003 = [s6_840, s6_800] := by decide
theorem s5_1003_safe : Safe 8 5 s5_1003 := by
  apply safe_succ 7 5 s5_1003 [s6_840, s6_800] (by decide) s5_1003_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_840_safe
  · subst z; exact s6_800_safe
def s5_1004 : State := ⟨[17,4,113,128], 340292751593883695651342750095975317790, 1, 1, 0, 0⟩
theorem s5_1004_edges : next config 5 s5_1004 = [s6_887, s6_841, s6_801] := by decide
theorem s5_1004_safe : Safe 8 5 s5_1004 := by
  apply safe_succ 7 5 s5_1004 [s6_887, s6_841, s6_801] (by decide) s5_1004_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_887_safe
  · subst z; exact s6_841_safe
  · subst z; exact s6_801_safe
def s5_1005 : State := ⟨[17,4,113,128], 340292751593883695651342750095975321878, 3, 2, 0, 0⟩
theorem s5_1005_edges : next config 5 s5_1005 = [s6_888, s6_802] := by decide
theorem s5_1005_safe : Safe 8 5 s5_1005 := by
  apply safe_succ 7 5 s5_1005 [s6_888, s6_802] (by decide) s5_1005_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_888_safe
  · subst z; exact s6_802_safe
def s5_1006 : State := ⟨[17,4,113,128], 340292751593883695651342750095977414934, 3, 2, 0, 0⟩
theorem s5_1006_edges : next config 5 s5_1006 = [s6_842, s6_803] := by decide
theorem s5_1006_safe : Safe 8 5 s5_1006 := by
  apply safe_succ 7 5 s5_1006 [s6_842, s6_803] (by decide) s5_1006_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_842_safe
  · subst z; exact s6_803_safe
def s5_1007 : State := ⟨[17,4,113,128], 340292751593883695688236238243394421014, 1, 1, 0, 0⟩
theorem s5_1007_edges : next config 5 s5_1007 = [s6_889, s6_843, s6_804] := by decide
theorem s5_1007_safe : Safe 8 5 s5_1007 := by
  apply safe_succ 7 5 s5_1007 [s6_889, s6_843, s6_804] (by decide) s5_1007_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_889_safe
  · subst z; exact s6_843_safe
  · subst z; exact s6_804_safe
def s5_1008 : State := ⟨[17,4,117,128], 340448520499639740480198664985854017814, 3, 2, 0, 0⟩
theorem s5_1008_edges : next config 5 s5_1008 = [s6_805] := by decide
theorem s5_1008_safe : Safe 8 5 s5_1008 := by
  apply safe_succ 7 5 s5_1008 [s6_805] (by decide) s5_1008_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_805_safe
def s5_1009 : State := ⟨[17,4,120,145], 44601832008676524644216957205216833860469014, 1, 0, 1, 0⟩
theorem s5_1009_edges : next config 5 s5_1009 = [s6_953, s6_375, s6_892] := by decide
theorem s5_1009_safe : Safe 8 5 s5_1009 := by
  apply safe_succ 7 5 s5_1009 [s6_953, s6_375, s6_892] (by decide) s5_1009_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_953_safe
  · subst z; exact s6_375_safe
  · subst z; exact s6_892_safe
def s5_1010 : State := ⟨[17,4,121,145], 44601833337904520429132830109023894140813590, 1, 0, 1, 0⟩
theorem s5_1010_edges : next config 5 s5_1010 = [s6_954, s6_378, s6_893] := by decide
theorem s5_1010_safe : Safe 8 5 s5_1010 := by
  apply safe_succ 7 5 s5_1010 [s6_954, s6_378, s6_893] (by decide) s5_1010_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_954_safe
  · subst z; exact s6_378_safe
  · subst z; exact s6_893_safe
def s5_1011 : State := ⟨[17,4,209,145], 822752278660603021122086421958103419712902851183438164459196694, 3, 2, 1, 0⟩
theorem s5_1011_edges : next config 5 s5_1011 = [s6_956, s6_394, s6_895] := by decide
theorem s5_1011_safe : Safe 8 5 s5_1011 := by
  apply safe_succ 7 5 s5_1011 [s6_956, s6_394, s6_895] (by decide) s5_1011_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_956_safe
  · subst z; exact s6_394_safe
  · subst z; exact s6_895_safe
def s5_1012 : State := ⟨[17,4,209,145], 822752278660603021122086421958103419712902851183438164461289750, 3, 2, 1, 0⟩
theorem s5_1012_edges : next config 5 s5_1012 = [s6_395, s6_844] := by decide
theorem s5_1012_safe : Safe 8 5 s5_1012 := by
  apply safe_succ 7 5 s5_1012 [s6_395, s6_844] (by decide) s5_1012_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_395_safe
  · subst z; exact s6_844_safe
def s5_1013 : State := ⟨[17,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835401449750, 1, 0, 1, 0⟩
theorem s5_1013_edges : next config 5 s5_1013 = [s6_957, s6_410, s6_896] := by decide
theorem s5_1013_safe : Safe 8 5 s5_1013 := by
  apply safe_succ 7 5 s5_1013 [s6_957, s6_410, s6_896] (by decide) s5_1013_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_957_safe
  · subst z; exact s6_410_safe
  · subst z; exact s6_896_safe
def s5_1014 : State := ⟨[17,12,64,145], 44601830679428167221534918366648232784892190, 3, 1, 1, 0⟩
theorem s5_1014_edges : next config 5 s5_1014 = [s6_1216, s6_743, s6_829] := by decide
theorem s5_1014_safe : Safe 8 5 s5_1014 := by
  apply safe_succ 7 5 s5_1014 [s6_1216, s6_743, s6_829] (by decide) s5_1014_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1216_safe
  · subst z; exact s6_743_safe
  · subst z; exact s6_829_safe
def s5_1015 : State := ⟨[17,12,64,145], 44601830679428167221534918366648232786989334, 3, 2, 1, 0⟩
theorem s5_1015_edges : next config 5 s5_1015 = [s6_1299, s6_411, s6_1217, s6_826, s6_844, s6_819, s6_825, s6_830] := by decide
theorem s5_1015_safe : Safe 8 5 s5_1015 := by
  apply safe_succ 7 5 s5_1015 [s6_1299, s6_411, s6_1217, s6_826, s6_844, s6_819, s6_825, s6_830] (by decide) s5_1015_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1299_safe
  · subst z; exact s6_411_safe
  · subst z; exact s6_1217_safe
  · subst z; exact s6_826_safe
  · subst z; exact s6_844_safe
  · subst z; exact s6_819_safe
  · subst z; exact s6_825_safe
  · subst z; exact s6_830_safe
def s5_1016 : State := ⟨[17,12,64,145], 44601830679428167221534918366648241374826774, 3, 1, 1, 0⟩
theorem s5_1016_edges : next config 5 s5_1016 = [s6_746, s6_831] := by decide
theorem s5_1016_safe : Safe 8 5 s5_1016 := by
  apply safe_succ 7 5 s5_1016 [s6_746, s6_831] (by decide) s5_1016_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_746_safe
  · subst z; exact s6_831_safe
def s5_1017 : State := ⟨[17,12,64,145], 44601830679428167221534955260136380203995414, 3, 1, 1, 0⟩
theorem s5_1017_edges : next config 5 s5_1017 = [s6_748, s6_832] := by decide
theorem s5_1017_safe : Safe 8 5 s5_1017 := by
  apply safe_succ 7 5 s5_1017 [s6_748, s6_832] (by decide) s5_1017_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_748_safe
  · subst z; exact s6_832_safe
def s5_1018 : State := ⟨[17,12,65,128], 340282366920938463518714839657194131734, 3, 2, 0, 0⟩
theorem s5_1018_edges : next config 5 s5_1018 = [s6_820, s6_818] := by decide
theorem s5_1018_safe : Safe 8 5 s5_1018 := by
  apply safe_succ 7 5 s5_1018 [s6_820, s6_818] (by decide) s5_1018_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_820_safe
  · subst z; exact s6_818_safe
def s5_1019 : State := ⟨[17,12,66,128], 340282366920938463555608327804613234966, 3, 2, 0, 0⟩
theorem s5_1019_edges : next config 5 s5_1019 = [s6_827, s6_819] := by decide
theorem s5_1019_safe : Safe 8 5 s5_1019 := by
  apply safe_succ 7 5 s5_1019 [s6_827, s6_819] (by decide) s5_1019_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_827_safe
  · subst z; exact s6_819_safe
def s5_1020 : State := ⟨[17,12,67,128], 340282366920938463629395304099449344286, 3, 1, 0, 0⟩
theorem s5_1020_edges : next config 5 s5_1020 = [s6_750, s6_822] := by decide
theorem s5_1020_safe : Safe 8 5 s5_1020 := by
  apply safe_succ 7 5 s5_1020 [s6_750, s6_822] (by decide) s5_1020_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_750_safe
  · subst z; exact s6_822_safe
def s5_1021 : State := ⟨[17,12,67,128], 340282366920943299406460738910986375446, 3, 0, 0, 0⟩
theorem s5_1021_edges : next config 5 s5_1021 = [s6_752, s6_823] := by decide
theorem s5_1021_safe : Safe 8 5 s5_1021 := by
  apply safe_succ 7 5 s5_1021 [s6_752, s6_823] (by decide) s5_1021_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_752_safe
  · subst z; exact s6_823_safe
def s5_1022 : State := ⟨[17,12,67,128], 340282366920944508258493377245322875158, 3, 0, 0, 0⟩
theorem s5_1022_edges : next config 5 s5_1022 = [s6_754, s6_824] := by decide
theorem s5_1022_safe : Safe 8 5 s5_1022 := by
  apply safe_succ 7 5 s5_1022 [s6_754, s6_824] (by decide) s5_1022_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_754_safe
  · subst z; exact s6_824_safe
def s5_1023 : State := ⟨[17,12,67,145], 44601830679428167221535102834088969880408342, 3, 0, 1, 0⟩
theorem s5_1023_edges : next config 5 s5_1023 = [s6_1304, s6_414, s6_758] := by decide
theorem s5_1023_safe : Safe 8 5 s5_1023 := by
  apply safe_succ 7 5 s5_1023 [s6_1304, s6_414, s6_758] (by decide) s5_1023_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1304_safe
  · subst z; exact s6_414_safe
  · subst z; exact s6_758_safe
def s5_1024 : State := ⟨[17,12,67,145], 44601830679428167221535139727577117299511574, 3, 0, 1, 0⟩
theorem s5_1024_edges : next config 5 s5_1024 = [s6_1305, s6_415, s6_760] := by decide
theorem s5_1024_safe : Safe 8 5 s5_1024 := by
  apply safe_succ 7 5 s5_1024 [s6_1305, s6_415, s6_760] (by decide) s5_1024_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1305_safe
  · subst z; exact s6_415_safe
  · subst z; exact s6_760_safe
def s5_1025 : State := ⟨[17,12,80,128], 340282366920939672407640966138949734678, 3, 2, 0, 0⟩
theorem s5_1025_edges : next config 5 s5_1025 = [s6_828, s6_825] := by decide
theorem s5_1025_safe : Safe 8 5 s5_1025 := by
  apply safe_succ 7 5 s5_1025 [s6_828, s6_825] (by decide) s5_1025_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_828_safe
  · subst z; exact s6_825_safe
def s5_1026 : State := ⟨[17,12,81,128], 340282366920940881333460580768124440854, 3, 2, 0, 0⟩
theorem s5_1026_edges : next config 5 s5_1026 = [s6_826] := by decide
theorem s5_1026_safe : Safe 8 5 s5_1026 := by
  apply safe_succ 7 5 s5_1026 [s6_826] (by decide) s5_1026_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_826_safe
def s5_1027 : State := ⟨[17,12,82,145], 44601830679428167226370695432083044321923350, 3, 0, 1, 0⟩
theorem s5_1027_edges : next config 5 s5_1027 = [s6_429, s6_762, s6_823] := by decide
theorem s5_1027_safe : Safe 8 5 s5_1027 := by
  apply safe_succ 7 5 s5_1027 [s6_429, s6_762, s6_823] (by decide) s5_1027_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_429_safe
  · subst z; exact s6_762_safe
  · subst z; exact s6_823_safe
def s5_1028 : State := ⟨[17,12,82,145], 44601830679428167227579547464721378658423062, 3, 0, 1, 0⟩
theorem s5_1028_edges : next config 5 s5_1028 = [s6_430, s6_764, s6_824] := by decide
theorem s5_1028_safe : Safe 8 5 s5_1028 := by
  apply safe_succ 7 5 s5_1028 [s6_430, s6_764, s6_824] (by decide) s5_1028_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_430_safe
  · subst z; exact s6_764_safe
  · subst z; exact s6_824_safe
def s5_1029 : State := ⟨[17,12,96,128], 340282367000166625996085689103316881694, 3, 1, 0, 0⟩
theorem s5_1029_edges : next config 5 s5_1029 = [s6_770, s6_841, s6_835, s6_829] := by decide
theorem s5_1029_safe : Safe 8 5 s5_1029 := by
  apply safe_succ 7 5 s5_1029 [s6_770, s6_841, s6_835, s6_829] (by decide) s5_1029_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_770_safe
  · subst z; exact s6_841_safe
  · subst z; exact s6_835_safe
  · subst z; exact s6_829_safe
def s5_1030 : State := ⟨[17,12,96,128], 340282367000166625996085689103318978838, 3, 2, 0, 0⟩
theorem s5_1030_edges : next config 5 s5_1030 = [s6_842, s6_836, s6_840, s6_830] := by decide
theorem s5_1030_safe : Safe 8 5 s5_1030 := by
  apply safe_succ 7 5 s5_1030 [s6_842, s6_836, s6_840, s6_830] (by decide) s5_1030_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_842_safe
  · subst z; exact s6_836_safe
  · subst z; exact s6_840_safe
  · subst z; exact s6_830_safe
def s5_1031 : State := ⟨[17,12,96,128], 340282367000166625996085689111906816278, 3, 1, 0, 0⟩
theorem s5_1031_edges : next config 5 s5_1031 = [s6_773, s6_837, s6_831] := by decide
theorem s5_1031_safe : Safe 8 5 s5_1031 := by
  apply safe_succ 7 5 s5_1031 [s6_773, s6_837, s6_831] (by decide) s5_1031_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_773_safe
  · subst z; exact s6_837_safe
  · subst z; exact s6_831_safe
def s5_1032 : State := ⟨[17,12,96,128], 340282367000166626032979177250735984918, 3, 1, 0, 0⟩
theorem s5_1032_edges : next config 5 s5_1032 = [s6_775, s6_843, s6_838, s6_832] := by decide
theorem s5_1032_safe : Safe 8 5 s5_1032 := by
  apply safe_succ 7 5 s5_1032 [s6_775, s6_843, s6_838, s6_832] (by decide) s5_1032_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_775_safe
  · subst z; exact s6_843_safe
  · subst z; exact s6_838_safe
  · subst z; exact s6_832_safe
def s5_1033 : State := ⟨[17,12,96,128], 340282367158622951024614364290404782358, 3, 1, 0, 0⟩
theorem s5_1033_edges : next config 5 s5_1033 = [s6_777, s6_839, s6_833] := by decide
theorem s5_1033_safe : Safe 8 5 s5_1033 := by
  apply safe_succ 7 5 s5_1033 [s6_777, s6_839, s6_833] (by decide) s5_1033_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_777_safe
  · subst z; exact s6_839_safe
  · subst z; exact s6_833_safe
def s5_1034 : State := ⟨[17,12,97,145], 44601830679428404906022461159661013416743190, 3, 0, 1, 0⟩
theorem s5_1034_edges : next config 5 s5_1034 = [s6_461, s6_781] := by decide
theorem s5_1034_safe : Safe 8 5 s5_1034 := by
  apply safe_succ 7 5 s5_1034 [s6_461, s6_781] (by decide) s5_1034_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_461_safe
  · subst z; exact s6_781_safe
def s5_1035 : State := ⟨[17,12,104,145], 44601830679448528859301084301409773580128534, 3, 0, 1, 0⟩
theorem s5_1035_edges : next config 5 s5_1035 = [s6_488, s6_1218, s6_788] := by decide
theorem s5_1035_safe : Safe 8 5 s5_1035 := by
  apply safe_succ 7 5 s5_1035 [s6_488, s6_1218, s6_788] (by decide) s5_1035_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_488_safe
  · subst z; exact s6_1218_safe
  · subst z; exact s6_788_safe
def s5_1036 : State := ⟨[17,12,112,145], 44601830684620543308232260259516322658062614, 3, 0, 1, 0⟩
theorem s5_1036_edges : next config 5 s5_1036 = [s6_527, s6_799] := by decide
theorem s5_1036_safe : Safe 8 5 s5_1036 := by
  apply safe_succ 7 5 s5_1036 [s6_527, s6_799] (by decide) s5_1036_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_527_safe
  · subst z; exact s6_799_safe
def s5_1037 : State := ⟨[17,12,113,145], 44601830689812840166767087888046818987282710, 3, 0, 1, 0⟩
theorem s5_1037_edges : next config 5 s5_1037 = [s6_528, s6_802] := by decide
theorem s5_1037_safe : Safe 8 5 s5_1037 := by
  apply safe_succ 7 5 s5_1037 [s6_528, s6_802] (by decide) s5_1037_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_528_safe
  · subst z; exact s6_802_safe
def s5_1038 : State := ⟨[17,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082070, 3, 0, 1, 0⟩
theorem s5_1038_edges : next config 5 s5_1038 = [s6_530, s6_812] := by decide
theorem s5_1038_safe : Safe 8 5 s5_1038 := by
  apply safe_succ 7 5 s5_1038 [s6_530, s6_812] (by decide) s5_1038_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_530_safe
  · subst z; exact s6_812_safe
def s5_1039 : State := ⟨[17,21,64,145], 44601830679428167221534918366648232786985246, 3, 1, 1, 0⟩
theorem s5_1039_edges : next config 5 s5_1039 = [s6_982, s6_1219, s6_744, s6_897, s6_907, s6_865] := by decide
theorem s5_1039_safe : Safe 8 5 s5_1039 := by
  apply safe_succ 7 5 s5_1039 [s6_982, s6_1219, s6_744, s6_897, s6_907, s6_865] (by decide) s5_1039_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_982_safe
  · subst z; exact s6_1219_safe
  · subst z; exact s6_744_safe
  · subst z; exact s6_897_safe
  · subst z; exact s6_907_safe
  · subst z; exact s6_865_safe
def s5_1040 : State := ⟨[17,21,64,145], 44601830679428167221534918366648232786985750, 3, 1, 1, 0⟩
theorem s5_1040_edges : next config 5 s5_1040 = [s6_745, s6_866] := by decide
theorem s5_1040_safe : Safe 8 5 s5_1040 := by
  apply safe_succ 7 5 s5_1040 [s6_745, s6_866] (by decide) s5_1040_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_745_safe
  · subst z; exact s6_866_safe
def s5_1041 : State := ⟨[17,21,64,145], 44601830679428167221534918366648232786989334, 3, 2, 1, 0⟩
theorem s5_1041_edges : next config 5 s5_1041 = [s6_1301, s6_531, s6_1220, s6_858, s6_895, s6_849, s6_857, s6_867] := by decide
theorem s5_1041_safe : Safe 8 5 s5_1041 := by
  apply safe_succ 7 5 s5_1041 [s6_1301, s6_531, s6_1220, s6_858, s6_895, s6_849, s6_857, s6_867] (by decide) s5_1041_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1301_safe
  · subst z; exact s6_531_safe
  · subst z; exact s6_1220_safe
  · subst z; exact s6_858_safe
  · subst z; exact s6_895_safe
  · subst z; exact s6_849_safe
  · subst z; exact s6_857_safe
  · subst z; exact s6_867_safe
def s5_1042 : State := ⟨[17,21,64,145], 44601830679428167221534918366648241376919830, 3, 1, 1, 0⟩
theorem s5_1042_edges : next config 5 s5_1042 = [s6_747, s6_898, s6_868] := by decide
theorem s5_1042_safe : Safe 8 5 s5_1042 := by
  apply safe_succ 7 5 s5_1042 [s6_747, s6_898, s6_868] (by decide) s5_1042_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_747_safe
  · subst z; exact s6_898_safe
  · subst z; exact s6_868_safe
def s5_1043 : State := ⟨[17,21,64,145], 44601830679428167221534955260136380206088470, 3, 1, 1, 0⟩
theorem s5_1043_edges : next config 5 s5_1043 = [s6_983, s6_749, s6_899, s6_869] := by decide
theorem s5_1043_safe : Safe 8 5 s5_1043 := by
  apply safe_succ 7 5 s5_1043 [s6_983, s6_749, s6_899, s6_869] (by decide) s5_1043_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_983_safe
  · subst z; exact s6_749_safe
  · subst z; exact s6_899_safe
  · subst z; exact s6_869_safe
def s5_1044 : State := ⟨[17,21,64,145], 44601830679428167221535213514553412139811094, 3, 2, 1, 0⟩
theorem s5_1044_edges : next config 5 s5_1044 = [s6_532, s6_870] := by decide
theorem s5_1044_safe : Safe 8 5 s5_1044 := by
  apply safe_succ 7 5 s5_1044 [s6_532, s6_870] (by decide) s5_1044_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_532_safe
  · subst z; exact s6_870_safe
def s5_1045 : State := ⟨[17,21,65,128], 340282366920938463518714839657194131734, 3, 2, 0, 0⟩
theorem s5_1045_edges : next config 5 s5_1045 = [s6_850, s6_848] := by decide
theorem s5_1045_safe : Safe 8 5 s5_1045 := by
  apply safe_succ 7 5 s5_1045 [s6_850, s6_848] (by decide) s5_1045_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_850_safe
  · subst z; exact s6_848_safe
def s5_1046 : State := ⟨[17,21,66,128], 340282366920938463555608327804613234966, 3, 2, 0, 0⟩
theorem s5_1046_edges : next config 5 s5_1046 = [s6_859, s6_849] := by decide
theorem s5_1046_safe : Safe 8 5 s5_1046 := by
  apply safe_succ 7 5 s5_1046 [s6_859, s6_849] (by decide) s5_1046_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_859_safe
  · subst z; exact s6_849_safe
def s5_1047 : State := ⟨[17,21,67,128], 340282366920938463629395304099451437342, 3, 1, 0, 0⟩
theorem s5_1047_edges : next config 5 s5_1047 = [s6_751, s6_913, s6_900, s6_908, s6_854] := by decide
theorem s5_1047_safe : Safe 8 5 s5_1047 := by
  apply safe_succ 7 5 s5_1047 [s6_751, s6_913, s6_900, s6_908, s6_854] (by decide) s5_1047_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_751_safe
  · subst z; exact s6_913_safe
  · subst z; exact s6_900_safe
  · subst z; exact s6_908_safe
  · subst z; exact s6_854_safe
def s5_1048 : State := ⟨[17,21,67,128], 340282366920943299406460738910988468502, 3, 0, 0, 0⟩
theorem s5_1048_edges : next config 5 s5_1048 = [s6_753, s6_914, s6_855] := by decide
theorem s5_1048_safe : Safe 8 5 s5_1048 := by
  apply safe_succ 7 5 s5_1048 [s6_753, s6_914, s6_855] (by decide) s5_1048_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_753_safe
  · subst z; exact s6_914_safe
  · subst z; exact s6_855_safe
def s5_1049 : State := ⟨[17,21,67,128], 340282366920944508258493377245324968214, 3, 0, 0, 0⟩
theorem s5_1049_edges : next config 5 s5_1049 = [s6_755, s6_915, s6_856] := by decide
theorem s5_1049_safe : Safe 8 5 s5_1049 := by
  apply safe_succ 7 5 s5_1049 [s6_755, s6_915, s6_856] (by decide) s5_1049_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_755_safe
  · subst z; exact s6_915_safe
  · subst z; exact s6_856_safe
def s5_1050 : State := ⟨[17,21,67,145], 44601830679428167221535102834088969882501398, 3, 0, 1, 0⟩
theorem s5_1050_edges : next config 5 s5_1050 = [s6_1306, s6_984, s6_533, s6_759, s6_916, s6_901] := by decide
theorem s5_1050_safe : Safe 8 5 s5_1050 := by
  apply safe_succ 7 5 s5_1050 [s6_1306, s6_984, s6_533, s6_759, s6_916, s6_901] (by decide) s5_1050_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1306_safe
  · subst z; exact s6_984_safe
  · subst z; exact s6_533_safe
  · subst z; exact s6_759_safe
  · subst z; exact s6_916_safe
  · subst z; exact s6_901_safe
def s5_1051 : State := ⟨[17,21,67,145], 44601830679428167221535139727577117301604630, 3, 0, 1, 0⟩
theorem s5_1051_edges : next config 5 s5_1051 = [s6_1307, s6_985, s6_534, s6_761, s6_917, s6_902] := by decide
theorem s5_1051_safe : Safe 8 5 s5_1051 := by
  apply safe_succ 7 5 s5_1051 [s6_1307, s6_985, s6_534, s6_761, s6_917, s6_902] (by decide) s5_1051_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1307_safe
  · subst z; exact s6_985_safe
  · subst z; exact s6_534_safe
  · subst z; exact s6_761_safe
  · subst z; exact s6_917_safe
  · subst z; exact s6_902_safe
def s5_1052 : State := ⟨[17,21,80,128], 340282366920939672407640966138949734678, 3, 2, 0, 0⟩
theorem s5_1052_edges : next config 5 s5_1052 = [s6_860, s6_857] := by decide
theorem s5_1052_safe : Safe 8 5 s5_1052 := by
  apply safe_succ 7 5 s5_1052 [s6_860, s6_857] (by decide) s5_1052_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_860_safe
  · subst z; exact s6_857_safe
def s5_1053 : State := ⟨[17,21,81,128], 340282366920940881333460580768124440854, 3, 2, 0, 0⟩
theorem s5_1053_edges : next config 5 s5_1053 = [s6_858] := by decide
theorem s5_1053_safe : Safe 8 5 s5_1053 := by
  apply safe_succ 7 5 s5_1053 [s6_858] (by decide) s5_1053_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_858_safe
def s5_1054 : State := ⟨[17,21,82,145], 44601830679428167226370695432083044324016406, 3, 0, 1, 0⟩
theorem s5_1054_edges : next config 5 s5_1054 = [s6_535, s6_763, s6_855] := by decide
theorem s5_1054_safe : Safe 8 5 s5_1054 := by
  apply safe_succ 7 5 s5_1054 [s6_535, s6_763, s6_855] (by decide) s5_1054_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_535_safe
  · subst z; exact s6_763_safe
  · subst z; exact s6_855_safe
def s5_1055 : State := ⟨[17,21,82,145], 44601830679428167227579547464721378660516118, 3, 0, 1, 0⟩
theorem s5_1055_edges : next config 5 s5_1055 = [s6_536, s6_765, s6_856] := by decide
theorem s5_1055_safe : Safe 8 5 s5_1055 := by
  apply safe_succ 7 5 s5_1055 [s6_536, s6_765, s6_856] (by decide) s5_1055_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_536_safe
  · subst z; exact s6_765_safe
  · subst z; exact s6_856_safe
def s5_1056 : State := ⟨[17,21,86,128], 340282366921020670511342122588493250838, 3, 0, 0, 0⟩
theorem s5_1056_edges : next config 5 s5_1056 = [s6_768, s6_852, s6_863] := by decide
theorem s5_1056_safe : Safe 8 5 s5_1056 := by
  apply safe_succ 7 5 s5_1056 [s6_768, s6_852, s6_863] (by decide) s5_1056_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_768_safe
  · subst z; exact s6_852_safe
  · subst z; exact s6_863_safe
def s5_1057 : State := ⟨[17,21,86,128], 340282366921021879363374760922829750550, 3, 0, 0, 0⟩
theorem s5_1057_edges : next config 5 s5_1057 = [s6_769, s6_853, s6_864] := by decide
theorem s5_1057_safe : Safe 8 5 s5_1057 := by
  apply safe_succ 7 5 s5_1057 [s6_769, s6_853, s6_864] (by decide) s5_1057_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_769_safe
  · subst z; exact s6_853_safe
  · subst z; exact s6_864_safe
def s5_1058 : State := ⟨[17,21,96,128], 340282367000166625996085689103318974750, 3, 1, 0, 0⟩
theorem s5_1058_edges : next config 5 s5_1058 = [s6_771, s6_931, s6_903, s6_909, s6_887, s6_890, s6_876, s6_865] := by decide
theorem s5_1058_safe : Safe 8 5 s5_1058 := by
  apply safe_succ 7 5 s5_1058 [s6_771, s6_931, s6_903, s6_909, s6_887, s6_890, s6_876, s6_865] (by decide) s5_1058_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_771_safe
  · subst z; exact s6_931_safe
  · subst z; exact s6_903_safe
  · subst z; exact s6_909_safe
  · subst z; exact s6_887_safe
  · subst z; exact s6_890_safe
  · subst z; exact s6_876_safe
  · subst z; exact s6_865_safe
def s5_1059 : State := ⟨[17,21,96,128], 340282367000166625996085689103318975254, 3, 1, 0, 0⟩
theorem s5_1059_edges : next config 5 s5_1059 = [s6_772, s6_877, s6_866] := by decide
theorem s5_1059_safe : Safe 8 5 s5_1059 := by
  apply safe_succ 7 5 s5_1059 [s6_772, s6_877, s6_866] (by decide) s5_1059_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_772_safe
  · subst z; exact s6_877_safe
  · subst z; exact s6_866_safe
def s5_1060 : State := ⟨[17,21,96,128], 340282367000166625996085689103318978838, 3, 2, 0, 0⟩
theorem s5_1060_edges : next config 5 s5_1060 = [s6_888, s6_878, s6_886, s6_867] := by decide
theorem s5_1060_safe : Safe 8 5 s5_1060 := by
  apply safe_succ 7 5 s5_1060 [s6_888, s6_878, s6_886, s6_867] (by decide) s5_1060_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_888_safe
  · subst z; exact s6_878_safe
  · subst z; exact s6_886_safe
  · subst z; exact s6_867_safe
def s5_1061 : State := ⟨[17,21,96,128], 340282367000166625996085689111908909334, 3, 1, 0, 0⟩
theorem s5_1061_edges : next config 5 s5_1061 = [s6_774, s6_904, s6_879, s6_868] := by decide
theorem s5_1061_safe : Safe 8 5 s5_1061 := by
  apply safe_succ 7 5 s5_1061 [s6_774, s6_904, s6_879, s6_868] (by decide) s5_1061_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_774_safe
  · subst z; exact s6_904_safe
  · subst z; exact s6_879_safe
  · subst z; exact s6_868_safe
def s5_1062 : State := ⟨[17,21,96,128], 340282367000166626032979177250738077974, 3, 1, 0, 0⟩
theorem s5_1062_edges : next config 5 s5_1062 = [s6_776, s6_932, s6_905, s6_889, s6_891, s6_880, s6_869] := by decide
theorem s5_1062_safe : Safe 8 5 s5_1062 := by
  apply safe_succ 7 5 s5_1062 [s6_776, s6_932, s6_905, s6_889, s6_891, s6_880, s6_869] (by decide) s5_1062_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_776_safe
  · subst z; exact s6_932_safe
  · subst z; exact s6_905_safe
  · subst z; exact s6_889_safe
  · subst z; exact s6_891_safe
  · subst z; exact s6_880_safe
  · subst z; exact s6_869_safe
def s5_1063 : State := ⟨[17,21,96,128], 340282367000166626291233594282671800598, 3, 2, 0, 0⟩
theorem s5_1063_edges : next config 5 s5_1063 = [s6_881, s6_870] := by decide
theorem s5_1063_safe : Safe 8 5 s5_1063 := by
  apply safe_succ 7 5 s5_1063 [s6_881, s6_870] (by decide) s5_1063_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_881_safe
  · subst z; exact s6_870_safe
def s5_1064 : State := ⟨[17,21,96,128], 340282367158622951024614364290406875414, 3, 1, 0, 0⟩
theorem s5_1064_edges : next config 5 s5_1064 = [s6_778, s6_882, s6_871] := by decide
theorem s5_1064_safe : Safe 8 5 s5_1064 := by
  apply safe_succ 7 5 s5_1064 [s6_778, s6_882, s6_871] (by decide) s5_1064_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_778_safe
  · subst z; exact s6_882_safe
  · subst z; exact s6_871_safe
def s5_1065 : State := ⟨[17,21,96,128], 340282368267817226224315090600022180118, 3, 2, 0, 0⟩
theorem s5_1065_edges : next config 5 s5_1065 = [s6_883, s6_872] := by decide
theorem s5_1065_safe : Safe 8 5 s5_1065 := by
  apply safe_succ 7 5 s5_1065 [s6_883, s6_872] (by decide) s5_1065_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_883_safe
  · subst z; exact s6_872_safe
def s5_1066 : State := ⟨[17,21,97,145], 44601830679428404906022461159661013418836246, 3, 0, 1, 0⟩
theorem s5_1066_edges : next config 5 s5_1066 = [s6_537, s6_782] := by decide
theorem s5_1066_safe : Safe 8 5 s5_1066 := by
  apply safe_succ 7 5 s5_1066 [s6_537, s6_782] (by decide) s5_1066_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_537_safe
  · subst z; exact s6_782_safe
def s5_1067 : State := ⟨[17,21,100,145], 44601830679429514100297660860387323034140950, 3, 0, 1, 0⟩
theorem s5_1067_edges : next config 5 s5_1067 = [s6_538, s6_784] := by decide
theorem s5_1067_safe : Safe 8 5 s5_1067 := by
  apply safe_succ 7 5 s5_1067 [s6_538, s6_784] (by decide) s5_1067_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_538_safe
  · subst z; exact s6_784_safe
def s5_1068 : State := ⟨[17,21,104,145], 44601830679448528859301084301409773582221590, 3, 0, 1, 0⟩
theorem s5_1068_edges : next config 5 s5_1068 = [s6_1392, s6_986, s6_539, s6_1221, s6_789, s6_934, s6_906, s6_910, s6_893, s6_894, s6_896, s6_892] := by decide
theorem s5_1068_safe : Safe 8 5 s5_1068 := by
  apply safe_succ 7 5 s5_1068 [s6_1392, s6_986, s6_539, s6_1221, s6_789, s6_934, s6_906, s6_910, s6_893, s6_894, s6_896, s6_892] (by decide) s5_1068_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1392_safe
  · subst z; exact s6_986_safe
  · subst z; exact s6_539_safe
  · subst z; exact s6_1221_safe
  · subst z; exact s6_789_safe
  · subst z; exact s6_934_safe
  · subst z; exact s6_906_safe
  · subst z; exact s6_910_safe
  · subst z; exact s6_893_safe
  · subst z; exact s6_894_safe
  · subst z; exact s6_896_safe
  · subst z; exact s6_892_safe
def s5_1069 : State := ⟨[17,21,108,128], 340282711801129888074482896206590837014, 3, 0, 0, 0⟩
theorem s5_1069_edges : next config 5 s5_1069 = [s6_797, s6_885] := by decide
theorem s5_1069_safe : Safe 8 5 s5_1069 := by
  apply safe_succ 7 5 s5_1069 [s6_797, s6_885] (by decide) s5_1069_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_797_safe
  · subst z; exact s6_885_safe
def s5_1070 : State := ⟨[17,21,112,145], 44601830684620543308232260259516322660155670, 3, 0, 1, 0⟩
theorem s5_1070_edges : next config 5 s5_1070 = [s6_540, s6_800] := by decide
theorem s5_1070_safe : Safe 8 5 s5_1070 := by
  apply safe_succ 7 5 s5_1070 [s6_540, s6_800] (by decide) s5_1070_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_540_safe
  · subst z; exact s6_800_safe
def s5_1071 : State := ⟨[17,21,113,145], 44601830689812840166767087888046818989375766, 3, 0, 1, 0⟩
theorem s5_1071_edges : next config 5 s5_1071 = [s6_541, s6_803] := by decide
theorem s5_1071_safe : Safe 8 5 s5_1071 := by
  apply safe_succ 7 5 s5_1071 [s6_541, s6_803] (by decide) s5_1071_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_541_safe
  · subst z; exact s6_803_safe
def s5_1072 : State := ⟨[17,21,117,145], 44601830845581745922811916743961708865978646, 3, 0, 1, 0⟩
theorem s5_1072_edges : next config 5 s5_1072 = [s6_542, s6_805] := by decide
theorem s5_1072_safe : Safe 8 5 s5_1072 := by
  apply safe_succ 7 5 s5_1072 [s6_542, s6_805] (by decide) s5_1072_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_542_safe
  · subst z; exact s6_805_safe
def s5_1073 : State := ⟨[17,21,120,128], 341611615278361145520659920110850605334, 3, 0, 0, 0⟩
theorem s5_1073_edges : next config 5 s5_1073 = [s6_806, s6_892] := by decide
theorem s5_1073_safe : Safe 8 5 s5_1073 := by
  apply safe_succ 7 5 s5_1073 [s6_806, s6_892] (by decide) s5_1073_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_806_safe
  · subst z; exact s6_892_safe
def s5_1074 : State := ⟨[17,21,121,128], 342940843274146061393563727171130949910, 3, 0, 0, 0⟩
theorem s5_1074_edges : next config 5 s5_1074 = [s6_808, s6_893] := by decide
theorem s5_1074_safe : Safe 8 5 s5_1074 := by
  apply safe_succ 7 5 s5_1074 [s6_808, s6_893] (by decide) s5_1074_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_808_safe
  · subst z; exact s6_893_safe
def s5_1075 : State := ⟨[17,21,125,128], 382817683147693537580677938979541287190, 3, 0, 0, 0⟩
theorem s5_1075_edges : next config 5 s5_1075 = [s6_810, s6_894] := by decide
theorem s5_1075_safe : Safe 8 5 s5_1075 := by
  apply safe_succ 7 5 s5_1075 [s6_810, s6_894] (by decide) s5_1075_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_810_safe
  · subst z; exact s6_894_safe
def s5_1076 : State := ⟨[17,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175126, 3, 0, 1, 0⟩
theorem s5_1076_edges : next config 5 s5_1076 = [s6_543, s6_813] := by decide
theorem s5_1076_safe : Safe 8 5 s5_1076 := by
  apply safe_succ 7 5 s5_1076 [s6_543, s6_813] (by decide) s5_1076_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_543_safe
  · subst z; exact s6_813_safe
def s5_1077 : State := ⟨[17,29,64,128], 340282366920938463481821351510311895326, 3, 1, 0, 0⟩
theorem s5_1077_edges : next config 5 s5_1077 = [s6_903, s6_897] := by decide
theorem s5_1077_safe : Safe 8 5 s5_1077 := by
  apply safe_succ 7 5 s5_1077 [s6_903, s6_897] (by decide) s5_1077_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_903_safe
  · subst z; exact s6_897_safe
def s5_1078 : State := ⟨[17,29,64,128], 340282366920938463481821351518901829910, 3, 1, 0, 0⟩
theorem s5_1078_edges : next config 5 s5_1078 = [s6_904, s6_898] := by decide
theorem s5_1078_safe : Safe 8 5 s5_1078 := by
  apply safe_succ 7 5 s5_1078 [s6_904, s6_898] (by decide) s5_1078_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_904_safe
  · subst z; exact s6_898_safe
def s5_1079 : State := ⟨[17,29,64,128], 340282366920938463518714839657730998550, 3, 1, 0, 0⟩
theorem s5_1079_edges : next config 5 s5_1079 = [s6_905, s6_899] := by decide
theorem s5_1079_safe : Safe 8 5 s5_1079 := by
  apply safe_succ 7 5 s5_1079 [s6_905, s6_899] (by decide) s5_1079_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_905_safe
  · subst z; exact s6_899_safe
def s5_1080 : State := ⟨[17,29,65,145], 44601830679428167221534955260136380742959382, 3, 0, 1, 0⟩
theorem s5_1080_edges : next config 5 s5_1080 = [s6_544, s6_901] := by decide
theorem s5_1080_safe : Safe 8 5 s5_1080 := by
  apply safe_succ 7 5 s5_1080 [s6_544, s6_901] (by decide) s5_1080_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_544_safe
  · subst z; exact s6_901_safe
def s5_1081 : State := ⟨[17,29,66,145], 44601830679428167221534992153624528162062614, 3, 0, 1, 0⟩
theorem s5_1081_edges : next config 5 s5_1081 = [s6_545] := by decide
theorem s5_1081_safe : Safe 8 5 s5_1081 := by
  apply safe_succ 7 5 s5_1081 [s6_545] (by decide) s5_1081_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_545_safe
def s5_1082 : State := ⟨[17,29,67,128], 340282366920938463666288792247407411478, 3, 0, 0, 0⟩
theorem s5_1082_edges : next config 5 s5_1082 = [s6_901] := by decide
theorem s5_1082_safe : Safe 8 5 s5_1082 := by
  apply safe_succ 7 5 s5_1082 [s6_901] (by decide) s5_1082_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_901_safe
def s5_1083 : State := ⟨[17,29,67,128], 340282366920938463703182280394826514710, 3, 0, 0, 0⟩
theorem s5_1083_edges : next config 5 s5_1083 = [s6_902] := by decide
theorem s5_1083_safe : Safe 8 5 s5_1083 := by
  apply safe_succ 7 5 s5_1083 [s6_902] (by decide) s5_1083_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_902_safe
def s5_1084 : State := ⟨[17,29,96,145], 44601830679428246449697432630985826867806486, 3, 0, 1, 0⟩
theorem s5_1084_edges : next config 5 s5_1084 = [s6_546, s6_906] := by decide
theorem s5_1084_safe : Safe 8 5 s5_1084 := by
  apply safe_succ 7 5 s5_1084 [s6_546, s6_906] (by decide) s5_1084_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_546_safe
  · subst z; exact s6_906_safe
def s5_1085 : State := ⟨[17,29,104,128], 340282387282576229647756113051107131670, 3, 0, 0, 0⟩
theorem s5_1085_edges : next config 5 s5_1085 = [s6_906] := by decide
theorem s5_1085_safe : Safe 8 5 s5_1085 := by
  apply safe_succ 7 5 s5_1085 [s6_906] (by decide) s5_1085_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_906_safe
def s5_1086 : State := ⟨[17,53,64,128], 340282366920938463481830358709029765406, 3, 1, 0, 0⟩
theorem s5_1086_edges : next config 5 s5_1086 = [s6_909, s6_907] := by decide
theorem s5_1086_safe : Safe 8 5 s5_1086 := by
  apply safe_succ 7 5 s5_1086 [s6_909, s6_907] (by decide) s5_1086_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_909_safe
  · subst z; exact s6_907_safe
def s5_1087 : State := ⟨[17,53,96,145], 44601830679428246449697432639993025585676566, 3, 0, 1, 0⟩
theorem s5_1087_edges : next config 5 s5_1087 = [s6_547, s6_910] := by decide
theorem s5_1087_safe : Safe 8 5 s5_1087 := by
  apply safe_succ 7 5 s5_1087 [s6_547, s6_910] (by decide) s5_1087_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_547_safe
  · subst z; exact s6_910_safe
def s5_1088 : State := ⟨[17,53,104,128], 340282387282576229647765120249825001750, 3, 0, 0, 0⟩
theorem s5_1088_edges : next config 5 s5_1088 = [s6_910] := by decide
theorem s5_1088_safe : Safe 8 5 s5_1088 := by
  apply safe_succ 7 5 s5_1088 [s6_910] (by decide) s5_1088_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_910_safe
def s5_1089 : State := ⟨[17,68,64,145], 44601830679428167221535213514553412139811094, 3, 2, 1, 0⟩
theorem s5_1089_edges : next config 5 s5_1089 = [s6_548, s6_911] := by decide
theorem s5_1089_safe : Safe 8 5 s5_1089 := by
  apply safe_succ 7 5 s5_1089 [s6_548, s6_911] (by decide) s5_1089_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_548_safe
  · subst z; exact s6_911_safe
def s5_1090 : State := ⟨[17,68,96,128], 340282367000166626291233594282671800598, 3, 2, 0, 0⟩
theorem s5_1090_edges : next config 5 s5_1090 = [s6_912, s6_911] := by decide
theorem s5_1090_safe : Safe 8 5 s5_1090 := by
  apply safe_succ 7 5 s5_1090 [s6_912, s6_911] (by decide) s5_1090_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_912_safe
  · subst z; exact s6_911_safe
def s5_1091 : State := ⟨[17,68,104,145], 44601830679448528859301379449314952932950294, 3, 0, 1, 0⟩
theorem s5_1091_edges : next config 5 s5_1091 = [s6_549] := by decide
theorem s5_1091_safe : Safe 8 5 s5_1091 := by
  apply safe_succ 7 5 s5_1091 [s6_549] (by decide) s5_1091_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_549_safe
def s5_1092 : State := ⟨[17,86,67,128], 340282366921015834918744128514051735830, 3, 0, 0, 0⟩
theorem s5_1092_edges : next config 5 s5_1092 = [s6_916] := by decide
theorem s5_1092_safe : Safe 8 5 s5_1092 := by
  apply safe_succ 7 5 s5_1092 [s6_916] (by decide) s5_1092_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_916_safe
def s5_1093 : State := ⟨[17,86,67,128], 340282366921015834955637616661470839062, 3, 0, 0, 0⟩
theorem s5_1093_edges : next config 5 s5_1093 = [s6_917] := by decide
theorem s5_1093_safe : Safe 8 5 s5_1093 := by
  apply safe_succ 7 5 s5_1093 [s6_917] (by decide) s5_1093_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_917_safe
def s5_1094 : State := ⟨[17,86,67,128], 340282366921020670658916075178167566614, 3, 0, 0, 0⟩
theorem s5_1094_edges : next config 5 s5_1094 = [s6_852, s6_918] := by decide
theorem s5_1094_safe : Safe 8 5 s5_1094 := by
  apply safe_succ 7 5 s5_1094 [s6_852, s6_918] (by decide) s5_1094_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_852_safe
  · subst z; exact s6_918_safe
def s5_1095 : State := ⟨[17,86,67,128], 340282366921021879510948713512504066326, 3, 0, 0, 0⟩
theorem s5_1095_edges : next config 5 s5_1095 = [s6_853, s6_919] := by decide
theorem s5_1095_safe : Safe 8 5 s5_1095 := by
  apply safe_succ 7 5 s5_1095 [s6_853, s6_919] (by decide) s5_1095_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_853_safe
  · subst z; exact s6_919_safe
def s5_1096 : State := ⟨[17,86,82,145], 44601830679428167303741947887419311503114518, 3, 0, 1, 0⟩
theorem s5_1096_edges : next config 5 s5_1096 = [s6_552, s6_766, s6_918] := by decide
theorem s5_1096_safe : Safe 8 5 s5_1096 := by
  apply safe_succ 7 5 s5_1096 [s6_552, s6_766, s6_918] (by decide) s5_1096_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_552_safe
  · subst z; exact s6_766_safe
  · subst z; exact s6_918_safe
def s5_1097 : State := ⟨[17,86,82,145], 44601830679428167304950799920057645839614230, 3, 0, 1, 0⟩
theorem s5_1097_edges : next config 5 s5_1097 = [s6_553, s6_767, s6_919] := by decide
theorem s5_1097_safe : Safe 8 5 s5_1097 := by
  apply safe_succ 7 5 s5_1097 [s6_553, s6_767, s6_919] (by decide) s5_1097_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_553_safe
  · subst z; exact s6_767_safe
  · subst z; exact s6_919_safe
def s5_1098 : State := ⟨[17,100,96,128], 340282368267817226224315090600020082974, 3, 1, 0, 0⟩
theorem s5_1098_edges : next config 5 s5_1098 = [s6_779, s6_925, s6_922] := by decide
theorem s5_1098_safe : Safe 8 5 s5_1098 := by
  apply safe_succ 7 5 s5_1098 [s6_779, s6_925, s6_922] (by decide) s5_1098_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_779_safe
  · subst z; exact s6_925_safe
  · subst z; exact s6_922_safe
def s5_1099 : State := ⟨[17,100,96,128], 340282368267817226224315090600022180118, 3, 2, 0, 0⟩
theorem s5_1099_edges : next config 5 s5_1099 = [s6_926, s6_923] := by decide
theorem s5_1099_safe : Safe 8 5 s5_1099 := by
  apply safe_succ 7 5 s5_1099 [s6_926, s6_923] (by decide) s5_1099_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_926_safe
  · subst z; exact s6_923_safe
def s5_1100 : State := ⟨[17,100,96,128], 340282368267817226261208578747439186198, 3, 1, 0, 0⟩
theorem s5_1100_edges : next config 5 s5_1100 = [s6_780, s6_927, s6_924] := by decide
theorem s5_1100_safe : Safe 8 5 s5_1100 := by
  apply safe_succ 7 5 s5_1100 [s6_780, s6_927, s6_924] (by decide) s5_1100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_780_safe
  · subst z; exact s6_927_safe
  · subst z; exact s6_924_safe
def s5_1101 : State := ⟨[17,100,104,145], 44601830679449796509901312530811270283329814, 3, 0, 1, 0⟩
theorem s5_1101_edges : next config 5 s5_1101 = [s6_570] := by decide
theorem s5_1101_safe : Safe 8 5 s5_1101 := by
  apply safe_succ 7 5 s5_1101 [s6_570] (by decide) s5_1101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_570_safe
def s5_1102 : State := ⟨[17,108,104,145], 44601830679773047412959511028192929600700694, 3, 0, 1, 0⟩
theorem s5_1102_edges : next config 5 s5_1102 = [s6_595, s6_795] := by decide
theorem s5_1102_safe : Safe 8 5 s5_1102 := by
  apply safe_succ 7 5 s5_1102 [s6_595, s6_795] (by decide) s5_1102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_595_safe
  · subst z; exact s6_795_safe
def s5_1103 : State := ⟨[17,117,96,145], 44601830845581745922811916743961708865978646, 3, 0, 1, 0⟩
theorem s5_1103_edges : next config 5 s5_1103 = [s6_614, s6_933] := by decide
theorem s5_1103_safe : Safe 8 5 s5_1103 := by
  apply safe_succ 7 5 s5_1103 [s6_614, s6_933] (by decide) s5_1103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_614_safe
  · subst z; exact s6_933_safe
def s5_1104 : State := ⟨[17,117,104,128], 340448540782049344131869088933105303830, 3, 0, 0, 0⟩
theorem s5_1104_edges : next config 5 s5_1104 = [s6_933] := by decide
theorem s5_1104_safe : Safe 8 5 s5_1104 := by
  apply safe_succ 7 5 s5_1104 [s6_933] (by decide) s5_1104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_933_safe
def s5_1105 : State := ⟨[17,125,104,128], 382817683147693537580677938979541287190, 3, 0, 0, 0⟩
theorem s5_1105_edges : next config 5 s5_1105 = [s6_934] := by decide
theorem s5_1105_safe : Safe 8 5 s5_1105 := by
  apply safe_succ 7 5 s5_1105 [s6_934] (by decide) s5_1105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_934_safe
def s5_1106 : State := ⟨[21,4,64,145], 44601830679428167221534918366648232786985246, 1, 1, 1, 0⟩
theorem s5_1106_edges : next config 5 s5_1106 = [s6_987, s6_1222, s6_958, s6_944] := by decide
theorem s5_1106_safe : Safe 8 5 s5_1106 := by
  apply safe_succ 7 5 s5_1106 [s6_987, s6_1222, s6_958, s6_944] (by decide) s5_1106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_987_safe
  · subst z; exact s6_1222_safe
  · subst z; exact s6_958_safe
  · subst z; exact s6_944_safe
def s5_1107 : State := ⟨[21,4,64,145], 44601830679428167221534918366648232786985750, 1, 1, 1, 0⟩
theorem s5_1107_edges : next config 5 s5_1107 = [s6_945] := by decide
theorem s5_1107_safe : Safe 8 5 s5_1107 := by
  apply safe_succ 7 5 s5_1107 [s6_945] (by decide) s5_1107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_945_safe
def s5_1108 : State := ⟨[21,4,64,145], 44601830679428167221534918366648232786989334, 3, 2, 1, 0⟩
theorem s5_1108_edges : next config 5 s5_1108 = [s6_956, s6_936, s6_940, s6_946] := by decide
theorem s5_1108_safe : Safe 8 5 s5_1108 := by
  apply safe_succ 7 5 s5_1108 [s6_956, s6_936, s6_940, s6_946] (by decide) s5_1108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_956_safe
  · subst z; exact s6_936_safe
  · subst z; exact s6_940_safe
  · subst z; exact s6_946_safe
def s5_1109 : State := ⟨[21,4,64,145], 44601830679428167221534918366648241376919830, 1, 1, 1, 0⟩
theorem s5_1109_edges : next config 5 s5_1109 = [s6_988, s6_959, s6_947] := by decide
theorem s5_1109_safe : Safe 8 5 s5_1109 := by
  apply safe_succ 7 5 s5_1109 [s6_988, s6_959, s6_947] (by decide) s5_1109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_988_safe
  · subst z; exact s6_959_safe
  · subst z; exact s6_947_safe
def s5_1110 : State := ⟨[21,4,64,145], 44601830679428167221534955260136380206088470, 1, 1, 1, 0⟩
theorem s5_1110_edges : next config 5 s5_1110 = [s6_989, s6_960, s6_948] := by decide
theorem s5_1110_safe : Safe 8 5 s5_1110 := by
  apply safe_succ 7 5 s5_1110 [s6_989, s6_960, s6_948] (by decide) s5_1110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_989_safe
  · subst z; exact s6_960_safe
  · subst z; exact s6_948_safe
def s5_1111 : State := ⟨[21,4,64,145], 44601830679428167221535213514553412139811094, 3, 2, 1, 0⟩
theorem s5_1111_edges : next config 5 s5_1111 = [s6_949] := by decide
theorem s5_1111_safe : Safe 8 5 s5_1111 := by
  apply safe_succ 7 5 s5_1111 [s6_949] (by decide) s5_1111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_949_safe
def s5_1112 : State := ⟨[21,4,67,145], 44601830679428167221535102834088969882501398, 1, 0, 1, 0⟩
theorem s5_1112_edges : next config 5 s5_1112 = [s6_1310, s6_990, s6_961] := by decide
theorem s5_1112_safe : Safe 8 5 s5_1112 := by
  apply safe_succ 7 5 s5_1112 [s6_1310, s6_990, s6_961] (by decide) s5_1112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1310_safe
  · subst z; exact s6_990_safe
  · subst z; exact s6_961_safe
def s5_1113 : State := ⟨[21,4,67,145], 44601830679428167221535139727577117301604630, 1, 0, 1, 0⟩
theorem s5_1113_edges : next config 5 s5_1113 = [s6_1311, s6_991, s6_962] := by decide
theorem s5_1113_safe : Safe 8 5 s5_1113 := by
  apply safe_succ 7 5 s5_1113 [s6_1311, s6_991, s6_962] (by decide) s5_1113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1311_safe
  · subst z; exact s6_991_safe
  · subst z; exact s6_962_safe
def s5_1114 : State := ⟨[21,4,82,145], 44601830679428167226370695432083044324016406, 1, 0, 1, 0⟩
theorem s5_1114_edges : next config 5 s5_1114 = [s6_971, s6_963, s6_942] := by decide
theorem s5_1114_safe : Safe 8 5 s5_1114 := by
  apply safe_succ 7 5 s5_1114 [s6_971, s6_963, s6_942] (by decide) s5_1114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_971_safe
  · subst z; exact s6_963_safe
  · subst z; exact s6_942_safe
def s5_1115 : State := ⟨[21,4,82,145], 44601830679428167227579547464721378660516118, 1, 0, 1, 0⟩
theorem s5_1115_edges : next config 5 s5_1115 = [s6_972, s6_964, s6_943] := by decide
theorem s5_1115_safe : Safe 8 5 s5_1115 := by
  apply safe_succ 7 5 s5_1115 [s6_972, s6_964, s6_943] (by decide) s5_1115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_972_safe
  · subst z; exact s6_964_safe
  · subst z; exact s6_943_safe
def s5_1116 : State := ⟨[21,4,97,145], 44601830679428404906022461159661013418836246, 1, 0, 1, 0⟩
theorem s5_1116_edges : next config 5 s5_1116 = [s6_965] := by decide
theorem s5_1116_safe : Safe 8 5 s5_1116 := by
  apply safe_succ 7 5 s5_1116 [s6_965] (by decide) s5_1116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_965_safe
def s5_1117 : State := ⟨[21,4,100,145], 44601830679429514100297660860387323034140950, 1, 0, 1, 0⟩
theorem s5_1117_edges : next config 5 s5_1117 = [] := by decide
theorem s5_1117_safe : Safe 8 5 s5_1117 := by
  apply safe_succ 7 5 s5_1117 [] (by decide) s5_1117_edges
  simp
def s5_1118 : State := ⟨[21,4,104,145], 44601830679448528859301084301409773582221590, 1, 0, 1, 0⟩
theorem s5_1118_edges : next config 5 s5_1118 = [s6_1393, s6_992, s6_1223, s6_974, s6_966, s6_955, s6_952, s6_957, s6_953] := by decide
theorem s5_1118_safe : Safe 8 5 s5_1118 := by
  apply safe_succ 7 5 s5_1118 [s6_1393, s6_992, s6_1223, s6_974, s6_966, s6_955, s6_952, s6_957, s6_953] (by decide) s5_1118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1393_safe
  · subst z; exact s6_992_safe
  · subst z; exact s6_1223_safe
  · subst z; exact s6_974_safe
  · subst z; exact s6_966_safe
  · subst z; exact s6_955_safe
  · subst z; exact s6_952_safe
  · subst z; exact s6_957_safe
  · subst z; exact s6_953_safe
def s5_1119 : State := ⟨[21,4,112,145], 44601830684620543308232260259516322660155670, 1, 0, 1, 0⟩
theorem s5_1119_edges : next config 5 s5_1119 = [s6_967] := by decide
theorem s5_1119_safe : Safe 8 5 s5_1119 := by
  apply safe_succ 7 5 s5_1119 [s6_967] (by decide) s5_1119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_967_safe
def s5_1120 : State := ⟨[21,4,113,145], 44601830689812840166767087888046818989375766, 1, 0, 1, 0⟩
theorem s5_1120_edges : next config 5 s5_1120 = [s6_968] := by decide
theorem s5_1120_safe : Safe 8 5 s5_1120 := by
  apply safe_succ 7 5 s5_1120 [s6_968] (by decide) s5_1120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_968_safe
def s5_1121 : State := ⟨[21,4,117,145], 44601830845581745922811916743961708865978646, 1, 0, 1, 0⟩
theorem s5_1121_edges : next config 5 s5_1121 = [] := by decide
theorem s5_1121_safe : Safe 8 5 s5_1121 := by
  apply safe_succ 7 5 s5_1121 [] (by decide) s5_1121_edges
  simp
def s5_1122 : State := ⟨[21,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175126, 1, 0, 1, 0⟩
theorem s5_1122_edges : next config 5 s5_1122 = [s6_969] := by decide
theorem s5_1122_safe : Safe 8 5 s5_1122 := by
  apply safe_succ 7 5 s5_1122 [s6_969] (by decide) s5_1122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_969_safe
def s5_1123 : State := ⟨[21,12,65,145], 44601830679428167221534955260136380206092566, 3, 0, 1, 0⟩
theorem s5_1123_edges : next config 5 s5_1123 = [s6_935, s6_961] := by decide
theorem s5_1123_safe : Safe 8 5 s5_1123 := by
  apply safe_succ 7 5 s5_1123 [s6_935, s6_961] (by decide) s5_1123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_935_safe
  · subst z; exact s6_961_safe
def s5_1124 : State := ⟨[21,12,66,145], 44601830679428167221534992153624527625195798, 3, 0, 1, 0⟩
theorem s5_1124_edges : next config 5 s5_1124 = [s6_936, s6_963] := by decide
theorem s5_1124_safe : Safe 8 5 s5_1124 := by
  apply safe_succ 7 5 s5_1124 [s6_936, s6_963] (by decide) s5_1124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_936_safe
  · subst z; exact s6_963_safe
def s5_1125 : State := ⟨[21,12,80,145], 44601830679428167222743844186262861961695510, 3, 0, 1, 0⟩
theorem s5_1125_edges : next config 5 s5_1125 = [s6_940, s6_964] := by decide
theorem s5_1125_safe : Safe 8 5 s5_1125 := by
  apply safe_succ 7 5 s5_1125 [s6_940, s6_964] (by decide) s5_1125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_940_safe
  · subst z; exact s6_964_safe
def s5_1126 : State := ⟨[21,12,81,145], 44601830679428167223952770005877491136401686, 3, 0, 1, 0⟩
theorem s5_1126_edges : next config 5 s5_1126 = [s6_941] := by decide
theorem s5_1126_safe : Safe 8 5 s5_1126 := by
  apply safe_succ 7 5 s5_1126 [s6_941] (by decide) s5_1126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_941_safe
def s5_1127 : State := ⟨[21,12,96,145], 44601830679428246449697432630985826330939670, 3, 0, 1, 0⟩
theorem s5_1127_edges : next config 5 s5_1127 = [s6_946, s6_969, s6_966, s6_967] := by decide
theorem s5_1127_safe : Safe 8 5 s5_1127 := by
  apply safe_succ 7 5 s5_1127 [s6_946, s6_969, s6_966, s6_967] (by decide) s5_1127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_946_safe
  · subst z; exact s6_969_safe
  · subst z; exact s6_966_safe
  · subst z; exact s6_967_safe
def s5_1128 : State := ⟨[21,12,209,145], 822752278660603021122086421958103419712902851183438164461293846, 3, 0, 1, 0⟩
theorem s5_1128_edges : next config 5 s5_1128 = [s6_956] := by decide
theorem s5_1128_safe : Safe 8 5 s5_1128 := by
  apply safe_succ 7 5 s5_1128 [s6_956] (by decide) s5_1128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_956_safe
def s5_1129 : State := ⟨[21,68,96,145], 44601830679428246449697727778891005683761430, 3, 0, 1, 0⟩
theorem s5_1129_edges : next config 5 s5_1129 = [s6_970] := by decide
theorem s5_1129_safe : Safe 8 5 s5_1129 := by
  apply safe_succ 7 5 s5_1129 [s6_970] (by decide) s5_1129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_970_safe
def s5_1130 : State := ⟨[21,100,96,145], 44601830679429514100297660860387323034140950, 3, 0, 1, 0⟩
theorem s5_1130_edges : next config 5 s5_1130 = [s6_951, s6_973] := by decide
theorem s5_1130_safe : Safe 8 5 s5_1130 := by
  apply safe_succ 7 5 s5_1130 [s6_951, s6_973] (by decide) s5_1130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_951_safe
  · subst z; exact s6_973_safe
def s5_1131 : State := ⟨[25,4,64,145], 44601830679428167221534918366648232818442526, 1, 1, 1, 0⟩
theorem s5_1131_edges : next config 5 s5_1131 = [s6_979] := by decide
theorem s5_1131_safe : Safe 8 5 s5_1131 := by
  apply safe_succ 7 5 s5_1131 [s6_979] (by decide) s5_1131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_979_safe
def s5_1132 : State := ⟨[25,4,64,145], 44601830679428167221534918366648232820539670, 3, 2, 1, 0⟩
theorem s5_1132_edges : next config 5 s5_1132 = [s6_977, s6_980] := by decide
theorem s5_1132_safe : Safe 8 5 s5_1132 := by
  apply safe_succ 7 5 s5_1132 [s6_977, s6_980] (by decide) s5_1132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_977_safe
  · subst z; exact s6_980_safe
def s5_1133 : State := ⟨[25,4,64,145], 44601830679428167221534955260136380237545750, 1, 1, 1, 0⟩
theorem s5_1133_edges : next config 5 s5_1133 = [s6_981] := by decide
theorem s5_1133_safe : Safe 8 5 s5_1133 := by
  apply safe_succ 7 5 s5_1133 [s6_981] (by decide) s5_1133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_981_safe
def s5_1134 : State := ⟨[25,4,67,145], 44601830679428167221535102834088969913958678, 1, 0, 1, 0⟩
theorem s5_1134_edges : next config 5 s5_1134 = [] := by decide
theorem s5_1134_safe : Safe 8 5 s5_1134 := by
  apply safe_succ 7 5 s5_1134 [] (by decide) s5_1134_edges
  simp
def s5_1135 : State := ⟨[25,4,67,145], 44601830679428167221535139727577117333061910, 1, 0, 1, 0⟩
theorem s5_1135_edges : next config 5 s5_1135 = [] := by decide
theorem s5_1135_safe : Safe 8 5 s5_1135 := by
  apply safe_succ 7 5 s5_1135 [] (by decide) s5_1135_edges
  simp
def s5_1136 : State := ⟨[25,4,104,145], 44601830679448528859301084301409773613678870, 1, 0, 1, 0⟩
theorem s5_1136_edges : next config 5 s5_1136 = [] := by decide
theorem s5_1136_safe : Safe 8 5 s5_1136 := by
  apply safe_succ 7 5 s5_1136 [] (by decide) s5_1136_edges
  simp
def s5_1137 : State := ⟨[25,21,65,145], 44601830679428167221534955260136380239642902, 3, 0, 1, 0⟩
theorem s5_1137_edges : next config 5 s5_1137 = [s6_984] := by decide
theorem s5_1137_safe : Safe 8 5 s5_1137 := by
  apply safe_succ 7 5 s5_1137 [s6_984] (by decide) s5_1137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_984_safe
def s5_1138 : State := ⟨[25,21,66,145], 44601830679428167221534992153624527658746134, 3, 0, 1, 0⟩
theorem s5_1138_edges : next config 5 s5_1138 = [] := by decide
theorem s5_1138_safe : Safe 8 5 s5_1138 := by
  apply safe_succ 7 5 s5_1138 [] (by decide) s5_1138_edges
  simp
def s5_1139 : State := ⟨[25,21,96,145], 44601830679428246449697432630985826364490006, 3, 0, 1, 0⟩
theorem s5_1139_edges : next config 5 s5_1139 = [s6_986] := by decide
theorem s5_1139_safe : Safe 8 5 s5_1139 := by
  apply safe_succ 7 5 s5_1139 [s6_986] (by decide) s5_1139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_986_safe
def s5_1140 : State := ⟨[29,4,65,145], 44601830679428167221534955260136380742959382, 1, 0, 1, 0⟩
theorem s5_1140_edges : next config 5 s5_1140 = [s6_990] := by decide
theorem s5_1140_safe : Safe 8 5 s5_1140 := by
  apply safe_succ 7 5 s5_1140 [s6_990] (by decide) s5_1140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_990_safe
def s5_1141 : State := ⟨[29,4,66,145], 44601830679428167221534992153624528162062614, 1, 0, 1, 0⟩
theorem s5_1141_edges : next config 5 s5_1141 = [] := by decide
theorem s5_1141_safe : Safe 8 5 s5_1141 := by
  apply safe_succ 7 5 s5_1141 [] (by decide) s5_1141_edges
  simp
def s5_1142 : State := ⟨[29,4,96,145], 44601830679428246449697432630985826867806486, 1, 0, 1, 0⟩
theorem s5_1142_edges : next config 5 s5_1142 = [s6_992] := by decide
theorem s5_1142_safe : Safe 8 5 s5_1142 := by
  apply safe_succ 7 5 s5_1142 [s6_992] (by decide) s5_1142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_992_safe
def s5_1143 : State := ⟨[33,4,64,145], 44602511244162009098461845115863104911118614, 3, 2, 1, 0⟩
theorem s5_1143_edges : next config 5 s5_1143 = [s6_1022, s6_1, s6_995] := by decide
theorem s5_1143_safe : Safe 8 5 s5_1143 := by
  apply safe_succ 7 5 s5_1143 [s6_1022, s6_1, s6_995] (by decide) s5_1143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1022_safe
  · subst z; exact s6_1_safe
  · subst z; exact s6_995_safe
def s5_1144 : State := ⟨[33,4,64,145], 66902575877958790363070636639296602880676118, 3, 2, 1, 0⟩
theorem s5_1144_edges : next config 5 s5_1144 = [s6_1024, s6_4, s6_996] := by decide
theorem s5_1144_safe : Safe 8 5 s5_1144 := by
  apply safe_succ 7 5 s5_1144 [s6_1024, s6_4, s6_996] (by decide) s5_1144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1024_safe
  · subst z; exact s6_4_safe
  · subst z; exact s6_996_safe
def s5_1145 : State := ⟨[33,4,64,163], 11692013100348635180234170979065583938492895924502, 3, 2, 1, 0⟩
theorem s5_1145_edges : next config 5 s5_1145 = [s6_18, s6_997] := by decide
theorem s5_1145_safe : Safe 8 5 s5_1145 := by
  apply safe_succ 7 5 s5_1145 [s6_18, s6_997] (by decide) s5_1145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_18_safe
  · subst z; exact s6_997_safe
def s5_1146 : State := ⟨[33,4,64,163], 14615016373649311548957786790644651548077688164630, 3, 2, 1, 0⟩
theorem s5_1146_edges : next config 5 s5_1146 = [s6_21, s6_998] := by decide
theorem s5_1146_safe : Safe 8 5 s5_1146 := by
  apply safe_succ 7 5 s5_1146 [s6_21, s6_998] (by decide) s5_1146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_21_safe
  · subst z; exact s6_998_safe
def s5_1147 : State := ⟨[33,4,96,129], 1020847100842043552922834903975443108118, 3, 2, 1, 0⟩
theorem s5_1147_edges : next config 5 s5_1147 = [s6_1053, s6_83, s6_999, s6_995] := by decide
theorem s5_1147_safe : Safe 8 5 s5_1147 := by
  apply safe_succ 7 5 s5_1147 [s6_1053, s6_83, s6_999, s6_995] (by decide) s5_1147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1053_safe
  · subst z; exact s6_83_safe
  · subst z; exact s6_999_safe
  · subst z; exact s6_995_safe
def s5_1148 : State := ⟨[33,4,96,130], 1701411834683920479849584118838979531030, 3, 2, 1, 0⟩
theorem s5_1148_edges : next config 5 s5_1148 = [s6_1415, s6_1055, s6_89, s6_1000, s6_997] := by decide
theorem s5_1148_safe : Safe 8 5 s5_1148 := by
  apply safe_succ 7 5 s5_1148 [s6_1415, s6_1055, s6_89, s6_1000, s6_997] (by decide) s5_1148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1415_safe
  · subst z; exact s6_1055_safe
  · subst z; exact s6_89_safe
  · subst z; exact s6_1000_safe
  · subst z; exact s6_997_safe
def s5_1149 : State := ⟨[33,4,96,132], 5784800237735182041410079408020198068502, 3, 2, 1, 0⟩
theorem s5_1149_edges : next config 5 s5_1149 = [s6_1058, s6_99, s6_1001] := by decide
theorem s5_1149_safe : Safe 8 5 s5_1149 := by
  apply safe_succ 7 5 s5_1149 [s6_1058, s6_99, s6_1001] (by decide) s5_1149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1058_safe
  · subst z; exact s6_99_safe
  · subst z; exact s6_1001_safe
def s5_1150 : State := ⟨[33,4,96,136], 87452568298760413272619985191644568817942, 3, 2, 1, 0⟩
theorem s5_1150_edges : next config 5 s5_1150 = [s6_1060, s6_105, s6_1002] := by decide
theorem s5_1150_safe : Safe 8 5 s5_1150 := by
  apply safe_succ 7 5 s5_1150 [s6_1060, s6_105, s6_1002] (by decide) s5_1150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1060_safe
  · subst z; exact s6_105_safe
  · subst z; exact s6_1002_safe
def s5_1151 : State := ⟨[33,4,96,136], 1481249143206924359618602377232167162937622, 3, 2, 1, 0⟩
theorem s5_1151_edges : next config 5 s5_1151 = [s6_1062, s6_111, s6_1003] := by decide
theorem s5_1151_safe : Safe 8 5 s5_1151 := by
  apply safe_succ 7 5 s5_1151 [s6_1062, s6_111, s6_1003] (by decide) s5_1151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1062_safe
  · subst z; exact s6_111_safe
  · subst z; exact s6_1003_safe
def s5_1152 : State := ⟨[33,4,96,140], 1394136857275164112971978477729634500808982, 3, 2, 1, 0⟩
theorem s5_1152_edges : next config 5 s5_1152 = [s6_1064, s6_115, s6_1004] := by decide
theorem s5_1152_safe : Safe 8 5 s5_1152 := by
  apply safe_succ 7 5 s5_1152 [s6_1064, s6_115, s6_1004] (by decide) s5_1152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1064_safe
  · subst z; exact s6_115_safe
  · subst z; exact s6_1004_safe
def s5_1153 : State := ⟨[33,4,96,144], 22301085480897623308161714358337473412665622, 3, 2, 1, 0⟩
theorem s5_1153_edges : next config 5 s5_1153 = [s6_1066, s6_119, s6_1005] := by decide
theorem s5_1153_safe : Safe 8 5 s5_1153 := by
  apply safe_succ 7 5 s5_1153 [s6_1066, s6_119, s6_1005] (by decide) s5_1153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1066_safe
  · subst z; exact s6_119_safe
  · subst z; exact s6_1005_safe
def s5_1154 : State := ⟨[33,4,96,145], 44601830679428246449697432630985834918773014, 1, 1, 1, 0⟩
theorem s5_1154_edges : next config 5 s5_1154 = [s6_1068, s6_1014, s6_1006] := by decide
theorem s5_1154_safe : Safe 8 5 s5_1154 := by
  apply safe_succ 7 5 s5_1154 [s6_1068, s6_1014, s6_1006] (by decide) s5_1154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1068_safe
  · subst z; exact s6_1014_safe
  · subst z; exact s6_1006_safe
def s5_1155 : State := ⟨[33,4,96,160], 1461501637671185285203851458712368708767839228182, 3, 2, 1, 0⟩
theorem s5_1155_edges : next config 5 s5_1155 = [s6_1070, s6_131, s6_1007] := by decide
theorem s5_1155_safe : Safe 8 5 s5_1155 := by
  apply safe_succ 7 5 s5_1155 [s6_1070, s6_131, s6_1007] (by decide) s5_1155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1070_safe
  · subst z; exact s6_131_safe
  · subst z; exact s6_1007_safe
def s5_1156 : State := ⟨[33,4,96,161], 2923003275002088203407536291428651728423771771158, 3, 2, 1, 0⟩
theorem s5_1156_edges : next config 5 s5_1156 = [s6_1071, s6_137, s6_1008, s6_998] := by decide
theorem s5_1156_safe : Safe 8 5 s5_1156 := by
  apply safe_succ 7 5 s5_1156 [s6_1071, s6_137, s6_1008, s6_998] (by decide) s5_1156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1071_safe
  · subst z; exact s6_137_safe
  · subst z; exact s6_1008_safe
  · subst z; exact s6_998_safe
def s5_1157 : State := ⟨[33,4,96,171], 3004847366354037811661459936544527472531436287885590, 1, 0, 1, 0⟩
theorem s5_1157_edges : next config 5 s5_1157 = [s6_150, s6_1009] := by decide
theorem s5_1157_safe : Safe 8 5 s5_1157 := by
  apply safe_succ 7 5 s5_1157 [s6_150, s6_1009] (by decide) s5_1157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_150_safe
  · subst z; exact s6_1009_safe
def s5_1158 : State := ⟨[33,4,96,171], 3007770369627338488030183552356106540141021080125718, 1, 0, 1, 0⟩
theorem s5_1158_edges : next config 5 s5_1158 = [s6_153, s6_1010] := by decide
theorem s5_1158_safe : Safe 8 5 s5_1158 := by
  apply safe_succ 7 5 s5_1158 [s6_153, s6_1010] (by decide) s5_1158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_153_safe
  · subst z; exact s6_1010_safe
def s5_1159 : State := ⟨[33,4,96,192], 6277101735386680764176071790207833042098441133575941198102, 3, 2, 1, 0⟩
theorem s5_1159_edges : next config 5 s5_1159 = [s6_1075, s6_155, s6_1011] := by decide
theorem s5_1159_safe : Safe 8 5 s5_1159 := by
  apply safe_succ 7 5 s5_1159 [s6_1075, s6_155, s6_1011] (by decide) s5_1159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1075_safe
  · subst z; exact s6_155_safe
  · subst z; exact s6_1011_safe
def s5_1160 : State := ⟨[33,4,96,224], 26959946667150639794667015087359913040637311048536658170215516934422, 3, 2, 1, 0⟩
theorem s5_1160_edges : next config 5 s5_1160 = [s6_1077, s6_181, s6_1012] := by decide
theorem s5_1160_safe : Safe 8 5 s5_1160 := by
  apply safe_succ 7 5 s5_1160 [s6_1077, s6_181, s6_1012] (by decide) s5_1160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1077_safe
  · subst z; exact s6_181_safe
  · subst z; exact s6_1012_safe
def s5_1161 : State := ⟨[33,4,104,128], 340282387282576229647756113059157971222, 3, 2, 0, 0⟩
theorem s5_1161_edges : next config 5 s5_1161 = [s6_1079, s6_201, s6_1008, s6_1001, s6_1013, s6_1000, s6_1002, s6_1005, s6_1007] := by decide
theorem s5_1161_safe : Safe 8 5 s5_1161 := by
  apply safe_succ 7 5 s5_1161 [s6_1079, s6_201, s6_1008, s6_1001, s6_1013, s6_1000, s6_1002, s6_1005, s6_1007] (by decide) s5_1161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1079_safe
  · subst z; exact s6_201_safe
  · subst z; exact s6_1008_safe
  · subst z; exact s6_1001_safe
  · subst z; exact s6_1013_safe
  · subst z; exact s6_1000_safe
  · subst z; exact s6_1002_safe
  · subst z; exact s6_1005_safe
  · subst z; exact s6_1007_safe
def s5_1162 : State := ⟨[33,4,104,140], 1399581375166181537991044141872490043474198, 1, 0, 1, 0⟩
theorem s5_1162_edges : next config 5 s5_1162 = [s6_1081, s6_215] := by decide
theorem s5_1162_safe : Safe 8 5 s5_1162 := by
  apply safe_succ 7 5 s5_1162 [s6_1081, s6_215] (by decide) s5_1162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1081_safe
  · subst z; exact s6_215_safe
def s5_1163 : State := ⟨[33,4,104,140], 1481249143227206769222254047656114414223638, 1, 0, 1, 0⟩
theorem s5_1163_edges : next config 5 s5_1163 = [s6_1083, s6_219] := by decide
theorem s5_1163_safe : Safe 8 5 s5_1163 := by
  apply safe_succ 7 5 s5_1163 [s6_1083, s6_219] (by decide) s5_1163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1083_safe
  · subst z; exact s6_219_safe
def s5_1164 : State := ⟨[33,4,104,145], 44602511244182370736228011050624645706350870, 1, 0, 1, 0⟩
theorem s5_1164_edges : next config 5 s5_1164 = [s6_1085, s6_225, s6_1015] := by decide
theorem s5_1164_safe : Safe 8 5 s5_1164 := by
  apply safe_succ 7 5 s5_1164 [s6_1085, s6_225, s6_1015] (by decide) s5_1164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1085_safe
  · subst z; exact s6_225_safe
  · subst z; exact s6_1015_safe
def s5_1165 : State := ⟨[33,4,104,145], 66902575877979152000836802574058143675908374, 1, 0, 1, 0⟩
theorem s5_1165_edges : next config 5 s5_1165 = [s6_1087, s6_234, s6_1016] := by decide
theorem s5_1165_safe : Safe 8 5 s5_1165 := by
  apply safe_succ 7 5 s5_1165 [s6_1087, s6_234, s6_1016] (by decide) s5_1165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1087_safe
  · subst z; exact s6_234_safe
  · subst z; exact s6_1016_safe
def s5_1166 : State := ⟨[33,4,104,163], 11692013100348635200595808745231518700033691156758, 1, 0, 1, 0⟩
theorem s5_1166_edges : next config 5 s5_1166 = [s6_274, s6_1017, s6_1009] := by decide
theorem s5_1166_safe : Safe 8 5 s5_1166 := by
  apply safe_succ 7 5 s5_1166 [s6_274, s6_1017, s6_1009] (by decide) s5_1166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_274_safe
  · subst z; exact s6_1017_safe
  · subst z; exact s6_1009_safe
def s5_1167 : State := ⟨[33,4,104,163], 14615016373649311569319424556810586309618483396886, 1, 0, 1, 0⟩
theorem s5_1167_edges : next config 5 s5_1167 = [s6_277, s6_1018, s6_1010] := by decide
theorem s5_1167_safe : Safe 8 5 s5_1167 := by
  apply safe_succ 7 5 s5_1167 [s6_277, s6_1018, s6_1010] (by decide) s5_1167_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_277_safe
  · subst z; exact s6_1018_safe
  · subst z; exact s6_1010_safe
def s5_1168 : State := ⟨[33,12,64,145], 44601830679428167221534918366648241374826774, 3, 1, 1, 0⟩
theorem s5_1168_edges : next config 5 s5_1168 = [s6_1093, s6_993, s6_1014] := by decide
theorem s5_1168_safe : Safe 8 5 s5_1168 := by
  apply safe_succ 7 5 s5_1168 [s6_1093, s6_993, s6_1014] (by decide) s5_1168_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1093_safe
  · subst z; exact s6_993_safe
  · subst z; exact s6_1014_safe
def s5_1169 : State := ⟨[33,12,96,145], 44602511244162088326624359380200698455068950, 3, 0, 1, 0⟩
theorem s5_1169_edges : next config 5 s5_1169 = [s6_1121, s6_432, s6_995, s6_1015] := by decide
theorem s5_1169_safe : Safe 8 5 s5_1169 := by
  apply safe_succ 7 5 s5_1169 [s6_1121, s6_432, s6_995, s6_1015] (by decide) s5_1169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1121_safe
  · subst z; exact s6_432_safe
  · subst z; exact s6_995_safe
  · subst z; exact s6_1015_safe
def s5_1170 : State := ⟨[33,12,96,145], 66902575877958869591233150903634196424626454, 3, 0, 1, 0⟩
theorem s5_1170_edges : next config 5 s5_1170 = [s6_1123, s6_436, s6_996, s6_1016] := by decide
theorem s5_1170_safe : Safe 8 5 s5_1170 := by
  apply safe_succ 7 5 s5_1170 [s6_1123, s6_436, s6_996, s6_1016] (by decide) s5_1170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1123_safe
  · subst z; exact s6_436_safe
  · subst z; exact s6_996_safe
  · subst z; exact s6_1016_safe
def s5_1171 : State := ⟨[33,12,96,163], 11692013100348635180313399141579848276086439874838, 3, 0, 1, 0⟩
theorem s5_1171_edges : next config 5 s5_1171 = [s6_453, s6_997, s6_1017] := by decide
theorem s5_1171_safe : Safe 8 5 s5_1171 := by
  apply safe_succ 7 5 s5_1171 [s6_453, s6_997, s6_1017] (by decide) s5_1171_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_453_safe
  · subst z; exact s6_997_safe
  · subst z; exact s6_1017_safe
def s5_1172 : State := ⟨[33,12,96,163], 14615016373649311549037014953158915885671232114966, 3, 0, 1, 0⟩
theorem s5_1172_edges : next config 5 s5_1172 = [s6_456, s6_998, s6_1018] := by decide
theorem s5_1172_safe : Safe 8 5 s5_1172 := by
  apply safe_succ 7 5 s5_1172 [s6_456, s6_998, s6_1018] (by decide) s5_1172_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_456_safe
  · subst z; exact s6_998_safe
  · subst z; exact s6_1018_safe
def s5_1173 : State := ⟨[33,12,104,129], 1020847121124453156574505327922694394134, 3, 0, 1, 0⟩
theorem s5_1173_edges : next config 5 s5_1173 = [s6_1125, s6_463, s6_999, s6_1015] := by decide
theorem s5_1173_safe : Safe 8 5 s5_1173 := by
  apply safe_succ 7 5 s5_1173 [s6_1125, s6_463, s6_999, s6_1015] (by decide) s5_1173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1125_safe
  · subst z; exact s6_463_safe
  · subst z; exact s6_999_safe
  · subst z; exact s6_1015_safe
def s5_1174 : State := ⟨[33,12,104,130], 1701411854966330083501254542786230817046, 3, 0, 1, 0⟩
theorem s5_1174_edges : next config 5 s5_1174 = [s6_1421, s6_1127, s6_467, s6_1000, s6_1017] := by decide
theorem s5_1174_safe : Safe 8 5 s5_1174 := by
  apply safe_succ 7 5 s5_1174 [s6_1421, s6_1127, s6_467, s6_1000, s6_1017] (by decide) s5_1174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1421_safe
  · subst z; exact s6_1127_safe
  · subst z; exact s6_467_safe
  · subst z; exact s6_1000_safe
  · subst z; exact s6_1017_safe
def s5_1175 : State := ⟨[33,12,104,132], 5784800258017591645061749831967449354518, 3, 0, 1, 0⟩
theorem s5_1175_edges : next config 5 s5_1175 = [s6_1130, s6_473, s6_1001] := by decide
theorem s5_1175_safe : Safe 8 5 s5_1175 := by
  apply safe_succ 7 5 s5_1175 [s6_1130, s6_473, s6_1001] (by decide) s5_1175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1130_safe
  · subst z; exact s6_473_safe
  · subst z; exact s6_1001_safe
def s5_1176 : State := ⟨[33,12,104,136], 87452568319042822876271655615591820103958, 3, 0, 1, 0⟩
theorem s5_1176_edges : next config 5 s5_1176 = [s6_1132, s6_477, s6_1002] := by decide
theorem s5_1176_safe : Safe 8 5 s5_1176 := by
  apply safe_succ 7 5 s5_1176 [s6_1132, s6_477, s6_1002] (by decide) s5_1176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1132_safe
  · subst z; exact s6_477_safe
  · subst z; exact s6_1002_safe
def s5_1177 : State := ⟨[33,12,104,140], 1394136857295446522575630148153581752094998, 3, 0, 1, 0⟩
theorem s5_1177_edges : next config 5 s5_1177 = [s6_1134, s6_481, s6_1004] := by decide
theorem s5_1177_safe : Safe 8 5 s5_1177 := by
  apply safe_succ 7 5 s5_1177 [s6_1134, s6_481, s6_1004] (by decide) s5_1177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1134_safe
  · subst z; exact s6_481_safe
  · subst z; exact s6_1004_safe
def s5_1178 : State := ⟨[33,12,104,144], 22301085480917905717765366028761420663951638, 3, 0, 1, 0⟩
theorem s5_1178_edges : next config 5 s5_1178 = [s6_1136, s6_485, s6_1005] := by decide
theorem s5_1178_safe : Safe 8 5 s5_1178 := by
  apply safe_succ 7 5 s5_1178 [s6_1136, s6_485, s6_1005] (by decide) s5_1178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1136_safe
  · subst z; exact s6_485_safe
  · subst z; exact s6_1005_safe
def s5_1179 : State := ⟨[33,12,104,160], 1461501637671185305486261062364039132715090514198, 3, 0, 1, 0⟩
theorem s5_1179_edges : next config 5 s5_1179 = [s6_1138, s6_490, s6_1007] := by decide
theorem s5_1179_safe : Safe 8 5 s5_1179 := by
  apply safe_succ 7 5 s5_1179 [s6_1138, s6_490, s6_1007] (by decide) s5_1179_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1138_safe
  · subst z; exact s6_490_safe
  · subst z; exact s6_1007_safe
def s5_1180 : State := ⟨[33,12,104,161], 2923003275002088223689945895080322152371023057174, 3, 0, 1, 0⟩
theorem s5_1180_edges : next config 5 s5_1180 = [s6_1139, s6_494, s6_1008, s6_1018] := by decide
theorem s5_1180_safe : Safe 8 5 s5_1180 := by
  apply safe_succ 7 5 s5_1180 [s6_1139, s6_494, s6_1008, s6_1018] (by decide) s5_1180_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1139_safe
  · subst z; exact s6_494_safe
  · subst z; exact s6_1008_safe
  · subst z; exact s6_1018_safe
def s5_1181 : State := ⟨[33,12,104,192], 6277101735386680764176071810490242645750111557523192484118, 3, 0, 1, 0⟩
theorem s5_1181_edges : next config 5 s5_1181 = [s6_1143, s6_504, s6_1011] := by decide
theorem s5_1181_safe : Safe 8 5 s5_1181 := by
  apply safe_succ 7 5 s5_1181 [s6_1143, s6_504, s6_1011] (by decide) s5_1181_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1143_safe
  · subst z; exact s6_504_safe
  · subst z; exact s6_1011_safe
def s5_1182 : State := ⟨[33,12,104,224], 26959946667150639794667015087359913060919720652188328594162768220438, 3, 0, 1, 0⟩
theorem s5_1182_edges : next config 5 s5_1182 = [s6_1145, s6_518, s6_1012] := by decide
theorem s5_1182_safe : Safe 8 5 s5_1182 := by
  apply safe_succ 7 5 s5_1182 [s6_1145, s6_518, s6_1012] (by decide) s5_1182_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1145_safe
  · subst z; exact s6_518_safe
  · subst z; exact s6_1012_safe
def s5_1183 : State := ⟨[33,12,104,232], 6901746346790563787434755862277365734838391548400034311275583381770518, 3, 0, 1, 0⟩
theorem s5_1183_edges : next config 5 s5_1183 = [s6_1147, s6_524, s6_1013] := by decide
theorem s5_1183_safe : Safe 8 5 s5_1183 := by
  apply safe_succ 7 5 s5_1183 [s6_1147, s6_524, s6_1013] (by decide) s5_1183_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1147_safe
  · subst z; exact s6_524_safe
  · subst z; exact s6_1013_safe
def s5_1184 : State := ⟨[33,21,64,145], 44601830679428167221534918366648241376919830, 3, 1, 1, 0⟩
theorem s5_1184_edges : next config 5 s5_1184 = [s6_1149, s6_1020, s6_1019] := by decide
theorem s5_1184_safe : Safe 8 5 s5_1184 := by
  apply safe_succ 7 5 s5_1184 [s6_1149, s6_1020, s6_1019] (by decide) s5_1184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1149_safe
  · subst z; exact s6_1020_safe
  · subst z; exact s6_1019_safe
def s5_1185 : State := ⟨[33,140,104,136], 1481249143227206769222254047656114414223638, 3, 0, 1, 0⟩
theorem s5_1185_edges : next config 5 s5_1185 = [s6_1153, s6_616, s6_1003] := by decide
theorem s5_1185_safe : Safe 8 5 s5_1185 := by
  apply safe_succ 7 5 s5_1185 [s6_1153, s6_616, s6_1003] (by decide) s5_1185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1153_safe
  · subst z; exact s6_616_safe
  · subst z; exact s6_1003_safe
def s5_1186 : State := ⟨[35,4,64,129], 1020847100762815390408570566407668961566, 3, 2, 1, 0⟩
theorem s5_1186_edges : next config 5 s5_1186 = [s6_1052, s6_1021] := by decide
theorem s5_1186_safe : Safe 8 5 s5_1186 := by
  apply safe_succ 7 5 s5_1186 [s6_1052, s6_1021] (by decide) s5_1186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1052_safe
  · subst z; exact s6_1021_safe
def s5_1187 : State := ⟨[35,4,64,129], 1020847100762815390408570566416258896150, 3, 2, 1, 0⟩
theorem s5_1187_edges : next config 5 s5_1187 = [s6_1053, s6_1022] := by decide
theorem s5_1187_safe : Safe 8 5 s5_1187 := by
  apply safe_succ 7 5 s5_1187 [s6_1053, s6_1022] (by decide) s5_1187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1053_safe
  · subst z; exact s6_1022_safe
def s5_1188 : State := ⟨[35,4,64,130], 1701411834604692317335319781271205384478, 3, 2, 1, 0⟩
theorem s5_1188_edges : next config 5 s5_1188 = [s6_1054] := by decide
theorem s5_1188_safe : Safe 8 5 s5_1188 := by
  apply safe_succ 7 5 s5_1188 [s6_1054] (by decide) s5_1188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1054_safe
def s5_1189 : State := ⟨[35,4,64,130], 1701411834604692317335319781279795319062, 3, 2, 1, 0⟩
theorem s5_1189_edges : next config 5 s5_1189 = [s6_1055] := by decide
theorem s5_1189_safe : Safe 8 5 s5_1189 := by
  apply safe_succ 7 5 s5_1189 [s6_1055] (by decide) s5_1189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1055_safe
def s5_1190 : State := ⟨[35,4,64,131], 3062541302288446171188818210998278230302, 3, 2, 1, 0⟩
theorem s5_1190_edges : next config 5 s5_1190 = [s6_1056] := by decide
theorem s5_1190_safe : Safe 8 5 s5_1190 := by
  apply safe_succ 7 5 s5_1190 [s6_1056] (by decide) s5_1190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1056_safe
def s5_1191 : State := ⟨[35,4,64,132], 5784800237655953878895815070452423921950, 3, 2, 1, 0⟩
theorem s5_1191_edges : next config 5 s5_1191 = [s6_1057] := by decide
theorem s5_1191_safe : Safe 8 5 s5_1191 := by
  apply safe_succ 7 5 s5_1191 [s6_1057] (by decide) s5_1191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1057_safe
def s5_1192 : State := ⟨[35,4,64,132], 5784800237655953878895815070461013856534, 3, 2, 1, 0⟩
theorem s5_1192_edges : next config 5 s5_1192 = [s6_1058] := by decide
theorem s5_1192_safe : Safe 8 5 s5_1192 := by
  apply safe_succ 7 5 s5_1192 [s6_1058] (by decide) s5_1192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1058_safe
def s5_1193 : State := ⟨[35,4,64,136], 87452568298681185110105720854076794671390, 3, 2, 1, 0⟩
theorem s5_1193_edges : next config 5 s5_1193 = [s6_1059] := by decide
theorem s5_1193_safe : Safe 8 5 s5_1193 := by
  apply safe_succ 7 5 s5_1193 [s6_1059] (by decide) s5_1193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1059_safe
def s5_1194 : State := ⟨[35,4,64,136], 87452568298681185110105720854085384605974, 3, 2, 1, 0⟩
theorem s5_1194_edges : next config 5 s5_1194 = [s6_1060] := by decide
theorem s5_1194_safe : Safe 8 5 s5_1194 := by
  apply safe_succ 7 5 s5_1194 [s6_1060] (by decide) s5_1194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1060_safe
def s5_1195 : State := ⟨[35,4,64,136], 1481249143206845131456088112894599388791070, 3, 2, 1, 0⟩
theorem s5_1195_edges : next config 5 s5_1195 = [s6_1061] := by decide
theorem s5_1195_safe : Safe 8 5 s5_1195 := by
  apply safe_succ 7 5 s5_1195 [s6_1061] (by decide) s5_1195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1061_safe
def s5_1196 : State := ⟨[35,4,64,136], 1481249143206845131456088112894607978725654, 3, 2, 1, 0⟩
theorem s5_1196_edges : next config 5 s5_1196 = [s6_1062] := by decide
theorem s5_1196_safe : Safe 8 5 s5_1196 := by
  apply safe_succ 7 5 s5_1196 [s6_1062] (by decide) s5_1196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1062_safe
def s5_1197 : State := ⟨[35,4,64,140], 1394136857275084884809464213392066726662430, 3, 2, 1, 0⟩
theorem s5_1197_edges : next config 5 s5_1197 = [s6_1063] := by decide
theorem s5_1197_safe : Safe 8 5 s5_1197 := by
  apply safe_succ 7 5 s5_1197 [s6_1063] (by decide) s5_1197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1063_safe
def s5_1198 : State := ⟨[35,4,64,140], 1394136857275084884809464213392075316597014, 3, 2, 1, 0⟩
theorem s5_1198_edges : next config 5 s5_1198 = [s6_1064] := by decide
theorem s5_1198_safe : Safe 8 5 s5_1198 := by
  apply safe_succ 7 5 s5_1198 [s6_1064] (by decide) s5_1198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1064_safe
def s5_1199 : State := ⟨[35,4,64,144], 22301085480897544079999200093999905638519070, 3, 2, 1, 0⟩
theorem s5_1199_edges : next config 5 s5_1199 = [s6_1065] := by decide
theorem s5_1199_safe : Safe 8 5 s5_1199 := by
  apply safe_succ 7 5 s5_1199 [s6_1065] (by decide) s5_1199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1065_safe
def s5_1200 : State := ⟨[35,4,64,144], 22301085480897544079999200093999914228453654, 3, 2, 1, 0⟩
theorem s5_1200_edges : next config 5 s5_1200 = [s6_1066] := by decide
theorem s5_1200_safe : Safe 8 5 s5_1200 := by
  apply safe_succ 7 5 s5_1200 [s6_1066] (by decide) s5_1200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1066_safe
def s5_1201 : State := ⟨[35,4,64,145], 44601830679428167221534918366648267144626462, 1, 1, 1, 0⟩
theorem s5_1201_edges : next config 5 s5_1201 = [s6_1154, s6_1092, s6_1067] := by decide
theorem s5_1201_safe : Safe 8 5 s5_1201 := by
  apply safe_succ 7 5 s5_1201 [s6_1154, s6_1092, s6_1067] (by decide) s5_1201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1154_safe
  · subst z; exact s6_1092_safe
  · subst z; exact s6_1067_safe
def s5_1202 : State := ⟨[35,4,64,145], 44601830679428167221534918366648275734561046, 1, 1, 1, 0⟩
theorem s5_1202_edges : next config 5 s5_1202 = [s6_1155, s6_1093, s6_1068] := by decide
theorem s5_1202_safe : Safe 8 5 s5_1202 := by
  apply safe_succ 7 5 s5_1202 [s6_1155, s6_1093, s6_1068] (by decide) s5_1202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1155_safe
  · subst z; exact s6_1093_safe
  · subst z; exact s6_1068_safe
def s5_1203 : State := ⟨[35,4,64,160], 1461501637671185285124623296198104371200065081630, 3, 2, 1, 0⟩
theorem s5_1203_edges : next config 5 s5_1203 = [s6_1069] := by decide
theorem s5_1203_safe : Safe 8 5 s5_1203 := by
  apply safe_succ 7 5 s5_1203 [s6_1069] (by decide) s5_1203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1069_safe
def s5_1204 : State := ⟨[35,4,64,160], 1461501637671185285124623296198104371208655016214, 3, 2, 1, 0⟩
theorem s5_1204_edges : next config 5 s5_1204 = [s6_1070] := by decide
theorem s5_1204_safe : Safe 8 5 s5_1204 := by
  apply safe_succ 7 5 s5_1204 [s6_1070] (by decide) s5_1204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1070_safe
def s5_1205 : State := ⟨[35,4,64,161], 2923003275002088203328308128914387390864587559190, 3, 2, 1, 0⟩
theorem s5_1205_edges : next config 5 s5_1205 = [s6_1071] := by decide
theorem s5_1205_safe : Safe 8 5 s5_1205 := by
  apply safe_succ 7 5 s5_1205 [s6_1071] (by decide) s5_1205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1071_safe
def s5_1206 : State := ⟨[35,4,64,163], 11692013098987505712550417125212085508791592882462, 3, 2, 1, 0⟩
theorem s5_1206_edges : next config 5 s5_1206 = [s6_1072] := by decide
theorem s5_1206_safe : Safe 8 5 s5_1206 := by
  apply safe_succ 7 5 s5_1206 [s6_1072] (by decide) s5_1206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1072_safe
def s5_1207 : State := ⟨[35,4,64,163], 11692013098987505712550417125212085508800182817046, 3, 2, 1, 0⟩
theorem s5_1207_edges : next config 5 s5_1207 = [s6_1073] := by decide
theorem s5_1207_safe : Safe 8 5 s5_1207 := by
  apply safe_succ 7 5 s5_1207 [s6_1073] (by decide) s5_1207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1073_safe
def s5_1208 : State := ⟨[35,4,64,192], 6277101735386680764176071790128604879584176796008167051550, 3, 2, 1, 0⟩
theorem s5_1208_edges : next config 5 s5_1208 = [s6_1074] := by decide
theorem s5_1208_safe : Safe 8 5 s5_1208 := by
  apply safe_succ 7 5 s5_1208 [s6_1074] (by decide) s5_1208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1074_safe
def s5_1209 : State := ⟨[35,4,64,192], 6277101735386680764176071790128604879584176796016756986134, 3, 2, 1, 0⟩
theorem s5_1209_edges : next config 5 s5_1209 = [s6_1075] := by decide
theorem s5_1209_safe : Safe 8 5 s5_1209 := by
  apply safe_succ 7 5 s5_1209 [s6_1075] (by decide) s5_1209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1075_safe
def s5_1210 : State := ⟨[35,4,67,128], 340282366920938463629395304133808951582, 3, 2, 0, 0⟩
theorem s5_1210_edges : next config 5 s5_1210 = [s6_1314, s6_1045, s6_1030, s6_1051, s6_1028, s6_1031, s6_1038, s6_1044] := by decide
theorem s5_1210_safe : Safe 8 5 s5_1210 := by
  apply safe_succ 7 5 s5_1210 [s6_1314, s6_1045, s6_1030, s6_1051, s6_1028, s6_1031, s6_1038, s6_1044] (by decide) s5_1210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1314_safe
  · subst z; exact s6_1045_safe
  · subst z; exact s6_1030_safe
  · subst z; exact s6_1051_safe
  · subst z; exact s6_1028_safe
  · subst z; exact s6_1031_safe
  · subst z; exact s6_1038_safe
  · subst z; exact s6_1044_safe
def s5_1211 : State := ⟨[35,4,67,129], 1020847100842043553070408856590889320734, 1, 0, 1, 0⟩
theorem s5_1211_edges : next config 5 s5_1211 = [s6_1158, s6_1094, s6_1040] := by decide
theorem s5_1211_safe : Safe 8 5 s5_1211 := by
  apply safe_succ 7 5 s5_1211 [s6_1158, s6_1094, s6_1040] (by decide) s5_1211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1158_safe
  · subst z; exact s6_1094_safe
  · subst z; exact s6_1040_safe
def s5_1212 : State := ⟨[35,4,67,129], 1020847100842043553070408856599479255318, 1, 0, 1, 0⟩
theorem s5_1212_edges : next config 5 s5_1212 = [s6_1159, s6_1095, s6_1041] := by decide
theorem s5_1212_safe : Safe 8 5 s5_1212 := by
  apply safe_succ 7 5 s5_1212 [s6_1159, s6_1095, s6_1041] (by decide) s5_1212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1159_safe
  · subst z; exact s6_1095_safe
  · subst z; exact s6_1041_safe
def s5_1213 : State := ⟨[35,4,67,130], 1701411834683920479997158071454425743646, 1, 0, 1, 0⟩
theorem s5_1213_edges : next config 5 s5_1213 = [s6_1160, s6_1096] := by decide
theorem s5_1213_safe : Safe 8 5 s5_1213 := by
  apply safe_succ 7 5 s5_1213 [s6_1160, s6_1096] (by decide) s5_1213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1160_safe
  · subst z; exact s6_1096_safe
def s5_1214 : State := ⟨[35,4,67,130], 1701411834683920479997158071463015678230, 1, 0, 1, 0⟩
theorem s5_1214_edges : next config 5 s5_1214 = [s6_1161, s6_1097] := by decide
theorem s5_1214_safe : Safe 8 5 s5_1214 := by
  apply safe_succ 7 5 s5_1214 [s6_1161, s6_1097] (by decide) s5_1214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1161_safe
  · subst z; exact s6_1097_safe
def s5_1215 : State := ⟨[35,4,67,131], 3062541302367674333850656501181498589470, 1, 0, 1, 0⟩
theorem s5_1215_edges : next config 5 s5_1215 = [s6_1162, s6_1098] := by decide
theorem s5_1215_safe : Safe 8 5 s5_1215 := by
  apply safe_succ 7 5 s5_1215 [s6_1162, s6_1098] (by decide) s5_1215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1162_safe
  · subst z; exact s6_1098_safe
def s5_1216 : State := ⟨[35,4,67,132], 5784800237735182041557653360635644281118, 1, 0, 1, 0⟩
theorem s5_1216_edges : next config 5 s5_1216 = [s6_1163, s6_1099, s6_1034] := by decide
theorem s5_1216_safe : Safe 8 5 s5_1216 := by
  apply safe_succ 7 5 s5_1216 [s6_1163, s6_1099, s6_1034] (by decide) s5_1216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1163_safe
  · subst z; exact s6_1099_safe
  · subst z; exact s6_1034_safe
def s5_1217 : State := ⟨[35,4,67,132], 5784800237735182041557653360644234215702, 1, 0, 1, 0⟩
theorem s5_1217_edges : next config 5 s5_1217 = [s6_1164, s6_1100, s6_1035] := by decide
theorem s5_1217_safe : Safe 8 5 s5_1217 := by
  apply safe_succ 7 5 s5_1217 [s6_1164, s6_1100, s6_1035] (by decide) s5_1217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1164_safe
  · subst z; exact s6_1100_safe
  · subst z; exact s6_1035_safe
def s5_1218 : State := ⟨[35,4,67,136], 87452568298760413272767559144260015030558, 1, 0, 1, 0⟩
theorem s5_1218_edges : next config 5 s5_1218 = [s6_1427, s6_1165, s6_1150, s6_1101, s6_1046, s6_1036] := by decide
theorem s5_1218_safe : Safe 8 5 s5_1218 := by
  apply safe_succ 7 5 s5_1218 [s6_1427, s6_1165, s6_1150, s6_1101, s6_1046, s6_1036] (by decide) s5_1218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1427_safe
  · subst z; exact s6_1165_safe
  · subst z; exact s6_1150_safe
  · subst z; exact s6_1101_safe
  · subst z; exact s6_1046_safe
  · subst z; exact s6_1036_safe
def s5_1219 : State := ⟨[35,4,67,136], 87452568298760413272767559144268604965142, 1, 0, 1, 0⟩
theorem s5_1219_edges : next config 5 s5_1219 = [s6_1428, s6_1166, s6_1151, s6_1102, s6_1047, s6_1037] := by decide
theorem s5_1219_safe : Safe 8 5 s5_1219 := by
  apply safe_succ 7 5 s5_1219 [s6_1428, s6_1166, s6_1151, s6_1102, s6_1047, s6_1037] (by decide) s5_1219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1428_safe
  · subst z; exact s6_1166_safe
  · subst z; exact s6_1151_safe
  · subst z; exact s6_1102_safe
  · subst z; exact s6_1047_safe
  · subst z; exact s6_1037_safe
def s5_1220 : State := ⟨[35,4,67,140], 1399581375145819900225025781063564694454558, 1, 0, 1, 0⟩
theorem s5_1220_edges : next config 5 s5_1220 = [s6_1316] := by decide
theorem s5_1220_safe : Safe 8 5 s5_1220 := by
  apply safe_succ 7 5 s5_1220 [s6_1316] (by decide) s5_1220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1316_safe
def s5_1221 : State := ⟨[35,4,67,140], 1481249143206845131456235686847189065203998, 1, 0, 1, 0⟩
theorem s5_1221_edges : next config 5 s5_1221 = [s6_1317] := by decide
theorem s5_1221_safe : Safe 8 5 s5_1221 := by
  apply safe_succ 7 5 s5_1221 [s6_1317] (by decide) s5_1221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1317_safe
def s5_1222 : State := ⟨[35,4,67,144], 22301085480897623308161861932290088858878238, 1, 0, 1, 0⟩
theorem s5_1222_edges : next config 5 s5_1222 = [s6_1167, s6_1105] := by decide
theorem s5_1222_safe : Safe 8 5 s5_1222 := by
  apply safe_succ 7 5 s5_1222 [s6_1167, s6_1105] (by decide) s5_1222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1167_safe
  · subst z; exact s6_1105_safe
def s5_1223 : State := ⟨[35,4,67,144], 22301085480897623308161861932290097448812822, 1, 0, 1, 0⟩
theorem s5_1223_edges : next config 5 s5_1223 = [s6_1168, s6_1106] := by decide
theorem s5_1223_safe : Safe 8 5 s5_1223 := by
  apply safe_succ 7 5 s5_1223 [s6_1168, s6_1106] (by decide) s5_1223_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1168_safe
  · subst z; exact s6_1106_safe
def s5_1224 : State := ⟨[35,4,67,145], 44602511244162009098461992689815720357331230, 1, 0, 1, 0⟩
theorem s5_1224_edges : next config 5 s5_1224 = [s6_1318, s6_1169, s6_1107] := by decide
theorem s5_1224_safe : Safe 8 5 s5_1224 := by
  apply safe_succ 7 5 s5_1224 [s6_1318, s6_1169, s6_1107] (by decide) s5_1224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1318_safe
  · subst z; exact s6_1169_safe
  · subst z; exact s6_1107_safe
def s5_1225 : State := ⟨[35,4,67,145], 66902575877958790363070784213249218326888734, 1, 0, 1, 0⟩
theorem s5_1225_edges : next config 5 s5_1225 = [s6_1319, s6_1170, s6_1108] := by decide
theorem s5_1225_safe : Safe 8 5 s5_1225 := by
  apply safe_succ 7 5 s5_1225 [s6_1319, s6_1170, s6_1108] (by decide) s5_1225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1319_safe
  · subst z; exact s6_1170_safe
  · subst z; exact s6_1108_safe
def s5_1226 : State := ⟨[35,4,67,160], 1461501637671185285203851458859942661383285440798, 1, 0, 1, 0⟩
theorem s5_1226_edges : next config 5 s5_1226 = [s6_1171, s6_1109] := by decide
theorem s5_1226_safe : Safe 8 5 s5_1226 := by
  apply safe_succ 7 5 s5_1226 [s6_1171, s6_1109] (by decide) s5_1226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1171_safe
  · subst z; exact s6_1109_safe
def s5_1227 : State := ⟨[35,4,67,160], 1461501637671185285203851458859942661391875375382, 1, 0, 1, 0⟩
theorem s5_1227_edges : next config 5 s5_1227 = [s6_1172, s6_1110] := by decide
theorem s5_1227_safe : Safe 8 5 s5_1227 := by
  apply safe_succ 7 5 s5_1227 [s6_1172, s6_1110] (by decide) s5_1227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1172_safe
  · subst z; exact s6_1110_safe
def s5_1228 : State := ⟨[35,4,67,161], 2923003275002088203407536291576225681047807918358, 1, 0, 1, 0⟩
theorem s5_1228_edges : next config 5 s5_1228 = [s6_1173, s6_1111] := by decide
theorem s5_1228_safe : Safe 8 5 s5_1228 := by
  apply safe_succ 7 5 s5_1228 [s6_1173, s6_1111] (by decide) s5_1228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1173_safe
  · subst z; exact s6_1111_safe
def s5_1229 : State := ⟨[35,4,67,163], 11692013098987505712629645287873923798974813241630, 1, 0, 1, 0⟩
theorem s5_1229_edges : next config 5 s5_1229 = [s6_1174, s6_1112, s6_1048] := by decide
theorem s5_1229_safe : Safe 8 5 s5_1229 := by
  apply safe_succ 7 5 s5_1229 [s6_1174, s6_1112, s6_1048] (by decide) s5_1229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1174_safe
  · subst z; exact s6_1112_safe
  · subst z; exact s6_1048_safe
def s5_1230 : State := ⟨[35,4,67,163], 11692013098987505712629645287873923798983403176214, 1, 0, 1, 0⟩
theorem s5_1230_edges : next config 5 s5_1230 = [s6_1175, s6_1113, s6_1049] := by decide
theorem s5_1230_safe : Safe 8 5 s5_1230 := by
  apply safe_succ 7 5 s5_1230 [s6_1175, s6_1113, s6_1049] (by decide) s5_1230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1175_safe
  · subst z; exact s6_1113_safe
  · subst z; exact s6_1049_safe
def s5_1231 : State := ⟨[35,4,67,171], 2993155353341141744779827722513200919062016319095070, 1, 0, 1, 0⟩
theorem s5_1231_edges : next config 5 s5_1231 = [s6_1320] := by decide
theorem s5_1231_safe : Safe 8 5 s5_1231 := by
  apply safe_succ 7 5 s5_1231 [s6_1320] (by decide) s5_1231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1320_safe
def s5_1232 : State := ⟨[35,4,67,171], 3004847366352676682193696954528307283716731117306142, 1, 0, 1, 0⟩
theorem s5_1232_edges : next config 5 s5_1232 = [s6_1321] := by decide
theorem s5_1232_safe : Safe 8 5 s5_1232 := by
  apply safe_succ 7 5 s5_1232 [s6_1321] (by decide) s5_1232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1321_safe
def s5_1233 : State := ⟨[35,4,67,192], 6277101735386680764176071790207833042246015086191387410718, 1, 0, 1, 0⟩
theorem s5_1233_edges : next config 5 s5_1233 = [s6_1178, s6_1114] := by decide
theorem s5_1233_safe : Safe 8 5 s5_1233 := by
  apply safe_succ 7 5 s5_1233 [s6_1178, s6_1114] (by decide) s5_1233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1178_safe
  · subst z; exact s6_1114_safe
def s5_1234 : State := ⟨[35,4,67,192], 6277101735386680764176071790207833042246015086199977345302, 1, 0, 1, 0⟩
theorem s5_1234_edges : next config 5 s5_1234 = [s6_1179, s6_1115] := by decide
theorem s5_1234_safe : Safe 8 5 s5_1234 := by
  apply safe_succ 7 5 s5_1234 [s6_1179, s6_1115] (by decide) s5_1234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1179_safe
  · subst z; exact s6_1115_safe
def s5_1235 : State := ⟨[35,4,67,195], 50216813883093446111026597752661497954962503197439629000990, 1, 0, 1, 0⟩
theorem s5_1235_edges : next config 5 s5_1235 = [s6_1180, s6_1116] := by decide
theorem s5_1235_safe : Safe 8 5 s5_1235 := by
  apply safe_succ 7 5 s5_1235 [s6_1180, s6_1116] (by decide) s5_1235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1180_safe
  · subst z; exact s6_1116_safe
def s5_1236 : State := ⟨[35,4,67,195], 50216813883093446111026597752661497954962503197448218935574, 1, 0, 1, 0⟩
theorem s5_1236_edges : next config 5 s5_1236 = [s6_1181, s6_1117] := by decide
theorem s5_1236_safe : Safe 8 5 s5_1236 := by
  apply safe_succ 7 5 s5_1236 [s6_1181, s6_1117] (by decide) s5_1236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1181_safe
  · subst z; exact s6_1117_safe
def s5_1237 : State := ⟨[35,4,67,224], 26959946667150639794667015087359913040637311048684232122830963147038, 1, 0, 1, 0⟩
theorem s5_1237_edges : next config 5 s5_1237 = [s6_1182, s6_1118] := by decide
theorem s5_1237_safe : Safe 8 5 s5_1237 := by
  apply safe_succ 7 5 s5_1237 [s6_1182, s6_1118] (by decide) s5_1237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1182_safe
  · subst z; exact s6_1118_safe
def s5_1238 : State := ⟨[35,4,67,224], 26959946667150639794667015087359913040637311048684232122839553081622, 1, 0, 1, 0⟩
theorem s5_1238_edges : next config 5 s5_1238 = [s6_1183, s6_1119] := by decide
theorem s5_1238_safe : Safe 8 5 s5_1238 := by
  apply safe_succ 7 5 s5_1238 [s6_1183, s6_1119] (by decide) s5_1238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1183_safe
  · subst z; exact s6_1119_safe
def s5_1239 : State := ⟨[35,4,96,128], 340282367000166625996085689137676488990, 3, 2, 0, 0⟩
theorem s5_1239_edges : next config 5 s5_1239 = [s6_1025, s6_1078, s6_1072, s6_1057, s6_1076, s6_1054, s6_1059, s6_1065, s6_1069] := by decide
theorem s5_1239_safe : Safe 8 5 s5_1239 := by
  apply safe_succ 7 5 s5_1239 [s6_1025, s6_1078, s6_1072, s6_1057, s6_1076, s6_1054, s6_1059, s6_1065, s6_1069] (by decide) s5_1239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1025_safe
  · subst z; exact s6_1078_safe
  · subst z; exact s6_1072_safe
  · subst z; exact s6_1057_safe
  · subst z; exact s6_1076_safe
  · subst z; exact s6_1054_safe
  · subst z; exact s6_1059_safe
  · subst z; exact s6_1065_safe
  · subst z; exact s6_1069_safe
def s5_1240 : State := ⟨[35,4,96,128], 340282367000166625996085689146266423574, 3, 2, 0, 0⟩
theorem s5_1240_edges : next config 5 s5_1240 = [s6_1026, s6_1079, s6_1073, s6_1058, s6_1077, s6_1055, s6_1060, s6_1066, s6_1070] := by decide
theorem s5_1240_safe : Safe 8 5 s5_1240 := by
  apply safe_succ 7 5 s5_1240 [s6_1026, s6_1079, s6_1073, s6_1058, s6_1077, s6_1055, s6_1060, s6_1066, s6_1070] (by decide) s5_1240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1026_safe
  · subst z; exact s6_1079_safe
  · subst z; exact s6_1073_safe
  · subst z; exact s6_1058_safe
  · subst z; exact s6_1077_safe
  · subst z; exact s6_1055_safe
  · subst z; exact s6_1060_safe
  · subst z; exact s6_1066_safe
  · subst z; exact s6_1070_safe
def s5_1241 : State := ⟨[35,4,96,140], 1399581375145899128387392471448568561991966, 1, 0, 1, 0⟩
theorem s5_1241_edges : next config 5 s5_1241 = [s6_1034, s6_1080] := by decide
theorem s5_1241_safe : Safe 8 5 s5_1241 := by
  apply safe_succ 7 5 s5_1241 [s6_1034, s6_1080] (by decide) s5_1241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1034_safe
  · subst z; exact s6_1080_safe
def s5_1242 : State := ⟨[35,4,96,140], 1399581375145899128387392471448577151926550, 1, 0, 1, 0⟩
theorem s5_1242_edges : next config 5 s5_1242 = [s6_1035, s6_1081] := by decide
theorem s5_1242_safe : Safe 8 5 s5_1242 := by
  apply safe_succ 7 5 s5_1242 [s6_1035, s6_1081] (by decide) s5_1242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1035_safe
  · subst z; exact s6_1081_safe
def s5_1243 : State := ⟨[35,4,96,140], 1481249143206924359618602377232192932741406, 1, 0, 1, 0⟩
theorem s5_1243_edges : next config 5 s5_1243 = [s6_1036, s6_1082] := by decide
theorem s5_1243_safe : Safe 8 5 s5_1243 := by
  apply safe_succ 7 5 s5_1243 [s6_1036, s6_1082] (by decide) s5_1243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1036_safe
  · subst z; exact s6_1082_safe
def s5_1244 : State := ⟨[35,4,96,140], 1481249143206924359618602377232201522675990, 1, 0, 1, 0⟩
theorem s5_1244_edges : next config 5 s5_1244 = [s6_1037, s6_1083] := by decide
theorem s5_1244_safe : Safe 8 5 s5_1244 := by
  apply safe_succ 7 5 s5_1244 [s6_1037, s6_1083] (by decide) s5_1244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1037_safe
  · subst z; exact s6_1083_safe
def s5_1245 : State := ⟨[35,4,96,145], 44602511244162088326624359380200724224868638, 1, 0, 1, 0⟩
theorem s5_1245_edges : next config 5 s5_1245 = [s6_1184, s6_1120, s6_1040, s6_1084] := by decide
theorem s5_1245_safe : Safe 8 5 s5_1245 := by
  apply safe_succ 7 5 s5_1245 [s6_1184, s6_1120, s6_1040, s6_1084] (by decide) s5_1245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1184_safe
  · subst z; exact s6_1120_safe
  · subst z; exact s6_1040_safe
  · subst z; exact s6_1084_safe
def s5_1246 : State := ⟨[35,4,96,145], 44602511244162088326624359380200732814803222, 1, 0, 1, 0⟩
theorem s5_1246_edges : next config 5 s5_1246 = [s6_1185, s6_1121, s6_1041, s6_1085] := by decide
theorem s5_1246_safe : Safe 8 5 s5_1246 := by
  apply safe_succ 7 5 s5_1246 [s6_1185, s6_1121, s6_1041, s6_1085] (by decide) s5_1246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1185_safe
  · subst z; exact s6_1121_safe
  · subst z; exact s6_1041_safe
  · subst z; exact s6_1085_safe
def s5_1247 : State := ⟨[35,4,96,145], 66902575877958869591233150903634222194426142, 1, 0, 1, 0⟩
theorem s5_1247_edges : next config 5 s5_1247 = [s6_1186, s6_1122, s6_1042, s6_1086] := by decide
theorem s5_1247_safe : Safe 8 5 s5_1247 := by
  apply safe_succ 7 5 s5_1247 [s6_1186, s6_1122, s6_1042, s6_1086] (by decide) s5_1247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1186_safe
  · subst z; exact s6_1122_safe
  · subst z; exact s6_1042_safe
  · subst z; exact s6_1086_safe
def s5_1248 : State := ⟨[35,4,96,145], 66902575877958869591233150903634230784360726, 1, 0, 1, 0⟩
theorem s5_1248_edges : next config 5 s5_1248 = [s6_1187, s6_1123, s6_1043, s6_1087] := by decide
theorem s5_1248_safe : Safe 8 5 s5_1248 := by
  apply safe_succ 7 5 s5_1248 [s6_1187, s6_1123, s6_1043, s6_1087] (by decide) s5_1248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1187_safe
  · subst z; exact s6_1123_safe
  · subst z; exact s6_1043_safe
  · subst z; exact s6_1087_safe
def s5_1249 : State := ⟨[35,4,96,171], 2993155353341141744779906950675567609447020186632478, 1, 0, 1, 0⟩
theorem s5_1249_edges : next config 5 s5_1249 = [s6_1046, s6_1088] := by decide
theorem s5_1249_safe : Safe 8 5 s5_1249 := by
  apply safe_succ 7 5 s5_1249 [s6_1046, s6_1088] (by decide) s5_1249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1046_safe
  · subst z; exact s6_1088_safe
def s5_1250 : State := ⟨[35,4,96,171], 2993155353341141744779906950675567609447028776567062, 1, 0, 1, 0⟩
theorem s5_1250_edges : next config 5 s5_1250 = [s6_1047, s6_1089] := by decide
theorem s5_1250_safe : Safe 8 5 s5_1250 := by
  apply safe_succ 7 5 s5_1250 [s6_1047, s6_1089] (by decide) s5_1250_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1047_safe
  · subst z; exact s6_1089_safe
def s5_1251 : State := ⟨[35,4,96,171], 3004847366352676682193776182690673974101734984843550, 1, 0, 1, 0⟩
theorem s5_1251_edges : next config 5 s5_1251 = [s6_1048, s6_1090] := by decide
theorem s5_1251_safe : Safe 8 5 s5_1251 := by
  apply safe_succ 7 5 s5_1251 [s6_1048, s6_1090] (by decide) s5_1251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1048_safe
  · subst z; exact s6_1090_safe
def s5_1252 : State := ⟨[35,4,96,171], 3004847366352676682193776182690673974101743574778134, 1, 0, 1, 0⟩
theorem s5_1252_edges : next config 5 s5_1252 = [s6_1049, s6_1091] := by decide
theorem s5_1252_safe : Safe 8 5 s5_1252 := by
  apply safe_succ 7 5 s5_1252 [s6_1049, s6_1091] (by decide) s5_1252_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1049_safe
  · subst z; exact s6_1091_safe
def s5_1253 : State := ⟨[35,4,104,129], 1020847121124453156574505327948464193822, 1, 0, 1, 0⟩
theorem s5_1253_edges : next config 5 s5_1253 = [s6_1188, s6_1124, s6_1084] := by decide
theorem s5_1253_safe : Safe 8 5 s5_1253 := by
  apply safe_succ 7 5 s5_1253 [s6_1188, s6_1124, s6_1084] (by decide) s5_1253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1188_safe
  · subst z; exact s6_1124_safe
  · subst z; exact s6_1084_safe
def s5_1254 : State := ⟨[35,4,104,129], 1020847121124453156574505327957054128406, 1, 0, 1, 0⟩
theorem s5_1254_edges : next config 5 s5_1254 = [s6_1189, s6_1125, s6_1085] := by decide
theorem s5_1254_safe : Safe 8 5 s5_1254 := by
  apply safe_succ 7 5 s5_1254 [s6_1189, s6_1125, s6_1085] (by decide) s5_1254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1189_safe
  · subst z; exact s6_1125_safe
  · subst z; exact s6_1085_safe
def s5_1255 : State := ⟨[35,4,104,130], 1701411854966330083501254542812000616734, 1, 0, 1, 0⟩
theorem s5_1255_edges : next config 5 s5_1255 = [s6_1190, s6_1126] := by decide
theorem s5_1255_safe : Safe 8 5 s5_1255 := by
  apply safe_succ 7 5 s5_1255 [s6_1190, s6_1126] (by decide) s5_1255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1190_safe
  · subst z; exact s6_1126_safe
def s5_1256 : State := ⟨[35,4,104,130], 1701411854966330083501254542820590551318, 1, 0, 1, 0⟩
theorem s5_1256_edges : next config 5 s5_1256 = [s6_1191, s6_1127] := by decide
theorem s5_1256_safe : Safe 8 5 s5_1256 := by
  apply safe_succ 7 5 s5_1256 [s6_1191, s6_1127] (by decide) s5_1256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1191_safe
  · subst z; exact s6_1127_safe
def s5_1257 : State := ⟨[35,4,104,131], 3062541322650083937354752972539073462558, 1, 0, 1, 0⟩
theorem s5_1257_edges : next config 5 s5_1257 = [s6_1192, s6_1128] := by decide
theorem s5_1257_safe : Safe 8 5 s5_1257 := by
  apply safe_succ 7 5 s5_1257 [s6_1192, s6_1128] (by decide) s5_1257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1192_safe
  · subst z; exact s6_1128_safe
def s5_1258 : State := ⟨[35,4,104,132], 5784800258017591645061749831993219154206, 1, 0, 1, 0⟩
theorem s5_1258_edges : next config 5 s5_1258 = [s6_1193, s6_1129, s6_1080] := by decide
theorem s5_1258_safe : Safe 8 5 s5_1258 := by
  apply safe_succ 7 5 s5_1258 [s6_1193, s6_1129, s6_1080] (by decide) s5_1258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1193_safe
  · subst z; exact s6_1129_safe
  · subst z; exact s6_1080_safe
def s5_1259 : State := ⟨[35,4,104,132], 5784800258017591645061749832001809088790, 1, 0, 1, 0⟩
theorem s5_1259_edges : next config 5 s5_1259 = [s6_1194, s6_1130, s6_1081] := by decide
theorem s5_1259_safe : Safe 8 5 s5_1259 := by
  apply safe_succ 7 5 s5_1259 [s6_1194, s6_1130, s6_1081] (by decide) s5_1259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1194_safe
  · subst z; exact s6_1130_safe
  · subst z; exact s6_1081_safe
def s5_1260 : State := ⟨[35,4,104,136], 87452568319042822876271655615617589903646, 1, 0, 1, 0⟩
theorem s5_1260_edges : next config 5 s5_1260 = [s6_1431, s6_1195, s6_1152, s6_1131, s6_1088, s6_1082] := by decide
theorem s5_1260_safe : Safe 8 5 s5_1260 := by
  apply safe_succ 7 5 s5_1260 [s6_1431, s6_1195, s6_1152, s6_1131, s6_1088, s6_1082] (by decide) s5_1260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1431_safe
  · subst z; exact s6_1195_safe
  · subst z; exact s6_1152_safe
  · subst z; exact s6_1131_safe
  · subst z; exact s6_1088_safe
  · subst z; exact s6_1082_safe
def s5_1261 : State := ⟨[35,4,104,136], 87452568319042822876271655615626179838230, 1, 0, 1, 0⟩
theorem s5_1261_edges : next config 5 s5_1261 = [s6_1432, s6_1196, s6_1153, s6_1132, s6_1089, s6_1083] := by decide
theorem s5_1261_safe : Safe 8 5 s5_1261 := by
  apply safe_succ 7 5 s5_1261 [s6_1432, s6_1196, s6_1153, s6_1132, s6_1089, s6_1083] (by decide) s5_1261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s6_1432_safe
  · subst z; exact s6_1196_safe
  · subst z; exact s6_1153_safe
  · subst z; exact s6_1132_safe
  · subst z; exact s6_1089_safe
  · subst z; exact s6_1083_safe
def s5_1262 : State := ⟨[35,4,104,144], 22301085480917905717765366028761446433751326, 1, 0, 1, 0⟩
theorem s5_1262_edges : next config 5 s5_1262 = [s6_1197, s6_1135] := by decide
theorem s5_1262_safe : Safe 8 5 s5_1262 := by
  apply safe_succ 7 5 s5_1262 [s6_1197, s6_1135] (by decide) s5_1262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1197_safe
  · subst z; exact s6_1135_safe
def s5_1263 : State := ⟨[35,4,104,144], 22301085480917905717765366028761455023685910, 1, 0, 1, 0⟩
theorem s5_1263_edges : next config 5 s5_1263 = [s6_1198, s6_1136] := by decide
theorem s5_1263_safe : Safe 8 5 s5_1263 := by
  apply safe_succ 7 5 s5_1263 [s6_1198, s6_1136] (by decide) s5_1263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1198_safe
  · subst z; exact s6_1136_safe
def s5_1264 : State := ⟨[35,4,104,160], 1461501637671185305486261062364039132740860313886, 1, 0, 1, 0⟩
theorem s5_1264_edges : next config 5 s5_1264 = [s6_1199, s6_1137] := by decide
theorem s5_1264_safe : Safe 8 5 s5_1264 := by
  apply safe_succ 7 5 s5_1264 [s6_1199, s6_1137] (by decide) s5_1264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1199_safe
  · subst z; exact s6_1137_safe
def s5_1265 : State := ⟨[35,4,104,160], 1461501637671185305486261062364039132749450248470, 1, 0, 1, 0⟩
theorem s5_1265_edges : next config 5 s5_1265 = [s6_1200, s6_1138] := by decide
theorem s5_1265_safe : Safe 8 5 s5_1265 := by
  apply safe_succ 7 5 s5_1265 [s6_1200, s6_1138] (by decide) s5_1265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1200_safe
  · subst z; exact s6_1138_safe
def s5_1266 : State := ⟨[35,4,104,161], 2923003275002088223689945895080322152405382791446, 1, 0, 1, 0⟩
theorem s5_1266_edges : next config 5 s5_1266 = [s6_1201, s6_1139] := by decide
theorem s5_1266_safe : Safe 8 5 s5_1266 := by
  apply safe_succ 7 5 s5_1266 [s6_1201, s6_1139] (by decide) s5_1266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1201_safe
  · subst z; exact s6_1139_safe
def s5_1267 : State := ⟨[35,4,104,163], 11692013098987505732912054891378020270332388114718, 1, 0, 1, 0⟩
theorem s5_1267_edges : next config 5 s5_1267 = [s6_1202, s6_1140, s6_1090] := by decide
theorem s5_1267_safe : Safe 8 5 s5_1267 := by
  apply safe_succ 7 5 s5_1267 [s6_1202, s6_1140, s6_1090] (by decide) s5_1267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1202_safe
  · subst z; exact s6_1140_safe
  · subst z; exact s6_1090_safe
def s5_1268 : State := ⟨[35,4,104,163], 11692013098987505732912054891378020270340978049302, 1, 0, 1, 0⟩
theorem s5_1268_edges : next config 5 s5_1268 = [s6_1203, s6_1141, s6_1091] := by decide
theorem s5_1268_safe : Safe 8 5 s5_1268 := by
  apply safe_succ 7 5 s5_1268 [s6_1203, s6_1141, s6_1091] (by decide) s5_1268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1203_safe
  · subst z; exact s6_1141_safe
  · subst z; exact s6_1091_safe
def s5_1269 : State := ⟨[35,4,104,192], 6277101735386680764176071810490242645750111557548962283806, 1, 0, 1, 0⟩
theorem s5_1269_edges : next config 5 s5_1269 = [s6_1206, s6_1142] := by decide
theorem s5_1269_safe : Safe 8 5 s5_1269 := by
  apply safe_succ 7 5 s5_1269 [s6_1206, s6_1142] (by decide) s5_1269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1206_safe
  · subst z; exact s6_1142_safe
def s5_1270 : State := ⟨[35,4,104,192], 6277101735386680764176071810490242645750111557557552218390, 1, 0, 1, 0⟩
theorem s5_1270_edges : next config 5 s5_1270 = [s6_1207, s6_1143] := by decide
theorem s5_1270_safe : Safe 8 5 s5_1270 := by
  apply safe_succ 7 5 s5_1270 [s6_1207, s6_1143] (by decide) s5_1270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1207_safe
  · subst z; exact s6_1143_safe
def s5_1271 : State := ⟨[35,4,104,224], 26959946667150639794667015087359913060919720652188328594188538020126, 1, 0, 1, 0⟩
theorem s5_1271_edges : next config 5 s5_1271 = [s6_1208, s6_1144] := by decide
theorem s5_1271_safe : Safe 8 5 s5_1271 := by
  apply safe_succ 7 5 s5_1271 [s6_1208, s6_1144] (by decide) s5_1271_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1208_safe
  · subst z; exact s6_1144_safe
def s5_1272 : State := ⟨[35,4,104,224], 26959946667150639794667015087359913060919720652188328594197127954710, 1, 0, 1, 0⟩
theorem s5_1272_edges : next config 5 s5_1272 = [s6_1209, s6_1145] := by decide
theorem s5_1272_safe : Safe 8 5 s5_1272 := by
  apply safe_succ 7 5 s5_1272 [s6_1209, s6_1145] (by decide) s5_1272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1209_safe
  · subst z; exact s6_1145_safe
def s5_1273 : State := ⟨[35,4,104,232], 6901746346790563787434755862277365734838391548400034311275609151570206, 1, 0, 1, 0⟩
theorem s5_1273_edges : next config 5 s5_1273 = [s6_1210, s6_1146] := by decide
theorem s5_1273_safe : Safe 8 5 s5_1273 := by
  apply safe_succ 7 5 s5_1273 [s6_1210, s6_1146] (by decide) s5_1273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1210_safe
  · subst z; exact s6_1146_safe
def s5_1274 : State := ⟨[35,4,104,232], 6901746346790563787434755862277365734838391548400034311275617741504790, 1, 0, 1, 0⟩
theorem s5_1274_edges : next config 5 s5_1274 = [s6_1211, s6_1147] := by decide
theorem s5_1274_safe : Safe 8 5 s5_1274 := by
  apply safe_succ 7 5 s5_1274 [s6_1211, s6_1147] (by decide) s5_1274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1211_safe
  · subst z; exact s6_1147_safe
def s5_1275 : State := ⟨[35,12,64,145], 44602511244162009098461845115863130680922398, 3, 0, 1, 0⟩
theorem s5_1275_edges : next config 5 s5_1275 = [s6_1021, s6_1120] := by decide
theorem s5_1275_safe : Safe 8 5 s5_1275 := by
  apply safe_succ 7 5 s5_1275 [s6_1021, s6_1120] (by decide) s5_1275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1021_safe
  · subst z; exact s6_1120_safe
def s5_1276 : State := ⟨[35,12,64,145], 44602511244162009098461845115863139270856982, 3, 0, 1, 0⟩
theorem s5_1276_edges : next config 5 s5_1276 = [s6_1022, s6_1121] := by decide
theorem s5_1276_safe : Safe 8 5 s5_1276 := by
  apply safe_succ 7 5 s5_1276 [s6_1022, s6_1121] (by decide) s5_1276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1022_safe
  · subst z; exact s6_1121_safe
def s5_1277 : State := ⟨[35,12,64,145], 66902575877958790363070636639296628650479902, 3, 0, 1, 0⟩
theorem s5_1277_edges : next config 5 s5_1277 = [s6_1023, s6_1122] := by decide
theorem s5_1277_safe : Safe 8 5 s5_1277 := by
  apply safe_succ 7 5 s5_1277 [s6_1023, s6_1122] (by decide) s5_1277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1023_safe
  · subst z; exact s6_1122_safe
def s5_1278 : State := ⟨[35,12,64,145], 66902575877958790363070636639296637240414486, 3, 0, 1, 0⟩
theorem s5_1278_edges : next config 5 s5_1278 = [s6_1024, s6_1123] := by decide
theorem s5_1278_safe : Safe 8 5 s5_1278 := by
  apply safe_succ 7 5 s5_1278 [s6_1024, s6_1123] (by decide) s5_1278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1024_safe
  · subst z; exact s6_1123_safe
def s5_1279 : State := ⟨[35,12,67,128], 340282367000166626143659641727352901918, 3, 0, 0, 0⟩
theorem s5_1279_edges : next config 5 s5_1279 = [s6_1025, s6_1112, s6_1103, s6_1116, s6_1096, s6_1101, s6_1105, s6_1109] := by decide
theorem s5_1279_safe : Safe 8 5 s5_1279 := by
  apply safe_succ 7 5 s5_1279 [s6_1025, s6_1112, s6_1103, s6_1116, s6_1096, s6_1101, s6_1105, s6_1109] (by decide) s5_1279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1025_safe
  · subst z; exact s6_1112_safe
  · subst z; exact s6_1103_safe
  · subst z; exact s6_1116_safe
  · subst z; exact s6_1096_safe
  · subst z; exact s6_1101_safe
  · subst z; exact s6_1105_safe
  · subst z; exact s6_1109_safe
def s5_1280 : State := ⟨[35,12,67,128], 340282367000166626143659641735942836502, 3, 0, 0, 0⟩
theorem s5_1280_edges : next config 5 s5_1280 = [s6_1026, s6_1113, s6_1104, s6_1117, s6_1097, s6_1102, s6_1106, s6_1110] := by decide
theorem s5_1280_safe : Safe 8 5 s5_1280 := by
  apply safe_succ 7 5 s5_1280 [s6_1026, s6_1113, s6_1104, s6_1117, s6_1097, s6_1102, s6_1106, s6_1110] (by decide) s5_1280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1026_safe
  · subst z; exact s6_1113_safe
  · subst z; exact s6_1104_safe
  · subst z; exact s6_1117_safe
  · subst z; exact s6_1097_safe
  · subst z; exact s6_1102_safe
  · subst z; exact s6_1106_safe
  · subst z; exact s6_1110_safe
def s5_1281 : State := ⟨[35,12,67,129], 1020847100762815390556144518997345374494, 3, 0, 1, 0⟩
theorem s5_1281_edges : next config 5 s5_1281 = [s6_1322, s6_1027, s6_1107] := by decide
theorem s5_1281_safe : Safe 8 5 s5_1281 := by
  apply safe_succ 7 5 s5_1281 [s6_1322, s6_1027, s6_1107] (by decide) s5_1281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1322_safe
  · subst z; exact s6_1027_safe
  · subst z; exact s6_1107_safe
def s5_1282 : State := ⟨[35,12,67,130], 1701411834604692317482893733860881797406, 3, 0, 1, 0⟩
theorem s5_1282_edges : next config 5 s5_1282 = [s6_1323, s6_1028] := by decide
theorem s5_1282_safe : Safe 8 5 s5_1282 := by
  apply safe_succ 7 5 s5_1282 [s6_1323, s6_1028] (by decide) s5_1282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1323_safe
  · subst z; exact s6_1028_safe
def s5_1283 : State := ⟨[35,12,67,131], 3062541302288446171336392163587954643230, 3, 0, 1, 0⟩
theorem s5_1283_edges : next config 5 s5_1283 = [s6_1324, s6_1029] := by decide
theorem s5_1283_safe : Safe 8 5 s5_1283 := by
  apply safe_succ 7 5 s5_1283 [s6_1324, s6_1029] (by decide) s5_1283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1324_safe
  · subst z; exact s6_1029_safe
def s5_1284 : State := ⟨[35,12,67,132], 5784800237655953879043389023042100334878, 3, 0, 1, 0⟩
theorem s5_1284_edges : next config 5 s5_1284 = [s6_1325, s6_1030] := by decide
theorem s5_1284_safe : Safe 8 5 s5_1284 := by
  apply safe_succ 7 5 s5_1284 [s6_1325, s6_1030] (by decide) s5_1284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1325_safe
  · subst z; exact s6_1030_safe
def s5_1285 : State := ⟨[35,12,67,136], 87452568298681185110253294806666471084318, 3, 0, 1, 0⟩
theorem s5_1285_edges : next config 5 s5_1285 = [s6_1326, s6_1031] := by decide
theorem s5_1285_safe : Safe 8 5 s5_1285 := by
  apply safe_succ 7 5 s5_1285 [s6_1326, s6_1031] (by decide) s5_1285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1326_safe
  · subst z; exact s6_1031_safe
def s5_1286 : State := ⟨[35,12,67,140], 1394136857275084884809611787344656403075358, 3, 0, 1, 0⟩
theorem s5_1286_edges : next config 5 s5_1286 = [s6_1327, s6_1033] := by decide
theorem s5_1286_safe : Safe 8 5 s5_1286 := by
  apply safe_succ 7 5 s5_1286 [s6_1327, s6_1033] (by decide) s5_1286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1327_safe
  · subst z; exact s6_1033_safe
def s5_1287 : State := ⟨[35,12,67,144], 22301085480897544079999347667952495314931998, 3, 0, 1, 0⟩
theorem s5_1287_edges : next config 5 s5_1287 = [s6_1328, s6_1038] := by decide
theorem s5_1287_safe : Safe 8 5 s5_1287 := by
  apply safe_succ 7 5 s5_1287 [s6_1328, s6_1038] (by decide) s5_1287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1328_safe
  · subst z; exact s6_1038_safe
def s5_1288 : State := ⟨[35,12,67,160], 1461501637671185285124623296345678323789741494558, 3, 0, 1, 0⟩
theorem s5_1288_edges : next config 5 s5_1288 = [s6_1329, s6_1044] := by decide
theorem s5_1288_safe : Safe 8 5 s5_1288 := by
  apply safe_succ 7 5 s5_1288 [s6_1329, s6_1044] (by decide) s5_1288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1329_safe
  · subst z; exact s6_1044_safe
def s5_1289 : State := ⟨[35,12,67,163], 11692013098987505712550417125359659461381269295390, 3, 0, 1, 0⟩
theorem s5_1289_edges : next config 5 s5_1289 = [s6_1330, s6_1045] := by decide
theorem s5_1289_safe : Safe 8 5 s5_1289 := by
  apply safe_succ 7 5 s5_1289 [s6_1330, s6_1045] (by decide) s5_1289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1330_safe
  · subst z; exact s6_1045_safe
def s5_1290 : State := ⟨[35,12,67,192], 6277101735386680764176071790128604879731750748597843464478, 3, 0, 1, 0⟩
theorem s5_1290_edges : next config 5 s5_1290 = [s6_1331, s6_1050] := by decide
theorem s5_1290_safe : Safe 8 5 s5_1290 := by
  apply safe_succ 7 5 s5_1290 [s6_1331, s6_1050] (by decide) s5_1290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1331_safe
  · subst z; exact s6_1050_safe
def s5_1291 : State := ⟨[35,12,67,195], 50216813883093446111026597752582269792448238859846085054750, 3, 0, 1, 0⟩
theorem s5_1291_edges : next config 5 s5_1291 = [s6_1332, s6_1051] := by decide
theorem s5_1291_safe : Safe 8 5 s5_1291 := by
  apply safe_succ 7 5 s5_1291 [s6_1332, s6_1051] (by decide) s5_1291_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1332_safe
  · subst z; exact s6_1051_safe
def s5_1292 : State := ⟨[35,12,96,129], 1020847100842043552922834904001212911902, 3, 0, 1, 0⟩
theorem s5_1292_edges : next config 5 s5_1292 = [s6_1052, s6_1094, s6_1124, s6_1120] := by decide
theorem s5_1292_safe : Safe 8 5 s5_1292 := by
  apply safe_succ 7 5 s5_1292 [s6_1052, s6_1094, s6_1124, s6_1120] (by decide) s5_1292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1052_safe
  · subst z; exact s6_1094_safe
  · subst z; exact s6_1124_safe
  · subst z; exact s6_1120_safe
def s5_1293 : State := ⟨[35,12,96,129], 1020847100842043552922834904009802846486, 3, 0, 1, 0⟩
theorem s5_1293_edges : next config 5 s5_1293 = [s6_1053, s6_1095, s6_1125, s6_1121] := by decide
theorem s5_1293_safe : Safe 8 5 s5_1293 := by
  apply safe_succ 7 5 s5_1293 [s6_1053, s6_1095, s6_1125, s6_1121] (by decide) s5_1293_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1053_safe
  · subst z; exact s6_1095_safe
  · subst z; exact s6_1125_safe
  · subst z; exact s6_1121_safe
def s5_1294 : State := ⟨[35,12,96,130], 1701411834683920479849584118864749334814, 3, 0, 1, 0⟩
theorem s5_1294_edges : next config 5 s5_1294 = [s6_1054, s6_1096, s6_1126] := by decide
theorem s5_1294_safe : Safe 8 5 s5_1294 := by
  apply safe_succ 7 5 s5_1294 [s6_1054, s6_1096, s6_1126] (by decide) s5_1294_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1054_safe
  · subst z; exact s6_1096_safe
  · subst z; exact s6_1126_safe
def s5_1295 : State := ⟨[35,12,96,130], 1701411834683920479849584118873339269398, 3, 0, 1, 0⟩
theorem s5_1295_edges : next config 5 s5_1295 = [s6_1055, s6_1097, s6_1127] := by decide
theorem s5_1295_safe : Safe 8 5 s5_1295 := by
  apply safe_succ 7 5 s5_1295 [s6_1055, s6_1097, s6_1127] (by decide) s5_1295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1055_safe
  · subst z; exact s6_1097_safe
  · subst z; exact s6_1127_safe
def s5_1296 : State := ⟨[35,12,96,131], 3062541302367674333703082548591822180638, 3, 0, 1, 0⟩
theorem s5_1296_edges : next config 5 s5_1296 = [s6_1056, s6_1098, s6_1128] := by decide
theorem s5_1296_safe : Safe 8 5 s5_1296 := by
  apply safe_succ 7 5 s5_1296 [s6_1056, s6_1098, s6_1128] (by decide) s5_1296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1056_safe
  · subst z; exact s6_1098_safe
  · subst z; exact s6_1128_safe
def s5_1297 : State := ⟨[35,12,96,132], 5784800237735182041410079408045967872286, 3, 0, 1, 0⟩
theorem s5_1297_edges : next config 5 s5_1297 = [s6_1057, s6_1099, s6_1129] := by decide
theorem s5_1297_safe : Safe 8 5 s5_1297 := by
  apply safe_succ 7 5 s5_1297 [s6_1057, s6_1099, s6_1129] (by decide) s5_1297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1057_safe
  · subst z; exact s6_1099_safe
  · subst z; exact s6_1129_safe
def s5_1298 : State := ⟨[35,12,96,132], 5784800237735182041410079408054557806870, 3, 0, 1, 0⟩
theorem s5_1298_edges : next config 5 s5_1298 = [s6_1058, s6_1100, s6_1130] := by decide
theorem s5_1298_safe : Safe 8 5 s5_1298 := by
  apply safe_succ 7 5 s5_1298 [s6_1058, s6_1100, s6_1130] (by decide) s5_1298_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1058_safe
  · subst z; exact s6_1100_safe
  · subst z; exact s6_1130_safe
def s5_1299 : State := ⟨[35,12,96,136], 87452568298760413272619985191670338621726, 3, 0, 1, 0⟩
theorem s5_1299_edges : next config 5 s5_1299 = [s6_1059, s6_1101, s6_1131] := by decide
theorem s5_1299_safe : Safe 8 5 s5_1299 := by
  apply safe_succ 7 5 s5_1299 [s6_1059, s6_1101, s6_1131] (by decide) s5_1299_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1059_safe
  · subst z; exact s6_1101_safe
  · subst z; exact s6_1131_safe
def s5_1300 : State := ⟨[35,12,96,136], 87452568298760413272619985191678928556310, 3, 0, 1, 0⟩
theorem s5_1300_edges : next config 5 s5_1300 = [s6_1060, s6_1102, s6_1132] := by decide
theorem s5_1300_safe : Safe 8 5 s5_1300 := by
  apply safe_succ 7 5 s5_1300 [s6_1060, s6_1102, s6_1132] (by decide) s5_1300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1060_safe
  · subst z; exact s6_1102_safe
  · subst z; exact s6_1132_safe
def s5_1301 : State := ⟨[35,12,96,140], 1394136857275164112971978477729660270612766, 3, 0, 1, 0⟩
theorem s5_1301_edges : next config 5 s5_1301 = [s6_1063, s6_1103, s6_1133] := by decide
theorem s5_1301_safe : Safe 8 5 s5_1301 := by
  apply safe_succ 7 5 s5_1301 [s6_1063, s6_1103, s6_1133] (by decide) s5_1301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1063_safe
  · subst z; exact s6_1103_safe
  · subst z; exact s6_1133_safe
def s5_1302 : State := ⟨[35,12,96,140], 1394136857275164112971978477729668860547350, 3, 0, 1, 0⟩
theorem s5_1302_edges : next config 5 s5_1302 = [s6_1064, s6_1104, s6_1134] := by decide
theorem s5_1302_safe : Safe 8 5 s5_1302 := by
  apply safe_succ 7 5 s5_1302 [s6_1064, s6_1104, s6_1134] (by decide) s5_1302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1064_safe
  · subst z; exact s6_1104_safe
  · subst z; exact s6_1134_safe
def s5_1303 : State := ⟨[35,12,96,144], 22301085480897623308161714358337499182469406, 3, 0, 1, 0⟩
theorem s5_1303_edges : next config 5 s5_1303 = [s6_1065, s6_1105, s6_1135] := by decide
theorem s5_1303_safe : Safe 8 5 s5_1303 := by
  apply safe_succ 7 5 s5_1303 [s6_1065, s6_1105, s6_1135] (by decide) s5_1303_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1065_safe
  · subst z; exact s6_1105_safe
  · subst z; exact s6_1135_safe
def s5_1304 : State := ⟨[35,12,96,144], 22301085480897623308161714358337507772403990, 3, 0, 1, 0⟩
theorem s5_1304_edges : next config 5 s5_1304 = [s6_1066, s6_1106, s6_1136] := by decide
theorem s5_1304_safe : Safe 8 5 s5_1304 := by
  apply safe_succ 7 5 s5_1304 [s6_1066, s6_1106, s6_1136] (by decide) s5_1304_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1066_safe
  · subst z; exact s6_1106_safe
  · subst z; exact s6_1136_safe
def s5_1305 : State := ⟨[35,12,96,160], 1461501637671185285203851458712368708793609031966, 3, 0, 1, 0⟩
theorem s5_1305_edges : next config 5 s5_1305 = [s6_1069, s6_1109, s6_1137] := by decide
theorem s5_1305_safe : Safe 8 5 s5_1305 := by
  apply safe_succ 7 5 s5_1305 [s6_1069, s6_1109, s6_1137] (by decide) s5_1305_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1069_safe
  · subst z; exact s6_1109_safe
  · subst z; exact s6_1137_safe
def s5_1306 : State := ⟨[35,12,96,160], 1461501637671185285203851458712368708802198966550, 3, 0, 1, 0⟩
theorem s5_1306_edges : next config 5 s5_1306 = [s6_1070, s6_1110, s6_1138] := by decide
theorem s5_1306_safe : Safe 8 5 s5_1306 := by
  apply safe_succ 7 5 s5_1306 [s6_1070, s6_1110, s6_1138] (by decide) s5_1306_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1070_safe
  · subst z; exact s6_1110_safe
  · subst z; exact s6_1138_safe
def s5_1307 : State := ⟨[35,12,96,161], 2923003275002088203407536291428651728458131509526, 3, 0, 1, 0⟩
theorem s5_1307_edges : next config 5 s5_1307 = [s6_1071, s6_1111, s6_1139] := by decide
theorem s5_1307_safe : Safe 8 5 s5_1307 := by
  apply safe_succ 7 5 s5_1307 [s6_1071, s6_1111, s6_1139] (by decide) s5_1307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1071_safe
  · subst z; exact s6_1111_safe
  · subst z; exact s6_1139_safe
def s5_1308 : State := ⟨[35,12,96,163], 11692013098987505712629645287726349846385136832798, 3, 0, 1, 0⟩
theorem s5_1308_edges : next config 5 s5_1308 = [s6_1072, s6_1112, s6_1140] := by decide
theorem s5_1308_safe : Safe 8 5 s5_1308 := by
  apply safe_succ 7 5 s5_1308 [s6_1072, s6_1112, s6_1140] (by decide) s5_1308_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1072_safe
  · subst z; exact s6_1112_safe
  · subst z; exact s6_1140_safe
def s5_1309 : State := ⟨[35,12,96,163], 11692013098987505712629645287726349846393726767382, 3, 0, 1, 0⟩
theorem s5_1309_edges : next config 5 s5_1309 = [s6_1073, s6_1113, s6_1141] := by decide
theorem s5_1309_safe : Safe 8 5 s5_1309 := by
  apply safe_succ 7 5 s5_1309 [s6_1073, s6_1113, s6_1141] (by decide) s5_1309_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1073_safe
  · subst z; exact s6_1113_safe
  · subst z; exact s6_1141_safe
def s5_1310 : State := ⟨[35,12,96,192], 6277101735386680764176071790207833042098441133601711001886, 3, 0, 1, 0⟩
theorem s5_1310_edges : next config 5 s5_1310 = [s6_1074, s6_1114, s6_1142] := by decide
theorem s5_1310_safe : Safe 8 5 s5_1310 := by
  apply safe_succ 7 5 s5_1310 [s6_1074, s6_1114, s6_1142] (by decide) s5_1310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1074_safe
  · subst z; exact s6_1114_safe
  · subst z; exact s6_1142_safe
def s5_1311 : State := ⟨[35,12,96,192], 6277101735386680764176071790207833042098441133610300936470, 3, 0, 1, 0⟩
theorem s5_1311_edges : next config 5 s5_1311 = [s6_1075, s6_1115, s6_1143] := by decide
theorem s5_1311_safe : Safe 8 5 s5_1311 := by
  apply safe_succ 7 5 s5_1311 [s6_1075, s6_1115, s6_1143] (by decide) s5_1311_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1075_safe
  · subst z; exact s6_1115_safe
  · subst z; exact s6_1143_safe
def s5_1312 : State := ⟨[35,12,96,224], 26959946667150639794667015087359913040637311048536658170241286738206, 3, 0, 1, 0⟩
theorem s5_1312_edges : next config 5 s5_1312 = [s6_1076, s6_1118, s6_1144] := by decide
theorem s5_1312_safe : Safe 8 5 s5_1312 := by
  apply safe_succ 7 5 s5_1312 [s6_1076, s6_1118, s6_1144] (by decide) s5_1312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1076_safe
  · subst z; exact s6_1118_safe
  · subst z; exact s6_1144_safe
def s5_1313 : State := ⟨[35,12,96,224], 26959946667150639794667015087359913040637311048536658170249876672790, 3, 0, 1, 0⟩
theorem s5_1313_edges : next config 5 s5_1313 = [s6_1077, s6_1119, s6_1145] := by decide
theorem s5_1313_safe : Safe 8 5 s5_1313 := by
  apply safe_succ 7 5 s5_1313 [s6_1077, s6_1119, s6_1145] (by decide) s5_1313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1077_safe
  · subst z; exact s6_1119_safe
  · subst z; exact s6_1145_safe
def s5_1314 : State := ⟨[35,12,104,128], 340282387282576229647756113084927775006, 3, 0, 0, 0⟩
theorem s5_1314_edges : next config 5 s5_1314 = [s6_1078, s6_1140, s6_1133, s6_1146, s6_1126, s6_1131, s6_1135, s6_1137] := by decide
theorem s5_1314_safe : Safe 8 5 s5_1314 := by
  apply safe_succ 7 5 s5_1314 [s6_1078, s6_1140, s6_1133, s6_1146, s6_1126, s6_1131, s6_1135, s6_1137] (by decide) s5_1314_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1078_safe
  · subst z; exact s6_1140_safe
  · subst z; exact s6_1133_safe
  · subst z; exact s6_1146_safe
  · subst z; exact s6_1126_safe
  · subst z; exact s6_1131_safe
  · subst z; exact s6_1135_safe
  · subst z; exact s6_1137_safe
def s5_1315 : State := ⟨[35,12,104,128], 340282387282576229647756113093517709590, 3, 0, 0, 0⟩
theorem s5_1315_edges : next config 5 s5_1315 = [s6_1079, s6_1141, s6_1134, s6_1147, s6_1127, s6_1132, s6_1136, s6_1138] := by decide
theorem s5_1315_safe : Safe 8 5 s5_1315 := by
  apply safe_succ 7 5 s5_1315 [s6_1079, s6_1141, s6_1134, s6_1147, s6_1127, s6_1132, s6_1136, s6_1138] (by decide) s5_1315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1079_safe
  · subst z; exact s6_1141_safe
  · subst z; exact s6_1134_safe
  · subst z; exact s6_1147_safe
  · subst z; exact s6_1127_safe
  · subst z; exact s6_1132_safe
  · subst z; exact s6_1136_safe
  · subst z; exact s6_1138_safe
def s5_1316 : State := ⟨[35,140,67,136], 1481249143206845131456235686847189065203998, 3, 0, 1, 0⟩
theorem s5_1316_edges : next config 5 s5_1316 = [s6_1334, s6_1032] := by decide
theorem s5_1316_safe : Safe 8 5 s5_1316 := by
  apply safe_succ 7 5 s5_1316 [s6_1334, s6_1032] (by decide) s5_1316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1334_safe
  · subst z; exact s6_1032_safe
def s5_1317 : State := ⟨[35,140,96,136], 1481249143206924359618602377232192932741406, 3, 0, 1, 0⟩
theorem s5_1317_edges : next config 5 s5_1317 = [s6_1061, s6_1150, s6_1152] := by decide
theorem s5_1317_safe : Safe 8 5 s5_1317 := by
  apply safe_succ 7 5 s5_1317 [s6_1061, s6_1150, s6_1152] (by decide) s5_1317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1061_safe
  · subst z; exact s6_1150_safe
  · subst z; exact s6_1152_safe
def s5_1318 : State := ⟨[35,140,96,136], 1481249143206924359618602377232201522675990, 3, 0, 1, 0⟩
theorem s5_1318_edges : next config 5 s5_1318 = [s6_1062, s6_1151, s6_1153] := by decide
theorem s5_1318_safe : Safe 8 5 s5_1318 := by
  apply safe_succ 7 5 s5_1318 [s6_1062, s6_1151, s6_1153] (by decide) s5_1318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1062_safe
  · subst z; exact s6_1151_safe
  · subst z; exact s6_1153_safe
def s5_1319 : State := ⟨[43,4,64,145], 44602511244162009098461845115871926773940510, 1, 0, 1, 0⟩
theorem s5_1319_edges : next config 5 s5_1319 = [s6_1184] := by decide
theorem s5_1319_safe : Safe 8 5 s5_1319 := by
  apply safe_succ 7 5 s5_1319 [s6_1184] (by decide) s5_1319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1184_safe
def s5_1320 : State := ⟨[43,4,64,145], 44602511244162009098461845115871935363875094, 1, 0, 1, 0⟩
theorem s5_1320_edges : next config 5 s5_1320 = [s6_1185] := by decide
theorem s5_1320_safe : Safe 8 5 s5_1320 := by
  apply safe_succ 7 5 s5_1320 [s6_1185] (by decide) s5_1320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1185_safe
def s5_1321 : State := ⟨[43,4,64,145], 66902575877958790363070636639305424743498014, 1, 0, 1, 0⟩
theorem s5_1321_edges : next config 5 s5_1321 = [s6_1186] := by decide
theorem s5_1321_safe : Safe 8 5 s5_1321 := by
  apply safe_succ 7 5 s5_1321 [s6_1186] (by decide) s5_1321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1186_safe
def s5_1322 : State := ⟨[43,4,64,145], 66902575877958790363070636639305433333432598, 1, 0, 1, 0⟩
theorem s5_1322_edges : next config 5 s5_1322 = [s6_1187] := by decide
theorem s5_1322_safe : Safe 8 5 s5_1322 := by
  apply safe_succ 7 5 s5_1322 [s6_1187] (by decide) s5_1322_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1187_safe
def s5_1323 : State := ⟨[43,4,67,128], 340282367000166626143659650523445920030, 1, 0, 0, 0⟩
theorem s5_1323_edges : next config 5 s5_1323 = [s6_1358, s6_1176, s6_1163, s6_1180, s6_1160, s6_1165, s6_1167, s6_1171] := by decide
theorem s5_1323_safe : Safe 8 5 s5_1323 := by
  apply safe_succ 7 5 s5_1323 [s6_1358, s6_1176, s6_1163, s6_1180, s6_1160, s6_1165, s6_1167, s6_1171] (by decide) s5_1323_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1358_safe
  · subst z; exact s6_1176_safe
  · subst z; exact s6_1163_safe
  · subst z; exact s6_1180_safe
  · subst z; exact s6_1160_safe
  · subst z; exact s6_1165_safe
  · subst z; exact s6_1167_safe
  · subst z; exact s6_1171_safe
def s5_1324 : State := ⟨[43,4,67,128], 340282367000166626143659650532035854614, 1, 0, 0, 0⟩
theorem s5_1324_edges : next config 5 s5_1324 = [s6_1359, s6_1177, s6_1164, s6_1181, s6_1161, s6_1166, s6_1168, s6_1172] := by decide
theorem s5_1324_safe : Safe 8 5 s5_1324 := by
  apply safe_succ 7 5 s5_1324 [s6_1359, s6_1177, s6_1164, s6_1181, s6_1161, s6_1166, s6_1168, s6_1172] (by decide) s5_1324_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1359_safe
  · subst z; exact s6_1177_safe
  · subst z; exact s6_1164_safe
  · subst z; exact s6_1181_safe
  · subst z; exact s6_1161_safe
  · subst z; exact s6_1166_safe
  · subst z; exact s6_1168_safe
  · subst z; exact s6_1172_safe
def s5_1325 : State := ⟨[43,4,67,129], 1020847100762815390556144527793438392606, 1, 0, 1, 0⟩
theorem s5_1325_edges : next config 5 s5_1325 = [s6_1360, s6_1169] := by decide
theorem s5_1325_safe : Safe 8 5 s5_1325 := by
  apply safe_succ 7 5 s5_1325 [s6_1360, s6_1169] (by decide) s5_1325_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1360_safe
  · subst z; exact s6_1169_safe
def s5_1326 : State := ⟨[43,4,67,130], 1701411834604692317482893742656974815518, 1, 0, 1, 0⟩
theorem s5_1326_edges : next config 5 s5_1326 = [s6_1362] := by decide
theorem s5_1326_safe : Safe 8 5 s5_1326 := by
  apply safe_succ 7 5 s5_1326 [s6_1362] (by decide) s5_1326_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1362_safe
def s5_1327 : State := ⟨[43,4,67,131], 3062541302288446171336392172384047661342, 1, 0, 1, 0⟩
theorem s5_1327_edges : next config 5 s5_1327 = [s6_1364] := by decide
theorem s5_1327_safe : Safe 8 5 s5_1327 := by
  apply safe_succ 7 5 s5_1327 [s6_1364] (by decide) s5_1327_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1364_safe
def s5_1328 : State := ⟨[43,4,67,132], 5784800237655953879043389031838193352990, 1, 0, 1, 0⟩
theorem s5_1328_edges : next config 5 s5_1328 = [s6_1366] := by decide
theorem s5_1328_safe : Safe 8 5 s5_1328 := by
  apply safe_succ 7 5 s5_1328 [s6_1366] (by decide) s5_1328_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1366_safe
def s5_1329 : State := ⟨[43,4,67,136], 87452568298681185110253294815462564102430, 1, 0, 1, 0⟩
theorem s5_1329_edges : next config 5 s5_1329 = [s6_1368] := by decide
theorem s5_1329_safe : Safe 8 5 s5_1329 := by
  apply safe_succ 7 5 s5_1329 [s6_1368] (by decide) s5_1329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1368_safe
def s5_1330 : State := ⟨[43,4,67,144], 22301085480897544079999347667961291407950110, 1, 0, 1, 0⟩
theorem s5_1330_edges : next config 5 s5_1330 = [s6_1370] := by decide
theorem s5_1330_safe : Safe 8 5 s5_1330 := by
  apply safe_succ 7 5 s5_1330 [s6_1370] (by decide) s5_1330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1370_safe
def s5_1331 : State := ⟨[43,4,67,160], 1461501637671185285124623296345678332585834512670, 1, 0, 1, 0⟩
theorem s5_1331_edges : next config 5 s5_1331 = [s6_1372] := by decide
theorem s5_1331_safe : Safe 8 5 s5_1331 := by
  apply safe_succ 7 5 s5_1331 [s6_1372] (by decide) s5_1331_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1372_safe
def s5_1332 : State := ⟨[43,4,67,163], 11692013098987505712550417125359659470177362313502, 1, 0, 1, 0⟩
theorem s5_1332_edges : next config 5 s5_1332 = [s6_1374] := by decide
theorem s5_1332_safe : Safe 8 5 s5_1332 := by
  apply safe_succ 7 5 s5_1332 [s6_1374] (by decide) s5_1332_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1374_safe
def s5_1333 : State := ⟨[43,4,67,171], 2993155353254029458848067475866577019568279749984542, 1, 0, 1, 0⟩
theorem s5_1333_edges : next config 5 s5_1333 = [s6_1376] := by decide
theorem s5_1333_safe : Safe 8 5 s5_1333 := by
  apply safe_succ 7 5 s5_1333 [s6_1376] (by decide) s5_1333_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1376_safe
def s5_1334 : State := ⟨[43,4,67,192], 6277101735386680764176071790128604879731750757393936482590, 1, 0, 1, 0⟩
theorem s5_1334_edges : next config 5 s5_1334 = [s6_1377] := by decide
theorem s5_1334_safe : Safe 8 5 s5_1334 := by
  apply safe_succ 7 5 s5_1334 [s6_1377] (by decide) s5_1334_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1377_safe
def s5_1335 : State := ⟨[43,4,67,195], 50216813883093446111026597752582269792448238868642178072862, 1, 0, 1, 0⟩
theorem s5_1335_edges : next config 5 s5_1335 = [s6_1379] := by decide
theorem s5_1335_safe : Safe 8 5 s5_1335 := by
  apply safe_succ 7 5 s5_1335 [s6_1379] (by decide) s5_1335_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1379_safe
def s5_1336 : State := ⟨[43,4,96,129], 1020847100842043552922834912797305930014, 1, 0, 1, 0⟩
theorem s5_1336_edges : next config 5 s5_1336 = [s6_1188, s6_1184] := by decide
theorem s5_1336_safe : Safe 8 5 s5_1336 := by
  apply safe_succ 7 5 s5_1336 [s6_1188, s6_1184] (by decide) s5_1336_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1188_safe
  · subst z; exact s6_1184_safe
def s5_1337 : State := ⟨[43,4,96,129], 1020847100842043552922834912805895864598, 1, 0, 1, 0⟩
theorem s5_1337_edges : next config 5 s5_1337 = [s6_1189, s6_1185] := by decide
theorem s5_1337_safe : Safe 8 5 s5_1337 := by
  apply safe_succ 7 5 s5_1337 [s6_1189, s6_1185] (by decide) s5_1337_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1189_safe
  · subst z; exact s6_1185_safe
def s5_1338 : State := ⟨[43,4,96,130], 1701411834683920479849584127660842352926, 1, 0, 1, 0⟩
theorem s5_1338_edges : next config 5 s5_1338 = [s6_1190] := by decide
theorem s5_1338_safe : Safe 8 5 s5_1338 := by
  apply safe_succ 7 5 s5_1338 [s6_1190] (by decide) s5_1338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1190_safe
def s5_1339 : State := ⟨[43,4,96,130], 1701411834683920479849584127669432287510, 1, 0, 1, 0⟩
theorem s5_1339_edges : next config 5 s5_1339 = [s6_1191] := by decide
theorem s5_1339_safe : Safe 8 5 s5_1339 := by
  apply safe_succ 7 5 s5_1339 [s6_1191] (by decide) s5_1339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1191_safe
def s5_1340 : State := ⟨[43,4,96,131], 3062541302367674333703082557387915198750, 1, 0, 1, 0⟩
theorem s5_1340_edges : next config 5 s5_1340 = [s6_1192] := by decide
theorem s5_1340_safe : Safe 8 5 s5_1340 := by
  apply safe_succ 7 5 s5_1340 [s6_1192] (by decide) s5_1340_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1192_safe
def s5_1341 : State := ⟨[43,4,96,132], 5784800237735182041410079416842060890398, 1, 0, 1, 0⟩
theorem s5_1341_edges : next config 5 s5_1341 = [s6_1193] := by decide
theorem s5_1341_safe : Safe 8 5 s5_1341 := by
  apply safe_succ 7 5 s5_1341 [s6_1193] (by decide) s5_1341_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1193_safe
def s5_1342 : State := ⟨[43,4,96,132], 5784800237735182041410079416850650824982, 1, 0, 1, 0⟩
theorem s5_1342_edges : next config 5 s5_1342 = [s6_1194] := by decide
theorem s5_1342_safe : Safe 8 5 s5_1342 := by
  apply safe_succ 7 5 s5_1342 [s6_1194] (by decide) s5_1342_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1194_safe
def s5_1343 : State := ⟨[43,4,96,136], 87452568298760413272619985200466431639838, 1, 0, 1, 0⟩
theorem s5_1343_edges : next config 5 s5_1343 = [s6_1195] := by decide
theorem s5_1343_safe : Safe 8 5 s5_1343 := by
  apply safe_succ 7 5 s5_1343 [s6_1195] (by decide) s5_1343_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1195_safe
def s5_1344 : State := ⟨[43,4,96,136], 87452568298760413272619985200475021574422, 1, 0, 1, 0⟩
theorem s5_1344_edges : next config 5 s5_1344 = [s6_1196] := by decide
theorem s5_1344_safe : Safe 8 5 s5_1344 := by
  apply safe_succ 7 5 s5_1344 [s6_1196] (by decide) s5_1344_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1196_safe
def s5_1345 : State := ⟨[43,4,96,144], 22301085480897623308161714358346295275487518, 1, 0, 1, 0⟩
theorem s5_1345_edges : next config 5 s5_1345 = [s6_1197] := by decide
theorem s5_1345_safe : Safe 8 5 s5_1345 := by
  apply safe_succ 7 5 s5_1345 [s6_1197] (by decide) s5_1345_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1197_safe
def s5_1346 : State := ⟨[43,4,96,144], 22301085480897623308161714358346303865422102, 1, 0, 1, 0⟩
theorem s5_1346_edges : next config 5 s5_1346 = [s6_1198] := by decide
theorem s5_1346_safe : Safe 8 5 s5_1346 := by
  apply safe_succ 7 5 s5_1346 [s6_1198] (by decide) s5_1346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1198_safe
def s5_1347 : State := ⟨[43,4,96,160], 1461501637671185285203851458712368717589702050078, 1, 0, 1, 0⟩
theorem s5_1347_edges : next config 5 s5_1347 = [s6_1199] := by decide
theorem s5_1347_safe : Safe 8 5 s5_1347 := by
  apply safe_succ 7 5 s5_1347 [s6_1199] (by decide) s5_1347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1199_safe
def s5_1348 : State := ⟨[43,4,96,160], 1461501637671185285203851458712368717598291984662, 1, 0, 1, 0⟩
theorem s5_1348_edges : next config 5 s5_1348 = [s6_1200] := by decide
theorem s5_1348_safe : Safe 8 5 s5_1348 := by
  apply safe_succ 7 5 s5_1348 [s6_1200] (by decide) s5_1348_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1200_safe
def s5_1349 : State := ⟨[43,4,96,161], 2923003275002088203407536291428651737254224527638, 1, 0, 1, 0⟩
theorem s5_1349_edges : next config 5 s5_1349 = [s6_1201] := by decide
theorem s5_1349_safe : Safe 8 5 s5_1349 := by
  apply safe_succ 7 5 s5_1349 [s6_1201] (by decide) s5_1349_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1201_safe
def s5_1350 : State := ⟨[43,4,96,163], 11692013098987505712629645287726349855181229850910, 1, 0, 1, 0⟩
theorem s5_1350_edges : next config 5 s5_1350 = [s6_1202] := by decide
theorem s5_1350_safe : Safe 8 5 s5_1350 := by
  apply safe_succ 7 5 s5_1350 [s6_1202] (by decide) s5_1350_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1202_safe
def s5_1351 : State := ⟨[43,4,96,163], 11692013098987505712629645287726349855189819785494, 1, 0, 1, 0⟩
theorem s5_1351_edges : next config 5 s5_1351 = [s6_1203] := by decide
theorem s5_1351_safe : Safe 8 5 s5_1351 := by
  apply safe_succ 7 5 s5_1351 [s6_1203] (by decide) s5_1351_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1203_safe
def s5_1352 : State := ⟨[43,4,96,171], 2993155353254029458848146704028943709953283617521950, 1, 0, 1, 0⟩
theorem s5_1352_edges : next config 5 s5_1352 = [s6_1204] := by decide
theorem s5_1352_safe : Safe 8 5 s5_1352 := by
  apply safe_succ 7 5 s5_1352 [s6_1204] (by decide) s5_1352_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1204_safe
def s5_1353 : State := ⟨[43,4,96,171], 2993155353254029458848146704028943709953292207456534, 1, 0, 1, 0⟩
theorem s5_1353_edges : next config 5 s5_1353 = [s6_1205] := by decide
theorem s5_1353_safe : Safe 8 5 s5_1353 := by
  apply safe_succ 7 5 s5_1353 [s6_1205] (by decide) s5_1353_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1205_safe
def s5_1354 : State := ⟨[43,4,96,192], 6277101735386680764176071790207833042098441142397804019998, 1, 0, 1, 0⟩
theorem s5_1354_edges : next config 5 s5_1354 = [s6_1206] := by decide
theorem s5_1354_safe : Safe 8 5 s5_1354 := by
  apply safe_succ 7 5 s5_1354 [s6_1206] (by decide) s5_1354_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1206_safe
def s5_1355 : State := ⟨[43,4,96,192], 6277101735386680764176071790207833042098441142406393954582, 1, 0, 1, 0⟩
theorem s5_1355_edges : next config 5 s5_1355 = [s6_1207] := by decide
theorem s5_1355_safe : Safe 8 5 s5_1355 := by
  apply safe_succ 7 5 s5_1355 [s6_1207] (by decide) s5_1355_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1207_safe
def s5_1356 : State := ⟨[43,4,96,224], 26959946667150639794667015087359913040637311048536658179037379756318, 1, 0, 1, 0⟩
theorem s5_1356_edges : next config 5 s5_1356 = [s6_1208] := by decide
theorem s5_1356_safe : Safe 8 5 s5_1356 := by
  apply safe_succ 7 5 s5_1356 [s6_1208] (by decide) s5_1356_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1208_safe
def s5_1357 : State := ⟨[43,4,96,224], 26959946667150639794667015087359913040637311048536658179045969690902, 1, 0, 1, 0⟩
theorem s5_1357_edges : next config 5 s5_1357 = [s6_1209] := by decide
theorem s5_1357_safe : Safe 8 5 s5_1357 := by
  apply safe_succ 7 5 s5_1357 [s6_1209] (by decide) s5_1357_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1209_safe
def s5_1358 : State := ⟨[43,4,104,128], 340282387282576229647756121881020793118, 1, 0, 0, 0⟩
theorem s5_1358_edges : next config 5 s5_1358 = [s6_1156, s6_1204, s6_1193, s6_1210, s6_1190, s6_1195, s6_1197, s6_1199] := by decide
theorem s5_1358_safe : Safe 8 5 s5_1358 := by
  apply safe_succ 7 5 s5_1358 [s6_1156, s6_1204, s6_1193, s6_1210, s6_1190, s6_1195, s6_1197, s6_1199] (by decide) s5_1358_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1156_safe
  · subst z; exact s6_1204_safe
  · subst z; exact s6_1193_safe
  · subst z; exact s6_1210_safe
  · subst z; exact s6_1190_safe
  · subst z; exact s6_1195_safe
  · subst z; exact s6_1197_safe
  · subst z; exact s6_1199_safe
def s5_1359 : State := ⟨[43,4,104,128], 340282387282576229647756121889610727702, 1, 0, 0, 0⟩
theorem s5_1359_edges : next config 5 s5_1359 = [s6_1157, s6_1205, s6_1194, s6_1211, s6_1191, s6_1196, s6_1198, s6_1200] := by decide
theorem s5_1359_safe : Safe 8 5 s5_1359 := by
  apply safe_succ 7 5 s5_1359 [s6_1157, s6_1205, s6_1194, s6_1211, s6_1191, s6_1196, s6_1198, s6_1200] (by decide) s5_1359_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1157_safe
  · subst z; exact s6_1205_safe
  · subst z; exact s6_1194_safe
  · subst z; exact s6_1211_safe
  · subst z; exact s6_1191_safe
  · subst z; exact s6_1196_safe
  · subst z; exact s6_1198_safe
  · subst z; exact s6_1200_safe
def s5_1360 : State := ⟨[49,4,64,145], 44601830679428167221534918367211182738309406, 1, 1, 1, 0⟩
theorem s5_1360_edges : next config 5 s5_1360 = [s6_1216, s6_1213] := by decide
theorem s5_1360_safe : Safe 8 5 s5_1360 := by
  apply safe_succ 7 5 s5_1360 [s6_1216, s6_1213] (by decide) s5_1360_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1216_safe
  · subst z; exact s6_1213_safe
def s5_1361 : State := ⟨[49,4,64,145], 44601830679428167221534918367211182738313494, 3, 2, 1, 0⟩
theorem s5_1361_edges : next config 5 s5_1361 = [s6_1214] := by decide
theorem s5_1361_safe : Safe 8 5 s5_1361 := by
  apply safe_succ 7 5 s5_1361 [s6_1214] (by decide) s5_1361_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1214_safe
def s5_1362 : State := ⟨[49,4,64,145], 44601830679428167221534918367211182740406550, 3, 2, 1, 0⟩
theorem s5_1362_edges : next config 5 s5_1362 = [s6_1217, s6_1215] := by decide
theorem s5_1362_safe : Safe 8 5 s5_1362 := by
  apply safe_succ 7 5 s5_1362 [s6_1217, s6_1215] (by decide) s5_1362_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1217_safe
  · subst z; exact s6_1215_safe
def s5_1363 : State := ⟨[49,4,104,145], 44601830679448528859301084301972723533545750, 1, 0, 1, 0⟩
theorem s5_1363_edges : next config 5 s5_1363 = [s6_1218] := by decide
theorem s5_1363_safe : Safe 8 5 s5_1363 := by
  apply safe_succ 7 5 s5_1363 [s6_1218] (by decide) s5_1363_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1218_safe
def s5_1364 : State := ⟨[49,12,96,145], 44601830679428246449697432631548776282263830, 3, 0, 1, 0⟩
theorem s5_1364_edges : next config 5 s5_1364 = [s6_1214, s6_1218] := by decide
theorem s5_1364_safe : Safe 8 5 s5_1364 := by
  apply safe_succ 7 5 s5_1364 [s6_1214, s6_1218] (by decide) s5_1364_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1214_safe
  · subst z; exact s6_1218_safe
def s5_1365 : State := ⟨[49,21,96,145], 44601830679428246449697432631548776284356886, 3, 0, 1, 0⟩
theorem s5_1365_edges : next config 5 s5_1365 = [s6_1221] := by decide
theorem s5_1365_safe : Safe 8 5 s5_1365 := by
  apply safe_succ 7 5 s5_1365 [s6_1221] (by decide) s5_1365_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1221_safe
def s5_1366 : State := ⟨[53,4,96,145], 44601830679428246449697432639993025585676566, 1, 0, 1, 0⟩
theorem s5_1366_edges : next config 5 s5_1366 = [s6_1223] := by decide
theorem s5_1366_safe : Safe 8 5 s5_1366 := by
  apply safe_succ 7 5 s5_1366 [s6_1223] (by decide) s5_1366_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1223_safe
def s5_1367 : State := ⟨[65,4,64,145], 44602511244162009098461882009351243740287254, 3, 2, 1, 0⟩
theorem s5_1367_edges : next config 5 s5_1367 = [s6_2, s6_1226] := by decide
theorem s5_1367_safe : Safe 8 5 s5_1367 := by
  apply safe_succ 7 5 s5_1367 [s6_2, s6_1226] (by decide) s5_1367_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_2_safe
  · subst z; exact s6_1226_safe
def s5_1368 : State := ⟨[65,4,64,145], 66902575877958790363070673532784741709844758, 3, 2, 1, 0⟩
theorem s5_1368_edges : next config 5 s5_1368 = [s6_5, s6_1228] := by decide
theorem s5_1368_safe : Safe 8 5 s5_1368 := by
  apply safe_succ 7 5 s5_1368 [s6_5, s6_1228] (by decide) s5_1368_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_5_safe
  · subst z; exact s6_1228_safe
def s5_1369 : State := ⟨[65,4,64,146], 89204682205957097258460245303862830288670998, 3, 2, 1, 0⟩
theorem s5_1369_edges : next config 5 s5_1369 = [s6_7, s6_1230] := by decide
theorem s5_1369_safe : Safe 8 5 s5_1369 := by
  apply safe_succ 7 5 s5_1369 [s6_7, s6_1230] (by decide) s5_1369_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_7_safe
  · subst z; exact s6_1230_safe
def s5_1370 : State := ⟨[65,4,64,146], 111504066275020036646142110078081464721805590, 3, 2, 1, 0⟩
theorem s5_1370_edges : next config 5 s5_1370 = [s6_10, s6_1231] := by decide
theorem s5_1370_safe : Safe 8 5 s5_1370 := by
  apply safe_succ 7 5 s5_1370 [s6_10, s6_1231] (by decide) s5_1370_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_10_safe
  · subst z; exact s6_1231_safe
def s5_1371 : State := ⟨[65,4,64,162], 5846006551025023507419431648237345348007994921238, 3, 2, 1, 0⟩
theorem s5_1371_edges : next config 5 s5_1371 = [s6_12, s6_1232] := by decide
theorem s5_1371_safe : Safe 8 5 s5_1371 := by
  apply safe_succ 7 5 s5_1371 [s6_12, s6_1232] (by decide) s5_1371_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_12_safe
  · subst z; exact s6_1232_safe
def s5_1372 : State := ⟨[65,4,64,162], 7307508186994796957939362627100129937936854618390, 3, 2, 1, 0⟩
theorem s5_1372_edges : next config 5 s5_1372 = [s6_15, s6_1233] := by decide
theorem s5_1372_safe : Safe 8 5 s5_1372 := by
  apply safe_succ 7 5 s5_1372 [s6_15, s6_1233] (by decide) s5_1372_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_15_safe
  · subst z; exact s6_1233_safe
def s5_1373 : State := ⟨[65,4,64,176], 95780971326419139128294233276893560963659213834359062, 3, 2, 1, 0⟩
theorem s5_1373_edges : next config 5 s5_1373 = [s6_23, s6_1234] := by decide
theorem s5_1373_safe : Safe 8 5 s5_1373 := by
  apply safe_succ 7 5 s5_1373 [s6_23, s6_1234] (by decide) s5_1373_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_23_safe
  · subst z; exact s6_1234_safe
def s5_1374 : State := ⟨[65,4,64,176], 95782432805755724832681813820190558974030508260921622, 3, 2, 1, 0⟩
theorem s5_1374_edges : next config 5 s5_1374 = [s6_25, s6_1235] := by decide
theorem s5_1374_safe : Safe 8 5 s5_1374 := by
  apply safe_succ 7 5 s5_1374 [s6_25, s6_1235] (by decide) s5_1374_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_25_safe
  · subst z; exact s6_1235_safe
def s5_1375 : State := ⟨[65,4,96,129], 1020847100842043552959728392114272276758, 3, 2, 1, 0⟩
theorem s5_1375_edges : next config 5 s5_1375 = [s6_1237, s6_1226] := by decide
theorem s5_1375_safe : Safe 8 5 s5_1375 := by
  apply safe_succ 7 5 s5_1375 [s6_1237, s6_1226] (by decide) s5_1375_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1237_safe
  · subst z; exact s6_1226_safe
def s5_1376 : State := ⟨[65,4,96,129], 1020847102109694153187957793610975478038, 3, 2, 1, 0⟩
theorem s5_1376_edges : next config 5 s5_1376 = [s6_1238, s6_1227] := by decide
theorem s5_1376_safe : Safe 8 5 s5_1376 := by
  apply safe_succ 7 5 s5_1376 [s6_1238, s6_1227] (by decide) s5_1376_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1238_safe
  · subst z; exact s6_1227_safe
def s5_1377 : State := ⟨[65,4,96,130], 1701411834683920479886477606977808699670, 3, 2, 1, 0⟩
theorem s5_1377_edges : next config 5 s5_1377 = [s6_1240, s6_1230, s6_1232] := by decide
theorem s5_1377_safe : Safe 8 5 s5_1377 := by
  apply safe_succ 7 5 s5_1377 [s6_1240, s6_1230, s6_1232] (by decide) s5_1377_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1240_safe
  · subst z; exact s6_1230_safe
  · subst z; exact s6_1232_safe
def s5_1378 : State := ⟨[65,4,96,130], 1701411835951571080114707008474511900950, 3, 2, 1, 0⟩
theorem s5_1378_edges : next config 5 s5_1378 = [s6_1241] := by decide
theorem s5_1378_safe : Safe 8 5 s5_1378 := by
  apply safe_succ 7 5 s5_1378 [s6_1241] (by decide) s5_1378_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1241_safe
def s5_1379 : State := ⟨[65,4,96,132], 5784800237735182041446972896159027237142, 3, 2, 1, 0⟩
theorem s5_1379_edges : next config 5 s5_1379 = [s6_1243] := by decide
theorem s5_1379_safe : Safe 8 5 s5_1379 := by
  apply safe_succ 7 5 s5_1379 [s6_1243] (by decide) s5_1379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1243_safe
def s5_1380 : State := ⟨[65,4,96,132], 5784800239002832641675202297655730438422, 3, 2, 1, 0⟩
theorem s5_1380_edges : next config 5 s5_1380 = [s6_1244] := by decide
theorem s5_1380_safe : Safe 8 5 s5_1380 := by
  apply safe_succ 7 5 s5_1380 [s6_1244] (by decide) s5_1380_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1244_safe
def s5_1381 : State := ⟨[65,4,96,136], 87452568298760413272656878679783397986582, 3, 2, 1, 0⟩
theorem s5_1381_edges : next config 5 s5_1381 = [s6_1246] := by decide
theorem s5_1381_safe : Safe 8 5 s5_1381 := by
  apply safe_succ 7 5 s5_1381 [s6_1246] (by decide) s5_1381_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1246_safe
def s5_1382 : State := ⟨[65,4,96,136], 87452568300028063872885108081280101187862, 3, 2, 1, 0⟩
theorem s5_1382_edges : next config 5 s5_1382 = [s6_1247] := by decide
theorem s5_1382_safe : Safe 8 5 s5_1382 := by
  apply safe_succ 7 5 s5_1382 [s6_1247] (by decide) s5_1382_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1247_safe
def s5_1383 : State := ⟨[65,4,96,136], 1481249143206924359618639270720305992106262, 3, 2, 1, 0⟩
theorem s5_1383_edges : next config 5 s5_1383 = [s6_1249] := by decide
theorem s5_1383_safe : Safe 8 5 s5_1383 := by
  apply safe_succ 7 5 s5_1383 [s6_1249] (by decide) s5_1383_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1249_safe
def s5_1384 : State := ⟨[65,4,96,140], 1394136857275164112972015371217773329977622, 3, 2, 1, 0⟩
theorem s5_1384_edges : next config 5 s5_1384 = [s6_1250] := by decide
theorem s5_1384_safe : Safe 8 5 s5_1384 := by
  apply safe_succ 7 5 s5_1384 [s6_1250] (by decide) s5_1384_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1250_safe
def s5_1385 : State := ⟨[65,4,96,144], 22301085480897623308161751251825612241834262, 3, 2, 1, 0⟩
theorem s5_1385_edges : next config 5 s5_1385 = [s6_1251, s6_1231, s6_1234] := by decide
theorem s5_1385_safe : Safe 8 5 s5_1385 := by
  apply safe_succ 7 5 s5_1385 [s6_1251, s6_1231, s6_1234] (by decide) s5_1385_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1251_safe
  · subst z; exact s6_1231_safe
  · subst z; exact s6_1234_safe
def s5_1386 : State := ⟨[65,4,96,144], 22301085480898890958761979481227108945035542, 3, 2, 1, 0⟩
theorem s5_1386_edges : next config 5 s5_1386 = [s6_1252] := by decide
theorem s5_1386_safe : Safe 8 5 s5_1386 := by
  apply safe_succ 7 5 s5_1386 [s6_1252] (by decide) s5_1386_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1252_safe
def s5_1387 : State := ⟨[65,4,96,145], 44601830679428246449697469524473973747941654, 1, 1, 1, 0⟩
theorem s5_1387_edges : next config 5 s5_1387 = [s6_1292, s6_1279, s6_1236, s6_1276, s6_1254] := by decide
theorem s5_1387_safe : Safe 8 5 s5_1387 := by
  apply safe_succ 7 5 s5_1387 [s6_1292, s6_1279, s6_1236, s6_1276, s6_1254] (by decide) s5_1387_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_1292_safe
  · subst z; exact s6_1279_safe
  · subst z; exact s6_1236_safe
  · subst z; exact s6_1276_safe
  · subst z; exact s6_1254_safe
def s5_1388 : State := ⟨[65,4,96,160], 1461501637671185285203851458749262196906668396822, 3, 2, 1, 0⟩
theorem s5_1388_edges : next config 5 s5_1388 = [s6_1255, s6_1233, s6_1235] := by decide
theorem s5_1388_safe : Safe 8 5 s5_1388 := by
  apply safe_succ 7 5 s5_1388 [s6_1255, s6_1233, s6_1235] (by decide) s5_1388_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1255_safe
  · subst z; exact s6_1233_safe
  · subst z; exact s6_1235_safe
def s5_1389 : State := ⟨[65,4,96,160], 1461501637671185286471502058977491598403371598102, 3, 2, 1, 0⟩
theorem s5_1389_edges : next config 5 s5_1389 = [s6_1256] := by decide
theorem s5_1389_safe : Safe 8 5 s5_1389 := by
  apply safe_succ 7 5 s5_1389 [s6_1256] (by decide) s5_1389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1256_safe
def s5_1390 : State := ⟨[65,4,96,192], 6277101735386680764176071790207833042135334621714770366742, 3, 2, 1, 0⟩
theorem s5_1390_edges : next config 5 s5_1390 = [s6_1258] := by decide
theorem s5_1390_safe : Safe 8 5 s5_1390 := by
  apply safe_succ 7 5 s5_1390 [s6_1258] (by decide) s5_1390_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1258_safe
def s5_1391 : State := ⟨[65,4,96,192], 6277101735386680764176071791475483642363564023211473568022, 3, 2, 1, 0⟩
theorem s5_1391_edges : next config 5 s5_1391 = [s6_1259] := by decide
theorem s5_1391_safe : Safe 8 5 s5_1391 := by
  apply safe_succ 7 5 s5_1391 [s6_1259] (by decide) s5_1391_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1259_safe
def s5_1392 : State := ⟨[65,4,96,193], 12554203470773361528011861213415499458237690066178804879638, 3, 2, 1, 0⟩
theorem s5_1392_edges : next config 5 s5_1392 = [s6_1261] := by decide
theorem s5_1392_safe : Safe 8 5 s5_1392 := by
  apply safe_succ 7 5 s5_1392 [s6_1261] (by decide) s5_1392_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1261_safe
def s5_1393 : State := ⟨[65,4,96,193], 12554203470773361528011861214683150058465919467675508080918, 3, 2, 1, 0⟩
theorem s5_1393_edges : next config 5 s5_1393 = [s6_1262] := by decide
theorem s5_1393_safe : Safe 8 5 s5_1393 := by
  apply safe_succ 7 5 s5_1393 [s6_1262] (by decide) s5_1393_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1262_safe
def s5_1394 : State := ⟨[65,4,96,224], 26959946667150639794667015087359913040637311048573551658354346103062, 3, 2, 1, 0⟩
theorem s5_1394_edges : next config 5 s5_1394 = [s6_1264] := by decide
theorem s5_1394_safe : Safe 8 5 s5_1394 := by
  apply safe_succ 7 5 s5_1394 [s6_1264] (by decide) s5_1394_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1264_safe
def s5_1395 : State := ⟨[65,4,96,224], 26959946667150639794667015087359913041904961648801781059851049304342, 3, 2, 1, 0⟩
theorem s5_1395_edges : next config 5 s5_1395 = [s6_1265] := by decide
theorem s5_1395_safe : Safe 8 5 s5_1395 := by
  apply safe_succ 7 5 s5_1395 [s6_1265] (by decide) s5_1395_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1265_safe
def s5_1396 : State := ⟨[65,4,96,224], 458319093341560876509339256479674003818831621809222711356012110086422, 3, 2, 1, 0⟩
theorem s5_1396_edges : next config 5 s5_1396 = [s6_1267] := by decide
theorem s5_1396_safe : Safe 8 5 s5_1396 := by
  apply safe_succ 7 5 s5_1396 [s6_1267] (by decide) s5_1396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1267_safe
def s5_1397 : State := ⟨[65,4,96,228], 431359146674410236714672241392654373146462127986910368276405203042582, 3, 2, 1, 0⟩
theorem s5_1397_edges : next config 5 s5_1397 = [s6_1268] := by decide
theorem s5_1397_safe : Safe 8 5 s5_1397 := by
  apply safe_succ 7 5 s5_1397 [s6_1268] (by decide) s5_1397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1268_safe
def s5_1398 : State := ⟨[65,4,100,145], 44602511244163355977224624503090333987438870, 1, 0, 1, 0⟩
theorem s5_1398_edges : next config 5 s5_1398 = [] := by decide
theorem s5_1398_safe : Safe 8 5 s5_1398 := by
  apply safe_succ 7 5 s5_1398 [] (by decide) s5_1398_edges
  simp
def s5_1399 : State := ⟨[65,4,100,145], 66902575877960137241833416026523831956996374, 1, 0, 1, 0⟩
theorem s5_1399_edges : next config 5 s5_1399 = [] := by decide
theorem s5_1399_safe : Safe 8 5 s5_1399 := by
  apply safe_succ 7 5 s5_1399 [] (by decide) s5_1399_edges
  simp
def s5_1400 : State := ⟨[65,4,104,128], 340282387282576229684649601197987139862, 3, 2, 0, 0⟩
theorem s5_1400_edges : next config 5 s5_1400 = [s6_1261, s6_1243, s6_1269, s6_1240, s6_1246, s6_1251, s6_1255] := by decide
theorem s5_1400_safe : Safe 8 5 s5_1400 := by
  apply safe_succ 7 5 s5_1400 [s6_1261, s6_1243, s6_1269, s6_1240, s6_1246, s6_1251, s6_1255] (by decide) s5_1400_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1261_safe
  · subst z; exact s6_1243_safe
  · subst z; exact s6_1269_safe
  · subst z; exact s6_1240_safe
  · subst z; exact s6_1246_safe
  · subst z; exact s6_1251_safe
  · subst z; exact s6_1255_safe
def s5_1401 : State := ⟨[65,4,104,128], 340282388550226829912879002694690341142, 3, 2, 0, 0⟩
theorem s5_1401_edges : next config 5 s5_1401 = [s6_1262, s6_1244, s6_1270, s6_1241, s6_1247, s6_1252, s6_1256] := by decide
theorem s5_1401_safe : Safe 8 5 s5_1401 := by
  apply safe_succ 7 5 s5_1401 [s6_1262, s6_1244, s6_1270, s6_1241, s6_1247, s6_1252, s6_1256] (by decide) s5_1401_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1262_safe
  · subst z; exact s6_1244_safe
  · subst z; exact s6_1270_safe
  · subst z; exact s6_1241_safe
  · subst z; exact s6_1247_safe
  · subst z; exact s6_1252_safe
  · subst z; exact s6_1256_safe
def s5_1402 : State := ⟨[65,4,104,128], 340282711801129888111376384354007712022, 3, 2, 0, 0⟩
theorem s5_1402_edges : next config 5 s5_1402 = [s6_1263, s6_1245, s6_1271, s6_1242, s6_1248, s6_1253, s6_1257] := by decide
theorem s5_1402_safe : Safe 8 5 s5_1402 := by
  apply safe_succ 7 5 s5_1402 [s6_1263, s6_1245, s6_1271, s6_1242, s6_1248, s6_1253, s6_1257] (by decide) s5_1402_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1263_safe
  · subst z; exact s6_1245_safe
  · subst z; exact s6_1271_safe
  · subst z; exact s6_1242_safe
  · subst z; exact s6_1248_safe
  · subst z; exact s6_1253_safe
  · subst z; exact s6_1257_safe
def s5_1403 : State := ⟨[65,4,104,140], 1399581375166181537991081035360628872642838, 1, 0, 1, 0⟩
theorem s5_1403_edges : next config 5 s5_1403 = [] := by decide
theorem s5_1403_safe : Safe 8 5 s5_1403 := by
  apply safe_succ 7 5 s5_1403 [] (by decide) s5_1403_edges
  simp
def s5_1404 : State := ⟨[65,4,104,140], 1481249143227206769222290941144253243392278, 1, 0, 1, 0⟩
theorem s5_1404_edges : next config 5 s5_1404 = [] := by decide
theorem s5_1404_safe : Safe 8 5 s5_1404 := by
  apply safe_succ 7 5 s5_1404 [] (by decide) s5_1404_edges
  simp
def s5_1405 : State := ⟨[65,4,104,145], 44602511244182370736228047944112784535519510, 1, 0, 1, 0⟩
theorem s5_1405_edges : next config 5 s5_1405 = [s6_1295, s6_1280, s6_1274, s6_1277] := by decide
theorem s5_1405_safe : Safe 8 5 s5_1405 := by
  apply safe_succ 7 5 s5_1405 [s6_1295, s6_1280, s6_1274, s6_1277] (by decide) s5_1405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1295_safe
  · subst z; exact s6_1280_safe
  · subst z; exact s6_1274_safe
  · subst z; exact s6_1277_safe
def s5_1406 : State := ⟨[65,4,104,145], 66902575877979152000836839467546282505077014, 1, 0, 1, 0⟩
theorem s5_1406_edges : next config 5 s5_1406 = [s6_1296, s6_1281, s6_1275, s6_1278] := by decide
theorem s5_1406_safe : Safe 8 5 s5_1406 := by
  apply safe_succ 7 5 s5_1406 [s6_1296, s6_1281, s6_1275, s6_1278] (by decide) s5_1406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1296_safe
  · subst z; exact s6_1281_safe
  · subst z; exact s6_1275_safe
  · subst z; exact s6_1278_safe
def s5_1407 : State := ⟨[65,4,104,146], 89204682205977458896226411238624371083903254, 1, 0, 1, 0⟩
theorem s5_1407_edges : next config 5 s5_1407 = [s6_1282] := by decide
theorem s5_1407_safe : Safe 8 5 s5_1407 := by
  apply safe_succ 7 5 s5_1407 [s6_1282] (by decide) s5_1407_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1282_safe
def s5_1408 : State := ⟨[65,4,104,146], 111504066275040398283908276012843005517037846, 1, 0, 1, 0⟩
theorem s5_1408_edges : next config 5 s5_1408 = [s6_1283] := by decide
theorem s5_1408_safe : Safe 8 5 s5_1408 := by
  apply safe_succ 7 5 s5_1408 [s6_1283] (by decide) s5_1408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1283_safe
def s5_1409 : State := ⟨[65,4,104,162], 5846006551025023527781069414403280109548790153494, 1, 0, 1, 0⟩
theorem s5_1409_edges : next config 5 s5_1409 = [s6_1284] := by decide
theorem s5_1409_safe : Safe 8 5 s5_1409 := by
  apply safe_succ 7 5 s5_1409 [s6_1284] (by decide) s5_1409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1284_safe
def s5_1410 : State := ⟨[65,4,104,162], 7307508186994796978301000393266064699477649850646, 1, 0, 1, 0⟩
theorem s5_1410_edges : next config 5 s5_1410 = [s6_1285] := by decide
theorem s5_1410_safe : Safe 8 5 s5_1410 := by
  apply safe_succ 7 5 s5_1410 [s6_1285] (by decide) s5_1410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1285_safe
def s5_1411 : State := ⟨[65,4,104,176], 95780971326419139128314594914659726898420754629591318, 1, 0, 1, 0⟩
theorem s5_1411_edges : next config 5 s5_1411 = [s6_1286] := by decide
theorem s5_1411_safe : Safe 8 5 s5_1411 := by
  apply safe_succ 7 5 s5_1411 [s6_1286] (by decide) s5_1411_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1286_safe
def s5_1412 : State := ⟨[65,4,104,176], 95782432805755724832702175457956724908792049056153878, 1, 0, 1, 0⟩
theorem s5_1412_edges : next config 5 s5_1412 = [s6_1287] := by decide
theorem s5_1412_safe : Safe 8 5 s5_1412 := by
  apply safe_succ 7 5 s5_1412 [s6_1287] (by decide) s5_1412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1287_safe
def s5_1413 : State := ⟨[65,4,104,228], 431359146674410236714672241398098891036211902405747803017764042506518, 1, 0, 1, 0⟩
theorem s5_1413_edges : next config 5 s5_1413 = [] := by decide
theorem s5_1413_safe : Safe 8 5 s5_1413 := by
  apply safe_succ 7 5 s5_1413 [] (by decide) s5_1413_edges
  simp
def s5_1414 : State := ⟨[65,4,104,228], 458319093341560876509339256479674003839114031412874381779959361372438, 1, 0, 1, 0⟩
theorem s5_1414_edges : next config 5 s5_1414 = [] := by decide
theorem s5_1414_safe : Safe 8 5 s5_1414 := by
  apply safe_succ 7 5 s5_1414 [] (by decide) s5_1414_edges
  simp
def s5_1415 : State := ⟨[65,4,104,236], 110427941548649020598956093796438192039475761146371283525920493859307798, 1, 0, 1, 0⟩
theorem s5_1415_edges : next config 5 s5_1415 = [] := by decide
theorem s5_1415_safe : Safe 8 5 s5_1415 := by
  apply safe_succ 7 5 s5_1415 [] (by decide) s5_1415_edges
  simp
def s5_1416 : State := ⟨[65,4,104,236], 117329687895439584386390849658709772974056135103126256087364109791723798, 1, 0, 1, 0⟩
theorem s5_1416_edges : next config 5 s5_1416 = [] := by decide
theorem s5_1416_safe : Safe 8 5 s5_1416 := by
  apply safe_succ 7 5 s5_1416 [] (by decide) s5_1416_edges
  simp
def s5_1417 : State := ⟨[65,4,108,129], 1020847445643006815038125599217544134934, 1, 0, 1, 0⟩
theorem s5_1417_edges : next config 5 s5_1417 = [s6_1274] := by decide
theorem s5_1417_safe : Safe 8 5 s5_1417 := by
  apply safe_succ 7 5 s5_1417 [s6_1274] (by decide) s5_1417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1274_safe
def s5_1418 : State := ⟨[65,4,108,130], 1701412179484883741964874814081080557846, 1, 0, 1, 0⟩
theorem s5_1418_edges : next config 5 s5_1418 = [] := by decide
theorem s5_1418_safe : Safe 8 5 s5_1418 := by
  apply safe_succ 7 5 s5_1418 [] (by decide) s5_1418_edges
  simp
def s5_1419 : State := ⟨[65,4,108,132], 5784800582536145303525370103262299095318, 1, 0, 1, 0⟩
theorem s5_1419_edges : next config 5 s5_1419 = [] := by decide
theorem s5_1419_safe : Safe 8 5 s5_1419 := by
  apply safe_succ 7 5 s5_1419 [] (by decide) s5_1419_edges
  simp
def s5_1420 : State := ⟨[65,4,108,136], 87452568643561376534735275886886669844758, 1, 0, 1, 0⟩
theorem s5_1420_edges : next config 5 s5_1420 = [] := by decide
theorem s5_1420_safe : Safe 8 5 s5_1420 := by
  apply safe_succ 7 5 s5_1420 [] (by decide) s5_1420_edges
  simp
def s5_1421 : State := ⟨[65,4,108,144], 22301085481242424271423829649032715513692438, 1, 0, 1, 0⟩
theorem s5_1421_edges : next config 5 s5_1421 = [] := by decide
theorem s5_1421_safe : Safe 8 5 s5_1421 := by
  apply safe_succ 7 5 s5_1421 [] (by decide) s5_1421_edges
  simp
def s5_1422 : State := ⟨[65,4,108,160], 1461501637671185630004814720827659404009940254998, 1, 0, 1, 0⟩
theorem s5_1422_edges : next config 5 s5_1422 = [] := by decide
theorem s5_1422_safe : Safe 8 5 s5_1422 := by
  apply safe_succ 7 5 s5_1422 [] (by decide) s5_1422_edges
  simp
def s5_1423 : State := ⟨[65,4,108,192], 6277101735386680764176072135008796304213731828818042224918, 1, 0, 1, 0⟩
theorem s5_1423_edges : next config 5 s5_1423 = [] := by decide
theorem s5_1423_safe : Safe 8 5 s5_1423 := by
  apply safe_succ 7 5 s5_1423 [] (by decide) s5_1423_edges
  simp
def s5_1424 : State := ⟨[65,4,108,193], 12554203470773361528011861558216462720316087273282076737814, 1, 0, 1, 0⟩
theorem s5_1424_edges : next config 5 s5_1424 = [] := by decide
theorem s5_1424_safe : Safe 8 5 s5_1424 := by
  apply safe_succ 7 5 s5_1424 [] (by decide) s5_1424_edges
  simp
def s5_1425 : State := ⟨[65,4,108,224], 26959946667150639794667015087359913385438274310651948865457617961238, 1, 0, 1, 0⟩
theorem s5_1425_edges : next config 5 s5_1425 = [] := by decide
theorem s5_1425_safe : Safe 8 5 s5_1425 := by
  apply safe_succ 7 5 s5_1425 [] (by decide) s5_1425_edges
  simp
def s5_1426 : State := ⟨[65,4,108,232], 6901746346790563787434755862277365735162910102058497931546878231511318, 1, 0, 1, 0⟩
theorem s5_1426_edges : next config 5 s5_1426 = [] := by decide
theorem s5_1426_safe : Safe 8 5 s5_1426 := by
  apply safe_succ 7 5 s5_1426 [] (by decide) s5_1426_edges
  simp
def s5_1427 : State := ⟨[65,4,108,236], 110427941548649020598956093796432747521929544684614296258984741588500758, 1, 0, 1, 0⟩
theorem s5_1427_edges : next config 5 s5_1427 = [] := by decide
theorem s5_1427_safe : Safe 8 5 s5_1427 := by
  apply safe_succ 7 5 s5_1427 [] (by decide) s5_1427_edges
  simp
def s5_1428 : State := ⟨[65,4,236,132], 110427941548649020598956093796438192039475761146371283525920493859307798, 1, 0, 1, 0⟩
theorem s5_1428_edges : next config 5 s5_1428 = [] := by decide
theorem s5_1428_safe : Safe 8 5 s5_1428 := by
  apply safe_succ 7 5 s5_1428 [] (by decide) s5_1428_edges
  simp
def s5_1429 : State := ⟨[65,4,241,145], 3533694129556768659166595001530439542899129882077862312516901239869473046, 1, 0, 1, 0⟩
theorem s5_1429_edges : next config 5 s5_1429 = [s6_1288] := by decide
theorem s5_1429_safe : Safe 8 5 s5_1429 := by
  apply safe_succ 7 5 s5_1429 [s6_1288] (by decide) s5_1429_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1288_safe
def s5_1430 : State := ⟨[65,4,241,145], 3533694129556768659166595001552739607532926663342471104040334737839030550, 1, 0, 1, 0⟩
theorem s5_1430_edges : next config 5 s5_1430 = [s6_1289] := by decide
theorem s5_1430_safe : Safe 8 5 s5_1430 := by
  apply safe_succ 7 5 s5_1430 [s6_1289] (by decide) s5_1430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1289_safe
def s5_1431 : State := ⟨[65,12,64,145], 44601830679428167221534955260136380203995414, 3, 1, 1, 0⟩
theorem s5_1431_edges : next config 5 s5_1431 = [s6_1224, s6_1279] := by decide
theorem s5_1431_safe : Safe 8 5 s5_1431 := by
  apply safe_succ 7 5 s5_1431 [s6_1224, s6_1279] (by decide) s5_1431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1224_safe
  · subst z; exact s6_1279_safe
def s5_1432 : State := ⟨[65,12,96,145], 44602511244162088326624396273688837284237590, 3, 0, 1, 0⟩
theorem s5_1432_edges : next config 5 s5_1432 = [s6_1226, s6_1288, s6_1280] := by decide
theorem s5_1432_safe : Safe 8 5 s5_1432 := by
  apply safe_succ 7 5 s5_1432 [s6_1226, s6_1288, s6_1280] (by decide) s5_1432_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1226_safe
  · subst z; exact s6_1288_safe
  · subst z; exact s6_1280_safe
def s5_1433 : State := ⟨[65,12,96,145], 66902575877958869591233187797122335253795094, 3, 0, 1, 0⟩
theorem s5_1433_edges : next config 5 s5_1433 = [s6_1228, s6_1289, s6_1281] := by decide
theorem s5_1433_safe : Safe 8 5 s5_1433 := by
  apply safe_succ 7 5 s5_1433 [s6_1228, s6_1289, s6_1281] (by decide) s5_1433_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1228_safe
  · subst z; exact s6_1289_safe
  · subst z; exact s6_1281_safe
def s5_1434 : State := ⟨[65,12,96,146], 89204682205957176486622759568200423832621334, 3, 0, 1, 0⟩
theorem s5_1434_edges : next config 5 s5_1434 = [s6_1230, s6_1282] := by decide
theorem s5_1434_safe : Safe 8 5 s5_1434 := by
  apply safe_succ 7 5 s5_1434 [s6_1230, s6_1282] (by decide) s5_1434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1230_safe
  · subst z; exact s6_1282_safe
def s5_1435 : State := ⟨[65,12,96,146], 111504066275020115874304624342419058265755926, 3, 0, 1, 0⟩
theorem s5_1435_edges : next config 5 s5_1435 = [s6_1231, s6_1283] := by decide
theorem s5_1435_safe : Safe 8 5 s5_1435 := by
  apply safe_succ 7 5 s5_1435 [s6_1231, s6_1283] (by decide) s5_1435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1231_safe
  · subst z; exact s6_1283_safe
def s5_1436 : State := ⟨[65,12,96,162], 5846006551025023507498659810751609685601538871574, 3, 0, 1, 0⟩
theorem s5_1436_edges : next config 5 s5_1436 = [s6_1232, s6_1284] := by decide
theorem s5_1436_safe : Safe 8 5 s5_1436 := by
  apply safe_succ 7 5 s5_1436 [s6_1232, s6_1284] (by decide) s5_1436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1232_safe
  · subst z; exact s6_1284_safe
def s5_1437 : State := ⟨[65,12,96,162], 7307508186994796958018590789614394275530398568726, 3, 0, 1, 0⟩
theorem s5_1437_edges : next config 5 s5_1437 = [s6_1233, s6_1285] := by decide
theorem s5_1437_safe : Safe 8 5 s5_1437 := by
  apply safe_succ 7 5 s5_1437 [s6_1233, s6_1285] (by decide) s5_1437_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1233_safe
  · subst z; exact s6_1285_safe
def s5_1438 : State := ⟨[65,12,96,176], 95780971326419139128294312505056075227996807378309398, 3, 0, 1, 0⟩
theorem s5_1438_edges : next config 5 s5_1438 = [s6_1234, s6_1286] := by decide
theorem s5_1438_safe : Safe 8 5 s5_1438 := by
  apply safe_succ 7 5 s5_1438 [s6_1234, s6_1286] (by decide) s5_1438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1234_safe
  · subst z; exact s6_1286_safe
def s5_1439 : State := ⟨[65,12,96,176], 95782432805755724832681893048353073238368101804871958, 3, 0, 1, 0⟩
theorem s5_1439_edges : next config 5 s5_1439 = [s6_1235, s6_1287] := by decide
theorem s5_1439_safe : Safe 8 5 s5_1439 := by
  apply safe_succ 7 5 s5_1439 [s6_1235, s6_1287] (by decide) s5_1439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1235_safe
  · subst z; exact s6_1287_safe
def s5_1440 : State := ⟨[65,12,104,129], 1020847121124453156611398816061523562774, 3, 0, 1, 0⟩
theorem s5_1440_edges : next config 5 s5_1440 = [s6_1237, s6_1280] := by decide
theorem s5_1440_safe : Safe 8 5 s5_1440 := by
  apply safe_succ 7 5 s5_1440 [s6_1237, s6_1280] (by decide) s5_1440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1237_safe
  · subst z; exact s6_1280_safe
def s5_1441 : State := ⟨[65,12,104,130], 1701411854966330083538148030925059985686, 3, 0, 1, 0⟩
theorem s5_1441_edges : next config 5 s5_1441 = [s6_1240, s6_1282, s6_1284] := by decide
theorem s5_1441_safe : Safe 8 5 s5_1441 := by
  apply safe_succ 7 5 s5_1441 [s6_1240, s6_1282, s6_1284] (by decide) s5_1441_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1240_safe
  · subst z; exact s6_1282_safe
  · subst z; exact s6_1284_safe
def s5_1442 : State := ⟨[65,12,104,132], 5784800258017591645098643320106278523158, 3, 0, 1, 0⟩
theorem s5_1442_edges : next config 5 s5_1442 = [s6_1243] := by decide
theorem s5_1442_safe : Safe 8 5 s5_1442 := by
  apply safe_succ 7 5 s5_1442 [s6_1243] (by decide) s5_1442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1243_safe
def s5_1443 : State := ⟨[65,12,104,136], 87452568319042822876308549103730649272598, 3, 0, 1, 0⟩
theorem s5_1443_edges : next config 5 s5_1443 = [s6_1246] := by decide
theorem s5_1443_safe : Safe 8 5 s5_1443 := by
  apply safe_succ 7 5 s5_1443 [s6_1246] (by decide) s5_1443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1246_safe
def s5_1444 : State := ⟨[65,12,104,140], 1394136857295446522575667041641720581263638, 3, 0, 1, 0⟩
theorem s5_1444_edges : next config 5 s5_1444 = [s6_1250] := by decide
theorem s5_1444_safe : Safe 8 5 s5_1444 := by
  apply safe_succ 7 5 s5_1444 [s6_1250] (by decide) s5_1444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1250_safe
def s5_1445 : State := ⟨[65,12,104,144], 22301085480917905717765402922249559493120278, 3, 0, 1, 0⟩
theorem s5_1445_edges : next config 5 s5_1445 = [s6_1251, s6_1283, s6_1286] := by decide
theorem s5_1445_safe : Safe 8 5 s5_1445 := by
  apply safe_succ 7 5 s5_1445 [s6_1251, s6_1283, s6_1286] (by decide) s5_1445_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1251_safe
  · subst z; exact s6_1283_safe
  · subst z; exact s6_1286_safe
def s5_1446 : State := ⟨[65,12,104,160], 1461501637671185305486261062400932620853919682838, 3, 0, 1, 0⟩
theorem s5_1446_edges : next config 5 s5_1446 = [s6_1255, s6_1285, s6_1287] := by decide
theorem s5_1446_safe : Safe 8 5 s5_1446 := by
  apply safe_succ 7 5 s5_1446 [s6_1255, s6_1285, s6_1287] (by decide) s5_1446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1255_safe
  · subst z; exact s6_1285_safe
  · subst z; exact s6_1287_safe
def s5_1447 : State := ⟨[65,12,104,192], 6277101735386680764176071810490242645787005045662021652758, 3, 0, 1, 0⟩
theorem s5_1447_edges : next config 5 s5_1447 = [s6_1258] := by decide
theorem s5_1447_safe : Safe 8 5 s5_1447 := by
  apply safe_succ 7 5 s5_1447 [s6_1258] (by decide) s5_1447_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1258_safe
def s5_1448 : State := ⟨[65,12,104,193], 12554203470773361528011861233697909061889360490126056165654, 3, 0, 1, 0⟩
theorem s5_1448_edges : next config 5 s5_1448 = [s6_1261] := by decide
theorem s5_1448_safe : Safe 8 5 s5_1448 := by
  apply safe_succ 7 5 s5_1448 [s6_1261] (by decide) s5_1448_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1261_safe
def s5_1449 : State := ⟨[65,12,104,224], 26959946667150639794667015087359913060919720652225222082301597389078, 3, 0, 1, 0⟩
theorem s5_1449_edges : next config 5 s5_1449 = [s6_1264] := by decide
theorem s5_1449_safe : Safe 8 5 s5_1449 := by
  apply safe_succ 7 5 s5_1449 [s6_1264] (by decide) s5_1449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1264_safe
def s5_1450 : State := ⟨[65,12,104,232], 6901746346790563787434755862277365734838391548400071204763722210939158, 3, 0, 1, 0⟩
theorem s5_1450_edges : next config 5 s5_1450 = [s6_1269] := by decide
theorem s5_1450_safe : Safe 8 5 s5_1450 := by
  apply safe_succ 7 5 s5_1450 [s6_1269] (by decide) s5_1450_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1269_safe
def s5_1451 : State := ⟨[65,21,64,145], 44601830679428167221534955260136380206088470, 3, 1, 1, 0⟩
theorem s5_1451_edges : next config 5 s5_1451 = [s6_1291, s6_1290] := by decide
theorem s5_1451_safe : Safe 8 5 s5_1451 := by
  apply safe_succ 7 5 s5_1451 [s6_1291, s6_1290] (by decide) s5_1451_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1291_safe
  · subst z; exact s6_1290_safe
def s5_1452 : State := ⟨[65,100,96,145], 44602511244163355977224624503090333987438870, 3, 0, 1, 0⟩
theorem s5_1452_edges : next config 5 s5_1452 = [s6_1227, s6_1293] := by decide
theorem s5_1452_safe : Safe 8 5 s5_1452 := by
  apply safe_succ 7 5 s5_1452 [s6_1227, s6_1293] (by decide) s5_1452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1227_safe
  · subst z; exact s6_1293_safe
def s5_1453 : State := ⟨[65,100,96,145], 66902575877960137241833416026523831956996374, 3, 0, 1, 0⟩
theorem s5_1453_edges : next config 5 s5_1453 = [s6_1229, s6_1294] := by decide
theorem s5_1453_safe : Safe 8 5 s5_1453 := by
  apply safe_succ 7 5 s5_1453 [s6_1229, s6_1294] (by decide) s5_1453_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1229_safe
  · subst z; exact s6_1294_safe
def s5_1454 : State := ⟨[65,100,104,129], 1020847122392103756839628217558226764054, 3, 0, 1, 0⟩
theorem s5_1454_edges : next config 5 s5_1454 = [s6_1293] := by decide
theorem s5_1454_safe : Safe 8 5 s5_1454 := by
  apply safe_succ 7 5 s5_1454 [s6_1293] (by decide) s5_1454_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1293_safe
def s5_1455 : State := ⟨[65,100,104,130], 1701411856233980683766377432421763186966, 3, 0, 1, 0⟩
theorem s5_1455_edges : next config 5 s5_1455 = [] := by decide
theorem s5_1455_safe : Safe 8 5 s5_1455 := by
  apply safe_succ 7 5 s5_1455 [] (by decide) s5_1455_edges
  simp
def s5_1456 : State := ⟨[65,100,104,132], 5784800259285242245326872721602981724438, 3, 0, 1, 0⟩
theorem s5_1456_edges : next config 5 s5_1456 = [] := by decide
theorem s5_1456_safe : Safe 8 5 s5_1456 := by
  apply safe_succ 7 5 s5_1456 [] (by decide) s5_1456_edges
  simp
def s5_1457 : State := ⟨[65,100,104,136], 87452568320310473476536778505227352473878, 3, 0, 1, 0⟩
theorem s5_1457_edges : next config 5 s5_1457 = [] := by decide
theorem s5_1457_safe : Safe 8 5 s5_1457 := by
  apply safe_succ 7 5 s5_1457 [] (by decide) s5_1457_edges
  simp
def s5_1458 : State := ⟨[65,100,104,144], 22301085480919173368365631151651056196321558, 3, 0, 1, 0⟩
theorem s5_1458_edges : next config 5 s5_1458 = [] := by decide
theorem s5_1458_safe : Safe 8 5 s5_1458 := by
  apply safe_succ 7 5 s5_1458 [] (by decide) s5_1458_edges
  simp
def s5_1459 : State := ⟨[65,100,104,160], 1461501637671185306753911662629162022350622884118, 3, 0, 1, 0⟩
theorem s5_1459_edges : next config 5 s5_1459 = [] := by decide
theorem s5_1459_safe : Safe 8 5 s5_1459 := by
  apply safe_succ 7 5 s5_1459 [] (by decide) s5_1459_edges
  simp
def s5_1460 : State := ⟨[65,100,104,192], 6277101735386680764176071811757893246015234447158724854038, 3, 0, 1, 0⟩
theorem s5_1460_edges : next config 5 s5_1460 = [] := by decide
theorem s5_1460_safe : Safe 8 5 s5_1460 := by
  apply safe_succ 7 5 s5_1460 [] (by decide) s5_1460_edges
  simp
def s5_1461 : State := ⟨[65,100,104,193], 12554203470773361528011861234965559662117589891622759366934, 3, 0, 1, 0⟩
theorem s5_1461_edges : next config 5 s5_1461 = [] := by decide
theorem s5_1461_safe : Safe 8 5 s5_1461 := by
  apply safe_succ 7 5 s5_1461 [] (by decide) s5_1461_edges
  simp
def s5_1462 : State := ⟨[65,100,104,224], 26959946667150639794667015087359913062187371252453451483798300590358, 3, 0, 1, 0⟩
theorem s5_1462_edges : next config 5 s5_1462 = [] := by decide
theorem s5_1462_safe : Safe 8 5 s5_1462 := by
  apply safe_succ 7 5 s5_1462 [] (by decide) s5_1462_edges
  simp
def s5_1463 : State := ⟨[65,100,104,228], 431359146674410236714672241392654373166744537590562038700352454328598, 3, 0, 1, 0⟩
theorem s5_1463_edges : next config 5 s5_1463 = [] := by decide
theorem s5_1463_safe : Safe 8 5 s5_1463 := by
  apply safe_succ 7 5 s5_1463 [] (by decide) s5_1463_edges
  simp
def s5_1464 : State := ⟨[65,100,104,232], 6901746346790563787434755862277365734839659199000299434165218914140438, 3, 0, 1, 0⟩
theorem s5_1464_edges : next config 5 s5_1464 = [] := by decide
theorem s5_1464_safe : Safe 8 5 s5_1464 := by
  apply safe_succ 7 5 s5_1464 [] (by decide) s5_1464_edges
  simp
def s5_1465 : State := ⟨[65,108,104,129], 1020847445643006815038125599217544134934, 3, 0, 1, 0⟩
theorem s5_1465_edges : next config 5 s5_1465 = [s6_1239, s6_1295] := by decide
theorem s5_1465_safe : Safe 8 5 s5_1465 := by
  apply safe_succ 7 5 s5_1465 [s6_1239, s6_1295] (by decide) s5_1465_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1239_safe
  · subst z; exact s6_1295_safe
def s5_1466 : State := ⟨[65,108,104,130], 1701412179484883741964874814081080557846, 3, 0, 1, 0⟩
theorem s5_1466_edges : next config 5 s5_1466 = [s6_1242] := by decide
theorem s5_1466_safe : Safe 8 5 s5_1466 := by
  apply safe_succ 7 5 s5_1466 [s6_1242] (by decide) s5_1466_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1242_safe
def s5_1467 : State := ⟨[65,108,104,132], 5784800582536145303525370103262299095318, 3, 0, 1, 0⟩
theorem s5_1467_edges : next config 5 s5_1467 = [s6_1245] := by decide
theorem s5_1467_safe : Safe 8 5 s5_1467 := by
  apply safe_succ 7 5 s5_1467 [s6_1245] (by decide) s5_1467_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1245_safe
def s5_1468 : State := ⟨[65,108,104,136], 87452568643561376534735275886886669844758, 3, 0, 1, 0⟩
theorem s5_1468_edges : next config 5 s5_1468 = [s6_1248] := by decide
theorem s5_1468_safe : Safe 8 5 s5_1468 := by
  apply safe_succ 7 5 s5_1468 [s6_1248] (by decide) s5_1468_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1248_safe
def s5_1469 : State := ⟨[65,108,104,144], 22301085481242424271423829649032715513692438, 3, 0, 1, 0⟩
theorem s5_1469_edges : next config 5 s5_1469 = [s6_1253] := by decide
theorem s5_1469_safe : Safe 8 5 s5_1469 := by
  apply safe_succ 7 5 s5_1469 [s6_1253] (by decide) s5_1469_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1253_safe
def s5_1470 : State := ⟨[65,108,104,160], 1461501637671185630004814720827659404009940254998, 3, 0, 1, 0⟩
theorem s5_1470_edges : next config 5 s5_1470 = [s6_1257] := by decide
theorem s5_1470_safe : Safe 8 5 s5_1470 := by
  apply safe_succ 7 5 s5_1470 [s6_1257] (by decide) s5_1470_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1257_safe
def s5_1471 : State := ⟨[65,108,104,192], 6277101735386680764176072135008796304213731828818042224918, 3, 0, 1, 0⟩
theorem s5_1471_edges : next config 5 s5_1471 = [s6_1260] := by decide
theorem s5_1471_safe : Safe 8 5 s5_1471 := by
  apply safe_succ 7 5 s5_1471 [s6_1260] (by decide) s5_1471_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1260_safe
def s5_1472 : State := ⟨[65,108,104,193], 12554203470773361528011861558216462720316087273282076737814, 3, 0, 1, 0⟩
theorem s5_1472_edges : next config 5 s5_1472 = [s6_1263] := by decide
theorem s5_1472_safe : Safe 8 5 s5_1472 := by
  apply safe_succ 7 5 s5_1472 [s6_1263] (by decide) s5_1472_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1263_safe
def s5_1473 : State := ⟨[65,108,104,224], 26959946667150639794667015087359913385438274310651948865457617961238, 3, 0, 1, 0⟩
theorem s5_1473_edges : next config 5 s5_1473 = [s6_1266] := by decide
theorem s5_1473_safe : Safe 8 5 s5_1473 := by
  apply safe_succ 7 5 s5_1473 [s6_1266] (by decide) s5_1473_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1266_safe
def s5_1474 : State := ⟨[65,108,104,232], 6901746346790563787434755862277365735162910102058497931546878231511318, 3, 0, 1, 0⟩
theorem s5_1474_edges : next config 5 s5_1474 = [s6_1271] := by decide
theorem s5_1474_safe : Safe 8 5 s5_1474 := by
  apply safe_succ 7 5 s5_1474 [s6_1271] (by decide) s5_1474_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1271_safe
def s5_1475 : State := ⟨[65,108,104,236], 110427941548649020598956093796432747521929544684614296258984741588500758, 3, 0, 1, 0⟩
theorem s5_1475_edges : next config 5 s5_1475 = [s6_1273] := by decide
theorem s5_1475_safe : Safe 8 5 s5_1475 := by
  apply safe_succ 7 5 s5_1475 [s6_1273] (by decide) s5_1475_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1273_safe
def s5_1476 : State := ⟨[65,140,104,136], 1481249143227206769222290941144253243392278, 3, 0, 1, 0⟩
theorem s5_1476_edges : next config 5 s5_1476 = [s6_1249] := by decide
theorem s5_1476_safe : Safe 8 5 s5_1476 := by
  apply safe_succ 7 5 s5_1476 [s6_1249] (by decide) s5_1476_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1249_safe
def s5_1477 : State := ⟨[65,228,104,224], 458319093341560876509339256479674003839114031412874381779959361372438, 3, 0, 1, 0⟩
theorem s5_1477_edges : next config 5 s5_1477 = [s6_1267] := by decide
theorem s5_1477_safe : Safe 8 5 s5_1477 := by
  apply safe_succ 7 5 s5_1477 [s6_1267] (by decide) s5_1477_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1267_safe
def s5_1478 : State := ⟨[65,236,104,232], 117329687895439584386390849658709772974056135103126256087364109791723798, 3, 0, 1, 0⟩
theorem s5_1478_edges : next config 5 s5_1478 = [s6_1272] := by decide
theorem s5_1478_safe : Safe 8 5 s5_1478 := by
  apply safe_succ 7 5 s5_1478 [s6_1272] (by decide) s5_1478_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1272_safe
def s5_1479 : State := ⟨[81,4,64,145], 44601830679428167223952770005877491134304534, 3, 2, 1, 0⟩
theorem s5_1479_edges : next config 5 s5_1479 = [s6_1297] := by decide
theorem s5_1479_safe : Safe 8 5 s5_1479 := by
  apply safe_succ 7 5 s5_1479 [s6_1297] (by decide) s5_1479_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1297_safe
def s5_1480 : State := ⟨[81,4,64,145], 44601830679428167223952770005877491136397590, 3, 2, 1, 0⟩
theorem s5_1480_edges : next config 5 s5_1480 = [s6_1299, s6_1298] := by decide
theorem s5_1480_safe : Safe 8 5 s5_1480 := by
  apply safe_succ 7 5 s5_1480 [s6_1299, s6_1298] (by decide) s5_1480_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1299_safe
  · subst z; exact s6_1298_safe
def s5_1481 : State := ⟨[81,4,104,145], 44601830679448528861718935940639031929536790, 1, 0, 1, 0⟩
theorem s5_1481_edges : next config 5 s5_1481 = [s6_1300] := by decide
theorem s5_1481_safe : Safe 8 5 s5_1481 := by
  apply safe_succ 7 5 s5_1481 [s6_1300] (by decide) s5_1481_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1300_safe
def s5_1482 : State := ⟨[81,12,96,145], 44601830679428246452115284270215084678254870, 3, 0, 1, 0⟩
theorem s5_1482_edges : next config 5 s5_1482 = [s6_1297, s6_1300] := by decide
theorem s5_1482_safe : Safe 8 5 s5_1482 := by
  apply safe_succ 7 5 s5_1482 [s6_1297, s6_1300] (by decide) s5_1482_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1297_safe
  · subst z; exact s6_1300_safe
def s5_1483 : State := ⟨[81,21,96,145], 44601830679428246452115284270215084680347926, 3, 0, 1, 0⟩
theorem s5_1483_edges : next config 5 s5_1483 = [s6_1302] := by decide
theorem s5_1483_safe : Safe 8 5 s5_1483 := by
  apply safe_succ 7 5 s5_1483 [s6_1302] (by decide) s5_1483_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1302_safe
def s5_1484 : State := ⟨[82,4,67,145], 44601830679428167226370806112547486579228950, 1, 0, 1, 0⟩
theorem s5_1484_edges : next config 5 s5_1484 = [s6_1312, s6_1308, s6_1304] := by decide
theorem s5_1484_safe : Safe 8 5 s5_1484 := by
  apply safe_succ 7 5 s5_1484 [s6_1312, s6_1308, s6_1304] (by decide) s5_1484_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1312_safe
  · subst z; exact s6_1308_safe
  · subst z; exact s6_1304_safe
def s5_1485 : State := ⟨[82,4,67,145], 44601830679428167226370843006035633998332182, 1, 0, 1, 0⟩
theorem s5_1485_edges : next config 5 s5_1485 = [s6_1313, s6_1309, s6_1305] := by decide
theorem s5_1485_safe : Safe 8 5 s5_1485 := by
  apply safe_succ 7 5 s5_1485 [s6_1313, s6_1309, s6_1305] (by decide) s5_1485_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1313_safe
  · subst z; exact s6_1309_safe
  · subst z; exact s6_1305_safe
def s5_1486 : State := ⟨[96,4,67,129], 1020847100842043553070408856590889320734, 1, 0, 1, 0⟩
theorem s5_1486_edges : next config 5 s5_1486 = [s6_1361, s6_1322, s6_1318] := by decide
theorem s5_1486_safe : Safe 8 5 s5_1486 := by
  apply safe_succ 7 5 s5_1486 [s6_1361, s6_1322, s6_1318] (by decide) s5_1486_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1361_safe
  · subst z; exact s6_1322_safe
  · subst z; exact s6_1318_safe
def s5_1487 : State := ⟨[96,4,67,130], 1701411834683920479997158071454425743646, 1, 0, 1, 0⟩
theorem s5_1487_edges : next config 5 s5_1487 = [s6_1363, s6_1323] := by decide
theorem s5_1487_safe : Safe 8 5 s5_1487 := by
  apply safe_succ 7 5 s5_1487 [s6_1363, s6_1323] (by decide) s5_1487_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1363_safe
  · subst z; exact s6_1323_safe
def s5_1488 : State := ⟨[96,4,67,131], 3062541302367674333850656501181498589470, 1, 0, 1, 0⟩
theorem s5_1488_edges : next config 5 s5_1488 = [s6_1365, s6_1324] := by decide
theorem s5_1488_safe : Safe 8 5 s5_1488 := by
  apply safe_succ 7 5 s5_1488 [s6_1365, s6_1324] (by decide) s5_1488_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1365_safe
  · subst z; exact s6_1324_safe
def s5_1489 : State := ⟨[96,4,67,132], 5784800237735182041557653360635644281118, 1, 0, 1, 0⟩
theorem s5_1489_edges : next config 5 s5_1489 = [s6_1367, s6_1325, s6_1316] := by decide
theorem s5_1489_safe : Safe 8 5 s5_1489 := by
  apply safe_succ 7 5 s5_1489 [s6_1367, s6_1325, s6_1316] (by decide) s5_1489_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1367_safe
  · subst z; exact s6_1325_safe
  · subst z; exact s6_1316_safe
def s5_1490 : State := ⟨[96,4,67,136], 87452568298760413272767559144260015030558, 1, 0, 1, 0⟩
theorem s5_1490_edges : next config 5 s5_1490 = [s6_1369, s6_1334, s6_1326, s6_1317] := by decide
theorem s5_1490_safe : Safe 8 5 s5_1490 := by
  apply safe_succ 7 5 s5_1490 [s6_1369, s6_1334, s6_1326, s6_1317] (by decide) s5_1490_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s6_1369_safe
  · subst z; exact s6_1334_safe
  · subst z; exact s6_1326_safe
  · subst z; exact s6_1317_safe
def s5_1491 : State := ⟨[96,4,67,144], 22301085480897623308161861932290088858878238, 1, 0, 1, 0⟩
theorem s5_1491_edges : next config 5 s5_1491 = [s6_1371, s6_1328] := by decide
theorem s5_1491_safe : Safe 8 5 s5_1491 := by
  apply safe_succ 7 5 s5_1491 [s6_1371, s6_1328] (by decide) s5_1491_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1371_safe
  · subst z; exact s6_1328_safe
def s5_1492 : State := ⟨[96,4,67,160], 1461501637671185285203851458859942661383285440798, 1, 0, 1, 0⟩
theorem s5_1492_edges : next config 5 s5_1492 = [s6_1373, s6_1329] := by decide
theorem s5_1492_safe : Safe 8 5 s5_1492 := by
  apply safe_succ 7 5 s5_1492 [s6_1373, s6_1329] (by decide) s5_1492_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1373_safe
  · subst z; exact s6_1329_safe
def s5_1493 : State := ⟨[96,4,67,163], 11692013098987505712629645287873923798974813241630, 1, 0, 1, 0⟩
theorem s5_1493_edges : next config 5 s5_1493 = [s6_1375, s6_1330, s6_1321] := by decide
theorem s5_1493_safe : Safe 8 5 s5_1493 := by
  apply safe_succ 7 5 s5_1493 [s6_1375, s6_1330, s6_1321] (by decide) s5_1493_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_1375_safe
  · subst z; exact s6_1330_safe
  · subst z; exact s6_1321_safe
def s5_1494 : State := ⟨[96,4,67,192], 6277101735386680764176071790207833042246015086191387410718, 1, 0, 1, 0⟩
theorem s5_1494_edges : next config 5 s5_1494 = [s6_1378, s6_1331] := by decide
theorem s5_1494_safe : Safe 8 5 s5_1494 := by
  apply safe_succ 7 5 s5_1494 [s6_1378, s6_1331] (by decide) s5_1494_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1378_safe
  · subst z; exact s6_1331_safe
def s5_1495 : State := ⟨[96,4,67,195], 50216813883093446111026597752661497954962503197439629000990, 1, 0, 1, 0⟩
theorem s5_1495_edges : next config 5 s5_1495 = [s6_1380, s6_1332] := by decide
theorem s5_1495_safe : Safe 8 5 s5_1495 := by
  apply safe_succ 7 5 s5_1495 [s6_1380, s6_1332] (by decide) s5_1495_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1380_safe
  · subst z; exact s6_1332_safe
def s5_1496 : State := ⟨[96,4,67,224], 26959946667150639794667015087359913040637311048684232122830963147038, 1, 0, 1, 0⟩
theorem s5_1496_edges : next config 5 s5_1496 = [s6_1381, s6_1333] := by decide
theorem s5_1496_safe : Safe 8 5 s5_1496 := by
  apply safe_succ 7 5 s5_1496 [s6_1381, s6_1333] (by decide) s5_1496_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1381_safe
  · subst z; exact s6_1333_safe
def s5_1497 : State := ⟨[96,12,67,128], 340282367000166626143659641727352901918, 3, 0, 0, 0⟩
theorem s5_1497_edges : next config 5 s5_1497 = [s6_1384, s6_1314, s6_1333, s6_1327, s6_1332, s6_1323, s6_1326, s6_1328, s6_1329] := by decide
theorem s5_1497_safe : Safe 8 5 s5_1497 := by
  apply safe_succ 7 5 s5_1497 [s6_1384, s6_1314, s6_1333, s6_1327, s6_1332, s6_1323, s6_1326, s6_1328, s6_1329] (by decide) s5_1497_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1384_safe
  · subst z; exact s6_1314_safe
  · subst z; exact s6_1333_safe
  · subst z; exact s6_1327_safe
  · subst z; exact s6_1332_safe
  · subst z; exact s6_1323_safe
  · subst z; exact s6_1326_safe
  · subst z; exact s6_1328_safe
  · subst z; exact s6_1329_safe
def s5_1498 : State := ⟨[97,4,96,129], 1020847101000499877951363579153941074198, 3, 2, 1, 0⟩
theorem s5_1498_edges : next config 5 s5_1498 = [s6_85, s6_1339, s6_1335] := by decide
theorem s5_1498_safe : Safe 8 5 s5_1498 := by
  apply safe_succ 7 5 s5_1498 [s6_85, s6_1339, s6_1335] (by decide) s5_1498_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_85_safe
  · subst z; exact s6_1339_safe
  · subst z; exact s6_1335_safe
def s5_1499 : State := ⟨[97,4,96,130], 1701411834842376804878112794017477497110, 3, 2, 1, 0⟩
theorem s5_1499_edges : next config 5 s5_1499 = [s6_91, s6_1340, s6_1337] := by decide
theorem s5_1499_safe : Safe 8 5 s5_1499 := by
  apply safe_succ 7 5 s5_1499 [s6_91, s6_1340, s6_1337] (by decide) s5_1499_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_91_safe
  · subst z; exact s6_1340_safe
  · subst z; exact s6_1337_safe
def s5_1500 : State := ⟨[97,4,96,132], 5784800237893638366438608083198696034582, 3, 2, 1, 0⟩
theorem s5_1500_edges : next config 5 s5_1500 = [s6_101, s6_1341] := by decide
theorem s5_1500_safe : Safe 8 5 s5_1500 := by
  apply safe_succ 7 5 s5_1500 [s6_101, s6_1341] (by decide) s5_1500_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_101_safe
  · subst z; exact s6_1341_safe
def s5_1501 : State := ⟨[97,4,96,136], 87452568298918869597648513866823066784022, 3, 2, 1, 0⟩
theorem s5_1501_edges : next config 5 s5_1501 = [s6_107, s6_1342] := by decide
theorem s5_1501_safe : Safe 8 5 s5_1501 := by
  apply safe_succ 7 5 s5_1501 [s6_107, s6_1342] (by decide) s5_1501_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_107_safe
  · subst z; exact s6_1342_safe
def s5_1502 : State := ⟨[97,4,96,136], 1481249143207082815943630905907345660903702, 3, 2, 1, 0⟩
theorem s5_1502_edges : next config 5 s5_1502 = [s6_113, s6_1343] := by decide
theorem s5_1502_safe : Safe 8 5 s5_1502 := by
  apply safe_succ 7 5 s5_1502 [s6_113, s6_1343] (by decide) s5_1502_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_113_safe
  · subst z; exact s6_1343_safe
def s5_1503 : State := ⟨[97,4,96,140], 1394136857275322569297007006404812998775062, 3, 2, 1, 0⟩
theorem s5_1503_edges : next config 5 s5_1503 = [s6_117, s6_1344] := by decide
theorem s5_1503_safe : Safe 8 5 s5_1503 := by
  apply safe_succ 7 5 s5_1503 [s6_117, s6_1344] (by decide) s5_1503_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_117_safe
  · subst z; exact s6_1344_safe
def s5_1504 : State := ⟨[97,4,96,144], 22301085480897781764486742887012651910631702, 3, 2, 1, 0⟩
theorem s5_1504_edges : next config 5 s5_1504 = [s6_121, s6_1345] := by decide
theorem s5_1504_safe : Safe 8 5 s5_1504 := by
  apply safe_succ 7 5 s5_1504 [s6_121, s6_1345] (by decide) s5_1504_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_121_safe
  · subst z; exact s6_1345_safe
def s5_1505 : State := ⟨[97,4,96,145], 44601830679428404906022461159661013416739094, 1, 1, 1, 0⟩
theorem s5_1505_edges : next config 5 s5_1505 = [s6_1352, s6_1346] := by decide
theorem s5_1505_safe : Safe 8 5 s5_1505 := by
  apply safe_succ 7 5 s5_1505 [s6_1352, s6_1346] (by decide) s5_1505_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1352_safe
  · subst z; exact s6_1346_safe
def s5_1506 : State := ⟨[97,4,96,160], 1461501637671185285362307783740897383946337194262, 3, 2, 1, 0⟩
theorem s5_1506_edges : next config 5 s5_1506 = [s6_133, s6_1347, s6_1338] := by decide
theorem s5_1506_safe : Safe 8 5 s5_1506 := by
  apply safe_succ 7 5 s5_1506 [s6_133, s6_1347, s6_1338] (by decide) s5_1506_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_133_safe
  · subst z; exact s6_1347_safe
  · subst z; exact s6_1338_safe
def s5_1507 : State := ⟨[97,4,96,192], 6277101735386680764176071790366289367126969808754439164182, 3, 2, 1, 0⟩
theorem s5_1507_edges : next config 5 s5_1507 = [s6_157, s6_1348] := by decide
theorem s5_1507_safe : Safe 8 5 s5_1507 := by
  apply safe_succ 7 5 s5_1507 [s6_157, s6_1348] (by decide) s5_1507_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_157_safe
  · subst z; exact s6_1348_safe
def s5_1508 : State := ⟨[97,4,96,224], 26959946667150639794667015087359913040795767373565186845394014900502, 3, 2, 1, 0⟩
theorem s5_1508_edges : next config 5 s5_1508 = [s6_183, s6_1349] := by decide
theorem s5_1508_safe : Safe 8 5 s5_1508 := by
  apply safe_succ 7 5 s5_1508 [s6_183, s6_1349] (by decide) s5_1508_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_183_safe
  · subst z; exact s6_1349_safe
def s5_1509 : State := ⟨[97,4,96,225], 53919893334301279589334030174379543714432911796105759326497625149718, 3, 2, 1, 0⟩
theorem s5_1509_edges : next config 5 s5_1509 = [s6_189, s6_1350] := by decide
theorem s5_1509_safe : Safe 8 5 s5_1509 := by
  apply safe_succ 7 5 s5_1509 [s6_189, s6_1350] (by decide) s5_1509_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_189_safe
  · subst z; exact s6_1350_safe
def s5_1510 : State := ⟨[97,4,104,128], 340282387441032554676284788237655937302, 3, 2, 0, 0⟩
theorem s5_1510_edges : next config 5 s5_1510 = [s6_1350, s6_1341, s6_1351, s6_1340, s6_1342, s6_1345, s6_1347] := by decide
theorem s5_1510_safe : Safe 8 5 s5_1510 := by
  apply safe_succ 7 5 s5_1510 [s6_1350, s6_1341, s6_1351, s6_1340, s6_1342, s6_1345, s6_1347] (by decide) s5_1510_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s6_1350_safe
  · subst z; exact s6_1341_safe
  · subst z; exact s6_1351_safe
  · subst z; exact s6_1340_safe
  · subst z; exact s6_1342_safe
  · subst z; exact s6_1345_safe
  · subst z; exact s6_1347_safe
def s5_1511 : State := ⟨[97,4,104,140], 1399581375166339994316072670547668541440278, 1, 0, 1, 0⟩
theorem s5_1511_edges : next config 5 s5_1511 = [] := by decide
theorem s5_1511_safe : Safe 8 5 s5_1511 := by
  apply safe_succ 7 5 s5_1511 [] (by decide) s5_1511_edges
  simp
def s5_1512 : State := ⟨[97,4,104,140], 1481249143227365225547282576331292912189718, 1, 0, 1, 0⟩
theorem s5_1512_edges : next config 5 s5_1512 = [] := by decide
theorem s5_1512_safe : Safe 8 5 s5_1512 := by
  apply safe_succ 7 5 s5_1512 [] (by decide) s5_1512_edges
  simp
def s5_1513 : State := ⟨[97,4,104,145], 44602511244182529192553039579299824204316950, 1, 0, 1, 0⟩
theorem s5_1513_edges : next config 5 s5_1513 = [s6_1353] := by decide
theorem s5_1513_safe : Safe 8 5 s5_1513 := by
  apply safe_succ 7 5 s5_1513 [s6_1353] (by decide) s5_1513_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1353_safe
def s5_1514 : State := ⟨[97,4,104,145], 66902575877979310457161831102733322173874454, 1, 0, 1, 0⟩
theorem s5_1514_edges : next config 5 s5_1514 = [s6_1354] := by decide
theorem s5_1514_safe : Safe 8 5 s5_1514 := by
  apply safe_succ 7 5 s5_1514 [s6_1354] (by decide) s5_1514_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1354_safe
def s5_1515 : State := ⟨[97,4,104,162], 5846006551025023527939525739394915296588458950934, 1, 0, 1, 0⟩
theorem s5_1515_edges : next config 5 s5_1515 = [s6_1355] := by decide
theorem s5_1515_safe : Safe 8 5 s5_1515 := by
  apply safe_succ 7 5 s5_1515 [s6_1355] (by decide) s5_1515_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1355_safe
def s5_1516 : State := ⟨[97,4,104,162], 7307508186994796978459456718257699886517318648086, 1, 0, 1, 0⟩
theorem s5_1516_edges : next config 5 s5_1516 = [s6_1356] := by decide
theorem s5_1516_safe : Safe 8 5 s5_1516 := by
  apply safe_succ 7 5 s5_1516 [s6_1356] (by decide) s5_1516_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1356_safe
def s5_1517 : State := ⟨[97,12,96,145], 44602511244162246782949387908875876953035030, 3, 0, 1, 0⟩
theorem s5_1517_edges : next config 5 s5_1517 = [s6_434, s6_1335, s6_1353] := by decide
theorem s5_1517_safe : Safe 8 5 s5_1517 := by
  apply safe_succ 7 5 s5_1517 [s6_434, s6_1335, s6_1353] (by decide) s5_1517_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_434_safe
  · subst z; exact s6_1335_safe
  · subst z; exact s6_1353_safe
def s5_1518 : State := ⟨[97,12,96,145], 66902575877959028047558179432309374922592534, 3, 0, 1, 0⟩
theorem s5_1518_edges : next config 5 s5_1518 = [s6_438, s6_1336, s6_1354] := by decide
theorem s5_1518_safe : Safe 8 5 s5_1518 := by
  apply safe_succ 7 5 s5_1518 [s6_438, s6_1336, s6_1354] (by decide) s5_1518_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_438_safe
  · subst z; exact s6_1336_safe
  · subst z; exact s6_1354_safe
def s5_1519 : State := ⟨[97,12,96,162], 5846006551025023507657116135743244872641207669014, 3, 0, 1, 0⟩
theorem s5_1519_edges : next config 5 s5_1519 = [s6_446, s6_1337, s6_1355] := by decide
theorem s5_1519_safe : Safe 8 5 s5_1519 := by
  apply safe_succ 7 5 s5_1519 [s6_446, s6_1337, s6_1355] (by decide) s5_1519_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_446_safe
  · subst z; exact s6_1337_safe
  · subst z; exact s6_1355_safe
def s5_1520 : State := ⟨[97,12,96,162], 7307508186994796958177047114606029462570067366166, 3, 0, 1, 0⟩
theorem s5_1520_edges : next config 5 s5_1520 = [s6_450, s6_1338, s6_1356] := by decide
theorem s5_1520_safe : Safe 8 5 s5_1520 := by
  apply safe_succ 7 5 s5_1520 [s6_450, s6_1338, s6_1356] (by decide) s5_1520_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_450_safe
  · subst z; exact s6_1338_safe
  · subst z; exact s6_1356_safe
def s5_1521 : State := ⟨[97,12,104,129], 1020847121282909481603034003101192360214, 3, 0, 1, 0⟩
theorem s5_1521_edges : next config 5 s5_1521 = [s6_1339, s6_1353] := by decide
theorem s5_1521_safe : Safe 8 5 s5_1521 := by
  apply safe_succ 7 5 s5_1521 [s6_1339, s6_1353] (by decide) s5_1521_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1339_safe
  · subst z; exact s6_1353_safe
def s5_1522 : State := ⟨[97,12,104,130], 1701411855124786408529783217964728783126, 3, 0, 1, 0⟩
theorem s5_1522_edges : next config 5 s5_1522 = [s6_1340, s6_1355] := by decide
theorem s5_1522_safe : Safe 8 5 s5_1522 := by
  apply safe_succ 7 5 s5_1522 [s6_1340, s6_1355] (by decide) s5_1522_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1340_safe
  · subst z; exact s6_1355_safe
def s5_1523 : State := ⟨[97,12,104,132], 5784800258176047970090278507145947320598, 3, 0, 1, 0⟩
theorem s5_1523_edges : next config 5 s5_1523 = [s6_1341] := by decide
theorem s5_1523_safe : Safe 8 5 s5_1523 := by
  apply safe_succ 7 5 s5_1523 [s6_1341] (by decide) s5_1523_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1341_safe
def s5_1524 : State := ⟨[97,12,104,136], 87452568319201279201300184290770318070038, 3, 0, 1, 0⟩
theorem s5_1524_edges : next config 5 s5_1524 = [s6_1342] := by decide
theorem s5_1524_safe : Safe 8 5 s5_1524 := by
  apply safe_succ 7 5 s5_1524 [s6_1342] (by decide) s5_1524_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1342_safe
def s5_1525 : State := ⟨[97,12,104,140], 1394136857295604978900658676828760250061078, 3, 0, 1, 0⟩
theorem s5_1525_edges : next config 5 s5_1525 = [s6_1344] := by decide
theorem s5_1525_safe : Safe 8 5 s5_1525 := by
  apply safe_succ 7 5 s5_1525 [s6_1344] (by decide) s5_1525_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1344_safe
def s5_1526 : State := ⟨[97,12,104,144], 22301085480918064174090394557436599161917718, 3, 0, 1, 0⟩
theorem s5_1526_edges : next config 5 s5_1526 = [s6_1345] := by decide
theorem s5_1526_safe : Safe 8 5 s5_1526 := by
  apply safe_succ 7 5 s5_1526 [s6_1345] (by decide) s5_1526_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1345_safe
def s5_1527 : State := ⟨[97,12,104,160], 1461501637671185305644717387392567807893588480278, 3, 0, 1, 0⟩
theorem s5_1527_edges : next config 5 s5_1527 = [s6_1347, s6_1356] := by decide
theorem s5_1527_safe : Safe 8 5 s5_1527 := by
  apply safe_succ 7 5 s5_1527 [s6_1347, s6_1356] (by decide) s5_1527_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1347_safe
  · subst z; exact s6_1356_safe
def s5_1528 : State := ⟨[97,12,104,192], 6277101735386680764176071810648698970778640232701690450198, 3, 0, 1, 0⟩
theorem s5_1528_edges : next config 5 s5_1528 = [s6_1348] := by decide
theorem s5_1528_safe : Safe 8 5 s5_1528 := by
  apply safe_succ 7 5 s5_1528 [s6_1348] (by decide) s5_1528_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1348_safe
def s5_1529 : State := ⟨[97,12,104,224], 26959946667150639794667015087359913061078176977216857269341266186518, 3, 0, 1, 0⟩
theorem s5_1529_edges : next config 5 s5_1529 = [s6_1349] := by decide
theorem s5_1529_safe : Safe 8 5 s5_1529 := by
  apply safe_succ 7 5 s5_1529 [s6_1349] (by decide) s5_1529_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1349_safe
def s5_1530 : State := ⟨[97,12,104,225], 53919893334301279589334030174379543734715321399757429750444876435734, 3, 0, 1, 0⟩
theorem s5_1530_edges : next config 5 s5_1530 = [s6_1350] := by decide
theorem s5_1530_safe : Safe 8 5 s5_1530 := by
  apply safe_succ 7 5 s5_1530 [s6_1350] (by decide) s5_1530_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1350_safe
def s5_1531 : State := ⟨[97,12,104,232], 6901746346790563787434755862277365734838550004725062839950761879736598, 3, 0, 1, 0⟩
theorem s5_1531_edges : next config 5 s5_1531 = [s6_1351] := by decide
theorem s5_1531_safe : Safe 8 5 s5_1531 := by
  apply safe_succ 7 5 s5_1531 [s6_1351] (by decide) s5_1531_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1351_safe
def s5_1532 : State := ⟨[97,140,104,136], 1481249143227365225547282576331292912189718, 3, 0, 1, 0⟩
theorem s5_1532_edges : next config 5 s5_1532 = [s6_1343] := by decide
theorem s5_1532_safe : Safe 8 5 s5_1532 := by
  apply safe_succ 7 5 s5_1532 [s6_1343] (by decide) s5_1532_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1343_safe
def s5_1533 : State := ⟨[104,4,67,128], 340282387203348067281065736877153255710, 1, 0, 0, 0⟩
theorem s5_1533_edges : next config 5 s5_1533 = [s6_1315, s6_1382, s6_1366, s6_1379, s6_1362, s6_1368, s6_1370, s6_1372] := by decide
theorem s5_1533_safe : Safe 8 5 s5_1533 := by
  apply safe_succ 7 5 s5_1533 [s6_1315, s6_1382, s6_1366, s6_1379, s6_1362, s6_1368, s6_1370, s6_1372] (by decide) s5_1533_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s6_1315_safe
  · subst z; exact s6_1382_safe
  · subst z; exact s6_1366_safe
  · subst z; exact s6_1379_safe
  · subst z; exact s6_1362_safe
  · subst z; exact s6_1368_safe
  · subst z; exact s6_1370_safe
  · subst z; exact s6_1372_safe
def s5_1534 : State := ⟨[104,4,67,128], 340282387282576229795330065674604183838, 1, 0, 0, 0⟩
theorem s5_1534_edges : next config 5 s5_1534 = [s6_1156, s6_1384, s6_1383, s6_1367, s6_1380, s6_1363, s6_1369, s6_1371, s6_1373] := by decide
theorem s5_1534_safe : Safe 8 5 s5_1534 := by
  apply safe_succ 7 5 s5_1534 [s6_1156, s6_1384, s6_1383, s6_1367, s6_1380, s6_1363, s6_1369, s6_1371, s6_1373] (by decide) s5_1534_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s6_1156_safe
  · subst z; exact s6_1384_safe
  · subst z; exact s6_1383_safe
  · subst z; exact s6_1367_safe
  · subst z; exact s6_1380_safe
  · subst z; exact s6_1363_safe
  · subst z; exact s6_1369_safe
  · subst z; exact s6_1371_safe
  · subst z; exact s6_1373_safe
def s5_1535 : State := ⟨[113,4,104,145], 44601830689833122576370739558470766238564630, 1, 0, 1, 0⟩
theorem s5_1535_edges : next config 5 s5_1535 = [s6_1389] := by decide
theorem s5_1535_safe : Safe 8 5 s5_1535 := by
  apply safe_succ 7 5 s5_1535 [s6_1389] (by decide) s5_1535_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1389_safe
def s5_1536 : State := ⟨[113,12,96,145], 44601830689812840166767087888046818987282710, 3, 0, 1, 0⟩
theorem s5_1536_edges : next config 5 s5_1536 = [s6_1386, s6_1389] := by decide
theorem s5_1536_safe : Safe 8 5 s5_1536 := by
  apply safe_succ 7 5 s5_1536 [s6_1386, s6_1389] (by decide) s5_1536_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1386_safe
  · subst z; exact s6_1389_safe
def s5_1537 : State := ⟨[113,21,96,145], 44601830689812840166767087888046818989375766, 3, 0, 1, 0⟩
theorem s5_1537_edges : next config 5 s5_1537 = [s6_1390] := by decide
theorem s5_1537_safe : Safe 8 5 s5_1537 := by
  apply safe_succ 7 5 s5_1537 [s6_1390] (by decide) s5_1537_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1390_safe
def s5_1538 : State := ⟨[117,4,96,145], 44601830845581745922811916743961708865978646, 1, 0, 1, 0⟩
theorem s5_1538_edges : next config 5 s5_1538 = [s6_1391] := by decide
theorem s5_1538_safe : Safe 8 5 s5_1538 := by
  apply safe_succ 7 5 s5_1538 [s6_1391] (by decide) s5_1538_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1391_safe
def s5_1539 : State := ⟨[121,4,104,145], 44601833337904520429132830109023894140813590, 1, 0, 1, 0⟩
theorem s5_1539_edges : next config 5 s5_1539 = [] := by decide
theorem s5_1539_safe : Safe 8 5 s5_1539 := by
  apply safe_succ 7 5 s5_1539 [] (by decide) s5_1539_edges
  simp
def s5_1540 : State := ⟨[131,4,64,146], 89207404464892464766167915407234137015259414, 3, 2, 1, 0⟩
theorem s5_1540_edges : next config 5 s5_1540 = [s6_1394] := by decide
theorem s5_1540_safe : Safe 8 5 s5_1540 := by
  apply safe_succ 7 5 s5_1540 [s6_1394] (by decide) s5_1540_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1394_safe
def s5_1541 : State := ⟨[131,4,64,162], 5846006553747282442786939355907448719314721509654, 3, 2, 1, 0⟩
theorem s5_1541_edges : next config 5 s5_1541 = [s6_1395] := by decide
theorem s5_1541_safe : Safe 8 5 s5_1541 := by
  apply safe_succ 7 5 s5_1541 [s6_1395] (by decide) s5_1541_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1395_safe
def s5_1542 : State := ⟨[131,4,96,130], 4423670770051428187556580978284535288086, 3, 2, 1, 0⟩
theorem s5_1542_edges : next config 5 s5_1542 = [s6_94, s6_1416, s6_1396, s6_1394, s6_1395] := by decide
theorem s5_1542_safe : Safe 8 5 s5_1542 := by
  apply safe_succ 7 5 s5_1542 [s6_94, s6_1416, s6_1396, s6_1394, s6_1395] (by decide) s5_1542_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_94_safe
  · subst z; exact s6_1416_safe
  · subst z; exact s6_1396_safe
  · subst z; exact s6_1394_safe
  · subst z; exact s6_1395_safe
def s5_1543 : State := ⟨[131,4,96,130], 4423670771319078787784810379781238489366, 3, 2, 1, 0⟩
theorem s5_1543_edges : next config 5 s5_1543 = [s6_95, s6_1397] := by decide
theorem s5_1543_safe : Safe 8 5 s5_1543 := by
  apply safe_succ 7 5 s5_1543 [s6_95, s6_1397] (by decide) s5_1543_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_95_safe
  · subst z; exact s6_1397_safe
def s5_1544 : State := ⟨[131,4,104,146], 89207404464912826403934081341995677810491670, 1, 0, 1, 0⟩
theorem s5_1544_edges : next config 5 s5_1544 = [s6_1399] := by decide
theorem s5_1544_safe : Safe 8 5 s5_1544 := by
  apply safe_succ 7 5 s5_1544 [s6_1399] (by decide) s5_1544_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1399_safe
def s5_1545 : State := ⟨[131,4,104,162], 5846006553747282463148577122073383480855516741910, 1, 0, 1, 0⟩
theorem s5_1545_edges : next config 5 s5_1545 = [s6_1400] := by decide
theorem s5_1545_safe : Safe 8 5 s5_1545 := by
  apply safe_succ 7 5 s5_1545 [s6_1400] (by decide) s5_1545_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1400_safe
def s5_1546 : State := ⟨[131,4,108,130], 4423671114852391449634978185387807146262, 1, 0, 1, 0⟩
theorem s5_1546_edges : next config 5 s5_1546 = [s6_344] := by decide
theorem s5_1546_safe : Safe 8 5 s5_1546 := by
  apply safe_succ 7 5 s5_1546 [s6_344] (by decide) s5_1546_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_344_safe
def s5_1547 : State := ⟨[131,12,96,146], 89207404464892543994330429671571730559209750, 3, 0, 1, 0⟩
theorem s5_1547_edges : next config 5 s5_1547 = [s6_1394, s6_1399] := by decide
theorem s5_1547_safe : Safe 8 5 s5_1547 := by
  apply safe_succ 7 5 s5_1547 [s6_1394, s6_1399] (by decide) s5_1547_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1394_safe
  · subst z; exact s6_1399_safe
def s5_1548 : State := ⟨[131,12,96,162], 5846006553747282442866167518421713056908265459990, 3, 0, 1, 0⟩
theorem s5_1548_edges : next config 5 s5_1548 = [s6_1395, s6_1400] := by decide
theorem s5_1548_safe : Safe 8 5 s5_1548 := by
  apply safe_succ 7 5 s5_1548 [s6_1395, s6_1400] (by decide) s5_1548_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1395_safe
  · subst z; exact s6_1400_safe
def s5_1549 : State := ⟨[131,12,104,130], 4423670790333837791208251402231786574102, 3, 0, 1, 0⟩
theorem s5_1549_edges : next config 5 s5_1549 = [s6_470, s6_1422, s6_1396, s6_1399, s6_1400] := by decide
theorem s5_1549_safe : Safe 8 5 s5_1549 := by
  apply safe_succ 7 5 s5_1549 [s6_470, s6_1422, s6_1396, s6_1399, s6_1400] (by decide) s5_1549_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s6_470_safe
  · subst z; exact s6_1422_safe
  · subst z; exact s6_1396_safe
  · subst z; exact s6_1399_safe
  · subst z; exact s6_1400_safe
def s5_1550 : State := ⟨[131,100,104,130], 4423670791601488391436480803728489775382, 3, 0, 1, 0⟩
theorem s5_1550_edges : next config 5 s5_1550 = [s6_562] := by decide
theorem s5_1550_safe : Safe 8 5 s5_1550 := by
  apply safe_succ 7 5 s5_1550 [s6_562] (by decide) s5_1550_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_562_safe
def s5_1551 : State := ⟨[131,108,104,130], 4423671114852391449634978185387807146262, 3, 0, 1, 0⟩
theorem s5_1551_edges : next config 5 s5_1551 = [s6_587, s6_1398] := by decide
theorem s5_1551_safe : Safe 8 5 s5_1551 := by
  apply safe_succ 7 5 s5_1551 [s6_587, s6_1398] (by decide) s5_1551_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_587_safe
  · subst z; exact s6_1398_safe
def s5_1552 : State := ⟨[146,4,64,145], 133804811473550659787677791457241678808809758, 1, 1, 1, 0⟩
theorem s5_1552_edges : next config 5 s5_1552 = [s6_1407, s6_1404] := by decide
theorem s5_1552_safe : Safe 8 5 s5_1552 := by
  apply safe_succ 7 5 s5_1552 [s6_1407, s6_1404] (by decide) s5_1552_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1407_safe
  · subst z; exact s6_1404_safe
def s5_1553 : State := ⟨[146,4,67,145], 133805492038284501664604865780409132021514526, 1, 0, 1, 0⟩
theorem s5_1553_edges : next config 5 s5_1553 = [s6_1408] := by decide
theorem s5_1553_safe : Safe 8 5 s5_1553 := by
  apply safe_succ 7 5 s5_1553 [s6_1408] (by decide) s5_1553_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1408_safe
def s5_1554 : State := ⟨[146,4,67,145], 156105556672081282929213657303842629991072030, 1, 0, 1, 0⟩
theorem s5_1554_edges : next config 5 s5_1554 = [s6_1409] := by decide
theorem s5_1554_safe : Safe 8 5 s5_1554 := by
  apply safe_succ 7 5 s5_1554 [s6_1409] (by decide) s5_1554_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1409_safe
def s5_1555 : State := ⟨[146,4,96,145], 133805492038284580892767232470794135889051934, 1, 0, 1, 0⟩
theorem s5_1555_edges : next config 5 s5_1555 = [s6_1410, s6_1405] := by decide
theorem s5_1555_safe : Safe 8 5 s5_1555 := by
  apply safe_succ 7 5 s5_1555 [s6_1410, s6_1405] (by decide) s5_1555_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1410_safe
  · subst z; exact s6_1405_safe
def s5_1556 : State := ⟨[146,4,96,145], 156105556672081362157376023994227633858609438, 1, 0, 1, 0⟩
theorem s5_1556_edges : next config 5 s5_1556 = [s6_1411, s6_1406] := by decide
theorem s5_1556_safe : Safe 8 5 s5_1556 := by
  apply safe_succ 7 5 s5_1556 [s6_1411, s6_1406] (by decide) s5_1556_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1411_safe
  · subst z; exact s6_1406_safe
def s5_1557 : State := ⟨[146,12,64,145], 133805492038284501664604718206456542345105694, 3, 0, 1, 0⟩
theorem s5_1557_edges : next config 5 s5_1557 = [s6_1401, s6_1410] := by decide
theorem s5_1557_safe : Safe 8 5 s5_1557 := by
  apply safe_succ 7 5 s5_1557 [s6_1401, s6_1410] (by decide) s5_1557_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1401_safe
  · subst z; exact s6_1410_safe
def s5_1558 : State := ⟨[146,12,64,145], 156105556672081282929213509729890040314663198, 3, 0, 1, 0⟩
theorem s5_1558_edges : next config 5 s5_1558 = [s6_1402, s6_1411] := by decide
theorem s5_1558_safe : Safe 8 5 s5_1558 := by
  apply safe_succ 7 5 s5_1558 [s6_1402, s6_1411] (by decide) s5_1558_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1402_safe
  · subst z; exact s6_1411_safe
def s5_1559 : State := ⟨[161,4,96,160], 4384504912332991121611221124144934748071114379542, 3, 2, 1, 0⟩
theorem s5_1559_edges : next config 5 s5_1559 = [s6_136, s6_1418, s6_1413] := by decide
theorem s5_1559_safe : Safe 8 5 s5_1559 := by
  apply safe_succ 7 5 s5_1559 [s6_136, s6_1418, s6_1413] (by decide) s5_1559_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_136_safe
  · subst z; exact s6_1418_safe
  · subst z; exact s6_1413_safe
def s5_1560 : State := ⟨[161,12,104,160], 4384504912332991141893630727796605172018365665558, 3, 0, 1, 0⟩
theorem s5_1560_edges : next config 5 s5_1560 = [s6_493, s6_1424, s6_1413] := by decide
theorem s5_1560_safe : Safe 8 5 s5_1560 := by
  apply safe_succ 7 5 s5_1560 [s6_493, s6_1424, s6_1413] (by decide) s5_1560_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_493_safe
  · subst z; exact s6_1424_safe
  · subst z; exact s6_1413_safe
def s5_1561 : State := ⟨[163,4,64,130], 11692013100348635180234170979065583938492895924502, 3, 2, 1, 0⟩
theorem s5_1561_edges : next config 5 s5_1561 = [s6_1415] := by decide
theorem s5_1561_safe : Safe 8 5 s5_1561 := by
  apply safe_succ 7 5 s5_1561 [s6_1415] (by decide) s5_1561_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1415_safe
def s5_1562 : State := ⟨[163,4,64,130], 11692013103070894115601678686772580797938451681558, 3, 2, 1, 0⟩
theorem s5_1562_edges : next config 5 s5_1562 = [s6_1416] := by decide
theorem s5_1562_safe : Safe 8 5 s5_1562 := by
  apply safe_succ 7 5 s5_1562 [s6_1416] (by decide) s5_1562_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1416_safe
def s5_1563 : State := ⟨[163,4,64,160], 13153514736318408630754101957928368528413165687070, 3, 2, 1, 0⟩
theorem s5_1563_edges : next config 5 s5_1563 = [s6_1417] := by decide
theorem s5_1563_safe : Safe 8 5 s5_1563 := by
  apply safe_succ 7 5 s5_1563 [s6_1417] (by decide) s5_1563_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1417_safe
def s5_1564 : State := ⟨[163,4,64,160], 16076518010980214467161471623360934567725030773014, 3, 2, 1, 0⟩
theorem s5_1564_edges : next config 5 s5_1564 = [s6_1418] := by decide
theorem s5_1564_safe : Safe 8 5 s5_1564 := by
  apply safe_succ 7 5 s5_1564 [s6_1418] (by decide) s5_1564_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1418_safe
def s5_1565 : State := ⟨[163,4,64,162], 17538019649672246853048910309930716017108036161814, 3, 2, 1, 0⟩
theorem s5_1565_edges : next config 5 s5_1565 = [s6_16, s6_1419] := by decide
theorem s5_1565_safe : Safe 8 5 s5_1565 := by
  apply safe_succ 7 5 s5_1565 [s6_16, s6_1419] (by decide) s5_1565_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_16_safe
  · subst z; exact s6_1419_safe
def s5_1566 : State := ⟨[163,4,64,162], 18999521285642020303568841288793500607036895858966, 3, 2, 1, 0⟩
theorem s5_1566_edges : next config 5 s5_1566 = [s6_17, s6_1420] := by decide
theorem s5_1566_safe : Safe 8 5 s5_1566 := by
  apply safe_succ 7 5 s5_1566 [s6_17, s6_1420] (by decide) s5_1566_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_17_safe
  · subst z; exact s6_1420_safe
def s5_1567 : State := ⟨[163,4,104,130], 11692013100348635200595808745231518700033691156758, 1, 0, 1, 0⟩
theorem s5_1567_edges : next config 5 s5_1567 = [s6_1429, s6_1421] := by decide
theorem s5_1567_safe : Safe 8 5 s5_1567 := by
  apply safe_succ 7 5 s5_1567 [s6_1429, s6_1421] (by decide) s5_1567_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1429_safe
  · subst z; exact s6_1421_safe
def s5_1568 : State := ⟨[163,4,104,130], 11692013103070894135963316452938515559479246913814, 1, 0, 1, 0⟩
theorem s5_1568_edges : next config 5 s5_1568 = [s6_1430, s6_1422] := by decide
theorem s5_1568_safe : Safe 8 5 s5_1568 := by
  apply safe_succ 7 5 s5_1568 [s6_1430, s6_1422] (by decide) s5_1568_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1430_safe
  · subst z; exact s6_1422_safe
def s5_1569 : State := ⟨[163,4,104,160], 13153514736318408651115739724094303289953960919326, 1, 0, 1, 0⟩
theorem s5_1569_edges : next config 5 s5_1569 = [s6_1433, s6_1423] := by decide
theorem s5_1569_safe : Safe 8 5 s5_1569 := by
  apply safe_succ 7 5 s5_1569 [s6_1433, s6_1423] (by decide) s5_1569_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1433_safe
  · subst z; exact s6_1423_safe
def s5_1570 : State := ⟨[163,4,104,160], 16076518010980214487523109389526869329265826005270, 1, 0, 1, 0⟩
theorem s5_1570_edges : next config 5 s5_1570 = [s6_1434, s6_1424] := by decide
theorem s5_1570_safe : Safe 8 5 s5_1570 := by
  apply safe_succ 7 5 s5_1570 [s6_1434, s6_1424] (by decide) s5_1570_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1434_safe
  · subst z; exact s6_1424_safe
def s5_1571 : State := ⟨[163,4,104,162], 17538019649672246873410548076096650778648831394070, 1, 0, 1, 0⟩
theorem s5_1571_edges : next config 5 s5_1571 = [s6_272, s6_1437, s6_1425] := by decide
theorem s5_1571_safe : Safe 8 5 s5_1571 := by
  apply safe_succ 7 5 s5_1571 [s6_272, s6_1437, s6_1425] (by decide) s5_1571_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_272_safe
  · subst z; exact s6_1437_safe
  · subst z; exact s6_1425_safe
def s5_1572 : State := ⟨[163,4,104,162], 18999521285642020323930479054959435368577691091222, 1, 0, 1, 0⟩
theorem s5_1572_edges : next config 5 s5_1572 = [s6_273, s6_1438, s6_1426] := by decide
theorem s5_1572_safe : Safe 8 5 s5_1572 := by
  apply safe_succ 7 5 s5_1572 [s6_273, s6_1438, s6_1426] (by decide) s5_1572_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_273_safe
  · subst z; exact s6_1438_safe
  · subst z; exact s6_1426_safe
def s5_1573 : State := ⟨[163,12,67,160], 13153514736318408630754101958075942481002842099998, 3, 0, 1, 0⟩
theorem s5_1573_edges : next config 5 s5_1573 = [s6_1414] := by decide
theorem s5_1573_safe : Safe 8 5 s5_1573 := by
  apply safe_succ 7 5 s5_1573 [s6_1414] (by decide) s5_1573_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1414_safe
def s5_1574 : State := ⟨[163,12,96,130], 11692013100348635180313399141579848276086439874838, 3, 0, 1, 0⟩
theorem s5_1574_edges : next config 5 s5_1574 = [s6_1415, s6_1421] := by decide
theorem s5_1574_safe : Safe 8 5 s5_1574 := by
  apply safe_succ 7 5 s5_1574 [s6_1415, s6_1421] (by decide) s5_1574_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1415_safe
  · subst z; exact s6_1421_safe
def s5_1575 : State := ⟨[163,12,96,130], 11692013103070894115680906849286845135531995631894, 3, 0, 1, 0⟩
theorem s5_1575_edges : next config 5 s5_1575 = [s6_1416, s6_1422] := by decide
theorem s5_1575_safe : Safe 8 5 s5_1575 := by
  apply safe_succ 7 5 s5_1575 [s6_1416, s6_1422] (by decide) s5_1575_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1416_safe
  · subst z; exact s6_1422_safe
def s5_1576 : State := ⟨[163,12,96,160], 13153514736318408630833330120442632866006709637406, 3, 0, 1, 0⟩
theorem s5_1576_edges : next config 5 s5_1576 = [s6_1417, s6_1423] := by decide
theorem s5_1576_safe : Safe 8 5 s5_1576 := by
  apply safe_succ 7 5 s5_1576 [s6_1417, s6_1423] (by decide) s5_1576_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1417_safe
  · subst z; exact s6_1423_safe
def s5_1577 : State := ⟨[163,12,96,160], 16076518010980214467240699785875198905318574723350, 3, 0, 1, 0⟩
theorem s5_1577_edges : next config 5 s5_1577 = [s6_1418, s6_1424] := by decide
theorem s5_1577_safe : Safe 8 5 s5_1577 := by
  apply safe_succ 7 5 s5_1577 [s6_1418, s6_1424] (by decide) s5_1577_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1418_safe
  · subst z; exact s6_1424_safe
def s5_1578 : State := ⟨[163,12,96,162], 17538019649672246853128138472444980354701580112150, 3, 0, 1, 0⟩
theorem s5_1578_edges : next config 5 s5_1578 = [s6_451, s6_1419, s6_1425] := by decide
theorem s5_1578_safe : Safe 8 5 s5_1578 := by
  apply safe_succ 7 5 s5_1578 [s6_451, s6_1419, s6_1425] (by decide) s5_1578_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_451_safe
  · subst z; exact s6_1419_safe
  · subst z; exact s6_1425_safe
def s5_1579 : State := ⟨[163,12,96,162], 18999521285642020303648069451307764944630439809302, 3, 0, 1, 0⟩
theorem s5_1579_edges : next config 5 s5_1579 = [s6_452, s6_1420, s6_1426] := by decide
theorem s5_1579_safe : Safe 8 5 s5_1579 := by
  apply safe_succ 7 5 s5_1579 [s6_452, s6_1420, s6_1426] (by decide) s5_1579_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_452_safe
  · subst z; exact s6_1420_safe
  · subst z; exact s6_1426_safe
def s5_1580 : State := ⟨[171,4,67,136], 2993155353341141744779827722513200919062016319095070, 1, 0, 1, 0⟩
theorem s5_1580_edges : next config 5 s5_1580 = [] := by decide
theorem s5_1580_safe : Safe 8 5 s5_1580 := by
  apply safe_succ 7 5 s5_1580 [] (by decide) s5_1580_edges
  simp
def s5_1581 : State := ⟨[171,4,67,160], 3006308867990007585111900639361023566736352690110750, 1, 0, 1, 0⟩
theorem s5_1581_edges : next config 5 s5_1581 = [] := by decide
theorem s5_1581_safe : Safe 8 5 s5_1581 := by
  apply safe_succ 7 5 s5_1581 [] (by decide) s5_1581_edges
  simp
def s5_1582 : State := ⟨[171,4,96,130], 3004847366354037811661459936544527472531436287885590, 1, 0, 1, 0⟩
theorem s5_1582_edges : next config 5 s5_1582 = [s6_1429] := by decide
theorem s5_1582_safe : Safe 8 5 s5_1582 := by
  apply safe_succ 7 5 s5_1582 [s6_1429] (by decide) s5_1582_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1429_safe
def s5_1583 : State := ⟨[171,4,96,130], 3004847366356760070596827444252234469390881843642646, 1, 0, 1, 0⟩
theorem s5_1583_edges : next config 5 s5_1583 = [s6_1430] := by decide
theorem s5_1583_safe : Safe 8 5 s5_1583 := by
  apply safe_succ 7 5 s5_1583 [s6_1430] (by decide) s5_1583_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1430_safe
def s5_1584 : State := ⟨[171,4,96,136], 2993155353341141744779906950675567609447020186632478, 1, 0, 1, 0⟩
theorem s5_1584_edges : next config 5 s5_1584 = [s6_1431] := by decide
theorem s5_1584_safe : Safe 8 5 s5_1584 := by
  apply safe_succ 7 5 s5_1584 [s6_1431] (by decide) s5_1584_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1431_safe
def s5_1585 : State := ⟨[171,4,96,136], 2993155353341141744779906950675567609447028776567062, 1, 0, 1, 0⟩
theorem s5_1585_edges : next config 5 s5_1585 = [s6_1432] := by decide
theorem s5_1585_safe : Safe 8 5 s5_1585 := by
  apply safe_succ 7 5 s5_1585 [s6_1432] (by decide) s5_1585_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1432_safe
def s5_1586 : State := ⟨[171,4,96,160], 3006308867990007585111979867523390257121356557648158, 1, 0, 1, 0⟩
theorem s5_1586_edges : next config 5 s5_1586 = [s6_1433] := by decide
theorem s5_1586_safe : Safe 8 5 s5_1586 := by
  apply safe_succ 7 5 s5_1586 [s6_1433] (by decide) s5_1586_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1433_safe
def s5_1587 : State := ⟨[171,4,96,160], 3009231871264669390948387237188822823160668422734102, 1, 0, 1, 0⟩
theorem s5_1587_edges : next config 5 s5_1587 = [s6_1434] := by decide
theorem s5_1587_safe : Safe 8 5 s5_1587 := by
  apply safe_succ 7 5 s5_1587 [s6_1434] (by decide) s5_1587_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1434_safe
def s5_1588 : State := ⟨[171,4,96,162], 2999001359804714199988645197213662340452803967779606, 1, 0, 1, 0⟩
theorem s5_1588_edges : next config 5 s5_1588 = [s6_1435] := by decide
theorem s5_1588_safe : Safe 8 5 s5_1588 := by
  apply safe_succ 7 5 s5_1588 [s6_1435] (by decide) s5_1588_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1435_safe
def s5_1589 : State := ⟨[171,4,96,162], 3000462861440683973439165128192525125042732827476758, 1, 0, 1, 0⟩
theorem s5_1589_edges : next config 5 s5_1589 = [s6_1436] := by decide
theorem s5_1589_safe : Safe 8 5 s5_1589 := by
  apply safe_succ 7 5 s5_1589 [s6_1436] (by decide) s5_1589_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1436_safe
def s5_1590 : State := ⟨[171,4,96,162], 3010693372903361423334274675875392604610051428122902, 1, 0, 1, 0⟩
theorem s5_1590_edges : next config 5 s5_1590 = [s6_1437] := by decide
theorem s5_1590_safe : Safe 8 5 s5_1590 := by
  apply safe_succ 7 5 s5_1590 [s6_1437] (by decide) s5_1590_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1437_safe
def s5_1591 : State := ⟨[171,4,96,162], 3012154874539331196784794606854255389199980287820054, 1, 0, 1, 0⟩
theorem s5_1591_edges : next config 5 s5_1591 = [s6_1438] := by decide
theorem s5_1591_safe : Safe 8 5 s5_1591 := by
  apply safe_succ 7 5 s5_1591 [s6_1438] (by decide) s5_1591_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_1438_safe
def s5_1592 : State := ⟨[171,4,96,170], 4495579036431558788229218465915136152580478891786518, 1, 0, 1, 0⟩
theorem s5_1592_edges : next config 5 s5_1592 = [s6_146, s6_1439] := by decide
theorem s5_1592_safe : Safe 8 5 s5_1592 := by
  apply safe_succ 7 5 s5_1592 [s6_146, s6_1439] (by decide) s5_1592_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_146_safe
  · subst z; exact s6_1439_safe
def s5_1593 : State := ⟨[171,4,96,170], 4497040538067528561679738396893998937170407751483670, 1, 0, 1, 0⟩
theorem s5_1593_edges : next config 5 s5_1593 = [s6_147, s6_1440] := by decide
theorem s5_1593_safe : Safe 8 5 s5_1593 := by
  apply safe_succ 7 5 s5_1593 [s6_147, s6_1440] (by decide) s5_1593_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_147_safe
  · subst z; exact s6_1440_safe
def s5_1594 : State := ⟨[193,4,96,192], 18831305206160042291847650636623165874303152022495420289302, 3, 2, 1, 0⟩
theorem s5_1594_edges : next config 5 s5_1594 = [s6_160, s6_1441] := by decide
theorem s5_1594_safe : Safe 8 5 s5_1594 := by
  apply safe_succ 7 5 s5_1594 [s6_160, s6_1441] (by decide) s5_1594_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_160_safe
  · subst z; exact s6_1441_safe
def s5_1595 : State := ⟨[193,4,96,192], 18831305206160042291847650637890816474531381423992123490582, 3, 2, 1, 0⟩
theorem s5_1595_edges : next config 5 s5_1595 = [s6_161, s6_1442] := by decide
theorem s5_1595_safe : Safe 8 5 s5_1595 := by
  apply safe_succ 7 5 s5_1595 [s6_161, s6_1442] (by decide) s5_1595_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_161_safe
  · subst z; exact s6_1442_safe
def s5_1596 : State := ⟨[193,4,108,192], 18831305206160042291847650981424129136381549229598692147478, 1, 0, 1, 0⟩
theorem s5_1596_edges : next config 5 s5_1596 = [s6_357] := by decide
theorem s5_1596_safe : Safe 8 5 s5_1596 := by
  apply safe_succ 7 5 s5_1596 [s6_357] (by decide) s5_1596_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_357_safe
def s5_1597 : State := ⟨[193,12,104,192], 18831305206160042291847650656905575477954822446442671575318, 3, 0, 1, 0⟩
theorem s5_1597_edges : next config 5 s5_1597 = [s6_507, s6_1441] := by decide
theorem s5_1597_safe : Safe 8 5 s5_1597 := by
  apply safe_succ 7 5 s5_1597 [s6_507, s6_1441] (by decide) s5_1597_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_507_safe
  · subst z; exact s6_1441_safe
def s5_1598 : State := ⟨[193,100,104,192], 18831305206160042291847650658173226078183051847939374776598, 3, 0, 1, 0⟩
theorem s5_1598_edges : next config 5 s5_1598 = [s6_575] := by decide
theorem s5_1598_safe : Safe 8 5 s5_1598 := by
  apply safe_succ 7 5 s5_1598 [s6_575] (by decide) s5_1598_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_575_safe
def s5_1599 : State := ⟨[193,108,104,192], 18831305206160042291847650981424129136381549229598692147478, 3, 0, 1, 0⟩
theorem s5_1599_edges : next config 5 s5_1599 = [s6_600, s6_1443] := by decide
theorem s5_1599_safe : Safe 8 5 s5_1599 := by
  apply safe_succ 7 5 s5_1599 [s6_600, s6_1443] (by decide) s5_1599_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_600_safe
  · subst z; exact s6_1443_safe
def s5_1600 : State := ⟨[225,4,96,224], 80879840001451919384001045261399174387911599893617803132414147498262, 3, 2, 1, 0⟩
theorem s5_1600_edges : next config 5 s5_1600 = [s6_186, s6_1444] := by decide
theorem s5_1600_safe : Safe 8 5 s5_1600 := by
  apply safe_succ 7 5 s5_1600 [s6_186, s6_1444] (by decide) s5_1600_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_186_safe
  · subst z; exact s6_1444_safe
def s5_1601 : State := ⟨[225,12,104,224], 80879840001451919384001045261399174408194009497269473556361398784278, 3, 0, 1, 0⟩
theorem s5_1601_edges : next config 5 s5_1601 = [s6_521, s6_1444] := by decide
theorem s5_1601_safe : Safe 8 5 s5_1601 := by
  apply safe_succ 7 5 s5_1601 [s6_521, s6_1444] (by decide) s5_1601_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_521_safe
  · subst z; exact s6_1444_safe
end HGP13.SectorGraph234
