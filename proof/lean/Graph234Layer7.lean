import Graph234Layer8
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s7_0 : State := ⟨[1,4,64,145], 133806172603018343541531644955671405881528606, 3, 3, 1, 0⟩
theorem s7_0_edges : next config 7 s7_0 = [s8_10] := by decide
theorem s7_0_safe : Safe 6 7 s7_0 := by
  apply safe_succ 5 7 s7_0 [s8_10] (by decide) s7_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_10_safe
def s7_1 : State := ⟨[1,4,64,145], 156105556672081282929213509729890040314663198, 3, 3, 1, 0⟩
theorem s7_1_edges : next config 7 s7_1 = [s8_11] := by decide
theorem s7_1_safe : Safe 6 7 s7_1 := by
  apply safe_succ 5 7 s7_1 [s8_11] (by decide) s7_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_11_safe
def s7_2 : State := ⟨[1,4,67,145], 44601830679428167221535102834088969880408342, 3, 3, 1, 0⟩
theorem s7_2_edges : next config 7 s7_2 = [] := by decide
theorem s7_2_safe : Safe 6 7 s7_2 := by
  apply safe_succ 5 7 s7_2 [] (by decide) s7_2_edges
  simp
def s7_3 : State := ⟨[1,4,67,145], 44601830679428167221535102834088969882501398, 3, 3, 1, 0⟩
theorem s7_3_edges : next config 7 s7_3 = [s8_59] := by decide
theorem s7_3_safe : Safe 6 7 s7_3 := by
  apply safe_succ 5 7 s7_3 [s8_59] (by decide) s7_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_59_safe
def s7_4 : State := ⟨[1,4,67,145], 44601830679428167221535139727577117299511574, 3, 3, 1, 0⟩
theorem s7_4_edges : next config 7 s7_4 = [] := by decide
theorem s7_4_safe : Safe 6 7 s7_4 := by
  apply safe_succ 5 7 s7_4 [] (by decide) s7_4_edges
  simp
def s7_5 : State := ⟨[1,4,67,145], 44601830679428167221535139727577117301604630, 3, 3, 1, 0⟩
theorem s7_5_edges : next config 7 s7_5 = [s8_60] := by decide
theorem s7_5_safe : Safe 6 7 s7_5 := by
  apply safe_succ 5 7 s7_5 [s8_60] (by decide) s7_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_60_safe
def s7_6 : State := ⟨[1,4,67,145], 44602511244162009098461992689815685997596958, 3, 3, 1, 0⟩
theorem s7_6_edges : next config 7 s7_6 = [] := by decide
theorem s7_6_safe : Safe 6 7 s7_6 := by
  apply safe_succ 5 7 s7_6 [] (by decide) s7_6_edges
  simp
def s7_7 : State := ⟨[1,4,67,145], 66902575877958790363070784213249183967154462, 3, 3, 1, 0⟩
theorem s7_7_edges : next config 7 s7_7 = [] := by decide
theorem s7_7_safe : Safe 6 7 s7_7 := by
  apply safe_succ 5 7 s7_7 [] (by decide) s7_7_edges
  simp
def s7_8 : State := ⟨[1,4,67,145], 1645504557321206042221871758435309295345806723633805342153969942, 2, 2, 1, 0⟩
theorem s7_8_edges : next config 7 s7_8 = [] := by decide
theorem s7_8_safe : Safe 6 7 s7_8 := by
  apply safe_succ 5 7 s7_8 [] (by decide) s7_8_edges
  simp
def s7_9 : State := ⟨[1,4,67,145], 1645529665728147588922626356394471502869935414782934836786041110, 2, 2, 1, 0⟩
theorem s7_9_edges : next config 7 s7_9 = [] := by decide
theorem s7_9_safe : Safe 6 7 s7_9 := by
  apply safe_succ 5 7 s7_9 [] (by decide) s7_9_edges
  simp
def s7_10 : State := ⟨[1,4,67,145], 2056880696651507552760614054074646921591490616255224013152915734, 2, 2, 1, 0⟩
theorem s7_10_edges : next config 7 s7_10 = [] := by decide
theorem s7_10_safe : Safe 6 7 s7_10 := by
  apply safe_succ 5 7 s7_10 [] (by decide) s7_10_edges
  simp
def s7_11 : State := ⟨[1,4,67,145], 27973577474460502716701378679352917375069580573771083155731710230, 2, 2, 1, 0⟩
theorem s7_11_edges : next config 7 s7_11 = [] := by decide
theorem s7_11_safe : Safe 6 7 s7_11 := by
  apply safe_succ 5 7 s7_11 [] (by decide) s7_11_edges
  simp
def s7_12 : State := ⟨[1,4,67,145], 27973602582867444263402133277312079582593709264920212650363781398, 2, 2, 1, 0⟩
theorem s7_12_edges : next config 7 s7_12 = [] := by decide
theorem s7_12_safe : Safe 6 7 s7_12 := by
  apply safe_succ 5 7 s7_12 [] (by decide) s7_12_edges
  simp
def s7_13 : State := ⟨[1,4,67,145], 28384953613790804227240120974992255001315264466392501826730656022, 2, 2, 1, 0⟩
theorem s7_13_edges : next config 7 s7_13 = [] := by decide
theorem s7_13_safe : Safe 6 7 s7_13 := by
  apply safe_succ 5 7 s7_13 [] (by decide) s7_13_edges
  simp
def s7_14 : State := ⟨[1,4,67,146], 89204682205957097258460355984327272545980702, 3, 3, 1, 0⟩
theorem s7_14_edges : next config 7 s7_14 = [] := by decide
theorem s7_14_safe : Safe 6 7 s7_14 := by
  apply safe_succ 5 7 s7_14 [] (by decide) s7_14_edges
  simp
def s7_15 : State := ⟨[1,4,67,146], 111504066275020036646142220758545906979115294, 3, 3, 1, 0⟩
theorem s7_15_edges : next config 7 s7_15 = [] := by decide
theorem s7_15_safe : Safe 6 7 s7_15 := by
  apply safe_succ 5 7 s7_15 [] (by decide) s7_15_edges
  simp
def s7_16 : State := ⟨[1,4,67,162], 5846006551025023507419431648348025812450252230942, 3, 3, 1, 0⟩
theorem s7_16_edges : next config 7 s7_16 = [] := by decide
theorem s7_16_safe : Safe 6 7 s7_16 := by
  apply safe_succ 5 7 s7_16 [] (by decide) s7_16_edges
  simp
def s7_17 : State := ⟨[1,4,67,162], 7307508186994796957939362627210810402379111928094, 3, 3, 1, 0⟩
theorem s7_17_edges : next config 7 s7_17 = [] := by decide
theorem s7_17_safe : Safe 6 7 s7_17 := by
  apply safe_succ 5 7 s7_17 [] (by decide) s7_17_edges
  simp
def s7_18 : State := ⟨[1,4,67,163], 11692013101709764647917924833066656320801055248670, 3, 3, 1, 0⟩
theorem s7_18_edges : next config 7 s7_18 = [] := by decide
theorem s7_18_safe : Safe 6 7 s7_18 := by
  apply safe_succ 5 7 s7_18 [] (by decide) s7_18_edges
  simp
def s7_19 : State := ⟨[1,4,67,163], 13153514736318408630754101958075942481002842099998, 3, 3, 1, 0⟩
theorem s7_19_edges : next config 7 s7_19 = [] := by decide
theorem s7_19_safe : Safe 6 7 s7_19 := by
  apply safe_succ 5 7 s7_19 [] (by decide) s7_19_edges
  simp
def s7_20 : State := ⟨[1,4,67,176], 95780971326419139128294233276893671644123656091668766, 3, 3, 1, 0⟩
theorem s7_20_edges : next config 7 s7_20 = [] := by decide
theorem s7_20_safe : Safe 6 7 s7_20 := by
  apply safe_succ 5 7 s7_20 [] (by decide) s7_20_edges
  simp
def s7_21 : State := ⟨[1,4,67,176], 95782432805755724832681813820190669654494950518231326, 3, 3, 1, 0⟩
theorem s7_21_edges : next config 7 s7_21 = [] := by decide
theorem s7_21_safe : Safe 6 7 s7_21 := by
  apply safe_succ 5 7 s7_21 [] (by decide) s7_21_edges
  simp
def s7_22 : State := ⟨[1,4,82,145], 44601830679428167226370695432083044321923350, 3, 3, 1, 0⟩
theorem s7_22_edges : next config 7 s7_22 = [] := by decide
theorem s7_22_safe : Safe 6 7 s7_22 := by
  apply safe_succ 5 7 s7_22 [] (by decide) s7_22_edges
  simp
def s7_23 : State := ⟨[1,4,82,145], 44601830679428167226370695432083044324016406, 3, 3, 1, 0⟩
theorem s7_23_edges : next config 7 s7_23 = [s8_89, s8_61, s8_8] := by decide
theorem s7_23_safe : Safe 6 7 s7_23 := by
  apply safe_succ 5 7 s7_23 [s8_89, s8_61, s8_8] (by decide) s7_23_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_89_safe
  · subst z; exact s8_61_safe
  · subst z; exact s8_8_safe
def s7_24 : State := ⟨[1,4,82,145], 44601830679428167227579547464721378658423062, 3, 3, 1, 0⟩
theorem s7_24_edges : next config 7 s7_24 = [] := by decide
theorem s7_24_safe : Safe 6 7 s7_24 := by
  apply safe_succ 5 7 s7_24 [] (by decide) s7_24_edges
  simp
def s7_25 : State := ⟨[1,4,82,145], 44601830679428167227579547464721378660516118, 3, 3, 1, 0⟩
theorem s7_25_edges : next config 7 s7_25 = [s8_90, s8_62, s8_9] := by decide
theorem s7_25_safe : Safe 6 7 s7_25 := by
  apply safe_succ 5 7 s7_25 [s8_90, s8_62, s8_9] (by decide) s7_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_90_safe
  · subst z; exact s8_62_safe
  · subst z; exact s8_9_safe
def s7_26 : State := ⟨[1,4,82,145], 44601830679428167303741947887419311503114518, 3, 3, 1, 0⟩
theorem s7_26_edges : next config 7 s7_26 = [] := by decide
theorem s7_26_safe : Safe 6 7 s7_26 := by
  apply safe_succ 5 7 s7_26 [] (by decide) s7_26_edges
  simp
def s7_27 : State := ⟨[1,4,82,145], 44601830679428167304950799920057645839614230, 3, 3, 1, 0⟩
theorem s7_27_edges : next config 7 s7_27 = [] := by decide
theorem s7_27_safe : Safe 6 7 s7_27 := by
  apply safe_succ 5 7 s7_27 [] (by decide) s7_27_edges
  simp
def s7_28 : State := ⟨[1,4,96,145], 44602511244162088326624359380200689865134366, 3, 3, 1, 0⟩
theorem s7_28_edges : next config 7 s7_28 = [s8_54, s8_12] := by decide
theorem s7_28_safe : Safe 6 7 s7_28 := by
  apply safe_succ 5 7 s7_28 [s8_54, s8_12] (by decide) s7_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_54_safe
  · subst z; exact s8_12_safe
def s7_29 : State := ⟨[1,4,96,145], 44602511244162088326624359380200698455068950, 3, 3, 1, 0⟩
theorem s7_29_edges : next config 7 s7_29 = [s8_13] := by decide
theorem s7_29_safe : Safe 6 7 s7_29 := by
  apply safe_succ 5 7 s7_29 [s8_13] (by decide) s7_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_13_safe
def s7_30 : State := ⟨[1,4,96,145], 44602511244162088326624396273688837284237590, 3, 3, 1, 0⟩
theorem s7_30_edges : next config 7 s7_30 = [s8_55, s8_14] := by decide
theorem s7_30_safe : Safe 6 7 s7_30 := by
  apply safe_succ 5 7 s7_30 [s8_55, s8_14] (by decide) s7_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_55_safe
  · subst z; exact s8_14_safe
def s7_31 : State := ⟨[1,4,96,145], 44602511244162246782949387908875876953035030, 3, 3, 1, 0⟩
theorem s7_31_edges : next config 7 s7_31 = [s8_15] := by decide
theorem s7_31_safe : Safe 6 7 s7_31 := by
  apply safe_succ 5 7 s7_31 [s8_15] (by decide) s7_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_15_safe
def s7_32 : State := ⟨[1,4,96,145], 44602511244163355977224587609602186568335646, 3, 3, 1, 0⟩
theorem s7_32_edges : next config 7 s7_32 = [s8_16] := by decide
theorem s7_32_safe : Safe 6 7 s7_32 := by
  apply safe_succ 5 7 s7_32 [s8_16] (by decide) s7_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_16_safe
def s7_33 : State := ⟨[1,4,96,145], 44602511244163355977224624503090333987438870, 3, 3, 1, 0⟩
theorem s7_33_edges : next config 7 s7_33 = [s8_17] := by decide
theorem s7_33_safe : Safe 6 7 s7_33 := by
  apply safe_succ 5 7 s7_33 [s8_17] (by decide) s7_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_17_safe
def s7_34 : State := ⟨[1,4,96,145], 66902575877958869591233150903634187834691870, 3, 3, 1, 0⟩
theorem s7_34_edges : next config 7 s7_34 = [s8_56, s8_20] := by decide
theorem s7_34_safe : Safe 6 7 s7_34 := by
  apply safe_succ 5 7 s7_34 [s8_56, s8_20] (by decide) s7_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_56_safe
  · subst z; exact s8_20_safe
def s7_35 : State := ⟨[1,4,96,145], 66902575877958869591233150903634196424626454, 3, 3, 1, 0⟩
theorem s7_35_edges : next config 7 s7_35 = [s8_21] := by decide
theorem s7_35_safe : Safe 6 7 s7_35 := by
  apply safe_succ 5 7 s7_35 [s8_21] (by decide) s7_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_21_safe
def s7_36 : State := ⟨[1,4,96,145], 66902575877958869591233187797122335253795094, 3, 3, 1, 0⟩
theorem s7_36_edges : next config 7 s7_36 = [s8_57, s8_22] := by decide
theorem s7_36_safe : Safe 6 7 s7_36 := by
  apply safe_succ 5 7 s7_36 [s8_57, s8_22] (by decide) s7_36_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_57_safe
  · subst z; exact s8_22_safe
def s7_37 : State := ⟨[1,4,96,145], 66902575877959028047558179432309374922592534, 3, 3, 1, 0⟩
theorem s7_37_edges : next config 7 s7_37 = [s8_23] := by decide
theorem s7_37_safe : Safe 6 7 s7_37 := by
  apply safe_succ 5 7 s7_37 [s8_23] (by decide) s7_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_23_safe
def s7_38 : State := ⟨[1,4,96,145], 66902575877960137241833379133035684537893150, 3, 3, 1, 0⟩
theorem s7_38_edges : next config 7 s7_38 = [s8_24] := by decide
theorem s7_38_safe : Safe 6 7 s7_38 := by
  apply safe_succ 5 7 s7_38 [s8_24] (by decide) s7_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_24_safe
def s7_39 : State := ⟨[1,4,96,145], 66902575877960137241833416026523831956996374, 3, 3, 1, 0⟩
theorem s7_39_edges : next config 7 s7_39 = [s8_25] := by decide
theorem s7_39_safe : Safe 6 7 s7_39 := by
  apply safe_succ 5 7 s7_39 [s8_25] (by decide) s7_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_25_safe
def s7_40 : State := ⟨[1,4,96,146], 89204682205957176486622722674712276413518110, 3, 3, 1, 0⟩
theorem s7_40_edges : next config 7 s7_40 = [s8_28] := by decide
theorem s7_40_safe : Safe 6 7 s7_40 := by
  apply safe_succ 5 7 s7_40 [s8_28] (by decide) s7_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_28_safe
def s7_41 : State := ⟨[1,4,96,146], 89204682205957176486622759568200423832621334, 3, 3, 1, 0⟩
theorem s7_41_edges : next config 7 s7_41 = [s8_29] := by decide
theorem s7_41_safe : Safe 6 7 s7_41 := by
  apply safe_succ 5 7 s7_41 [s8_29] (by decide) s7_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_29_safe
def s7_42 : State := ⟨[1,4,96,146], 89207404464892543994330429671571730559209750, 3, 3, 1, 0⟩
theorem s7_42_edges : next config 7 s7_42 = [s8_30] := by decide
theorem s7_42_safe : Safe 6 7 s7_42 := by
  apply safe_succ 5 7 s7_42 [s8_30] (by decide) s7_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_30_safe
def s7_43 : State := ⟨[1,4,96,146], 111504066275020115874304587448930910846652702, 3, 3, 1, 0⟩
theorem s7_43_edges : next config 7 s7_43 = [s8_31] := by decide
theorem s7_43_safe : Safe 6 7 s7_43 := by
  apply safe_succ 5 7 s7_43 [s8_31] (by decide) s7_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_31_safe
def s7_44 : State := ⟨[1,4,96,146], 111504066275020115874304624342419058265755926, 3, 3, 1, 0⟩
theorem s7_44_edges : next config 7 s7_44 = [s8_32] := by decide
theorem s7_44_safe : Safe 6 7 s7_44 := by
  apply safe_succ 5 7 s7_44 [s8_32] (by decide) s7_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_32_safe
def s7_45 : State := ⟨[1,4,96,162], 5846006551025023507498659810714716197454119768350, 3, 3, 1, 0⟩
theorem s7_45_edges : next config 7 s7_45 = [s8_33] := by decide
theorem s7_45_safe : Safe 6 7 s7_45 := by
  apply safe_succ 5 7 s7_45 [s8_33] (by decide) s7_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_33_safe
def s7_46 : State := ⟨[1,4,96,162], 5846006551025023507498659810751609685601538871574, 3, 3, 1, 0⟩
theorem s7_46_edges : next config 7 s7_46 = [s8_34] := by decide
theorem s7_46_safe : Safe 6 7 s7_46 := by
  apply safe_succ 5 7 s7_46 [s8_34] (by decide) s7_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_34_safe
def s7_47 : State := ⟨[1,4,96,162], 5846006551025023507657116135743244872641207669014, 3, 3, 1, 0⟩
theorem s7_47_edges : next config 7 s7_47 = [s8_35] := by decide
theorem s7_47_safe : Safe 6 7 s7_47 := by
  apply safe_succ 5 7 s7_47 [s8_35] (by decide) s7_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_35_safe
def s7_48 : State := ⟨[1,4,96,162], 5846006553747282442866167518421713056908265459990, 3, 3, 1, 0⟩
theorem s7_48_edges : next config 7 s7_48 = [s8_36] := by decide
theorem s7_48_safe : Safe 6 7 s7_48 := by
  apply safe_succ 5 7 s7_48 [s8_36] (by decide) s7_48_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_36_safe
def s7_49 : State := ⟨[1,4,96,162], 7307508186994796958018590789577500787382979465502, 3, 3, 1, 0⟩
theorem s7_49_edges : next config 7 s7_49 = [s8_37] := by decide
theorem s7_49_safe : Safe 6 7 s7_49 := by
  apply safe_succ 5 7 s7_49 [s8_37] (by decide) s7_49_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_37_safe
def s7_50 : State := ⟨[1,4,96,162], 7307508186994796958018590789614394275530398568726, 3, 3, 1, 0⟩
theorem s7_50_edges : next config 7 s7_50 = [s8_38] := by decide
theorem s7_50_safe : Safe 6 7 s7_50 := by
  apply safe_succ 5 7 s7_50 [s8_38] (by decide) s7_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_38_safe
def s7_51 : State := ⟨[1,4,96,162], 7307508186994796958177047114606029462570067366166, 3, 3, 1, 0⟩
theorem s7_51_edges : next config 7 s7_51 = [s8_39] := by decide
theorem s7_51_safe : Safe 6 7 s7_51 := by
  apply safe_succ 5 7 s7_51 [s8_39] (by decide) s7_51_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_39_safe
def s7_52 : State := ⟨[1,4,96,162], 17538019649672246853128138472444980354701580112150, 3, 3, 1, 0⟩
theorem s7_52_edges : next config 7 s7_52 = [s8_40] := by decide
theorem s7_52_safe : Safe 6 7 s7_52 := by
  apply safe_succ 5 7 s7_52 [s8_40] (by decide) s7_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_40_safe
def s7_53 : State := ⟨[1,4,96,162], 18999521285642020303648069451307764944630439809302, 3, 3, 1, 0⟩
theorem s7_53_edges : next config 7 s7_53 = [s8_41] := by decide
theorem s7_53_safe : Safe 6 7 s7_53 := by
  apply safe_succ 5 7 s7_53 [s8_41] (by decide) s7_53_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_41_safe
def s7_54 : State := ⟨[1,4,96,163], 11692013100348635180313399141579848276086439874838, 3, 3, 1, 0⟩
theorem s7_54_edges : next config 7 s7_54 = [s8_42] := by decide
theorem s7_54_safe : Safe 6 7 s7_54 := by
  apply safe_succ 5 7 s7_54 [s8_42] (by decide) s7_54_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_42_safe
def s7_55 : State := ⟨[1,4,96,163], 11692013101709764647997152995433346705804922786078, 3, 3, 1, 0⟩
theorem s7_55_edges : next config 7 s7_55 = [s8_43] := by decide
theorem s7_55_safe : Safe 6 7 s7_55 := by
  apply safe_succ 5 7 s7_55 [s8_43] (by decide) s7_55_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_43_safe
def s7_56 : State := ⟨[1,4,96,163], 13153514736318408630833330120442632866006709637406, 3, 3, 1, 0⟩
theorem s7_56_edges : next config 7 s7_56 = [s8_44] := by decide
theorem s7_56_safe : Safe 6 7 s7_56 := by
  apply safe_succ 5 7 s7_56 [s8_44] (by decide) s7_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_44_safe
def s7_57 : State := ⟨[1,4,96,163], 14615016373649311549037014953158915885671232114966, 3, 3, 1, 0⟩
theorem s7_57_edges : next config 7 s7_57 = [s8_45] := by decide
theorem s7_57_safe : Safe 6 7 s7_57 := by
  apply safe_succ 5 7 s7_57 [s8_45] (by decide) s7_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_45_safe
def s7_58 : State := ⟨[1,4,96,176], 95780971326419139128294312505056038334508659959206174, 3, 3, 1, 0⟩
theorem s7_58_edges : next config 7 s7_58 = [s8_46] := by decide
theorem s7_58_safe : Safe 6 7 s7_58 := by
  apply safe_succ 5 7 s7_58 [s8_46] (by decide) s7_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_46_safe
def s7_59 : State := ⟨[1,4,96,176], 95780971326419139128294312505056075227996807378309398, 3, 3, 1, 0⟩
theorem s7_59_edges : next config 7 s7_59 = [s8_47] := by decide
theorem s7_59_safe : Safe 6 7 s7_59 := by
  apply safe_succ 5 7 s7_59 [s8_47] (by decide) s7_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_47_safe
def s7_60 : State := ⟨[1,4,96,176], 95782432805755724832681893048353036344879954385768734, 3, 3, 1, 0⟩
theorem s7_60_edges : next config 7 s7_60 = [s8_48] := by decide
theorem s7_60_safe : Safe 6 7 s7_60 := by
  apply safe_succ 5 7 s7_60 [s8_48] (by decide) s7_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_48_safe
def s7_61 : State := ⟨[1,4,96,176], 95782432805755724832681893048353073238368101804871958, 3, 3, 1, 0⟩
theorem s7_61_edges : next config 7 s7_61 = [s8_49] := by decide
theorem s7_61_safe : Safe 6 7 s7_61 := by
  apply safe_succ 5 7 s7_61 [s8_49] (by decide) s7_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_49_safe
def s7_62 : State := ⟨[1,4,97,145], 44601830679428404906022461159661013416743190, 3, 3, 1, 0⟩
theorem s7_62_edges : next config 7 s7_62 = [] := by decide
theorem s7_62_safe : Safe 6 7 s7_62 := by
  apply safe_succ 5 7 s7_62 [] (by decide) s7_62_edges
  simp
def s7_63 : State := ⟨[1,4,97,145], 44601830679428404906022461159661013418836246, 3, 3, 1, 0⟩
theorem s7_63_edges : next config 7 s7_63 = [s8_63] := by decide
theorem s7_63_safe : Safe 6 7 s7_63 := by
  apply safe_succ 5 7 s7_63 [s8_63] (by decide) s7_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_63_safe
def s7_64 : State := ⟨[1,4,100,145], 44601830679429514100297660860387323034140950, 3, 3, 1, 0⟩
theorem s7_64_edges : next config 7 s7_64 = [s8_93] := by decide
theorem s7_64_safe : Safe 6 7 s7_64 := by
  apply safe_succ 5 7 s7_64 [s8_93] (by decide) s7_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_93_safe
def s7_65 : State := ⟨[1,4,104,129], 1020847121124453156574505327914104459550, 3, 3, 1, 0⟩
theorem s7_65_edges : next config 7 s7_65 = [s8_12] := by decide
theorem s7_65_safe : Safe 6 7 s7_65 := by
  apply safe_succ 5 7 s7_65 [s8_12] (by decide) s7_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_12_safe
def s7_66 : State := ⟨[1,4,104,129], 1020847121124453156574505327922694394134, 3, 3, 1, 0⟩
theorem s7_66_edges : next config 7 s7_66 = [s8_13] := by decide
theorem s7_66_safe : Safe 6 7 s7_66 := by
  apply safe_succ 5 7 s7_66 [s8_13] (by decide) s7_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_13_safe
def s7_67 : State := ⟨[1,4,104,129], 1020847121124453156611398816061523562774, 3, 3, 1, 0⟩
theorem s7_67_edges : next config 7 s7_67 = [s8_14] := by decide
theorem s7_67_safe : Safe 6 7 s7_67 := by
  apply safe_succ 5 7 s7_67 [s8_14] (by decide) s7_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_14_safe
def s7_68 : State := ⟨[1,4,104,129], 1020847121282909481603034003101192360214, 3, 3, 1, 0⟩
theorem s7_68_edges : next config 7 s7_68 = [s8_15] := by decide
theorem s7_68_safe : Safe 6 7 s7_68 := by
  apply safe_succ 5 7 s7_68 [s8_15] (by decide) s7_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_15_safe
def s7_69 : State := ⟨[1,4,104,129], 1020847122392103756802734729410807660830, 3, 3, 1, 0⟩
theorem s7_69_edges : next config 7 s7_69 = [s8_16] := by decide
theorem s7_69_safe : Safe 6 7 s7_69 := by
  apply safe_succ 5 7 s7_69 [s8_16] (by decide) s7_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_16_safe
def s7_70 : State := ⟨[1,4,104,129], 1020847122392103756839628217558226764054, 3, 3, 1, 0⟩
theorem s7_70_edges : next config 7 s7_70 = [s8_17] := by decide
theorem s7_70_safe : Safe 6 7 s7_70 := by
  apply safe_succ 5 7 s7_70 [s8_17] (by decide) s7_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_17_safe
def s7_71 : State := ⟨[1,4,104,129], 1020847445643006815001232111070125031710, 3, 3, 1, 0⟩
theorem s7_71_edges : next config 7 s7_71 = [s8_18] := by decide
theorem s7_71_safe : Safe 6 7 s7_71 := by
  apply safe_succ 5 7 s7_71 [s8_18] (by decide) s7_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_18_safe
def s7_72 : State := ⟨[1,4,104,129], 1020847445643006815038125599217544134934, 3, 3, 1, 0⟩
theorem s7_72_edges : next config 7 s7_72 = [s8_19] := by decide
theorem s7_72_safe : Safe 6 7 s7_72 := by
  apply safe_succ 5 7 s7_72 [s8_19] (by decide) s7_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_19_safe
def s7_73 : State := ⟨[1,4,104,130], 1701411854966330083501254542777640882462, 3, 3, 1, 0⟩
theorem s7_73_edges : next config 7 s7_73 = [s8_28, s8_33] := by decide
theorem s7_73_safe : Safe 6 7 s7_73 := by
  apply safe_succ 5 7 s7_73 [s8_28, s8_33] (by decide) s7_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_28_safe
  · subst z; exact s8_33_safe
def s7_74 : State := ⟨[1,4,104,130], 1701411854966330083501254542786230817046, 3, 3, 1, 0⟩
theorem s7_74_edges : next config 7 s7_74 = [] := by decide
theorem s7_74_safe : Safe 6 7 s7_74 := by
  apply safe_succ 5 7 s7_74 [] (by decide) s7_74_edges
  simp
def s7_75 : State := ⟨[1,4,104,130], 1701411854966330083538148030925059985686, 3, 3, 1, 0⟩
theorem s7_75_edges : next config 7 s7_75 = [s8_29, s8_34] := by decide
theorem s7_75_safe : Safe 6 7 s7_75 := by
  apply safe_succ 5 7 s7_75 [s8_29, s8_34] (by decide) s7_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_29_safe
  · subst z; exact s8_34_safe
def s7_76 : State := ⟨[1,4,104,130], 1701411855124786408529783217964728783126, 3, 3, 1, 0⟩
theorem s7_76_edges : next config 7 s7_76 = [s8_35] := by decide
theorem s7_76_safe : Safe 6 7 s7_76 := by
  apply safe_succ 5 7 s7_76 [s8_35] (by decide) s7_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_35_safe
def s7_77 : State := ⟨[1,4,104,130], 1701411856233980683729483944274344083742, 3, 3, 1, 0⟩
theorem s7_77_edges : next config 7 s7_77 = [] := by decide
theorem s7_77_safe : Safe 6 7 s7_77 := by
  apply safe_succ 5 7 s7_77 [] (by decide) s7_77_edges
  simp
def s7_78 : State := ⟨[1,4,104,130], 1701411856233980683766377432421763186966, 3, 3, 1, 0⟩
theorem s7_78_edges : next config 7 s7_78 = [] := by decide
theorem s7_78_safe : Safe 6 7 s7_78 := by
  apply safe_succ 5 7 s7_78 [] (by decide) s7_78_edges
  simp
def s7_79 : State := ⟨[1,4,104,130], 1701412179484883741927981325933661454622, 3, 3, 1, 0⟩
theorem s7_79_edges : next config 7 s7_79 = [] := by decide
theorem s7_79_safe : Safe 6 7 s7_79 := by
  apply safe_succ 5 7 s7_79 [] (by decide) s7_79_edges
  simp
def s7_80 : State := ⟨[1,4,104,130], 1701412179484883741964874814081080557846, 3, 3, 1, 0⟩
theorem s7_80_edges : next config 7 s7_80 = [] := by decide
theorem s7_80_safe : Safe 6 7 s7_80 := by
  apply safe_succ 5 7 s7_80 [] (by decide) s7_80_edges
  simp
def s7_81 : State := ⟨[1,4,104,130], 4423670790333837791208251402231786574102, 3, 3, 1, 0⟩
theorem s7_81_edges : next config 7 s7_81 = [s8_30, s8_36] := by decide
theorem s7_81_safe : Safe 6 7 s7_81 := by
  apply safe_succ 5 7 s7_81 [s8_30, s8_36] (by decide) s7_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_30_safe
  · subst z; exact s8_36_safe
def s7_82 : State := ⟨[1,4,104,130], 4423670791601488391436480803728489775382, 3, 3, 1, 0⟩
theorem s7_82_edges : next config 7 s7_82 = [] := by decide
theorem s7_82_safe : Safe 6 7 s7_82 := by
  apply safe_succ 5 7 s7_82 [] (by decide) s7_82_edges
  simp
def s7_83 : State := ⟨[1,4,104,130], 4423671114852391449634978185387807146262, 3, 3, 1, 0⟩
theorem s7_83_edges : next config 7 s7_83 = [] := by decide
theorem s7_83_safe : Safe 6 7 s7_83 := by
  apply safe_succ 5 7 s7_83 [] (by decide) s7_83_edges
  simp
def s7_84 : State := ⟨[1,4,104,131], 3062541322650083937354752972504713728286, 3, 3, 1, 0⟩
theorem s7_84_edges : next config 7 s7_84 = [s8_43] := by decide
theorem s7_84_safe : Safe 6 7 s7_84 := by
  apply safe_succ 5 7 s7_84 [s8_43] (by decide) s7_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_43_safe
def s7_85 : State := ⟨[1,4,104,131], 3062541323917734537582982374001416929566, 3, 3, 1, 0⟩
theorem s7_85_edges : next config 7 s7_85 = [] := by decide
theorem s7_85_safe : Safe 6 7 s7_85 := by
  apply safe_succ 5 7 s7_85 [] (by decide) s7_85_edges
  simp
def s7_86 : State := ⟨[1,4,104,131], 3062541647168637595781479755660734300446, 3, 3, 1, 0⟩
theorem s7_86_edges : next config 7 s7_86 = [] := by decide
theorem s7_86_safe : Safe 6 7 s7_86 := by
  apply safe_succ 5 7 s7_86 [] (by decide) s7_86_edges
  simp
def s7_87 : State := ⟨[1,4,104,132], 5784800258017591645061749831958859419934, 3, 3, 1, 0⟩
theorem s7_87_edges : next config 7 s7_87 = [] := by decide
theorem s7_87_safe : Safe 6 7 s7_87 := by
  apply safe_succ 5 7 s7_87 [] (by decide) s7_87_edges
  simp
def s7_88 : State := ⟨[1,4,104,132], 5784800258017591645061749831967449354518, 3, 3, 1, 0⟩
theorem s7_88_edges : next config 7 s7_88 = [] := by decide
theorem s7_88_safe : Safe 6 7 s7_88 := by
  apply safe_succ 5 7 s7_88 [] (by decide) s7_88_edges
  simp
def s7_89 : State := ⟨[1,4,104,132], 5784800258017591645098643320106278523158, 3, 3, 1, 0⟩
theorem s7_89_edges : next config 7 s7_89 = [] := by decide
theorem s7_89_safe : Safe 6 7 s7_89 := by
  apply safe_succ 5 7 s7_89 [] (by decide) s7_89_edges
  simp
def s7_90 : State := ⟨[1,4,104,132], 5784800258176047970090278507145947320598, 3, 3, 1, 0⟩
theorem s7_90_edges : next config 7 s7_90 = [] := by decide
theorem s7_90_safe : Safe 6 7 s7_90 := by
  apply safe_succ 5 7 s7_90 [] (by decide) s7_90_edges
  simp
def s7_91 : State := ⟨[1,4,104,132], 5784800259285242245289979233455562621214, 3, 3, 1, 0⟩
theorem s7_91_edges : next config 7 s7_91 = [] := by decide
theorem s7_91_safe : Safe 6 7 s7_91 := by
  apply safe_succ 5 7 s7_91 [] (by decide) s7_91_edges
  simp
def s7_92 : State := ⟨[1,4,104,132], 5784800259285242245326872721602981724438, 3, 3, 1, 0⟩
theorem s7_92_edges : next config 7 s7_92 = [] := by decide
theorem s7_92_safe : Safe 6 7 s7_92 := by
  apply safe_succ 5 7 s7_92 [] (by decide) s7_92_edges
  simp
def s7_93 : State := ⟨[1,4,104,132], 5784800582536145303488476615114879992094, 3, 3, 1, 0⟩
theorem s7_93_edges : next config 7 s7_93 = [] := by decide
theorem s7_93_safe : Safe 6 7 s7_93 := by
  apply safe_succ 5 7 s7_93 [] (by decide) s7_93_edges
  simp
def s7_94 : State := ⟨[1,4,104,132], 5784800582536145303525370103262299095318, 3, 3, 1, 0⟩
theorem s7_94_edges : next config 7 s7_94 = [] := by decide
theorem s7_94_safe : Safe 6 7 s7_94 := by
  apply safe_succ 5 7 s7_94 [] (by decide) s7_94_edges
  simp
def s7_95 : State := ⟨[1,4,104,136], 87452568319042822876271655615583230169374, 3, 3, 1, 0⟩
theorem s7_95_edges : next config 7 s7_95 = [] := by decide
theorem s7_95_safe : Safe 6 7 s7_95 := by
  apply safe_succ 5 7 s7_95 [] (by decide) s7_95_edges
  simp
def s7_96 : State := ⟨[1,4,104,136], 87452568319042822876271655615591820103958, 3, 3, 1, 0⟩
theorem s7_96_edges : next config 7 s7_96 = [] := by decide
theorem s7_96_safe : Safe 6 7 s7_96 := by
  apply safe_succ 5 7 s7_96 [] (by decide) s7_96_edges
  simp
def s7_97 : State := ⟨[1,4,104,136], 87452568319042822876308549103730649272598, 3, 3, 1, 0⟩
theorem s7_97_edges : next config 7 s7_97 = [] := by decide
theorem s7_97_safe : Safe 6 7 s7_97 := by
  apply safe_succ 5 7 s7_97 [] (by decide) s7_97_edges
  simp
def s7_98 : State := ⟨[1,4,104,136], 87452568319201279201300184290770318070038, 3, 3, 1, 0⟩
theorem s7_98_edges : next config 7 s7_98 = [] := by decide
theorem s7_98_safe : Safe 6 7 s7_98 := by
  apply safe_succ 5 7 s7_98 [] (by decide) s7_98_edges
  simp
def s7_99 : State := ⟨[1,4,104,136], 87452568320310473476499885017079933370654, 3, 3, 1, 0⟩
theorem s7_99_edges : next config 7 s7_99 = [] := by decide
theorem s7_99_safe : Safe 6 7 s7_99 := by
  apply safe_succ 5 7 s7_99 [] (by decide) s7_99_edges
  simp
def s7_100 : State := ⟨[1,4,104,136], 87452568320310473476536778505227352473878, 3, 3, 1, 0⟩
theorem s7_100_edges : next config 7 s7_100 = [] := by decide
theorem s7_100_safe : Safe 6 7 s7_100 := by
  apply safe_succ 5 7 s7_100 [] (by decide) s7_100_edges
  simp
def s7_101 : State := ⟨[1,4,104,136], 87452568643561376534698382398739250741534, 3, 3, 1, 0⟩
theorem s7_101_edges : next config 7 s7_101 = [] := by decide
theorem s7_101_safe : Safe 6 7 s7_101 := by
  apply safe_succ 5 7 s7_101 [] (by decide) s7_101_edges
  simp
def s7_102 : State := ⟨[1,4,104,136], 87452568643561376534735275886886669844758, 3, 3, 1, 0⟩
theorem s7_102_edges : next config 7 s7_102 = [] := by decide
theorem s7_102_safe : Safe 6 7 s7_102 := by
  apply safe_succ 5 7 s7_102 [] (by decide) s7_102_edges
  simp
def s7_103 : State := ⟨[1,4,104,136], 1481249143227206769222254047656105824289054, 3, 3, 1, 0⟩
theorem s7_103_edges : next config 7 s7_103 = [] := by decide
theorem s7_103_safe : Safe 6 7 s7_103 := by
  apply safe_succ 5 7 s7_103 [] (by decide) s7_103_edges
  simp
def s7_104 : State := ⟨[1,4,104,136], 1481249143227206769222254047656114414223638, 3, 3, 1, 0⟩
theorem s7_104_edges : next config 7 s7_104 = [] := by decide
theorem s7_104_safe : Safe 6 7 s7_104 := by
  apply safe_succ 5 7 s7_104 [] (by decide) s7_104_edges
  simp
def s7_105 : State := ⟨[1,4,104,136], 1481249143227206769222290941144253243392278, 3, 3, 1, 0⟩
theorem s7_105_edges : next config 7 s7_105 = [] := by decide
theorem s7_105_safe : Safe 6 7 s7_105 := by
  apply safe_succ 5 7 s7_105 [] (by decide) s7_105_edges
  simp
def s7_106 : State := ⟨[1,4,104,136], 1481249143227365225547282576331292912189718, 3, 3, 1, 0⟩
theorem s7_106_edges : next config 7 s7_106 = [] := by decide
theorem s7_106_safe : Safe 6 7 s7_106 := by
  apply safe_succ 5 7 s7_106 [] (by decide) s7_106_edges
  simp
def s7_107 : State := ⟨[1,4,104,140], 1394136857295446522575630148153573162160414, 3, 3, 1, 0⟩
theorem s7_107_edges : next config 7 s7_107 = [] := by decide
theorem s7_107_safe : Safe 6 7 s7_107 := by
  apply safe_succ 5 7 s7_107 [] (by decide) s7_107_edges
  simp
def s7_108 : State := ⟨[1,4,104,140], 1394136857295446522575630148153581752094998, 3, 3, 1, 0⟩
theorem s7_108_edges : next config 7 s7_108 = [] := by decide
theorem s7_108_safe : Safe 6 7 s7_108 := by
  apply safe_succ 5 7 s7_108 [] (by decide) s7_108_edges
  simp
def s7_109 : State := ⟨[1,4,104,140], 1394136857295446522575667041641720581263638, 3, 3, 1, 0⟩
theorem s7_109_edges : next config 7 s7_109 = [] := by decide
theorem s7_109_safe : Safe 6 7 s7_109 := by
  apply safe_succ 5 7 s7_109 [] (by decide) s7_109_edges
  simp
def s7_110 : State := ⟨[1,4,104,140], 1394136857295604978900658676828760250061078, 3, 3, 1, 0⟩
theorem s7_110_edges : next config 7 s7_110 = [] := by decide
theorem s7_110_safe : Safe 6 7 s7_110 := by
  apply safe_succ 5 7 s7_110 [] (by decide) s7_110_edges
  simp
def s7_111 : State := ⟨[1,4,104,144], 22301085480917905717765366028761412074017054, 3, 3, 1, 0⟩
theorem s7_111_edges : next config 7 s7_111 = [s8_20, s8_31, s8_46] := by decide
theorem s7_111_safe : Safe 6 7 s7_111 := by
  apply safe_succ 5 7 s7_111 [s8_20, s8_31, s8_46] (by decide) s7_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_20_safe
  · subst z; exact s8_31_safe
  · subst z; exact s8_46_safe
def s7_112 : State := ⟨[1,4,104,144], 22301085480917905717765366028761420663951638, 3, 3, 1, 0⟩
theorem s7_112_edges : next config 7 s7_112 = [s8_21] := by decide
theorem s7_112_safe : Safe 6 7 s7_112 := by
  apply safe_succ 5 7 s7_112 [s8_21] (by decide) s7_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_21_safe
def s7_113 : State := ⟨[1,4,104,144], 22301085480917905717765402922249559493120278, 3, 3, 1, 0⟩
theorem s7_113_edges : next config 7 s7_113 = [s8_22, s8_32, s8_47] := by decide
theorem s7_113_safe : Safe 6 7 s7_113 := by
  apply safe_succ 5 7 s7_113 [s8_22, s8_32, s8_47] (by decide) s7_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_22_safe
  · subst z; exact s8_32_safe
  · subst z; exact s8_47_safe
def s7_114 : State := ⟨[1,4,104,144], 22301085480918064174090394557436599161917718, 3, 3, 1, 0⟩
theorem s7_114_edges : next config 7 s7_114 = [s8_23] := by decide
theorem s7_114_safe : Safe 6 7 s7_114 := by
  apply safe_succ 5 7 s7_114 [s8_23] (by decide) s7_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_23_safe
def s7_115 : State := ⟨[1,4,104,144], 22301085480919173368365594258162908777218334, 3, 3, 1, 0⟩
theorem s7_115_edges : next config 7 s7_115 = [s8_24] := by decide
theorem s7_115_safe : Safe 6 7 s7_115 := by
  apply safe_succ 5 7 s7_115 [s8_24] (by decide) s7_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_24_safe
def s7_116 : State := ⟨[1,4,104,144], 22301085480919173368365631151651056196321558, 3, 3, 1, 0⟩
theorem s7_116_edges : next config 7 s7_116 = [s8_25] := by decide
theorem s7_116_safe : Safe 6 7 s7_116 := by
  apply safe_succ 5 7 s7_116 [s8_25] (by decide) s7_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_25_safe
def s7_117 : State := ⟨[1,4,104,144], 22301085481242424271423792755544568094589214, 3, 3, 1, 0⟩
theorem s7_117_edges : next config 7 s7_117 = [s8_26] := by decide
theorem s7_117_safe : Safe 6 7 s7_117 := by
  apply safe_succ 5 7 s7_117 [s8_26] (by decide) s7_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_26_safe
def s7_118 : State := ⟨[1,4,104,144], 22301085481242424271423829649032715513692438, 3, 3, 1, 0⟩
theorem s7_118_edges : next config 7 s7_118 = [s8_27] := by decide
theorem s7_118_safe : Safe 6 7 s7_118 := by
  apply safe_succ 5 7 s7_118 [s8_27] (by decide) s7_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_27_safe
def s7_119 : State := ⟨[1,4,104,145], 44601830679448528859301084301409773580128534, 3, 3, 1, 0⟩
theorem s7_119_edges : next config 7 s7_119 = [s8_94, s8_274] := by decide
theorem s7_119_safe : Safe 6 7 s7_119 := by
  apply safe_succ 5 7 s7_119 [s8_94, s8_274] (by decide) s7_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_94_safe
  · subst z; exact s8_274_safe
def s7_120 : State := ⟨[1,4,104,145], 44601830679448528859301084301409773582221590, 3, 3, 1, 0⟩
theorem s7_120_edges : next config 7 s7_120 = [s8_95, s8_126, s8_275, s8_92, s8_64, s8_50, s8_58, s8_51] := by decide
theorem s7_120_safe : Safe 6 7 s7_120 := by
  apply safe_succ 5 7 s7_120 [s8_95, s8_126, s8_275, s8_92, s8_64, s8_50, s8_58, s8_51] (by decide) s7_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s8_95_safe
  · subst z; exact s8_126_safe
  · subst z; exact s8_275_safe
  · subst z; exact s8_92_safe
  · subst z; exact s8_64_safe
  · subst z; exact s8_50_safe
  · subst z; exact s8_58_safe
  · subst z; exact s8_51_safe
def s7_121 : State := ⟨[1,4,104,145], 44601830679448528859301379449314952932950294, 3, 3, 1, 0⟩
theorem s7_121_edges : next config 7 s7_121 = [] := by decide
theorem s7_121_safe : Safe 6 7 s7_121 := by
  apply safe_succ 5 7 s7_121 [] (by decide) s7_121_edges
  simp
def s7_122 : State := ⟨[1,4,104,145], 44601830679449796509901312530811270283329814, 3, 3, 1, 0⟩
theorem s7_122_edges : next config 7 s7_122 = [s8_96] := by decide
theorem s7_122_safe : Safe 6 7 s7_122 := by
  apply safe_succ 5 7 s7_122 [s8_96] (by decide) s7_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_96_safe
def s7_123 : State := ⟨[1,4,104,145], 44601830679773047412959511028192929600700694, 3, 3, 1, 0⟩
theorem s7_123_edges : next config 7 s7_123 = [s8_97] := by decide
theorem s7_123_safe : Safe 6 7 s7_123 := by
  apply safe_succ 5 7 s7_123 [s8_97] (by decide) s7_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_97_safe
def s7_124 : State := ⟨[1,4,104,145], 133806172603038705179297810890432946676760862, 1, 1, 1, 0⟩
theorem s7_124_edges : next config 7 s7_124 = [s8_65] := by decide
theorem s7_124_safe : Safe 6 7 s7_124 := by
  apply safe_succ 5 7 s7_124 [s8_65] (by decide) s7_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_65_safe
def s7_125 : State := ⟨[1,4,104,145], 156105556672101644566979675664651581109895454, 1, 1, 1, 0⟩
theorem s7_125_edges : next config 7 s7_125 = [s8_66] := by decide
theorem s7_125_safe : Safe 6 7 s7_125 := by
  apply safe_succ 5 7 s7_125 [s8_66] (by decide) s7_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_66_safe
def s7_126 : State := ⟨[1,4,104,160], 1461501637671185305486261062364039132706500579614, 3, 3, 1, 0⟩
theorem s7_126_edges : next config 7 s7_126 = [s8_37, s8_48] := by decide
theorem s7_126_safe : Safe 6 7 s7_126 := by
  apply safe_succ 5 7 s7_126 [s8_37, s8_48] (by decide) s7_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_37_safe
  · subst z; exact s8_48_safe
def s7_127 : State := ⟨[1,4,104,160], 1461501637671185305486261062364039132715090514198, 3, 3, 1, 0⟩
theorem s7_127_edges : next config 7 s7_127 = [] := by decide
theorem s7_127_safe : Safe 6 7 s7_127 := by
  apply safe_succ 5 7 s7_127 [] (by decide) s7_127_edges
  simp
def s7_128 : State := ⟨[1,4,104,160], 1461501637671185305486261062400932620853919682838, 3, 3, 1, 0⟩
theorem s7_128_edges : next config 7 s7_128 = [s8_38, s8_49] := by decide
theorem s7_128_safe : Safe 6 7 s7_128 := by
  apply safe_succ 5 7 s7_128 [s8_38, s8_49] (by decide) s7_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_38_safe
  · subst z; exact s8_49_safe
def s7_129 : State := ⟨[1,4,104,160], 1461501637671185305644717387392567807893588480278, 3, 3, 1, 0⟩
theorem s7_129_edges : next config 7 s7_129 = [s8_39] := by decide
theorem s7_129_safe : Safe 6 7 s7_129 := by
  apply safe_succ 5 7 s7_129 [s8_39] (by decide) s7_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_39_safe
def s7_130 : State := ⟨[1,4,104,160], 1461501637671185306753911662592268534203203780894, 3, 3, 1, 0⟩
theorem s7_130_edges : next config 7 s7_130 = [] := by decide
theorem s7_130_safe : Safe 6 7 s7_130 := by
  apply safe_succ 5 7 s7_130 [] (by decide) s7_130_edges
  simp
def s7_131 : State := ⟨[1,4,104,160], 1461501637671185306753911662629162022350622884118, 3, 3, 1, 0⟩
theorem s7_131_edges : next config 7 s7_131 = [] := by decide
theorem s7_131_safe : Safe 6 7 s7_131 := by
  apply safe_succ 5 7 s7_131 [] (by decide) s7_131_edges
  simp
def s7_132 : State := ⟨[1,4,104,160], 1461501637671185630004814720790765915862521151774, 3, 3, 1, 0⟩
theorem s7_132_edges : next config 7 s7_132 = [] := by decide
theorem s7_132_safe : Safe 6 7 s7_132 := by
  apply safe_succ 5 7 s7_132 [] (by decide) s7_132_edges
  simp
def s7_133 : State := ⟨[1,4,104,160], 1461501637671185630004814720827659404009940254998, 3, 3, 1, 0⟩
theorem s7_133_edges : next config 7 s7_133 = [] := by decide
theorem s7_133_safe : Safe 6 7 s7_133 := by
  apply safe_succ 5 7 s7_133 [] (by decide) s7_133_edges
  simp
def s7_134 : State := ⟨[1,4,104,160], 4384504912332991141893630727796605172018365665558, 3, 3, 1, 0⟩
theorem s7_134_edges : next config 7 s7_134 = [] := by decide
theorem s7_134_safe : Safe 6 7 s7_134 := by
  apply safe_succ 5 7 s7_134 [] (by decide) s7_134_edges
  simp
def s7_135 : State := ⟨[1,4,104,161], 2923003275002088223689945895080322152371023057174, 3, 3, 1, 0⟩
theorem s7_135_edges : next config 7 s7_135 = [s8_45] := by decide
theorem s7_135_safe : Safe 6 7 s7_135 := by
  apply safe_succ 5 7 s7_135 [s8_45] (by decide) s7_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_45_safe
def s7_136 : State := ⟨[1,4,104,162], 25108406947392729606368181220611735078775808399257509105942, 2, 2, 1, 0⟩
theorem s7_136_edges : next config 7 s7_136 = [] := by decide
theorem s7_136_safe : Safe 6 7 s7_136 := by
  apply safe_succ 5 7 s7_136 [] (by decide) s7_136_edges
  simp
def s7_137 : State := ⟨[1,4,104,162], 31385508682779410368842841176135647641024665413994470773014, 2, 2, 1, 0⟩
theorem s7_137_edges : next config 7 s7_137 = [] := by decide
theorem s7_137_safe : Safe 6 7 s7_137 := by
  apply safe_succ 5 7 s7_137 [] (by decide) s7_137_edges
  simp
def s7_138 : State := ⟨[1,4,104,163], 11692013102390329402121439526011766344615710494998, 2, 2, 1, 0⟩
theorem s7_138_edges : next config 7 s7_138 = [] := by decide
theorem s7_138_safe : Safe 6 7 s7_138 := by
  apply safe_succ 5 7 s7_138 [] (by decide) s7_138_edges
  simp
def s7_139 : State := ⟨[1,4,104,163], 11692013103070894135963316452938515559479246917910, 2, 2, 1, 0⟩
theorem s7_139_edges : next config 7 s7_139 = [] := by decide
theorem s7_139_safe : Safe 6 7 s7_139 := by
  apply safe_succ 5 7 s7_139 [] (by decide) s7_139_edges
  simp
def s7_140 : State := ⟨[1,4,104,163], 14615016374329876303161301483737335524473429889302, 2, 2, 1, 0⟩
theorem s7_140_edges : next config 7 s7_140 = [] := by decide
theorem s7_140_safe : Safe 6 7 s7_140 := by
  apply safe_succ 5 7 s7_140 [] (by decide) s7_140_edges
  simp
def s7_141 : State := ⟨[1,4,104,163], 16076518010980214487523109389526869329265826009366, 2, 2, 1, 0⟩
theorem s7_141_edges : next config 7 s7_141 = [] := by decide
theorem s7_141_safe : Safe 6 7 s7_141 := by
  apply safe_succ 5 7 s7_141 [] (by decide) s7_141_edges
  simp
def s7_142 : State := ⟨[1,4,104,163], 17538019649672246873410548076096650778648831398166, 2, 2, 1, 0⟩
theorem s7_142_edges : next config 7 s7_142 = [] := by decide
theorem s7_142_safe : Safe 6 7 s7_142 := by
  apply safe_succ 5 7 s7_142 [] (by decide) s7_142_edges
  simp
def s7_143 : State := ⟨[1,4,104,163], 18999521285642020323930479054959435368577691095318, 2, 2, 1, 0⟩
theorem s7_143_edges : next config 7 s7_143 = [] := by decide
theorem s7_143_safe : Safe 6 7 s7_143 := by
  apply safe_succ 5 7 s7_143 [] (by decide) s7_143_edges
  simp
def s7_144 : State := ⟨[1,4,104,170], 4495579036431558788249500875518787823004426143072534, 1, 1, 1, 0⟩
theorem s7_144_edges : next config 7 s7_144 = [] := by decide
theorem s7_144_safe : Safe 6 7 s7_144 := by
  apply safe_succ 5 7 s7_144 [] (by decide) s7_144_edges
  simp
def s7_145 : State := ⟨[1,4,104,170], 4497040538067528561700020806497650607594355002769686, 1, 1, 1, 0⟩
theorem s7_145_edges : next config 7 s7_145 = [] := by decide
theorem s7_145_safe : Safe 6 7 s7_145 := by
  apply safe_succ 5 7 s7_145 [] (by decide) s7_145_edges
  simp
def s7_146 : State := ⟨[1,4,104,171], 2999001359804714200008927606817314010876751219065622, 1, 1, 1, 0⟩
theorem s7_146_edges : next config 7 s7_146 = [] := by decide
theorem s7_146_safe : Safe 6 7 s7_146 := by
  apply safe_succ 5 7 s7_146 [] (by decide) s7_146_edges
  simp
def s7_147 : State := ⟨[1,4,104,171], 3000462861440683973459447537796176795466680078762774, 1, 1, 1, 0⟩
theorem s7_147_edges : next config 7 s7_147 = [] := by decide
theorem s7_147_safe : Safe 6 7 s7_147 := by
  apply safe_succ 5 7 s7_147 [] (by decide) s7_147_edges
  simp
def s7_148 : State := ⟨[1,4,104,171], 3004847366354037811681742346148179142955383539171606, 1, 1, 1, 0⟩
theorem s7_148_edges : next config 7 s7_148 = [] := by decide
theorem s7_148_safe : Safe 6 7 s7_148 := by
  apply safe_succ 5 7 s7_148 [] (by decide) s7_148_edges
  simp
def s7_149 : State := ⟨[1,4,104,171], 3004847366355398941149426100002032641385102022082846, 1, 1, 1, 0⟩
theorem s7_149_edges : next config 7 s7_149 = [] := by decide
theorem s7_149_safe : Safe 6 7 s7_149 := by
  apply safe_succ 5 7 s7_149 [] (by decide) s7_149_edges
  simp
def s7_150 : State := ⟨[1,4,104,171], 3006308867990007585132262277127041927545303808934174, 1, 1, 1, 0⟩
theorem s7_150_edges : next config 7 s7_150 = [] := by decide
theorem s7_150_safe : Safe 6 7 s7_150 := by
  apply safe_succ 5 7 s7_150 [] (by decide) s7_150_edges
  simp
def s7_151 : State := ⟨[1,4,104,171], 3007770369627338488050465961959758210564968331411734, 1, 1, 1, 0⟩
theorem s7_151_edges : next config 7 s7_151 = [] := by decide
theorem s7_151_safe : Safe 6 7 s7_151 := by
  apply safe_succ 5 7 s7_151 [] (by decide) s7_151_edges
  simp
def s7_152 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645750111557514602549534, 3, 3, 1, 0⟩
theorem s7_152_edges : next config 7 s7_152 = [] := by decide
theorem s7_152_safe : Safe 6 7 s7_152 := by
  apply safe_succ 5 7 s7_152 [] (by decide) s7_152_edges
  simp
def s7_153 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645750111557523192484118, 3, 3, 1, 0⟩
theorem s7_153_edges : next config 7 s7_153 = [] := by decide
theorem s7_153_safe : Safe 6 7 s7_153 := by
  apply safe_succ 5 7 s7_153 [] (by decide) s7_153_edges
  simp
def s7_154 : State := ⟨[1,4,104,192], 6277101735386680764176071810490242645787005045662021652758, 3, 3, 1, 0⟩
theorem s7_154_edges : next config 7 s7_154 = [] := by decide
theorem s7_154_safe : Safe 6 7 s7_154 := by
  apply safe_succ 5 7 s7_154 [] (by decide) s7_154_edges
  simp
def s7_155 : State := ⟨[1,4,104,192], 6277101735386680764176071810648698970778640232701690450198, 3, 3, 1, 0⟩
theorem s7_155_edges : next config 7 s7_155 = [] := by decide
theorem s7_155_safe : Safe 6 7 s7_155 := by
  apply safe_succ 5 7 s7_155 [] (by decide) s7_155_edges
  simp
def s7_156 : State := ⟨[1,4,104,192], 6277101735386680764176071811757893245978340959011305750814, 3, 3, 1, 0⟩
theorem s7_156_edges : next config 7 s7_156 = [] := by decide
theorem s7_156_safe : Safe 6 7 s7_156 := by
  apply safe_succ 5 7 s7_156 [] (by decide) s7_156_edges
  simp
def s7_157 : State := ⟨[1,4,104,192], 6277101735386680764176071811757893246015234447158724854038, 3, 3, 1, 0⟩
theorem s7_157_edges : next config 7 s7_157 = [] := by decide
theorem s7_157_safe : Safe 6 7 s7_157 := by
  apply safe_succ 5 7 s7_157 [] (by decide) s7_157_edges
  simp
def s7_158 : State := ⟨[1,4,104,192], 6277101735386680764176072135008796304176838340670623121694, 3, 3, 1, 0⟩
theorem s7_158_edges : next config 7 s7_158 = [] := by decide
theorem s7_158_safe : Safe 6 7 s7_158 := by
  apply safe_succ 5 7 s7_158 [] (by decide) s7_158_edges
  simp
def s7_159 : State := ⟨[1,4,104,192], 6277101735386680764176072135008796304213731828818042224918, 3, 3, 1, 0⟩
theorem s7_159_edges : next config 7 s7_159 = [] := by decide
theorem s7_159_safe : Safe 6 7 s7_159 := by
  apply safe_succ 5 7 s7_159 [] (by decide) s7_159_edges
  simp
def s7_160 : State := ⟨[1,4,104,192], 18831305206160042291847650656905575477954822446442671575318, 3, 3, 1, 0⟩
theorem s7_160_edges : next config 7 s7_160 = [] := by decide
theorem s7_160_safe : Safe 6 7 s7_160 := by
  apply safe_succ 5 7 s7_160 [] (by decide) s7_160_edges
  simp
def s7_161 : State := ⟨[1,4,104,192], 18831305206160042291847650658173226078183051847939374776598, 3, 3, 1, 0⟩
theorem s7_161_edges : next config 7 s7_161 = [] := by decide
theorem s7_161_safe : Safe 6 7 s7_161 := by
  apply safe_succ 5 7 s7_161 [] (by decide) s7_161_edges
  simp
def s7_162 : State := ⟨[1,4,104,192], 18831305206160042291847650981424129136381549229598692147478, 3, 3, 1, 0⟩
theorem s7_162_edges : next config 7 s7_162 = [] := by decide
theorem s7_162_safe : Safe 6 7 s7_162 := by
  apply safe_succ 5 7 s7_162 [] (by decide) s7_162_edges
  simp
def s7_163 : State := ⟨[1,4,104,193], 12554203470773361528011861233697909061889360490126056165654, 3, 3, 1, 0⟩
theorem s7_163_edges : next config 7 s7_163 = [] := by decide
theorem s7_163_safe : Safe 6 7 s7_163 := by
  apply safe_succ 5 7 s7_163 [] (by decide) s7_163_edges
  simp
def s7_164 : State := ⟨[1,4,104,193], 12554203470773361528011861234965559662117589891622759366934, 3, 3, 1, 0⟩
theorem s7_164_edges : next config 7 s7_164 = [] := by decide
theorem s7_164_safe : Safe 6 7 s7_164 := by
  apply safe_succ 5 7 s7_164 [] (by decide) s7_164_edges
  simp
def s7_165 : State := ⟨[1,4,104,193], 12554203470773361528011861558216462720316087273282076737814, 3, 3, 1, 0⟩
theorem s7_165_edges : next config 7 s7_165 = [] := by decide
theorem s7_165_safe : Safe 6 7 s7_165 := by
  apply safe_succ 5 7 s7_165 [] (by decide) s7_165_edges
  simp
def s7_166 : State := ⟨[1,4,104,194], 25108406947392729606368181220611735078775808399257509105942, 2, 2, 1, 0⟩
theorem s7_166_edges : next config 7 s7_166 = [] := by decide
theorem s7_166_safe : Safe 6 7 s7_166 := by
  apply safe_succ 5 7 s7_166 [] (by decide) s7_166_edges
  simp
def s7_167 : State := ⟨[1,4,104,194], 25108406948854231242337954671131666057638592989186368803094, 2, 2, 1, 0⟩
theorem s7_167_edges : next config 7 s7_167 = [] := by decide
theorem s7_167_safe : Safe 6 7 s7_167 := by
  apply safe_succ 5 7 s7_167 [] (by decide) s7_167_edges
  simp
def s7_168 : State := ⟨[1,4,104,210], 1645504557321206042244173864763327963878962239978716087013413142, 2, 2, 1, 0⟩
theorem s7_168_edges : next config 7 s7_168 = [] := by decide
theorem s7_168_safe : Safe 6 7 s7_168 := by
  apply safe_succ 5 7 s7_168 [] (by decide) s7_168_edges
  simp
def s7_169 : State := ⟨[1,4,104,210], 1645504557321206042244173864763652482432620666705499243033985302, 2, 2, 1, 0⟩
theorem s7_169_edges : next config 7 s7_169 = [] := by decide
theorem s7_169_safe : Safe 6 7 s7_169 := by
  apply safe_succ 5 7 s7_169 [] (by decide) s7_169_edges
  simp
def s7_170 : State := ⟨[1,4,104,210], 1645504557321206042266473248832390903266644104752934721446547734, 2, 2, 1, 0⟩
theorem s7_170_edges : next config 7 s7_170 = [] := by decide
theorem s7_170_safe : Safe 6 7 s7_170 := by
  apply safe_succ 5 7 s7_170 [] (by decide) s7_170_edges
  simp
def s7_171 : State := ⟨[1,4,104,210], 1645504557321206042266473248832715421820302531479717877467119894, 2, 2, 1, 0⟩
theorem s7_171_edges : next config 7 s7_171 = [] := by decide
theorem s7_171_safe : Safe 6 7 s7_171 := by
  apply safe_succ 5 7 s7_171 [] (by decide) s7_171_edges
  simp
def s7_172 : State := ⟨[1,4,104,210], 1645529665728147588878026227126898301978483776309900497127543062, 2, 2, 1, 0⟩
theorem s7_172_edges : next config 7 s7_172 = [] := by decide
theorem s7_172_safe : Safe 6 7 s7_172 := by
  apply safe_succ 5 7 s7_172 [] (by decide) s7_172_edges
  simp
def s7_173 : State := ⟨[1,4,104,210], 1645529665728147588878026227127222820532142203036683653148115222, 2, 2, 1, 0⟩
theorem s7_173_edges : next config 7 s7_173 = [] := by decide
theorem s7_173_safe : Safe 6 7 s7_173 := by
  apply safe_succ 5 7 s7_173 [] (by decide) s7_173_edges
  simp
def s7_174 : State := ⟨[1,4,104,210], 1645535942829882975558788701786853825891046025166915234089210134, 2, 2, 1, 0⟩
theorem s7_174_edges : next config 7 s7_174 = [] := by decide
theorem s7_174_safe : Safe 6 7 s7_174 := by
  apply safe_succ 5 7 s7_174 [] (by decide) s7_174_edges
  simp
def s7_175 : State := ⟨[1,4,104,210], 1645535942829882975558788701787178344444704451893698390109782294, 2, 2, 1, 0⟩
theorem s7_175_edges : next config 7 s7_175 = [] := by decide
theorem s7_175_safe : Safe 6 7 s7_175 := by
  apply safe_succ 5 7 s7_175 [] (by decide) s7_175_edges
  simp
def s7_176 : State := ⟨[1,4,104,210], 2056880696651507552716012563677606036946185198070736241259778326, 2, 2, 1, 0⟩
theorem s7_176_edges : next config 7 s7_176 = [] := by decide
theorem s7_176_safe : Safe 6 7 s7_176 := by
  apply safe_succ 5 7 s7_176 [] (by decide) s7_176_edges
  simp
def s7_177 : State := ⟨[1,4,104,210], 2056880696651507552716012563677930555499843624797519397280350486, 2, 2, 1, 0⟩
theorem s7_177_edges : next config 7 s7_177 = [] := by decide
theorem s7_177_safe : Safe 6 7 s7_177 := by
  apply safe_succ 5 7 s7_177 [] (by decide) s7_177_edges
  simp
def s7_178 : State := ⟨[1,4,104,210], 2056886973753242939374475654268498621471065582153532343788310806, 2, 2, 1, 0⟩
theorem s7_178_edges : next config 7 s7_178 = [] := by decide
theorem s7_178_safe : Safe 6 7 s7_178 := by
  apply safe_succ 5 7 s7_178 [] (by decide) s7_178_edges
  simp
def s7_179 : State := ⟨[1,4,104,210], 2056886973753242939374475654268823140024724008880315499808882966, 2, 2, 1, 0⟩
theorem s7_179_edges : next config 7 s7_179 = [] := by decide
theorem s7_179_safe : Safe 6 7 s7_179 := by
  apply safe_succ 5 7 s7_179 [] (by decide) s7_179_edges
  simp
def s7_180 : State := ⟨[1,4,104,210], 27973577474460502716723680785680936043602736090115993900591153430, 2, 2, 1, 0⟩
theorem s7_180_edges : next config 7 s7_180 = [] := by decide
theorem s7_180_safe : Safe 6 7 s7_180 := by
  apply safe_succ 5 7 s7_180 [] (by decide) s7_180_edges
  simp
def s7_181 : State := ⟨[1,4,104,210], 27973577474460502716745980169749998982990417954890212535024288022, 2, 2, 1, 0⟩
theorem s7_181_edges : next config 7 s7_181 = [] := by decide
theorem s7_181_safe : Safe 6 7 s7_181 := by
  apply safe_succ 5 7 s7_181 [] (by decide) s7_181_edges
  simp
def s7_182 : State := ⟨[1,4,104,210], 27973602582867444263357533148044506381702257626447178310705283350, 2, 2, 1, 0⟩
theorem s7_182_edges : next config 7 s7_182 = [] := by decide
theorem s7_182_safe : Safe 6 7 s7_182 := by
  apply safe_succ 5 7 s7_182 [] (by decide) s7_182_edges
  simp
def s7_183 : State := ⟨[1,4,104,210], 27973608859969179650038295622704461905614819875304193047666950422, 2, 2, 1, 0⟩
theorem s7_183_edges : next config 7 s7_183 = [] := by decide
theorem s7_183_safe : Safe 6 7 s7_183 := by
  apply safe_succ 5 7 s7_183 [] (by decide) s7_183_edges
  simp
def s7_184 : State := ⟨[1,4,104,210], 28384953613790804227195519484595214116669959048208014054837518614, 2, 2, 1, 0⟩
theorem s7_184_edges : next config 7 s7_184 = [] := by decide
theorem s7_184_safe : Safe 6 7 s7_184 := by
  apply safe_succ 5 7 s7_184 [] (by decide) s7_184_edges
  simp
def s7_185 : State := ⟨[1,4,104,210], 28384959890892539613853982575186106701194839432290810157366051094, 2, 2, 1, 0⟩
theorem s7_185_edges : next config 7 s7_185 = [] := by decide
theorem s7_185_safe : Safe 6 7 s7_185 := by
  apply safe_succ 5 7 s7_185 [] (by decide) s7_185_edges
  simp
def s7_186 : State := ⟨[1,4,104,214], 26328072917139296674568711603123585538620000519630319216595370262, 2, 2, 1, 0⟩
theorem s7_186_edges : next config 7 s7_186 = [] := by decide
theorem s7_186_safe : Safe 6 7 s7_186 := by
  apply safe_succ 5 7 s7_186 [] (by decide) s7_186_edges
  simp
def s7_187 : State := ⟨[1,4,104,214], 26328072917139296674591010987192648478007682384404537851028504854, 2, 2, 1, 0⟩
theorem s7_187_edges : next config 7 s7_187 = [] := by decide
theorem s7_187_safe : Safe 6 7 s7_187 := by
  apply safe_succ 5 7 s7_187 [] (by decide) s7_187_edges
  simp
def s7_188 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652188328594154178285854, 3, 3, 1, 0⟩
theorem s7_188_edges : next config 7 s7_188 = [] := by decide
theorem s7_188_safe : Safe 6 7 s7_188 := by
  apply safe_succ 5 7 s7_188 [] (by decide) s7_188_edges
  simp
def s7_189 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652188328594162768220438, 3, 3, 1, 0⟩
theorem s7_189_edges : next config 7 s7_189 = [] := by decide
theorem s7_189_safe : Safe 6 7 s7_189 := by
  apply safe_succ 5 7 s7_189 [] (by decide) s7_189_edges
  simp
def s7_190 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913060919720652225222082301597389078, 3, 3, 1, 0⟩
theorem s7_190_edges : next config 7 s7_190 = [] := by decide
theorem s7_190_safe : Safe 6 7 s7_190 := by
  apply safe_succ 5 7 s7_190 [] (by decide) s7_190_edges
  simp
def s7_191 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913061078176977216857269341266186518, 3, 3, 1, 0⟩
theorem s7_191_edges : next config 7 s7_191 = [] := by decide
theorem s7_191_safe : Safe 6 7 s7_191 := by
  apply safe_succ 5 7 s7_191 [] (by decide) s7_191_edges
  simp
def s7_192 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913062187371252416557995650881487134, 3, 3, 1, 0⟩
theorem s7_192_edges : next config 7 s7_192 = [] := by decide
theorem s7_192_safe : Safe 6 7 s7_192 := by
  apply safe_succ 5 7 s7_192 [] (by decide) s7_192_edges
  simp
def s7_193 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913062187371252453451483798300590358, 3, 3, 1, 0⟩
theorem s7_193_edges : next config 7 s7_193 = [] := by decide
theorem s7_193_safe : Safe 6 7 s7_193 := by
  apply safe_succ 5 7 s7_193 [] (by decide) s7_193_edges
  simp
def s7_194 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913385438274310615055377310198858014, 3, 3, 1, 0⟩
theorem s7_194_edges : next config 7 s7_194 = [] := by decide
theorem s7_194_safe : Safe 6 7 s7_194 := by
  apply safe_succ 5 7 s7_194 [] (by decide) s7_194_edges
  simp
def s7_195 : State := ⟨[1,4,104,224], 26959946667150639794667015087359913385438274310651948865457617961238, 3, 3, 1, 0⟩
theorem s7_195_edges : next config 7 s7_195 = [] := by decide
theorem s7_195_safe : Safe 6 7 s7_195 := by
  apply safe_succ 5 7 s7_195 [] (by decide) s7_195_edges
  simp
def s7_196 : State := ⟨[1,4,104,224], 80879840001451919384001045261399174408194009497269473556361398784278, 3, 3, 1, 0⟩
theorem s7_196_edges : next config 7 s7_196 = [] := by decide
theorem s7_196_safe : Safe 6 7 s7_196 := by
  apply safe_succ 5 7 s7_196 [] (by decide) s7_196_edges
  simp
def s7_197 : State := ⟨[1,4,104,224], 458319093341560876509339256479674003839114031412837488291811942269214, 3, 3, 1, 0⟩
theorem s7_197_edges : next config 7 s7_197 = [] := by decide
theorem s7_197_safe : Safe 6 7 s7_197 := by
  apply safe_succ 5 7 s7_197 [] (by decide) s7_197_edges
  simp
def s7_198 : State := ⟨[1,4,104,224], 458319093341560876509339256479674003839114031412874381779959361372438, 3, 3, 1, 0⟩
theorem s7_198_edges : next config 7 s7_198 = [] := by decide
theorem s7_198_safe : Safe 6 7 s7_198 := by
  apply safe_succ 5 7 s7_198 [] (by decide) s7_198_edges
  simp
def s7_199 : State := ⟨[1,4,104,225], 53919893334301279589334030174379543734715321399757429750444876435734, 3, 3, 1, 0⟩
theorem s7_199_edges : next config 7 s7_199 = [] := by decide
theorem s7_199_safe : Safe 6 7 s7_199 := by
  apply safe_succ 5 7 s7_199 [] (by decide) s7_199_edges
  simp
def s7_200 : State := ⟨[1,4,104,228], 431359146674410236714672241392654373166744537590525145212205035225374, 3, 3, 1, 0⟩
theorem s7_200_edges : next config 7 s7_200 = [] := by decide
theorem s7_200_safe : Safe 6 7 s7_200 := by
  apply safe_succ 5 7 s7_200 [] (by decide) s7_200_edges
  simp
def s7_201 : State := ⟨[1,4,104,228], 431359146674410236714672241392654373166744537590562038700352454328598, 3, 3, 1, 0⟩
theorem s7_201_edges : next config 7 s7_201 = [] := by decide
theorem s7_201_safe : Safe 6 7 s7_201 := by
  apply safe_succ 5 7 s7_201 [] (by decide) s7_201_edges
  simp
def s7_202 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400034311275574791835934, 3, 3, 1, 0⟩
theorem s7_202_edges : next config 7 s7_202 = [] := by decide
theorem s7_202_safe : Safe 6 7 s7_202 := by
  apply safe_succ 5 7 s7_202 [] (by decide) s7_202_edges
  simp
def s7_203 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400034311275583381770518, 3, 3, 1, 0⟩
theorem s7_203_edges : next config 7 s7_203 = [] := by decide
theorem s7_203_safe : Safe 6 7 s7_203 := by
  apply safe_succ 5 7 s7_203 [] (by decide) s7_203_edges
  simp
def s7_204 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838391548400071204763722210939158, 3, 3, 1, 0⟩
theorem s7_204_edges : next config 7 s7_204 = [] := by decide
theorem s7_204_safe : Safe 6 7 s7_204 := by
  apply safe_succ 5 7 s7_204 [] (by decide) s7_204_edges
  simp
def s7_205 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734838550004725062839950761879736598, 3, 3, 1, 0⟩
theorem s7_205_edges : next config 7 s7_205 = [] := by decide
theorem s7_205_safe : Safe 6 7 s7_205 := by
  apply safe_succ 5 7 s7_205 [] (by decide) s7_205_edges
  simp
def s7_206 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734839659199000262540677071495037214, 3, 3, 1, 0⟩
theorem s7_206_edges : next config 7 s7_206 = [] := by decide
theorem s7_206_safe : Safe 6 7 s7_206 := by
  apply safe_succ 5 7 s7_206 [] (by decide) s7_206_edges
  simp
def s7_207 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365734839659199000299434165218914140438, 3, 3, 1, 0⟩
theorem s7_207_edges : next config 7 s7_207 = [] := by decide
theorem s7_207_safe : Safe 6 7 s7_207 := by
  apply safe_succ 5 7 s7_207 [] (by decide) s7_207_edges
  simp
def s7_208 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365735162910102058461038058730812408094, 3, 3, 1, 0⟩
theorem s7_208_edges : next config 7 s7_208 = [] := by decide
theorem s7_208_safe : Safe 6 7 s7_208 := by
  apply safe_succ 5 7 s7_208 [] (by decide) s7_208_edges
  simp
def s7_209 : State := ⟨[1,4,104,232], 6901746346790563787434755862277365735162910102058497931546878231511318, 3, 3, 1, 0⟩
theorem s7_209_edges : next config 7 s7_209 = [] := by decide
theorem s7_209_safe : Safe 6 7 s7_209 := by
  apply safe_succ 5 7 s7_209 [] (by decide) s7_209_edges
  simp
def s7_210 : State := ⟨[1,4,104,232], 117329687895439584386390849658709772974056135103126219193875962372620574, 3, 3, 1, 0⟩
theorem s7_210_edges : next config 7 s7_210 = [] := by decide
theorem s7_210_safe : Safe 6 7 s7_210 := by
  apply safe_succ 5 7 s7_210 [] (by decide) s7_210_edges
  simp
def s7_211 : State := ⟨[1,4,104,232], 117329687895439584386390849658709772974056135103126256087364109791723798, 3, 3, 1, 0⟩
theorem s7_211_edges : next config 7 s7_211 = [] := by decide
theorem s7_211_safe : Safe 6 7 s7_211 := by
  apply safe_succ 5 7 s7_211 [] (by decide) s7_211_edges
  simp
def s7_212 : State := ⟨[1,4,104,236], 110427941548649020598956093796432747521929544684614259365496594169397534, 3, 3, 1, 0⟩
theorem s7_212_edges : next config 7 s7_212 = [] := by decide
theorem s7_212_safe : Safe 6 7 s7_212 := by
  apply safe_succ 5 7 s7_212 [] (by decide) s7_212_edges
  simp
def s7_213 : State := ⟨[1,4,104,236], 110427941548649020598956093796432747521929544684614296258984741588500758, 3, 3, 1, 0⟩
theorem s7_213_edges : next config 7 s7_213 = [] := by decide
theorem s7_213_safe : Safe 6 7 s7_213 := by
  apply safe_succ 5 7 s7_213 [] (by decide) s7_213_edges
  simp
def s7_214 : State := ⟨[1,4,108,145], 44602511244506889289886437777407793136992542, 1, 1, 1, 0⟩
theorem s7_214_edges : next config 7 s7_214 = [] := by decide
theorem s7_214_safe : Safe 6 7 s7_214 := by
  apply safe_succ 5 7 s7_214 [] (by decide) s7_214_edges
  simp
def s7_215 : State := ⟨[1,4,108,145], 44602511244506889289886474670895940556095766, 1, 1, 1, 0⟩
theorem s7_215_edges : next config 7 s7_215 = [] := by decide
theorem s7_215_safe : Safe 6 7 s7_215 := by
  apply safe_succ 5 7 s7_215 [] (by decide) s7_215_edges
  simp
def s7_216 : State := ⟨[1,4,108,145], 66902575878303670554495229300841291106550046, 1, 1, 1, 0⟩
theorem s7_216_edges : next config 7 s7_216 = [] := by decide
theorem s7_216_safe : Safe 6 7 s7_216 := by
  apply safe_succ 5 7 s7_216 [] (by decide) s7_216_edges
  simp
def s7_217 : State := ⟨[1,4,108,145], 66902575878303670554495266194329438525653270, 1, 1, 1, 0⟩
theorem s7_217_edges : next config 7 s7_217 = [] := by decide
theorem s7_217_safe : Safe 6 7 s7_217 := by
  apply safe_succ 5 7 s7_217 [] (by decide) s7_217_edges
  simp
def s7_218 : State := ⟨[1,4,112,145], 44601830684620543308232260259516322658062614, 3, 3, 1, 0⟩
theorem s7_218_edges : next config 7 s7_218 = [] := by decide
theorem s7_218_safe : Safe 6 7 s7_218 := by
  apply safe_succ 5 7 s7_218 [] (by decide) s7_218_edges
  simp
def s7_219 : State := ⟨[1,4,112,145], 44601830684620543308232260259516322660155670, 3, 3, 1, 0⟩
theorem s7_219_edges : next config 7 s7_219 = [s8_67] := by decide
theorem s7_219_safe : Safe 6 7 s7_219 := by
  apply safe_succ 5 7 s7_219 [s8_67] (by decide) s7_219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_67_safe
def s7_220 : State := ⟨[1,4,113,145], 44601830689812840166767087888046818987282710, 3, 3, 1, 0⟩
theorem s7_220_edges : next config 7 s7_220 = [s8_100] := by decide
theorem s7_220_safe : Safe 6 7 s7_220 := by
  apply safe_succ 5 7 s7_220 [s8_100] (by decide) s7_220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_100_safe
def s7_221 : State := ⟨[1,4,113,145], 44601830689812840166767087888046818989375766, 3, 3, 1, 0⟩
theorem s7_221_edges : next config 7 s7_221 = [s8_101, s8_68] := by decide
theorem s7_221_safe : Safe 6 7 s7_221 := by
  apply safe_succ 5 7 s7_221 [s8_101, s8_68] (by decide) s7_221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_101_safe
  · subst z; exact s8_68_safe
def s7_222 : State := ⟨[1,4,117,145], 44601830845581745922811916743961708865978646, 3, 3, 1, 0⟩
theorem s7_222_edges : next config 7 s7_222 = [s8_102] := by decide
theorem s7_222_safe : Safe 6 7 s7_222 := by
  apply safe_succ 5 7 s7_222 [s8_102] (by decide) s7_222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_102_safe
def s7_223 : State := ⟨[1,4,194,104], 25108406947392729606368181220611735078775808399257509105942, 2, 2, 1, 0⟩
theorem s7_223_edges : next config 7 s7_223 = [] := by decide
theorem s7_223_safe : Safe 6 7 s7_223 := by
  apply safe_succ 5 7 s7_223 [] (by decide) s7_223_edges
  simp
def s7_224 : State := ⟨[1,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082070, 3, 3, 1, 0⟩
theorem s7_224_edges : next config 7 s7_224 = [s8_103] := by decide
theorem s7_224_safe : Safe 6 7 s7_224 := by
  apply safe_succ 5 7 s7_224 [s8_103] (by decide) s7_224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_103_safe
def s7_225 : State := ⟨[1,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175126, 3, 3, 1, 0⟩
theorem s7_225_edges : next config 7 s7_225 = [s8_104, s8_69] := by decide
theorem s7_225_safe : Safe 6 7 s7_225 := by
  apply safe_succ 5 7 s7_225 [s8_104, s8_69] (by decide) s7_225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_104_safe
  · subst z; exact s8_69_safe
def s7_226 : State := ⟨[1,4,249,145], 904625697166532776746648320380418882614915937571053134569312999698937741598, 1, 1, 1, 0⟩
theorem s7_226_edges : next config 7 s7_226 = [] := by decide
theorem s7_226_safe : Safe 6 7 s7_226 := by
  apply safe_succ 5 7 s7_226 [] (by decide) s7_226_edges
  simp
def s7_227 : State := ⟨[1,4,249,145], 904625697166532776746648320380418882614915937571053134606206487846356844822, 1, 1, 1, 0⟩
theorem s7_227_edges : next config 7 s7_227 = [] := by decide
theorem s7_227_safe : Safe 6 7 s7_227 := by
  apply safe_succ 5 7 s7_227 [] (by decide) s7_227_edges
  simp
def s7_228 : State := ⟨[1,4,249,145], 904625697166532776746648320380441182679549734352317743360836433196907299102, 1, 1, 1, 0⟩
theorem s7_228_edges : next config 7 s7_228 = [] := by decide
theorem s7_228_safe : Safe 6 7 s7_228 := by
  apply safe_succ 5 7 s7_228 [] (by decide) s7_228_edges
  simp
def s7_229 : State := ⟨[1,4,249,145], 904625697166532776746648320380441182679549734352317743397729921344326402326, 1, 1, 1, 0⟩
theorem s7_229_edges : next config 7 s7_229 = [] := by decide
theorem s7_229_safe : Safe 6 7 s7_229 := by
  apply safe_succ 5 7 s7_229 [] (by decide) s7_229_edges
  simp
def s7_230 : State := ⟨[1,12,65,145], 44601830679428167221534955260136380206092566, 3, 3, 1, 0⟩
theorem s7_230_edges : next config 7 s7_230 = [s8_59] := by decide
theorem s7_230_safe : Safe 6 7 s7_230 := by
  apply safe_succ 5 7 s7_230 [s8_59] (by decide) s7_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_59_safe
def s7_231 : State := ⟨[1,12,66,145], 44601830679428167221534992153624527625195798, 3, 3, 1, 0⟩
theorem s7_231_edges : next config 7 s7_231 = [s8_60, s8_61] := by decide
theorem s7_231_safe : Safe 6 7 s7_231 := by
  apply safe_succ 5 7 s7_231 [s8_60, s8_61] (by decide) s7_231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_60_safe
  · subst z; exact s8_61_safe
def s7_232 : State := ⟨[1,12,67,145], 44601830679428167226370843006035633998336278, 3, 1, 1, 0⟩
theorem s7_232_edges : next config 7 s7_232 = [s8_0] := by decide
theorem s7_232_safe : Safe 6 7 s7_232 := by
  apply safe_succ 5 7 s7_232 [s8_0] (by decide) s7_232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_0_safe
def s7_233 : State := ⟨[1,12,67,145], 44601830679428167227579695038673968334835990, 3, 1, 1, 0⟩
theorem s7_233_edges : next config 7 s7_233 = [s8_2] := by decide
theorem s7_233_safe : Safe 6 7 s7_233 := by
  apply safe_succ 5 7 s7_233 [s8_2] (by decide) s7_233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_2_safe
def s7_234 : State := ⟨[1,12,67,145], 133806172603018343541531792529623995557941534, 3, 1, 1, 0⟩
theorem s7_234_edges : next config 7 s7_234 = [s8_6] := by decide
theorem s7_234_safe : Safe 6 7 s7_234 := by
  apply safe_succ 5 7 s7_234 [s8_6] (by decide) s7_234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_6_safe
def s7_235 : State := ⟨[1,12,67,145], 156105556672081282929213657303842629991076126, 3, 1, 1, 0⟩
theorem s7_235_edges : next config 7 s7_235 = [s8_7] := by decide
theorem s7_235_safe : Safe 6 7 s7_235 := by
  apply safe_succ 5 7 s7_235 [s8_7] (by decide) s7_235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_7_safe
def s7_236 : State := ⟨[1,12,80,145], 44601830679428167222743844186262861961695510, 3, 3, 1, 0⟩
theorem s7_236_edges : next config 7 s7_236 = [s8_62] := by decide
theorem s7_236_safe : Safe 6 7 s7_236 := by
  apply safe_succ 5 7 s7_236 [s8_62] (by decide) s7_236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_62_safe
def s7_237 : State := ⟨[1,12,81,145], 44601830679428167223952770005877491136401686, 3, 3, 1, 0⟩
theorem s7_237_edges : next config 7 s7_237 = [] := by decide
theorem s7_237_safe : Safe 6 7 s7_237 := by
  apply safe_succ 5 7 s7_237 [] (by decide) s7_237_edges
  simp
def s7_238 : State := ⟨[1,12,96,145], 44601830679428246449697432630985826330939670, 3, 3, 1, 0⟩
theorem s7_238_edges : next config 7 s7_238 = [s8_406, s8_106, s8_276, s8_63, s8_69, s8_64, s8_67] := by decide
theorem s7_238_safe : Safe 6 7 s7_238 := by
  apply safe_succ 5 7 s7_238 [s8_406, s8_106, s8_276, s8_63, s8_69, s8_64, s8_67] (by decide) s7_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s8_406_safe
  · subst z; exact s8_106_safe
  · subst z; exact s8_276_safe
  · subst z; exact s8_63_safe
  · subst z; exact s8_69_safe
  · subst z; exact s8_64_safe
  · subst z; exact s8_67_safe
def s7_239 : State := ⟨[1,12,96,145], 133806172603018422769694159220008999425478942, 3, 1, 1, 0⟩
theorem s7_239_edges : next config 7 s7_239 = [s8_10, s8_65] := by decide
theorem s7_239_safe : Safe 6 7 s7_239 := by
  apply safe_succ 5 7 s7_239 [s8_10, s8_65] (by decide) s7_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_10_safe
  · subst z; exact s8_65_safe
def s7_240 : State := ⟨[1,12,96,145], 156105556672081362157376023994227633858613534, 3, 1, 1, 0⟩
theorem s7_240_edges : next config 7 s7_240 = [s8_11, s8_66] := by decide
theorem s7_240_safe : Safe 6 7 s7_240 := by
  apply safe_succ 5 7 s7_240 [s8_11, s8_66] (by decide) s7_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_11_safe
  · subst z; exact s8_66_safe
def s7_241 : State := ⟨[1,12,104,145], 44602511244182370736228011050624637116420382, 3, 1, 1, 0⟩
theorem s7_241_edges : next config 7 s7_241 = [s8_12] := by decide
theorem s7_241_safe : Safe 6 7 s7_241 := by
  apply safe_succ 5 7 s7_241 [s8_12] (by decide) s7_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_12_safe
def s7_242 : State := ⟨[1,12,104,145], 44602511244182370736228011050624645706354966, 3, 1, 1, 0⟩
theorem s7_242_edges : next config 7 s7_242 = [s8_13] := by decide
theorem s7_242_safe : Safe 6 7 s7_242 := by
  apply safe_succ 5 7 s7_242 [s8_13] (by decide) s7_242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_13_safe
def s7_243 : State := ⟨[1,12,104,145], 44602511244182370736228047944112784535523606, 3, 1, 1, 0⟩
theorem s7_243_edges : next config 7 s7_243 = [s8_14] := by decide
theorem s7_243_safe : Safe 6 7 s7_243 := by
  apply safe_succ 5 7 s7_243 [s8_14] (by decide) s7_243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_14_safe
def s7_244 : State := ⟨[1,12,104,145], 44602511244182529192553039579299824204321046, 3, 1, 1, 0⟩
theorem s7_244_edges : next config 7 s7_244 = [s8_15] := by decide
theorem s7_244_safe : Safe 6 7 s7_244 := by
  apply safe_succ 5 7 s7_244 [s8_15] (by decide) s7_244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_15_safe
def s7_245 : State := ⟨[1,12,104,145], 66902575877979152000836802574058135085977886, 3, 1, 1, 0⟩
theorem s7_245_edges : next config 7 s7_245 = [s8_20] := by decide
theorem s7_245_safe : Safe 6 7 s7_245 := by
  apply safe_succ 5 7 s7_245 [s8_20] (by decide) s7_245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_20_safe
def s7_246 : State := ⟨[1,12,104,145], 66902575877979152000836802574058143675912470, 3, 1, 1, 0⟩
theorem s7_246_edges : next config 7 s7_246 = [s8_21] := by decide
theorem s7_246_safe : Safe 6 7 s7_246 := by
  apply safe_succ 5 7 s7_246 [s8_21] (by decide) s7_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_21_safe
def s7_247 : State := ⟨[1,12,104,145], 66902575877979152000836839467546282505081110, 3, 1, 1, 0⟩
theorem s7_247_edges : next config 7 s7_247 = [s8_22] := by decide
theorem s7_247_safe : Safe 6 7 s7_247 := by
  apply safe_succ 5 7 s7_247 [s8_22] (by decide) s7_247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_22_safe
def s7_248 : State := ⟨[1,12,104,145], 66902575877979310457161831102733322173878550, 3, 1, 1, 0⟩
theorem s7_248_edges : next config 7 s7_248 = [s8_23] := by decide
theorem s7_248_safe : Safe 6 7 s7_248 := by
  apply safe_succ 5 7 s7_248 [s8_23] (by decide) s7_248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_23_safe
def s7_249 : State := ⟨[1,12,104,146], 89204682205977458896226374345136223664804126, 3, 1, 1, 0⟩
theorem s7_249_edges : next config 7 s7_249 = [s8_28] := by decide
theorem s7_249_safe : Safe 6 7 s7_249 := by
  apply safe_succ 5 7 s7_249 [s8_28] (by decide) s7_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_28_safe
def s7_250 : State := ⟨[1,12,104,146], 89204682205977458896226411238624371083907350, 3, 1, 1, 0⟩
theorem s7_250_edges : next config 7 s7_250 = [s8_29] := by decide
theorem s7_250_safe : Safe 6 7 s7_250 := by
  apply safe_succ 5 7 s7_250 [s8_29] (by decide) s7_250_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_29_safe
def s7_251 : State := ⟨[1,12,104,146], 89207404464912826403934081341995677810495766, 3, 1, 1, 0⟩
theorem s7_251_edges : next config 7 s7_251 = [s8_30] := by decide
theorem s7_251_safe : Safe 6 7 s7_251 := by
  apply safe_succ 5 7 s7_251 [s8_30] (by decide) s7_251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_30_safe
def s7_252 : State := ⟨[1,12,104,146], 111504066275040398283908239119354858097938718, 3, 1, 1, 0⟩
theorem s7_252_edges : next config 7 s7_252 = [s8_31] := by decide
theorem s7_252_safe : Safe 6 7 s7_252 := by
  apply safe_succ 5 7 s7_252 [s8_31] (by decide) s7_252_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_31_safe
def s7_253 : State := ⟨[1,12,104,146], 111504066275040398283908276012843005517041942, 3, 1, 1, 0⟩
theorem s7_253_edges : next config 7 s7_253 = [s8_32] := by decide
theorem s7_253_safe : Safe 6 7 s7_253 := by
  apply safe_succ 5 7 s7_253 [s8_32] (by decide) s7_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_32_safe
def s7_254 : State := ⟨[1,12,104,162], 5846006551025023527781069414366386621401371054366, 3, 1, 1, 0⟩
theorem s7_254_edges : next config 7 s7_254 = [s8_33] := by decide
theorem s7_254_safe : Safe 6 7 s7_254 := by
  apply safe_succ 5 7 s7_254 [s8_33] (by decide) s7_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_33_safe
def s7_255 : State := ⟨[1,12,104,162], 5846006551025023527781069414403280109548790157590, 3, 1, 1, 0⟩
theorem s7_255_edges : next config 7 s7_255 = [s8_34] := by decide
theorem s7_255_safe : Safe 6 7 s7_255 := by
  apply safe_succ 5 7 s7_255 [s8_34] (by decide) s7_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_34_safe
def s7_256 : State := ⟨[1,12,104,162], 5846006551025023527939525739394915296588458955030, 3, 1, 1, 0⟩
theorem s7_256_edges : next config 7 s7_256 = [s8_35] := by decide
theorem s7_256_safe : Safe 6 7 s7_256 := by
  apply safe_succ 5 7 s7_256 [s8_35] (by decide) s7_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_35_safe
def s7_257 : State := ⟨[1,12,104,162], 5846006553747282463148577122073383480855516746006, 3, 1, 1, 0⟩
theorem s7_257_edges : next config 7 s7_257 = [s8_36] := by decide
theorem s7_257_safe : Safe 6 7 s7_257 := by
  apply safe_succ 5 7 s7_257 [s8_36] (by decide) s7_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_36_safe
def s7_258 : State := ⟨[1,12,104,162], 7307508186994796978301000393229171211330230751518, 3, 1, 1, 0⟩
theorem s7_258_edges : next config 7 s7_258 = [s8_37] := by decide
theorem s7_258_safe : Safe 6 7 s7_258 := by
  apply safe_succ 5 7 s7_258 [s8_37] (by decide) s7_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_37_safe
def s7_259 : State := ⟨[1,12,104,162], 7307508186994796978301000393266064699477649854742, 3, 1, 1, 0⟩
theorem s7_259_edges : next config 7 s7_259 = [s8_38] := by decide
theorem s7_259_safe : Safe 6 7 s7_259 := by
  apply safe_succ 5 7 s7_259 [s8_38] (by decide) s7_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_38_safe
def s7_260 : State := ⟨[1,12,104,162], 7307508186994796978459456718257699886517318652182, 3, 1, 1, 0⟩
theorem s7_260_edges : next config 7 s7_260 = [s8_39] := by decide
theorem s7_260_safe : Safe 6 7 s7_260 := by
  apply safe_succ 5 7 s7_260 [s8_39] (by decide) s7_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_39_safe
def s7_261 : State := ⟨[1,12,104,162], 17538019649672246873410548076096650778648831398166, 3, 1, 1, 0⟩
theorem s7_261_edges : next config 7 s7_261 = [s8_40] := by decide
theorem s7_261_safe : Safe 6 7 s7_261 := by
  apply safe_succ 5 7 s7_261 [s8_40] (by decide) s7_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_40_safe
def s7_262 : State := ⟨[1,12,104,162], 18999521285642020323930479054959435368577691095318, 3, 1, 1, 0⟩
theorem s7_262_edges : next config 7 s7_262 = [s8_41] := by decide
theorem s7_262_safe : Safe 6 7 s7_262 := by
  apply safe_succ 5 7 s7_262 [s8_41] (by decide) s7_262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_41_safe
def s7_263 : State := ⟨[1,12,104,163], 11692013100348635200595808745231518700033691160854, 3, 1, 1, 0⟩
theorem s7_263_edges : next config 7 s7_263 = [s8_42] := by decide
theorem s7_263_safe : Safe 6 7 s7_263 := by
  apply safe_succ 5 7 s7_263 [s8_42] (by decide) s7_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_42_safe
def s7_264 : State := ⟨[1,12,104,163], 11692013101709764668279562599085017129752174072094, 3, 1, 1, 0⟩
theorem s7_264_edges : next config 7 s7_264 = [s8_43] := by decide
theorem s7_264_safe : Safe 6 7 s7_264 := by
  apply safe_succ 5 7 s7_264 [s8_43] (by decide) s7_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_43_safe
def s7_265 : State := ⟨[1,12,104,163], 13153514736318408651115739724094303289953960923422, 3, 1, 1, 0⟩
theorem s7_265_edges : next config 7 s7_265 = [s8_44] := by decide
theorem s7_265_safe : Safe 6 7 s7_265 := by
  apply safe_succ 5 7 s7_265 [s8_44] (by decide) s7_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_44_safe
def s7_266 : State := ⟨[1,12,104,163], 14615016373649311569319424556810586309618483400982, 3, 1, 1, 0⟩
theorem s7_266_edges : next config 7 s7_266 = [s8_45] := by decide
theorem s7_266_safe : Safe 6 7 s7_266 := by
  apply safe_succ 5 7 s7_266 [s8_45] (by decide) s7_266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_45_safe
def s7_267 : State := ⟨[1,12,104,176], 95780971326419139128314594914659690004932607210492190, 3, 1, 1, 0⟩
theorem s7_267_edges : next config 7 s7_267 = [s8_46] := by decide
theorem s7_267_safe : Safe 6 7 s7_267 := by
  apply safe_succ 5 7 s7_267 [s8_46] (by decide) s7_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_46_safe
def s7_268 : State := ⟨[1,12,104,176], 95780971326419139128314594914659726898420754629595414, 3, 1, 1, 0⟩
theorem s7_268_edges : next config 7 s7_268 = [s8_47] := by decide
theorem s7_268_safe : Safe 6 7 s7_268 := by
  apply safe_succ 5 7 s7_268 [s8_47] (by decide) s7_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_47_safe
def s7_269 : State := ⟨[1,12,104,176], 95782432805755724832702175457956688015303901637054750, 3, 1, 1, 0⟩
theorem s7_269_edges : next config 7 s7_269 = [s8_48] := by decide
theorem s7_269_safe : Safe 6 7 s7_269 := by
  apply safe_succ 5 7 s7_269 [s8_48] (by decide) s7_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_48_safe
def s7_270 : State := ⟨[1,12,104,176], 95782432805755724832702175457956724908792049056157974, 3, 1, 1, 0⟩
theorem s7_270_edges : next config 7 s7_270 = [s8_49] := by decide
theorem s7_270_safe : Safe 6 7 s7_270 := by
  apply safe_succ 5 7 s7_270 [s8_49] (by decide) s7_270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_49_safe
def s7_271 : State := ⟨[1,12,209,145], 822752278660603021122086421958103419712902851183438164461293846, 3, 3, 1, 0⟩
theorem s7_271_edges : next config 7 s7_271 = [] := by decide
theorem s7_271_safe : Safe 6 7 s7_271 := by
  apply safe_succ 5 7 s7_271 [] (by decide) s7_271_edges
  simp
def s7_272 : State := ⟨[1,12,241,145], 3533694129556768659166595001530439542899129882077862275623413092450373918, 3, 1, 1, 0⟩
theorem s7_272_edges : next config 7 s7_272 = [s8_54] := by decide
theorem s7_272_safe : Safe 6 7 s7_272 := by
  apply safe_succ 5 7 s7_272 [s8_54] (by decide) s7_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_54_safe
def s7_273 : State := ⟨[1,12,241,145], 3533694129556768659166595001530439542899129882077862312516901239869477142, 3, 1, 1, 0⟩
theorem s7_273_edges : next config 7 s7_273 = [s8_55] := by decide
theorem s7_273_safe : Safe 6 7 s7_273 := by
  apply safe_succ 5 7 s7_273 [s8_55] (by decide) s7_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_55_safe
def s7_274 : State := ⟨[1,12,241,145], 3533694129556768659166595001552739607532926663342471067146846590419931422, 3, 1, 1, 0⟩
theorem s7_274_edges : next config 7 s7_274 = [s8_56] := by decide
theorem s7_274_safe : Safe 6 7 s7_274 := by
  apply safe_succ 5 7 s7_274 [s8_56] (by decide) s7_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_56_safe
def s7_275 : State := ⟨[1,12,241,145], 3533694129556768659166595001552739607532926663342471104040334737839034646, 3, 1, 1, 0⟩
theorem s7_275_edges : next config 7 s7_275 = [s8_57] := by decide
theorem s7_275_safe : Safe 6 7 s7_275 := by
  apply safe_succ 5 7 s7_275 [s8_57] (by decide) s7_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_57_safe
def s7_276 : State := ⟨[1,21,65,145], 44601830679428167221534955260136380206092566, 3, 3, 1, 0⟩
theorem s7_276_edges : next config 7 s7_276 = [s8_70] := by decide
theorem s7_276_safe : Safe 6 7 s7_276 := by
  apply safe_succ 5 7 s7_276 [s8_70] (by decide) s7_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_70_safe
def s7_277 : State := ⟨[1,21,66,145], 44601830679428167221534992153624527625195798, 3, 3, 1, 0⟩
theorem s7_277_edges : next config 7 s7_277 = [s8_71, s8_74] := by decide
theorem s7_277_safe : Safe 6 7 s7_277 := by
  apply safe_succ 5 7 s7_277 [s8_71, s8_74] (by decide) s7_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_71_safe
  · subst z; exact s8_74_safe
def s7_278 : State := ⟨[1,21,67,145], 44601830679428167226370843006035634000429334, 3, 1, 1, 0⟩
theorem s7_278_edges : next config 7 s7_278 = [s8_87] := by decide
theorem s7_278_safe : Safe 6 7 s7_278 := by
  apply safe_succ 5 7 s7_278 [s8_87] (by decide) s7_278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_87_safe
def s7_279 : State := ⟨[1,21,67,145], 44601830679428167227579695038673968336929046, 3, 1, 1, 0⟩
theorem s7_279_edges : next config 7 s7_279 = [s8_88] := by decide
theorem s7_279_safe : Safe 6 7 s7_279 := by
  apply safe_succ 5 7 s7_279 [s8_88] (by decide) s7_279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_88_safe
def s7_280 : State := ⟨[1,21,80,145], 44601830679428167222743844186262861961695510, 3, 3, 1, 0⟩
theorem s7_280_edges : next config 7 s7_280 = [s8_75] := by decide
theorem s7_280_safe : Safe 6 7 s7_280 := by
  apply safe_succ 5 7 s7_280 [s8_75] (by decide) s7_280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_75_safe
def s7_281 : State := ⟨[1,21,81,145], 44601830679428167223952770005877491136401686, 3, 3, 1, 0⟩
theorem s7_281_edges : next config 7 s7_281 = [] := by decide
theorem s7_281_safe : Safe 6 7 s7_281 := by
  apply safe_succ 5 7 s7_281 [] (by decide) s7_281_edges
  simp
def s7_282 : State := ⟨[1,21,86,145], 44601830679428167303741947887419311505211670, 3, 1, 1, 0⟩
theorem s7_282_edges : next config 7 s7_282 = [s8_72] := by decide
theorem s7_282_safe : Safe 6 7 s7_282 := by
  apply safe_succ 5 7 s7_282 [s8_72] (by decide) s7_282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_72_safe
def s7_283 : State := ⟨[1,21,86,145], 44601830679428167304950799920057645841711382, 3, 1, 1, 0⟩
theorem s7_283_edges : next config 7 s7_283 = [s8_73] := by decide
theorem s7_283_safe : Safe 6 7 s7_283 := by
  apply safe_succ 5 7 s7_283 [s8_73] (by decide) s7_283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_73_safe
def s7_284 : State := ⟨[1,21,96,145], 44601830679428246449697432630985826330939670, 3, 3, 1, 0⟩
theorem s7_284_edges : next config 7 s7_284 = [s8_407, s8_108, s8_277, s8_78, s8_85, s8_79, s8_83] := by decide
theorem s7_284_safe : Safe 6 7 s7_284 := by
  apply safe_succ 5 7 s7_284 [s8_407, s8_108, s8_277, s8_78, s8_85, s8_79, s8_83] (by decide) s7_284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s8_407_safe
  · subst z; exact s8_108_safe
  · subst z; exact s8_277_safe
  · subst z; exact s8_78_safe
  · subst z; exact s8_85_safe
  · subst z; exact s8_79_safe
  · subst z; exact s8_83_safe
def s7_285 : State := ⟨[1,21,96,145], 44601830679428246449697727778891005683761430, 3, 3, 1, 0⟩
theorem s7_285_edges : next config 7 s7_285 = [s8_80] := by decide
theorem s7_285_safe : Safe 6 7 s7_285 := by
  apply safe_succ 5 7 s7_285 [s8_80] (by decide) s7_285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_80_safe
def s7_286 : State := ⟨[1,21,96,145], 44601830679429514100297660860387323034140950, 3, 3, 1, 0⟩
theorem s7_286_edges : next config 7 s7_286 = [s8_109, s8_81] := by decide
theorem s7_286_safe : Safe 6 7 s7_286 := by
  apply safe_succ 5 7 s7_286 [s8_109, s8_81] (by decide) s7_286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_109_safe
  · subst z; exact s8_81_safe
def s7_287 : State := ⟨[1,21,108,145], 44601830679773047412959511028192929602797846, 3, 1, 1, 0⟩
theorem s7_287_edges : next config 7 s7_287 = [s8_110] := by decide
theorem s7_287_safe : Safe 6 7 s7_287 := by
  apply safe_succ 5 7 s7_287 [s8_110] (by decide) s7_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_110_safe
def s7_288 : State := ⟨[1,21,120,145], 44601832008676524644216957205216833862566166, 3, 1, 1, 0⟩
theorem s7_288_edges : next config 7 s7_288 = [] := by decide
theorem s7_288_safe : Safe 6 7 s7_288 := by
  apply safe_succ 5 7 s7_288 [] (by decide) s7_288_edges
  simp
def s7_289 : State := ⟨[1,21,121,145], 44601833337904520429132830109023894142910742, 3, 1, 1, 0⟩
theorem s7_289_edges : next config 7 s7_289 = [s8_111] := by decide
theorem s7_289_safe : Safe 6 7 s7_289 := by
  apply safe_succ 5 7 s7_289 [s8_111] (by decide) s7_289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_111_safe
def s7_290 : State := ⟨[1,21,125,145], 44601873214744393976609017223235702553248022, 3, 1, 1, 0⟩
theorem s7_290_edges : next config 7 s7_290 = [s8_112, s8_278] := by decide
theorem s7_290_safe : Safe 6 7 s7_290 := by
  apply safe_succ 5 7 s7_290 [s8_112, s8_278] (by decide) s7_290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_112_safe
  · subst z; exact s8_278_safe
def s7_291 : State := ⟨[1,21,209,145], 822752278660603021122086421958103419712902851183438164461293846, 3, 3, 1, 0⟩
theorem s7_291_edges : next config 7 s7_291 = [] := by decide
theorem s7_291_safe : Safe 6 7 s7_291 := by
  apply safe_succ 5 7 s7_291 [] (by decide) s7_291_edges
  simp
def s7_292 : State := ⟨[1,21,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546902, 3, 1, 1, 0⟩
theorem s7_292_edges : next config 7 s7_292 = [s8_113] := by decide
theorem s7_292_safe : Safe 6 7 s7_292 := by
  apply safe_succ 5 7 s7_292 [s8_113] (by decide) s7_292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_113_safe
def s7_293 : State := ⟨[1,29,67,145], 44601830679428167221535102834088970419372310, 3, 1, 1, 0⟩
theorem s7_293_edges : next config 7 s7_293 = [] := by decide
theorem s7_293_safe : Safe 6 7 s7_293 := by
  apply safe_succ 5 7 s7_293 [] (by decide) s7_293_edges
  simp
def s7_294 : State := ⟨[1,29,67,145], 44601830679428167221535139727577117838475542, 3, 1, 1, 0⟩
theorem s7_294_edges : next config 7 s7_294 = [] := by decide
theorem s7_294_safe : Safe 6 7 s7_294 := by
  apply safe_succ 5 7 s7_294 [] (by decide) s7_294_edges
  simp
def s7_295 : State := ⟨[1,29,104,145], 44601830679448528859301084301409774119092502, 3, 1, 1, 0⟩
theorem s7_295_edges : next config 7 s7_295 = [s8_115, s8_279] := by decide
theorem s7_295_safe : Safe 6 7 s7_295 := by
  apply safe_succ 5 7 s7_295 [s8_115, s8_279] (by decide) s7_295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_115_safe
  · subst z; exact s8_279_safe
def s7_296 : State := ⟨[1,53,104,145], 44601830679448528859301084310416972836962582, 3, 1, 1, 0⟩
theorem s7_296_edges : next config 7 s7_296 = [s8_116] := by decide
theorem s7_296_safe : Safe 6 7 s7_296 := by
  apply safe_succ 5 7 s7_296 [s8_116] (by decide) s7_296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_116_safe
def s7_297 : State := ⟨[1,68,96,145], 44601830679428246449697727778891005683761430, 3, 3, 1, 0⟩
theorem s7_297_edges : next config 7 s7_297 = [s8_86] := by decide
theorem s7_297_safe : Safe 6 7 s7_297 := by
  apply safe_succ 5 7 s7_297 [s8_86] (by decide) s7_297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_86_safe
def s7_298 : State := ⟨[1,86,67,145], 44601830679428167298906355289425237063696662, 3, 1, 1, 0⟩
theorem s7_298_edges : next config 7 s7_298 = [] := by decide
theorem s7_298_safe : Safe 6 7 s7_298 := by
  apply safe_succ 5 7 s7_298 [] (by decide) s7_298_edges
  simp
def s7_299 : State := ⟨[1,86,67,145], 44601830679428167298906392182913384482799894, 3, 1, 1, 0⟩
theorem s7_299_edges : next config 7 s7_299 = [] := by decide
theorem s7_299_safe : Safe 6 7 s7_299 := by
  apply safe_succ 5 7 s7_299 [] (by decide) s7_299_edges
  simp
def s7_300 : State := ⟨[1,86,67,145], 44601830679428167303742095461371901179527446, 3, 1, 1, 0⟩
theorem s7_300_edges : next config 7 s7_300 = [s8_72] := by decide
theorem s7_300_safe : Safe 6 7 s7_300 := by
  apply safe_succ 5 7 s7_300 [s8_72] (by decide) s7_300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_72_safe
def s7_301 : State := ⟨[1,86,67,145], 44601830679428167304950947494010235516027158, 3, 1, 1, 0⟩
theorem s7_301_edges : next config 7 s7_301 = [s8_73] := by decide
theorem s7_301_safe : Safe 6 7 s7_301 := by
  apply safe_succ 5 7 s7_301 [s8_73] (by decide) s7_301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_73_safe
def s7_302 : State := ⟨[1,100,96,145], 44601830679429514100297660860387323034140950, 3, 3, 1, 0⟩
theorem s7_302_edges : next config 7 s7_302 = [s8_123, s8_91] := by decide
theorem s7_302_safe : Safe 6 7 s7_302 := by
  apply safe_succ 5 7 s7_302 [s8_123, s8_91] (by decide) s7_302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_123_safe
  · subst z; exact s8_91_safe
def s7_303 : State := ⟨[1,100,104,145], 44602511244183638386828239280026133819621662, 3, 1, 1, 0⟩
theorem s7_303_edges : next config 7 s7_303 = [] := by decide
theorem s7_303_safe : Safe 6 7 s7_303 := by
  apply safe_succ 5 7 s7_303 [] (by decide) s7_303_edges
  simp
def s7_304 : State := ⟨[1,100,104,145], 44602511244183638386828276173514281238724886, 3, 1, 1, 0⟩
theorem s7_304_edges : next config 7 s7_304 = [] := by decide
theorem s7_304_safe : Safe 6 7 s7_304 := by
  apply safe_succ 5 7 s7_304 [] (by decide) s7_304_edges
  simp
def s7_305 : State := ⟨[1,100,104,145], 66902575877980419651437030803459631789179166, 3, 1, 1, 0⟩
theorem s7_305_edges : next config 7 s7_305 = [] := by decide
theorem s7_305_safe : Safe 6 7 s7_305 := by
  apply safe_succ 5 7 s7_305 [] (by decide) s7_305_edges
  simp
def s7_306 : State := ⟨[1,100,104,145], 66902575877980419651437067696947779208282390, 3, 1, 1, 0⟩
theorem s7_306_edges : next config 7 s7_306 = [] := by decide
theorem s7_306_safe : Safe 6 7 s7_306 := by
  apply safe_succ 5 7 s7_306 [] (by decide) s7_306_edges
  simp
def s7_307 : State := ⟨[1,108,104,145], 44602511244506889289886437777407793136992542, 3, 1, 1, 0⟩
theorem s7_307_edges : next config 7 s7_307 = [s8_18] := by decide
theorem s7_307_safe : Safe 6 7 s7_307 := by
  apply safe_succ 5 7 s7_307 [s8_18] (by decide) s7_307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_18_safe
def s7_308 : State := ⟨[1,108,104,145], 44602511244506889289886474670895940556095766, 3, 1, 1, 0⟩
theorem s7_308_edges : next config 7 s7_308 = [s8_19] := by decide
theorem s7_308_safe : Safe 6 7 s7_308 := by
  apply safe_succ 5 7 s7_308 [s8_19] (by decide) s7_308_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_19_safe
def s7_309 : State := ⟨[1,108,104,145], 66902575878303670554495229300841291106550046, 3, 1, 1, 0⟩
theorem s7_309_edges : next config 7 s7_309 = [s8_26] := by decide
theorem s7_309_safe : Safe 6 7 s7_309 := by
  apply safe_succ 5 7 s7_309 [s8_26] (by decide) s7_309_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_26_safe
def s7_310 : State := ⟨[1,108,104,145], 66902575878303670554495266194329438525653270, 3, 1, 1, 0⟩
theorem s7_310_edges : next config 7 s7_310 = [s8_27] := by decide
theorem s7_310_safe : Safe 6 7 s7_310 := by
  apply safe_succ 5 7 s7_310 [s8_27] (by decide) s7_310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_27_safe
def s7_311 : State := ⟨[1,117,104,145], 44601830845602028332415568414385656117264662, 3, 1, 1, 0⟩
theorem s7_311_edges : next config 7 s7_311 = [s8_124] := by decide
theorem s7_311_safe : Safe 6 7 s7_311 := by
  apply safe_succ 5 7 s7_311 [s8_124] (by decide) s7_311_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_124_safe
def s7_312 : State := ⟨[1,125,104,145], 44601873214744393976609017223235702553248022, 3, 1, 1, 0⟩
theorem s7_312_edges : next config 7 s7_312 = [s8_125, s8_280] := by decide
theorem s7_312_safe : Safe 6 7 s7_312 := by
  apply safe_succ 5 7 s7_312 [s8_125, s8_280] (by decide) s7_312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_125_safe
  · subst z; exact s8_280_safe
def s7_313 : State := ⟨[3,4,67,145], 44601830679428167221535065940600822461305118, 3, 3, 1, 0⟩
theorem s7_313_edges : next config 7 s7_313 = [s8_451, s8_281] := by decide
theorem s7_313_safe : Safe 6 7 s7_313 := by
  apply safe_succ 5 7 s7_313 [s8_451, s8_281] (by decide) s7_313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_451_safe
  · subst z; exact s8_281_safe
def s7_314 : State := ⟨[3,4,67,145], 44601830679428167221535065940600822463398174, 3, 3, 1, 0⟩
theorem s7_314_edges : next config 7 s7_314 = [s8_452, s8_282, s8_105] := by decide
theorem s7_314_safe : Safe 6 7 s7_314 := by
  apply safe_succ 5 7 s7_314 [s8_452, s8_282, s8_105] (by decide) s7_314_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_452_safe
  · subst z; exact s8_282_safe
  · subst z; exact s8_105_safe
def s7_315 : State := ⟨[3,4,67,145], 133806172603018343541531792529623995557941534, 3, 2, 1, 0⟩
theorem s7_315_edges : next config 7 s7_315 = [s8_6] := by decide
theorem s7_315_safe : Safe 6 7 s7_315 := by
  apply safe_succ 5 7 s7_315 [s8_6] (by decide) s7_315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_6_safe
def s7_316 : State := ⟨[3,4,67,145], 156105556672081282929213657303842629991076126, 3, 2, 1, 0⟩
theorem s7_316_edges : next config 7 s7_316 = [s8_7] := by decide
theorem s7_316_safe : Safe 6 7 s7_316 := by
  apply safe_succ 5 7 s7_316 [s8_7] (by decide) s7_316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_7_safe
def s7_317 : State := ⟨[3,4,96,145], 44601830679428246449697432630985826328842526, 3, 3, 1, 0⟩
theorem s7_317_edges : next config 7 s7_317 = [s8_453, s8_287, s8_103, s8_94] := by decide
theorem s7_317_safe : Safe 6 7 s7_317 := by
  apply safe_succ 5 7 s7_317 [s8_453, s8_287, s8_103, s8_94] (by decide) s7_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_453_safe
  · subst z; exact s8_287_safe
  · subst z; exact s8_103_safe
  · subst z; exact s8_94_safe
def s7_318 : State := ⟨[3,4,96,145], 44601830679428246449697432630985826330935582, 3, 3, 1, 0⟩
theorem s7_318_edges : next config 7 s7_318 = [s8_454, s8_288, s8_123, s8_106, s8_93, s8_104, s8_95] := by decide
theorem s7_318_safe : Safe 6 7 s7_318 := by
  apply safe_succ 5 7 s7_318 [s8_454, s8_288, s8_123, s8_106, s8_93, s8_104, s8_95] (by decide) s7_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s8_454_safe
  · subst z; exact s8_288_safe
  · subst z; exact s8_123_safe
  · subst z; exact s8_106_safe
  · subst z; exact s8_93_safe
  · subst z; exact s8_104_safe
  · subst z; exact s8_95_safe
def s7_319 : State := ⟨[3,4,96,145], 44601830679429514100297660860387323032043806, 3, 3, 1, 0⟩
theorem s7_319_edges : next config 7 s7_319 = [s8_96] := by decide
theorem s7_319_safe : Safe 6 7 s7_319 := by
  apply safe_succ 5 7 s7_319 [s8_96] (by decide) s7_319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_96_safe
def s7_320 : State := ⟨[3,4,96,145], 133806172603018422769694159220008999425478942, 3, 2, 1, 0⟩
theorem s7_320_edges : next config 7 s7_320 = [s8_10, s8_98] := by decide
theorem s7_320_safe : Safe 6 7 s7_320 := by
  apply safe_succ 5 7 s7_320 [s8_10, s8_98] (by decide) s7_320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_10_safe
  · subst z; exact s8_98_safe
def s7_321 : State := ⟨[3,4,96,145], 156105556672081362157376023994227633858613534, 3, 2, 1, 0⟩
theorem s7_321_edges : next config 7 s7_321 = [s8_11, s8_99] := by decide
theorem s7_321_safe : Safe 6 7 s7_321 := by
  apply safe_succ 5 7 s7_321 [s8_11, s8_99] (by decide) s7_321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_11_safe
  · subst z; exact s8_99_safe
def s7_322 : State := ⟨[3,4,104,145], 44602511244182370736228011050624637116420382, 3, 2, 1, 0⟩
theorem s7_322_edges : next config 7 s7_322 = [s8_455, s8_12, s8_291] := by decide
theorem s7_322_safe : Safe 6 7 s7_322 := by
  apply safe_succ 5 7 s7_322 [s8_455, s8_12, s8_291] (by decide) s7_322_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_455_safe
  · subst z; exact s8_12_safe
  · subst z; exact s8_291_safe
def s7_323 : State := ⟨[3,4,104,145], 44602511244183638386828239280026133819621662, 3, 2, 1, 0⟩
theorem s7_323_edges : next config 7 s7_323 = [s8_16] := by decide
theorem s7_323_safe : Safe 6 7 s7_323 := by
  apply safe_succ 5 7 s7_323 [s8_16] (by decide) s7_323_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_16_safe
def s7_324 : State := ⟨[3,4,104,145], 44602511244506889289886437777407793136992542, 3, 2, 1, 0⟩
theorem s7_324_edges : next config 7 s7_324 = [s8_18] := by decide
theorem s7_324_safe : Safe 6 7 s7_324 := by
  apply safe_succ 5 7 s7_324 [s8_18] (by decide) s7_324_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_18_safe
def s7_325 : State := ⟨[3,4,104,145], 66902575877979152000836802574058135085977886, 3, 2, 1, 0⟩
theorem s7_325_edges : next config 7 s7_325 = [s8_456, s8_20, s8_293] := by decide
theorem s7_325_safe : Safe 6 7 s7_325 := by
  apply safe_succ 5 7 s7_325 [s8_456, s8_20, s8_293] (by decide) s7_325_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_456_safe
  · subst z; exact s8_20_safe
  · subst z; exact s8_293_safe
def s7_326 : State := ⟨[3,4,104,145], 66902575877980419651437030803459631789179166, 3, 2, 1, 0⟩
theorem s7_326_edges : next config 7 s7_326 = [s8_24] := by decide
theorem s7_326_safe : Safe 6 7 s7_326 := by
  apply safe_succ 5 7 s7_326 [s8_24] (by decide) s7_326_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_24_safe
def s7_327 : State := ⟨[3,4,104,145], 66902575878303670554495229300841291106550046, 3, 2, 1, 0⟩
theorem s7_327_edges : next config 7 s7_327 = [s8_26] := by decide
theorem s7_327_safe : Safe 6 7 s7_327 := by
  apply safe_succ 5 7 s7_327 [s8_26] (by decide) s7_327_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_26_safe
def s7_328 : State := ⟨[3,4,104,146], 89204682205977458896226374345136223664804126, 3, 2, 1, 0⟩
theorem s7_328_edges : next config 7 s7_328 = [s8_28, s8_98] := by decide
theorem s7_328_safe : Safe 6 7 s7_328 := by
  apply safe_succ 5 7 s7_328 [s8_28, s8_98] (by decide) s7_328_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_28_safe
  · subst z; exact s8_98_safe
def s7_329 : State := ⟨[3,4,104,146], 111504066275040398283908239119354858097938718, 3, 2, 1, 0⟩
theorem s7_329_edges : next config 7 s7_329 = [s8_31, s8_99] := by decide
theorem s7_329_safe : Safe 6 7 s7_329 := by
  apply safe_succ 5 7 s7_329 [s8_31, s8_99] (by decide) s7_329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_31_safe
  · subst z; exact s8_99_safe
def s7_330 : State := ⟨[3,4,104,162], 5846006551025023527781069414366386621401371054366, 3, 2, 1, 0⟩
theorem s7_330_edges : next config 7 s7_330 = [s8_33] := by decide
theorem s7_330_safe : Safe 6 7 s7_330 := by
  apply safe_succ 5 7 s7_330 [s8_33] (by decide) s7_330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_33_safe
def s7_331 : State := ⟨[3,4,104,162], 7307508186994796978301000393229171211330230751518, 3, 2, 1, 0⟩
theorem s7_331_edges : next config 7 s7_331 = [s8_37] := by decide
theorem s7_331_safe : Safe 6 7 s7_331 := by
  apply safe_succ 5 7 s7_331 [s8_37] (by decide) s7_331_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_37_safe
def s7_332 : State := ⟨[3,4,104,163], 11692013101709764668279562599085017129752174072094, 3, 2, 1, 0⟩
theorem s7_332_edges : next config 7 s7_332 = [s8_43] := by decide
theorem s7_332_safe : Safe 6 7 s7_332 := by
  apply safe_succ 5 7 s7_332 [s8_43] (by decide) s7_332_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_43_safe
def s7_333 : State := ⟨[3,4,104,163], 13153514736318408651115739724094303289953960923422, 3, 2, 1, 0⟩
theorem s7_333_edges : next config 7 s7_333 = [s8_44] := by decide
theorem s7_333_safe : Safe 6 7 s7_333 := by
  apply safe_succ 5 7 s7_333 [s8_44] (by decide) s7_333_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_44_safe
def s7_334 : State := ⟨[3,4,104,176], 95780971326419139128314594914659690004932607210492190, 3, 2, 1, 0⟩
theorem s7_334_edges : next config 7 s7_334 = [s8_46] := by decide
theorem s7_334_safe : Safe 6 7 s7_334 := by
  apply safe_succ 5 7 s7_334 [s8_46] (by decide) s7_334_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_46_safe
def s7_335 : State := ⟨[3,4,104,176], 95782432805755724832702175457956688015303901637054750, 3, 2, 1, 0⟩
theorem s7_335_edges : next config 7 s7_335 = [s8_48] := by decide
theorem s7_335_safe : Safe 6 7 s7_335 := by
  apply safe_succ 5 7 s7_335 [s8_48] (by decide) s7_335_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_48_safe
def s7_336 : State := ⟨[3,4,108,145], 44601830679773047412959511028192929600700702, 1, 1, 1, 0⟩
theorem s7_336_edges : next config 7 s7_336 = [] := by decide
theorem s7_336_safe : Safe 6 7 s7_336 := by
  apply safe_succ 5 7 s7_336 [] (by decide) s7_336_edges
  simp
def s7_337 : State := ⟨[3,4,121,145], 44601833337904520429132830109023894140813598, 1, 1, 1, 0⟩
theorem s7_337_edges : next config 7 s7_337 = [] := by decide
theorem s7_337_safe : Safe 6 7 s7_337 := by
  apply safe_succ 5 7 s7_337 [] (by decide) s7_337_edges
  simp
def s7_338 : State := ⟨[3,4,241,145], 3533694129556768659166595001530439542899129882077862275623413092450373918, 3, 2, 1, 0⟩
theorem s7_338_edges : next config 7 s7_338 = [s8_54] := by decide
theorem s7_338_safe : Safe 6 7 s7_338 := by
  apply safe_succ 5 7 s7_338 [s8_54] (by decide) s7_338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_54_safe
def s7_339 : State := ⟨[3,4,241,145], 3533694129556768659166595001552739607532926663342471067146846590419931422, 3, 2, 1, 0⟩
theorem s7_339_edges : next config 7 s7_339 = [s8_56] := by decide
theorem s7_339_safe : Safe 6 7 s7_339 := by
  apply safe_succ 5 7 s7_339 [s8_56] (by decide) s7_339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_56_safe
def s7_340 : State := ⟨[3,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835401449758, 1, 1, 1, 0⟩
theorem s7_340_edges : next config 7 s7_340 = [] := by decide
theorem s7_340_safe : Safe 6 7 s7_340 := by
  apply safe_succ 5 7 s7_340 [] (by decide) s7_340_edges
  simp
def s7_341 : State := ⟨[3,12,64,145], 44601830679428167221534918366648232786989342, 3, 3, 1, 0⟩
theorem s7_341_edges : next config 7 s7_341 = [s8_457, s8_295, s8_105, s8_106] := by decide
theorem s7_341_safe : Safe 6 7 s7_341 := by
  apply safe_succ 5 7 s7_341 [s8_457, s8_295, s8_105, s8_106] (by decide) s7_341_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_457_safe
  · subst z; exact s8_295_safe
  · subst z; exact s8_105_safe
  · subst z; exact s8_106_safe
def s7_342 : State := ⟨[3,12,104,145], 44601830679448528859301084301409773580128542, 3, 1, 1, 0⟩
theorem s7_342_edges : next config 7 s7_342 = [s8_458, s8_299, s8_94] := by decide
theorem s7_342_safe : Safe 6 7 s7_342 := by
  apply safe_succ 5 7 s7_342 [s8_458, s8_299, s8_94] (by decide) s7_342_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_458_safe
  · subst z; exact s8_299_safe
  · subst z; exact s8_94_safe
def s7_343 : State := ⟨[3,12,104,145], 133806172603038705179297810890432946676764958, 3, 0, 1, 0⟩
theorem s7_343_edges : next config 7 s7_343 = [s8_65, s8_98] := by decide
theorem s7_343_safe : Safe 6 7 s7_343 := by
  apply safe_succ 5 7 s7_343 [s8_65, s8_98] (by decide) s7_343_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_65_safe
  · subst z; exact s8_98_safe
def s7_344 : State := ⟨[3,12,104,145], 156105556672101644566979675664651581109899550, 3, 0, 1, 0⟩
theorem s7_344_edges : next config 7 s7_344 = [s8_66, s8_99] := by decide
theorem s7_344_safe : Safe 6 7 s7_344 := by
  apply safe_succ 5 7 s7_344 [s8_66, s8_99] (by decide) s7_344_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_66_safe
  · subst z; exact s8_99_safe
def s7_345 : State := ⟨[3,12,113,145], 44601830689812840166767087888046818987282718, 3, 1, 1, 0⟩
theorem s7_345_edges : next config 7 s7_345 = [s8_100] := by decide
theorem s7_345_safe : Safe 6 7 s7_345 := by
  apply safe_succ 5 7 s7_345 [s8_100] (by decide) s7_345_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_100_safe
def s7_346 : State := ⟨[3,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082078, 3, 1, 1, 0⟩
theorem s7_346_edges : next config 7 s7_346 = [s8_103] := by decide
theorem s7_346_safe : Safe 6 7 s7_346 := by
  apply safe_succ 5 7 s7_346 [s8_103] (by decide) s7_346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_103_safe
def s7_347 : State := ⟨[3,21,64,145], 44601830679428167221534918366648232786989342, 3, 3, 1, 0⟩
theorem s7_347_edges : next config 7 s7_347 = [s8_459, s8_301, s8_107, s8_108] := by decide
theorem s7_347_safe : Safe 6 7 s7_347 := by
  apply safe_succ 5 7 s7_347 [s8_459, s8_301, s8_107, s8_108] (by decide) s7_347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_459_safe
  · subst z; exact s8_301_safe
  · subst z; exact s8_107_safe
  · subst z; exact s8_108_safe
def s7_348 : State := ⟨[3,21,100,145], 44601830679429514100297660860387323034140958, 3, 1, 1, 0⟩
theorem s7_348_edges : next config 7 s7_348 = [] := by decide
theorem s7_348_safe : Safe 6 7 s7_348 := by
  apply safe_succ 5 7 s7_348 [] (by decide) s7_348_edges
  simp
def s7_349 : State := ⟨[3,21,104,145], 44601830679448528859301084301409773582221598, 3, 1, 1, 0⟩
theorem s7_349_edges : next config 7 s7_349 = [s8_265, s8_460, s8_305, s8_114, s8_125, s8_115, s8_116, s8_112, s8_113] := by decide
theorem s7_349_safe : Safe 6 7 s7_349 := by
  apply safe_succ 5 7 s7_349 [s8_265, s8_460, s8_305, s8_114, s8_125, s8_115, s8_116, s8_112, s8_113] (by decide) s7_349_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s8_265_safe
  · subst z; exact s8_460_safe
  · subst z; exact s8_305_safe
  · subst z; exact s8_114_safe
  · subst z; exact s8_125_safe
  · subst z; exact s8_115_safe
  · subst z; exact s8_116_safe
  · subst z; exact s8_112_safe
  · subst z; exact s8_113_safe
def s7_350 : State := ⟨[3,21,113,145], 44601830689812840166767087888046818989375774, 3, 1, 1, 0⟩
theorem s7_350_edges : next config 7 s7_350 = [] := by decide
theorem s7_350_safe : Safe 6 7 s7_350 := by
  apply safe_succ 5 7 s7_350 [] (by decide) s7_350_edges
  simp
def s7_351 : State := ⟨[3,21,117,145], 44601830845581745922811916743961708865978654, 3, 1, 1, 0⟩
theorem s7_351_edges : next config 7 s7_351 = [] := by decide
theorem s7_351_safe : Safe 6 7 s7_351 := by
  apply safe_succ 5 7 s7_351 [] (by decide) s7_351_edges
  simp
def s7_352 : State := ⟨[3,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175134, 3, 1, 1, 0⟩
theorem s7_352_edges : next config 7 s7_352 = [] := by decide
theorem s7_352_safe : Safe 6 7 s7_352 := by
  apply safe_succ 5 7 s7_352 [] (by decide) s7_352_edges
  simp
def s7_353 : State := ⟨[3,22,67,145], 44601830679428167221535065940600822467592478, 3, 1, 1, 0⟩
theorem s7_353_edges : next config 7 s7_353 = [s8_117] := by decide
theorem s7_353_safe : Safe 6 7 s7_353 := by
  apply safe_succ 5 7 s7_353 [s8_117] (by decide) s7_353_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_117_safe
def s7_354 : State := ⟨[3,22,96,145], 44601830679428246449697432630985826335129886, 3, 1, 1, 0⟩
theorem s7_354_edges : next config 7 s7_354 = [s8_119, s8_114] := by decide
theorem s7_354_safe : Safe 6 7 s7_354 := by
  apply safe_succ 5 7 s7_354 [s8_119, s8_114] (by decide) s7_354_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_119_safe
  · subst z; exact s8_114_safe
def s7_355 : State := ⟨[3,29,67,145], 44601830679428167221535065940600823000269086, 3, 1, 1, 0⟩
theorem s7_355_edges : next config 7 s7_355 = [s8_307] := by decide
theorem s7_355_safe : Safe 6 7 s7_355 := by
  apply safe_succ 5 7 s7_355 [s8_307] (by decide) s7_355_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_307_safe
def s7_356 : State := ⟨[3,29,96,145], 44601830679428246449697432630985826867806494, 3, 1, 1, 0⟩
theorem s7_356_edges : next config 7 s7_356 = [s8_308, s8_115] := by decide
theorem s7_356_safe : Safe 6 7 s7_356 := by
  apply safe_succ 5 7 s7_356 [s8_308, s8_115] (by decide) s7_356_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_308_safe
  · subst z; exact s8_115_safe
def s7_357 : State := ⟨[3,53,67,145], 44601830679428167221535065949608021718139166, 3, 1, 1, 0⟩
theorem s7_357_edges : next config 7 s7_357 = [s8_351, s8_118] := by decide
theorem s7_357_safe : Safe 6 7 s7_357 := by
  apply safe_succ 5 7 s7_357 [s8_351, s8_118] (by decide) s7_357_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_351_safe
  · subst z; exact s8_118_safe
def s7_358 : State := ⟨[3,53,96,145], 44601830679428246449697432639993025585676574, 3, 1, 1, 0⟩
theorem s7_358_edges : next config 7 s7_358 = [s8_352, s8_120, s8_116] := by decide
theorem s7_358_safe : Safe 6 7 s7_358 := by
  apply safe_succ 5 7 s7_358 [s8_352, s8_120, s8_116] (by decide) s7_358_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_352_safe
  · subst z; exact s8_120_safe
  · subst z; exact s8_116_safe
def s7_359 : State := ⟨[3,54,64,145], 44601830679428167221534918384662631300661534, 3, 1, 1, 0⟩
theorem s7_359_edges : next config 7 s7_359 = [s8_121, s8_117, s8_119] := by decide
theorem s7_359_safe : Safe 6 7 s7_359 := by
  apply safe_succ 5 7 s7_359 [s8_121, s8_117, s8_119] (by decide) s7_359_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_121_safe
  · subst z; exact s8_117_safe
  · subst z; exact s8_119_safe
def s7_360 : State := ⟨[3,54,64,145], 44601830679428167221534918393669830551208222, 3, 1, 1, 0⟩
theorem s7_360_edges : next config 7 s7_360 = [s8_122, s8_118, s8_120] := by decide
theorem s7_360_safe : Safe 6 7 s7_360 := by
  apply safe_succ 5 7 s7_360 [s8_122, s8_118, s8_120] (by decide) s7_360_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_122_safe
  · subst z; exact s8_118_safe
  · subst z; exact s8_120_safe
def s7_361 : State := ⟨[3,86,67,145], 44601830679428167298906318395937089644593438, 3, 1, 1, 0⟩
theorem s7_361_edges : next config 7 s7_361 = [s8_461, s8_317] := by decide
theorem s7_361_safe : Safe 6 7 s7_361 := by
  apply safe_succ 5 7 s7_361 [s8_461, s8_317] (by decide) s7_361_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_461_safe
  · subst z; exact s8_317_safe
def s7_362 : State := ⟨[3,100,104,145], 44601830679449796509901312530811270283329822, 3, 1, 1, 0⟩
theorem s7_362_edges : next config 7 s7_362 = [] := by decide
theorem s7_362_safe : Safe 6 7 s7_362 := by
  apply safe_succ 5 7 s7_362 [] (by decide) s7_362_edges
  simp
def s7_363 : State := ⟨[3,108,104,145], 44601830679773047412959511028192929600700702, 3, 1, 1, 0⟩
theorem s7_363_edges : next config 7 s7_363 = [s8_97] := by decide
theorem s7_363_safe : Safe 6 7 s7_363 := by
  apply safe_succ 5 7 s7_363 [s8_97] (by decide) s7_363_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_97_safe
def s7_364 : State := ⟨[3,117,96,145], 44601830845581745922811916743961708865978654, 3, 1, 1, 0⟩
theorem s7_364_edges : next config 7 s7_364 = [s8_124] := by decide
theorem s7_364_safe : Safe 6 7 s7_364 := by
  apply safe_succ 5 7 s7_364 [s8_124] (by decide) s7_364_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_124_safe
def s7_365 : State := ⟨[9,4,96,145], 44601830679428246449697432630985826330936086, 3, 3, 1, 0⟩
theorem s7_365_edges : next config 7 s7_365 = [s8_126] := by decide
theorem s7_365_safe : Safe 6 7 s7_365 := by
  apply safe_succ 5 7 s7_365 [s8_126] (by decide) s7_365_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_126_safe
def s7_366 : State := ⟨[9,21,104,145], 44601830679448528859301084301409773582222102, 3, 1, 1, 0⟩
theorem s7_366_edges : next config 7 s7_366 = [] := by decide
theorem s7_366_safe : Safe 6 7 s7_366 := by
  apply safe_succ 5 7 s7_366 [] (by decide) s7_366_edges
  simp
def s7_367 : State := ⟨[17,4,67,128], 340282366921020670658916075178169663766, 3, 2, 0, 0⟩
theorem s7_367_edges : next config 7 s7_367 = [s8_127] := by decide
theorem s7_367_safe : Safe 6 7 s7_367 := by
  apply safe_succ 5 7 s7_367 [s8_127] (by decide) s7_367_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_127_safe
def s7_368 : State := ⟨[17,4,67,128], 340282366921021879510948713512506163478, 3, 2, 0, 0⟩
theorem s7_368_edges : next config 7 s7_368 = [s8_128] := by decide
theorem s7_368_safe : Safe 6 7 s7_368 := by
  apply safe_succ 5 7 s7_368 [s8_128] (by decide) s7_368_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_128_safe
def s7_369 : State := ⟨[17,4,67,145], 44601830679428167221535065940600822461305118, 3, 3, 1, 0⟩
theorem s7_369_edges : next config 7 s7_369 = [s8_230, s8_378, s8_333, s8_176] := by decide
theorem s7_369_safe : Safe 6 7 s7_369 := by
  apply safe_succ 5 7 s7_369 [s8_230, s8_378, s8_333, s8_176] (by decide) s7_369_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_230_safe
  · subst z; exact s8_378_safe
  · subst z; exact s8_333_safe
  · subst z; exact s8_176_safe
def s7_370 : State := ⟨[17,4,67,145], 44601830679428167221535065940600822463398174, 3, 3, 1, 0⟩
theorem s7_370_edges : next config 7 s7_370 = [s8_379, s8_266, s8_334, s8_162] := by decide
theorem s7_370_safe : Safe 6 7 s7_370 := by
  apply safe_succ 5 7 s7_370 [s8_379, s8_266, s8_334, s8_162] (by decide) s7_370_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_379_safe
  · subst z; exact s8_266_safe
  · subst z; exact s8_334_safe
  · subst z; exact s8_162_safe
def s7_371 : State := ⟨[17,4,67,145], 44601830679428167226370843006035633998336278, 3, 2, 1, 0⟩
theorem s7_371_edges : next config 7 s7_371 = [s8_231, s8_0, s8_177] := by decide
theorem s7_371_safe : Safe 6 7 s7_371 := by
  apply safe_succ 5 7 s7_371 [s8_231, s8_0, s8_177] (by decide) s7_371_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_231_safe
  · subst z; exact s8_0_safe
  · subst z; exact s8_177_safe
def s7_372 : State := ⟨[17,4,67,145], 44601830679428167226370843006035634000429334, 3, 2, 1, 0⟩
theorem s7_372_edges : next config 7 s7_372 = [s8_1, s8_163] := by decide
theorem s7_372_safe : Safe 6 7 s7_372 := by
  apply safe_succ 5 7 s7_372 [s8_1, s8_163] (by decide) s7_372_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_1_safe
  · subst z; exact s8_163_safe
def s7_373 : State := ⟨[17,4,67,145], 44601830679428167227579695038673968334835990, 3, 2, 1, 0⟩
theorem s7_373_edges : next config 7 s7_373 = [s8_232, s8_2, s8_178] := by decide
theorem s7_373_safe : Safe 6 7 s7_373 := by
  apply safe_succ 5 7 s7_373 [s8_232, s8_2, s8_178] (by decide) s7_373_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_232_safe
  · subst z; exact s8_2_safe
  · subst z; exact s8_178_safe
def s7_374 : State := ⟨[17,4,67,145], 44601830679428167227579695038673968336929046, 3, 2, 1, 0⟩
theorem s7_374_edges : next config 7 s7_374 = [s8_3, s8_164] := by decide
theorem s7_374_safe : Safe 6 7 s7_374 := by
  apply safe_succ 5 7 s7_374 [s8_3, s8_164] (by decide) s7_374_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_3_safe
  · subst z; exact s8_164_safe
def s7_375 : State := ⟨[17,4,67,145], 44601830679428167303742095461371901179527446, 3, 2, 1, 0⟩
theorem s7_375_edges : next config 7 s7_375 = [s8_234, s8_4, s8_179] := by decide
theorem s7_375_safe : Safe 6 7 s7_375 := by
  apply safe_succ 5 7 s7_375 [s8_234, s8_4, s8_179] (by decide) s7_375_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_234_safe
  · subst z; exact s8_4_safe
  · subst z; exact s8_179_safe
def s7_376 : State := ⟨[17,4,67,145], 44601830679428167304950947494010235516027158, 3, 2, 1, 0⟩
theorem s7_376_edges : next config 7 s7_376 = [s8_235, s8_5, s8_180] := by decide
theorem s7_376_safe : Safe 6 7 s7_376 := by
  apply safe_succ 5 7 s7_376 [s8_235, s8_5, s8_180] (by decide) s7_376_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_235_safe
  · subst z; exact s8_5_safe
  · subst z; exact s8_180_safe
def s7_377 : State := ⟨[17,4,86,145], 44601830679428167303741947887419311505211670, 3, 2, 1, 0⟩
theorem s7_377_edges : next config 7 s7_377 = [s8_8] := by decide
theorem s7_377_safe : Safe 6 7 s7_377 := by
  apply safe_succ 5 7 s7_377 [s8_8] (by decide) s7_377_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_8_safe
def s7_378 : State := ⟨[17,4,86,145], 44601830679428167304950799920057645841711382, 3, 2, 1, 0⟩
theorem s7_378_edges : next config 7 s7_378 = [s8_9] := by decide
theorem s7_378_safe : Safe 6 7 s7_378 := by
  apply safe_succ 5 7 s7_378 [s8_9] (by decide) s7_378_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_9_safe
def s7_379 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826328842526, 3, 3, 1, 0⟩
theorem s7_379_edges : next config 7 s7_379 = [s8_236, s8_432, s8_335, s8_181, s8_146, s8_158, s8_131] := by decide
theorem s7_379_safe : Safe 6 7 s7_379 := by
  apply safe_succ 5 7 s7_379 [s8_236, s8_432, s8_335, s8_181, s8_146, s8_158, s8_131] (by decide) s7_379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s8_236_safe
  · subst z; exact s8_432_safe
  · subst z; exact s8_335_safe
  · subst z; exact s8_181_safe
  · subst z; exact s8_146_safe
  · subst z; exact s8_158_safe
  · subst z; exact s8_131_safe
def s7_380 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826330935582, 3, 3, 1, 0⟩
theorem s7_380_edges : next config 7 s7_380 = [s8_433, s8_267, s8_336, s8_217, s8_165, s8_147, s8_129, s8_159, s8_132] := by decide
theorem s7_380_safe : Safe 6 7 s7_380 := by
  apply safe_succ 5 7 s7_380 [s8_433, s8_267, s8_336, s8_217, s8_165, s8_147, s8_129, s8_159, s8_132] (by decide) s7_380_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s8_433_safe
  · subst z; exact s8_267_safe
  · subst z; exact s8_336_safe
  · subst z; exact s8_217_safe
  · subst z; exact s8_165_safe
  · subst z; exact s8_147_safe
  · subst z; exact s8_129_safe
  · subst z; exact s8_159_safe
  · subst z; exact s8_132_safe
def s7_381 : State := ⟨[17,4,96,145], 44601830679428246449697432630985826330936086, 3, 3, 1, 0⟩
theorem s7_381_edges : next config 7 s7_381 = [s8_133] := by decide
theorem s7_381_safe : Safe 6 7 s7_381 := by
  apply safe_succ 5 7 s7_381 [s8_133] (by decide) s7_381_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_133_safe
def s7_382 : State := ⟨[17,4,96,145], 44601830679428246449697432630985834918777110, 3, 3, 1, 0⟩
theorem s7_382_edges : next config 7 s7_382 = [s8_237, s8_182, s8_134] := by decide
theorem s7_382_safe : Safe 6 7 s7_382 := by
  apply safe_succ 5 7 s7_382 [s8_237, s8_182, s8_134] (by decide) s7_382_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_237_safe
  · subst z; exact s8_182_safe
  · subst z; exact s8_134_safe
def s7_383 : State := ⟨[17,4,96,145], 44601830679428246449697432630985834920870166, 3, 3, 1, 0⟩
theorem s7_383_edges : next config 7 s7_383 = [s8_166, s8_135] := by decide
theorem s7_383_safe : Safe 6 7 s7_383 := by
  apply safe_succ 5 7 s7_383 [s8_166, s8_135] (by decide) s7_383_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_166_safe
  · subst z; exact s8_135_safe
def s7_384 : State := ⟨[17,4,96,145], 44601830679428246449697469524473973747945750, 3, 3, 1, 0⟩
theorem s7_384_edges : next config 7 s7_384 = [s8_238, s8_434, s8_183, s8_148, s8_160, s8_136] := by decide
theorem s7_384_safe : Safe 6 7 s7_384 := by
  apply safe_succ 5 7 s7_384 [s8_238, s8_434, s8_183, s8_148, s8_160, s8_136] (by decide) s7_384_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s8_238_safe
  · subst z; exact s8_434_safe
  · subst z; exact s8_183_safe
  · subst z; exact s8_148_safe
  · subst z; exact s8_160_safe
  · subst z; exact s8_136_safe
def s7_385 : State := ⟨[17,4,96,145], 44601830679428246449697469524473973750038806, 3, 3, 1, 0⟩
theorem s7_385_edges : next config 7 s7_385 = [s8_435, s8_268, s8_218, s8_167, s8_149, s8_130, s8_161, s8_137] := by decide
theorem s7_385_safe : Safe 6 7 s7_385 := by
  apply safe_succ 5 7 s7_385 [s8_435, s8_268, s8_218, s8_167, s8_149, s8_130, s8_161, s8_137] (by decide) s7_385_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s8_435_safe
  · subst z; exact s8_268_safe
  · subst z; exact s8_218_safe
  · subst z; exact s8_167_safe
  · subst z; exact s8_149_safe
  · subst z; exact s8_130_safe
  · subst z; exact s8_161_safe
  · subst z; exact s8_137_safe
def s7_386 : State := ⟨[17,4,96,145], 44601830679428404906022461159661013416743190, 3, 3, 1, 0⟩
theorem s7_386_edges : next config 7 s7_386 = [s8_239, s8_184, s8_138] := by decide
theorem s7_386_safe : Safe 6 7 s7_386 := by
  apply safe_succ 5 7 s7_386 [s8_239, s8_184, s8_138] (by decide) s7_386_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_239_safe
  · subst z; exact s8_184_safe
  · subst z; exact s8_138_safe
def s7_387 : State := ⟨[17,4,96,145], 44601830679428404906022461159661013418836246, 3, 3, 1, 0⟩
theorem s7_387_edges : next config 7 s7_387 = [s8_168, s8_139] := by decide
theorem s7_387_safe : Safe 6 7 s7_387 := by
  apply safe_succ 5 7 s7_387 [s8_168, s8_139] (by decide) s7_387_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_168_safe
  · subst z; exact s8_139_safe
def s7_388 : State := ⟨[17,4,96,145], 44601830679429514100297660860387323032043806, 3, 3, 1, 0⟩
theorem s7_388_edges : next config 7 s7_388 = [s8_240, s8_185, s8_140] := by decide
theorem s7_388_safe : Safe 6 7 s7_388 := by
  apply safe_succ 5 7 s7_388 [s8_240, s8_185, s8_140] (by decide) s7_388_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_240_safe
  · subst z; exact s8_185_safe
  · subst z; exact s8_140_safe
def s7_389 : State := ⟨[17,4,96,145], 44601830679429514100297697753875470451147030, 3, 3, 1, 0⟩
theorem s7_389_edges : next config 7 s7_389 = [s8_241, s8_186, s8_141] := by decide
theorem s7_389_safe : Safe 6 7 s7_389 := by
  apply safe_succ 5 7 s7_389 [s8_241, s8_186, s8_141] (by decide) s7_389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_241_safe
  · subst z; exact s8_186_safe
  · subst z; exact s8_141_safe
def s7_390 : State := ⟨[17,4,100,128], 340282368267817226224315090600022180126, 3, 3, 0, 0⟩
theorem s7_390_edges : next config 7 s7_390 = [s8_129] := by decide
theorem s7_390_safe : Safe 6 7 s7_390 := by
  apply safe_succ 5 7 s7_390 [s8_129] (by decide) s7_390_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_129_safe
def s7_391 : State := ⟨[17,4,100,128], 340282368267817226261208578747441283350, 3, 3, 0, 0⟩
theorem s7_391_edges : next config 7 s7_391 = [s8_130] := by decide
theorem s7_391_safe : Safe 6 7 s7_391 := by
  apply safe_succ 5 7 s7_391 [s8_130] (by decide) s7_391_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_130_safe
def s7_392 : State := ⟨[17,4,104,128], 340282387282576229647756113050568167710, 3, 3, 0, 0⟩
theorem s7_392_edges : next config 7 s7_392 = [s8_187, s8_131] := by decide
theorem s7_392_safe : Safe 6 7 s7_392 := by
  apply safe_succ 5 7 s7_392 [s8_187, s8_131] (by decide) s7_392_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_187_safe
  · subst z; exact s8_131_safe
def s7_393 : State := ⟨[17,4,104,128], 340282387282576229647756113050570260766, 3, 3, 0, 0⟩
theorem s7_393_edges : next config 7 s7_393 = [s8_221, s8_169, s8_152, s8_144, s8_132] := by decide
theorem s7_393_safe : Safe 6 7 s7_393 := by
  apply safe_succ 5 7 s7_393 [s8_221, s8_169, s8_152, s8_144, s8_132] (by decide) s7_393_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s8_221_safe
  · subst z; exact s8_169_safe
  · subst z; exact s8_152_safe
  · subst z; exact s8_144_safe
  · subst z; exact s8_132_safe
def s7_394 : State := ⟨[17,4,104,128], 340282387282576229647756113050570261270, 3, 3, 0, 0⟩
theorem s7_394_edges : next config 7 s7_394 = [s8_133] := by decide
theorem s7_394_safe : Safe 6 7 s7_394 := by
  apply safe_succ 5 7 s7_394 [s8_133] (by decide) s7_394_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_133_safe
def s7_395 : State := ⟨[17,4,104,128], 340282387282576229647756113059158102294, 3, 3, 0, 0⟩
theorem s7_395_edges : next config 7 s7_395 = [s8_188, s8_134] := by decide
theorem s7_395_safe : Safe 6 7 s7_395 := by
  apply safe_succ 5 7 s7_395 [s8_188, s8_134] (by decide) s7_395_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_188_safe
  · subst z; exact s8_134_safe
def s7_396 : State := ⟨[17,4,104,128], 340282387282576229647756113059160195350, 3, 3, 0, 0⟩
theorem s7_396_edges : next config 7 s7_396 = [s8_170, s8_135] := by decide
theorem s7_396_safe : Safe 6 7 s7_396 := by
  apply safe_succ 5 7 s7_396 [s8_170, s8_135] (by decide) s7_396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_170_safe
  · subst z; exact s8_135_safe
def s7_397 : State := ⟨[17,4,104,128], 340282387282576229684649601197987270934, 3, 3, 0, 0⟩
theorem s7_397_edges : next config 7 s7_397 = [s8_189, s8_136] := by decide
theorem s7_397_safe : Safe 6 7 s7_397 := by
  apply safe_succ 5 7 s7_397 [s8_189, s8_136] (by decide) s7_397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_189_safe
  · subst z; exact s8_136_safe
def s7_398 : State := ⟨[17,4,104,128], 340282387282576229684649601197989363990, 3, 3, 0, 0⟩
theorem s7_398_edges : next config 7 s7_398 = [s8_222, s8_171, s8_153, s8_145, s8_137] := by decide
theorem s7_398_safe : Safe 6 7 s7_398 := by
  apply safe_succ 5 7 s7_398 [s8_222, s8_171, s8_153, s8_145, s8_137] (by decide) s7_398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s8_222_safe
  · subst z; exact s8_171_safe
  · subst z; exact s8_153_safe
  · subst z; exact s8_145_safe
  · subst z; exact s8_137_safe
def s7_399 : State := ⟨[17,4,104,128], 340282387441032554676284788237656068374, 3, 3, 0, 0⟩
theorem s7_399_edges : next config 7 s7_399 = [s8_190, s8_138] := by decide
theorem s7_399_safe : Safe 6 7 s7_399 := by
  apply safe_succ 5 7 s7_399 [s8_190, s8_138] (by decide) s7_399_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_190_safe
  · subst z; exact s8_138_safe
def s7_400 : State := ⟨[17,4,104,128], 340282387441032554676284788237658161430, 3, 3, 0, 0⟩
theorem s7_400_edges : next config 7 s7_400 = [s8_172, s8_139] := by decide
theorem s7_400_safe : Safe 6 7 s7_400 := by
  apply safe_succ 5 7 s7_400 [s8_172, s8_139] (by decide) s7_400_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_172_safe
  · subst z; exact s8_139_safe
def s7_401 : State := ⟨[17,4,104,128], 340282388550226829875985514547271368990, 3, 3, 0, 0⟩
theorem s7_401_edges : next config 7 s7_401 = [s8_191, s8_140] := by decide
theorem s7_401_safe : Safe 6 7 s7_401 := by
  apply safe_succ 5 7 s7_401 [s8_191, s8_140] (by decide) s7_401_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_191_safe
  · subst z; exact s8_140_safe
def s7_402 : State := ⟨[17,4,104,128], 340282388550226829912879002694690472214, 3, 3, 0, 0⟩
theorem s7_402_edges : next config 7 s7_402 = [s8_192, s8_141] := by decide
theorem s7_402_safe : Safe 6 7 s7_402 := by
  apply safe_succ 5 7 s7_402 [s8_192, s8_141] (by decide) s7_402_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_192_safe
  · subst z; exact s8_141_safe
def s7_403 : State := ⟨[17,4,104,128], 340282711801129888074482896206588739870, 3, 3, 0, 0⟩
theorem s7_403_edges : next config 7 s7_403 = [s8_193, s8_142] := by decide
theorem s7_403_safe : Safe 6 7 s7_403 := by
  apply safe_succ 5 7 s7_403 [s8_193, s8_142] (by decide) s7_403_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_193_safe
  · subst z; exact s8_142_safe
def s7_404 : State := ⟨[17,4,104,128], 340282711801129888111376384354007843094, 3, 3, 0, 0⟩
theorem s7_404_edges : next config 7 s7_404 = [s8_194, s8_143] := by decide
theorem s7_404_safe : Safe 6 7 s7_404 := by
  apply safe_succ 5 7 s7_404 [s8_194, s8_143] (by decide) s7_404_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_194_safe
  · subst z; exact s8_143_safe
def s7_405 : State := ⟨[17,4,108,145], 44601830679773047412959511028192929600700702, 1, 1, 1, 0⟩
theorem s7_405_edges : next config 7 s7_405 = [s8_242, s8_195] := by decide
theorem s7_405_safe : Safe 6 7 s7_405 := by
  apply safe_succ 5 7 s7_405 [s8_242, s8_195] (by decide) s7_405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_242_safe
  · subst z; exact s8_195_safe
def s7_406 : State := ⟨[17,4,108,145], 44601830679773047412959511028192929602797846, 3, 2, 1, 0⟩
theorem s7_406_edges : next config 7 s7_406 = [s8_50] := by decide
theorem s7_406_safe : Safe 6 7 s7_406 := by
  apply safe_succ 5 7 s7_406 [s8_50] (by decide) s7_406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_50_safe
def s7_407 : State := ⟨[17,4,108,145], 44601830679773047412959547921681077019803926, 1, 1, 1, 0⟩
theorem s7_407_edges : next config 7 s7_407 = [s8_243, s8_196] := by decide
theorem s7_407_safe : Safe 6 7 s7_407 := by
  apply safe_succ 5 7 s7_407 [s8_243, s8_196] (by decide) s7_407_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_243_safe
  · subst z; exact s8_196_safe
def s7_408 : State := ⟨[17,4,113,128], 340292751593883695651342750095975321886, 3, 3, 0, 0⟩
theorem s7_408_edges : next config 7 s7_408 = [s8_197, s8_146] := by decide
theorem s7_408_safe : Safe 6 7 s7_408 := by
  apply safe_succ 5 7 s7_408 [s8_197, s8_146] (by decide) s7_408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_197_safe
  · subst z; exact s8_146_safe
def s7_409 : State := ⟨[17,4,113,128], 340292751593883695651342750095977414942, 3, 3, 0, 0⟩
theorem s7_409_edges : next config 7 s7_409 = [s8_173, s8_147] := by decide
theorem s7_409_safe : Safe 6 7 s7_409 := by
  apply safe_succ 5 7 s7_409 [s8_173, s8_147] (by decide) s7_409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_173_safe
  · subst z; exact s8_147_safe
def s7_410 : State := ⟨[17,4,113,128], 340292751593883695688236238243394425110, 3, 3, 0, 0⟩
theorem s7_410_edges : next config 7 s7_410 = [s8_198, s8_148] := by decide
theorem s7_410_safe : Safe 6 7 s7_410 := by
  apply safe_succ 5 7 s7_410 [s8_198, s8_148] (by decide) s7_410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_198_safe
  · subst z; exact s8_148_safe
def s7_411 : State := ⟨[17,4,113,128], 340292751593883695688236238243396518166, 3, 3, 0, 0⟩
theorem s7_411_edges : next config 7 s7_411 = [s8_174, s8_149] := by decide
theorem s7_411_safe : Safe 6 7 s7_411 := by
  apply safe_succ 5 7 s7_411 [s8_174, s8_149] (by decide) s7_411_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_174_safe
  · subst z; exact s8_149_safe
def s7_412 : State := ⟨[17,4,117,128], 340448520499639740480198664985854017822, 3, 3, 0, 0⟩
theorem s7_412_edges : next config 7 s7_412 = [s8_150] := by decide
theorem s7_412_safe : Safe 6 7 s7_412 := by
  apply safe_succ 5 7 s7_412 [s8_150] (by decide) s7_412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_150_safe
def s7_413 : State := ⟨[17,4,117,128], 340448520499639740517092153133273121046, 3, 3, 0, 0⟩
theorem s7_413_edges : next config 7 s7_413 = [s8_151] := by decide
theorem s7_413_safe : Safe 6 7 s7_413 := by
  apply safe_succ 5 7 s7_413 [s8_151] (by decide) s7_413_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_151_safe
def s7_414 : State := ⟨[17,4,120,145], 44601832008676524644216957205216833862566166, 3, 2, 1, 0⟩
theorem s7_414_edges : next config 7 s7_414 = [s8_51] := by decide
theorem s7_414_safe : Safe 6 7 s7_414 := by
  apply safe_succ 5 7 s7_414 [s8_51] (by decide) s7_414_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_51_safe
def s7_415 : State := ⟨[17,4,121,145], 44601833337904520429132830109023894140813598, 1, 1, 1, 0⟩
theorem s7_415_edges : next config 7 s7_415 = [s8_244, s8_199] := by decide
theorem s7_415_safe : Safe 6 7 s7_415 := by
  apply safe_succ 5 7 s7_415 [s8_244, s8_199] (by decide) s7_415_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_244_safe
  · subst z; exact s8_199_safe
def s7_416 : State := ⟨[17,4,121,145], 44601833337904520429132830109023894142910742, 3, 2, 1, 0⟩
theorem s7_416_edges : next config 7 s7_416 = [s8_52] := by decide
theorem s7_416_safe : Safe 6 7 s7_416 := by
  apply safe_succ 5 7 s7_416 [s8_52] (by decide) s7_416_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_52_safe
def s7_417 : State := ⟨[17,4,121,145], 44601833337904520429132867002512041559916822, 1, 1, 1, 0⟩
theorem s7_417_edges : next config 7 s7_417 = [s8_245, s8_200] := by decide
theorem s7_417_safe : Safe 6 7 s7_417 := by
  apply safe_succ 5 7 s7_417 [s8_245, s8_200] (by decide) s7_417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_245_safe
  · subst z; exact s8_200_safe
def s7_418 : State := ⟨[17,4,125,145], 44601873214744393976609017223235702553248022, 3, 2, 1, 0⟩
theorem s7_418_edges : next config 7 s7_418 = [s8_53, s8_337, s8_175] := by decide
theorem s7_418_safe : Safe 6 7 s7_418 := by
  apply safe_succ 5 7 s7_418 [s8_53, s8_337, s8_175] (by decide) s7_418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_53_safe
  · subst z; exact s8_337_safe
  · subst z; exact s8_175_safe
def s7_419 : State := ⟨[17,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835401449758, 1, 1, 1, 0⟩
theorem s7_419_edges : next config 7 s7_419 = [s8_251, s8_206] := by decide
theorem s7_419_safe : Safe 6 7 s7_419 := by
  apply safe_succ 5 7 s7_419 [s8_251, s8_206] (by decide) s7_419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_251_safe
  · subst z; exact s8_206_safe
def s7_420 : State := ⟨[17,4,249,145], 904625697166532776746648320380418881934351203729176207642563784835403546902, 3, 2, 1, 0⟩
theorem s7_420_edges : next config 7 s7_420 = [s8_58] := by decide
theorem s7_420_safe : Safe 6 7 s7_420 := by
  apply safe_succ 5 7 s7_420 [s8_58] (by decide) s7_420_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_58_safe
def s7_421 : State := ⟨[17,4,249,145], 904625697166532776746648320380418881934351203729176207679457272982820552982, 1, 1, 1, 0⟩
theorem s7_421_edges : next config 7 s7_421 = [s8_252, s8_207] := by decide
theorem s7_421_safe : Safe 6 7 s7_421 := by
  apply safe_succ 5 7 s7_421 [s8_252, s8_207] (by decide) s7_421_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_252_safe
  · subst z; exact s8_207_safe
def s7_422 : State := ⟨[17,12,64,145], 44601830679428167221534918366648232786989342, 3, 3, 1, 0⟩
theorem s7_422_edges : next config 7 s7_422 = [s8_338, s8_165] := by decide
theorem s7_422_safe : Safe 6 7 s7_422 := by
  apply safe_succ 5 7 s7_422 [s8_338, s8_165] (by decide) s7_422_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_338_safe
  · subst z; exact s8_165_safe
def s7_423 : State := ⟨[17,12,64,145], 44601830679428167221534918366648241376923926, 3, 3, 1, 0⟩
theorem s7_423_edges : next config 7 s7_423 = [s8_166] := by decide
theorem s7_423_safe : Safe 6 7 s7_423 := by
  apply safe_succ 5 7 s7_423 [s8_166] (by decide) s7_423_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_166_safe
def s7_424 : State := ⟨[17,12,64,145], 44601830679428167221534955260136380206092566, 3, 3, 1, 0⟩
theorem s7_424_edges : next config 7 s7_424 = [s8_167] := by decide
theorem s7_424_safe : Safe 6 7 s7_424 := by
  apply safe_succ 5 7 s7_424 [s8_167] (by decide) s7_424_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_167_safe
def s7_425 : State := ⟨[17,12,67,128], 340282366920938463629395304099451441438, 3, 3, 0, 0⟩
theorem s7_425_edges : next config 7 s7_425 = [s8_162] := by decide
theorem s7_425_safe : Safe 6 7 s7_425 := by
  apply safe_succ 5 7 s7_425 [s8_162] (by decide) s7_425_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_162_safe
def s7_426 : State := ⟨[17,12,67,128], 340282366920943299406460738910988472598, 3, 2, 0, 0⟩
theorem s7_426_edges : next config 7 s7_426 = [s8_163] := by decide
theorem s7_426_safe : Safe 6 7 s7_426 := by
  apply safe_succ 5 7 s7_426 [s8_163] (by decide) s7_426_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_163_safe
def s7_427 : State := ⟨[17,12,67,128], 340282366920944508258493377245324972310, 3, 2, 0, 0⟩
theorem s7_427_edges : next config 7 s7_427 = [s8_164] := by decide
theorem s7_427_safe : Safe 6 7 s7_427 := by
  apply safe_succ 5 7 s7_427 [s8_164] (by decide) s7_427_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_164_safe
def s7_428 : State := ⟨[17,12,67,145], 44601830679428167221535102834088969882505494, 3, 2, 1, 0⟩
theorem s7_428_edges : next config 7 s7_428 = [s8_384, s8_59] := by decide
theorem s7_428_safe : Safe 6 7 s7_428 := by
  apply safe_succ 5 7 s7_428 [s8_384, s8_59] (by decide) s7_428_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_384_safe
  · subst z; exact s8_59_safe
def s7_429 : State := ⟨[17,12,67,145], 44601830679428167221535139727577117301608726, 3, 2, 1, 0⟩
theorem s7_429_edges : next config 7 s7_429 = [s8_385, s8_60] := by decide
theorem s7_429_safe : Safe 6 7 s7_429 := by
  apply safe_succ 5 7 s7_429 [s8_385, s8_60] (by decide) s7_429_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_385_safe
  · subst z; exact s8_60_safe
def s7_430 : State := ⟨[17,12,82,145], 44601830679428167226370695432083044324020502, 3, 2, 1, 0⟩
theorem s7_430_edges : next config 7 s7_430 = [s8_61, s8_163] := by decide
theorem s7_430_safe : Safe 6 7 s7_430 := by
  apply safe_succ 5 7 s7_430 [s8_61, s8_163] (by decide) s7_430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_61_safe
  · subst z; exact s8_163_safe
def s7_431 : State := ⟨[17,12,82,145], 44601830679428167227579547464721378660520214, 3, 2, 1, 0⟩
theorem s7_431_edges : next config 7 s7_431 = [s8_62, s8_164] := by decide
theorem s7_431_safe : Safe 6 7 s7_431 := by
  apply safe_succ 5 7 s7_431 [s8_62, s8_164] (by decide) s7_431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_62_safe
  · subst z; exact s8_164_safe
def s7_432 : State := ⟨[17,12,96,128], 340282367000166625996085689103318978846, 3, 3, 0, 0⟩
theorem s7_432_edges : next config 7 s7_432 = [s8_173, s8_169, s8_165] := by decide
theorem s7_432_safe : Safe 6 7 s7_432 := by
  apply safe_succ 5 7 s7_432 [s8_173, s8_169, s8_165] (by decide) s7_432_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_173_safe
  · subst z; exact s8_169_safe
  · subst z; exact s8_165_safe
def s7_433 : State := ⟨[17,12,96,128], 340282367000166625996085689111908913430, 3, 3, 0, 0⟩
theorem s7_433_edges : next config 7 s7_433 = [s8_170, s8_166] := by decide
theorem s7_433_safe : Safe 6 7 s7_433 := by
  apply safe_succ 5 7 s7_433 [s8_170, s8_166] (by decide) s7_433_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_170_safe
  · subst z; exact s8_166_safe
def s7_434 : State := ⟨[17,12,96,128], 340282367000166626032979177250738082070, 3, 3, 0, 0⟩
theorem s7_434_edges : next config 7 s7_434 = [s8_174, s8_171, s8_167] := by decide
theorem s7_434_safe : Safe 6 7 s7_434 := by
  apply safe_succ 5 7 s7_434 [s8_174, s8_171, s8_167] (by decide) s7_434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_174_safe
  · subst z; exact s8_171_safe
  · subst z; exact s8_167_safe
def s7_435 : State := ⟨[17,12,96,128], 340282367158622951024614364290406879510, 3, 3, 0, 0⟩
theorem s7_435_edges : next config 7 s7_435 = [s8_172, s8_168] := by decide
theorem s7_435_safe : Safe 6 7 s7_435 := by
  apply safe_succ 5 7 s7_435 [s8_172, s8_168] (by decide) s7_435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_172_safe
  · subst z; exact s8_168_safe
def s7_436 : State := ⟨[17,12,97,145], 44601830679428404906022461159661013418840342, 3, 2, 1, 0⟩
theorem s7_436_edges : next config 7 s7_436 = [s8_63] := by decide
theorem s7_436_safe : Safe 6 7 s7_436 := by
  apply safe_succ 5 7 s7_436 [s8_63] (by decide) s7_436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_63_safe
def s7_437 : State := ⟨[17,12,104,145], 44601830679448528859301084301409773580128542, 3, 1, 1, 0⟩
theorem s7_437_edges : next config 7 s7_437 = [s8_339, s8_131] := by decide
theorem s7_437_safe : Safe 6 7 s7_437 := by
  apply safe_succ 5 7 s7_437 [s8_339, s8_131] (by decide) s7_437_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_339_safe
  · subst z; exact s8_131_safe
def s7_438 : State := ⟨[17,12,104,145], 44601830679448528859301084301409773582225686, 3, 2, 1, 0⟩
theorem s7_438_edges : next config 7 s7_438 = [s8_64, s8_340] := by decide
theorem s7_438_safe : Safe 6 7 s7_438 := by
  apply safe_succ 5 7 s7_438 [s8_64, s8_340] (by decide) s7_438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_64_safe
  · subst z; exact s8_340_safe
def s7_439 : State := ⟨[17,12,104,145], 44601830679448528859301084301409782170063126, 3, 1, 1, 0⟩
theorem s7_439_edges : next config 7 s7_439 = [s8_134] := by decide
theorem s7_439_safe : Safe 6 7 s7_439 := by
  apply safe_succ 5 7 s7_439 [s8_134] (by decide) s7_439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_134_safe
def s7_440 : State := ⟨[17,12,104,145], 44601830679448528859301121194897920999231766, 3, 1, 1, 0⟩
theorem s7_440_edges : next config 7 s7_440 = [s8_136] := by decide
theorem s7_440_safe : Safe 6 7 s7_440 := by
  apply safe_succ 5 7 s7_440 [s8_136] (by decide) s7_440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_136_safe
def s7_441 : State := ⟨[17,12,104,145], 44601830679448687315626112830084960668029206, 3, 1, 1, 0⟩
theorem s7_441_edges : next config 7 s7_441 = [s8_138] := by decide
theorem s7_441_safe : Safe 6 7 s7_441 := by
  apply safe_succ 5 7 s7_441 [s8_138] (by decide) s7_441_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_138_safe
def s7_442 : State := ⟨[17,12,112,145], 44601830684620543308232260259516322660159766, 3, 2, 1, 0⟩
theorem s7_442_edges : next config 7 s7_442 = [s8_67] := by decide
theorem s7_442_safe : Safe 6 7 s7_442 := by
  apply safe_succ 5 7 s7_442 [s8_67] (by decide) s7_442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_67_safe
def s7_443 : State := ⟨[17,12,113,145], 44601830689812840166767087888046818987282718, 3, 1, 1, 0⟩
theorem s7_443_edges : next config 7 s7_443 = [s8_146] := by decide
theorem s7_443_safe : Safe 6 7 s7_443 := by
  apply safe_succ 5 7 s7_443 [s8_146] (by decide) s7_443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_146_safe
def s7_444 : State := ⟨[17,12,113,145], 44601830689812840166767087888046818989379862, 3, 2, 1, 0⟩
theorem s7_444_edges : next config 7 s7_444 = [s8_68] := by decide
theorem s7_444_safe : Safe 6 7 s7_444 := by
  apply safe_succ 5 7 s7_444 [s8_68] (by decide) s7_444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_68_safe
def s7_445 : State := ⟨[17,12,113,145], 44601830689812840166767124781534966406385942, 3, 1, 1, 0⟩
theorem s7_445_edges : next config 7 s7_445 = [s8_148] := by decide
theorem s7_445_safe : Safe 6 7 s7_445 := by
  apply safe_succ 5 7 s7_445 [s8_148] (by decide) s7_445_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_148_safe
def s7_446 : State := ⟨[17,12,125,128], 382817683147693537580677938979541291286, 3, 2, 0, 0⟩
theorem s7_446_edges : next config 7 s7_446 = [s8_175] := by decide
theorem s7_446_safe : Safe 6 7 s7_446 := by
  apply safe_succ 5 7 s7_446 [s8_175] (by decide) s7_446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_175_safe
def s7_447 : State := ⟨[17,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228914082078, 3, 1, 1, 0⟩
theorem s7_447_edges : next config 7 s7_447 = [s8_158] := by decide
theorem s7_447_safe : Safe 6 7 s7_447 := by
  apply safe_succ 5 7 s7_447 [s8_158] (by decide) s7_447_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_158_safe
def s7_448 : State := ⟨[17,12,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179222, 3, 2, 1, 0⟩
theorem s7_448_edges : next config 7 s7_448 = [s8_69] := by decide
theorem s7_448_safe : Safe 6 7 s7_448 := by
  apply safe_succ 5 7 s7_448 [s8_69] (by decide) s7_448_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_69_safe
def s7_449 : State := ⟨[17,12,241,145], 3533694129556768659166595001530438862334396040200935385767686376333185302, 3, 1, 1, 0⟩
theorem s7_449_edges : next config 7 s7_449 = [s8_160] := by decide
theorem s7_449_safe : Safe 6 7 s7_449 := by
  apply safe_succ 5 7 s7_449 [s8_160] (by decide) s7_449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_160_safe
def s7_450 : State := ⟨[17,21,64,145], 44601830679428167221534918366648232786989342, 3, 3, 1, 0⟩
theorem s7_450_edges : next config 7 s7_450 = [s8_341, s8_181] := by decide
theorem s7_450_safe : Safe 6 7 s7_450 := by
  apply safe_succ 5 7 s7_450 [s8_341, s8_181] (by decide) s7_450_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_341_safe
  · subst z; exact s8_181_safe
def s7_451 : State := ⟨[17,21,64,145], 44601830679428167221534918366648241376923926, 3, 3, 1, 0⟩
theorem s7_451_edges : next config 7 s7_451 = [s8_182] := by decide
theorem s7_451_safe : Safe 6 7 s7_451 := by
  apply safe_succ 5 7 s7_451 [s8_182] (by decide) s7_451_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_182_safe
def s7_452 : State := ⟨[17,21,64,145], 44601830679428167221534955260136380206092566, 3, 3, 1, 0⟩
theorem s7_452_edges : next config 7 s7_452 = [s8_183] := by decide
theorem s7_452_safe : Safe 6 7 s7_452 := by
  apply safe_succ 5 7 s7_452 [s8_183] (by decide) s7_452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_183_safe
def s7_453 : State := ⟨[17,21,67,128], 340282366920938463629395304099451441438, 3, 3, 0, 0⟩
theorem s7_453_edges : next config 7 s7_453 = [s8_212, s8_176] := by decide
theorem s7_453_safe : Safe 6 7 s7_453 := by
  apply safe_succ 5 7 s7_453 [s8_212, s8_176] (by decide) s7_453_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_212_safe
  · subst z; exact s8_176_safe
def s7_454 : State := ⟨[17,21,67,128], 340282366920943299406460738910988472598, 3, 2, 0, 0⟩
theorem s7_454_edges : next config 7 s7_454 = [s8_177] := by decide
theorem s7_454_safe : Safe 6 7 s7_454 := by
  apply safe_succ 5 7 s7_454 [s8_177] (by decide) s7_454_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_177_safe
def s7_455 : State := ⟨[17,21,67,128], 340282366920944508258493377245324972310, 3, 2, 0, 0⟩
theorem s7_455_edges : next config 7 s7_455 = [s8_178] := by decide
theorem s7_455_safe : Safe 6 7 s7_455 := by
  apply safe_succ 5 7 s7_455 [s8_178] (by decide) s7_455_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_178_safe
def s7_456 : State := ⟨[17,21,67,128], 340282366921020670658916075178169663766, 3, 2, 0, 0⟩
theorem s7_456_edges : next config 7 s7_456 = [s8_179] := by decide
theorem s7_456_safe : Safe 6 7 s7_456 := by
  apply safe_succ 5 7 s7_456 [s8_179] (by decide) s7_456_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_179_safe
def s7_457 : State := ⟨[17,21,67,128], 340282366921021879510948713512506163478, 3, 2, 0, 0⟩
theorem s7_457_edges : next config 7 s7_457 = [s8_180] := by decide
theorem s7_457_safe : Safe 6 7 s7_457 := by
  apply safe_succ 5 7 s7_457 [s8_180] (by decide) s7_457_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_180_safe
def s7_458 : State := ⟨[17,21,67,145], 44601830679428167221535102834088969882505494, 3, 2, 1, 0⟩
theorem s7_458_edges : next config 7 s7_458 = [s8_386, s8_70, s8_213] := by decide
theorem s7_458_safe : Safe 6 7 s7_458 := by
  apply safe_succ 5 7 s7_458 [s8_386, s8_70, s8_213] (by decide) s7_458_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_386_safe
  · subst z; exact s8_70_safe
  · subst z; exact s8_213_safe
def s7_459 : State := ⟨[17,21,67,145], 44601830679428167221535139727577117301608726, 3, 2, 1, 0⟩
theorem s7_459_edges : next config 7 s7_459 = [s8_387, s8_71, s8_214] := by decide
theorem s7_459_safe : Safe 6 7 s7_459 := by
  apply safe_succ 5 7 s7_459 [s8_387, s8_71, s8_214] (by decide) s7_459_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_387_safe
  · subst z; exact s8_71_safe
  · subst z; exact s8_214_safe
def s7_460 : State := ⟨[17,21,67,145], 44601830679428167303742095461371901181624598, 3, 0, 1, 0⟩
theorem s7_460_edges : next config 7 s7_460 = [s8_72, s8_127] := by decide
theorem s7_460_safe : Safe 6 7 s7_460 := by
  apply safe_succ 5 7 s7_460 [s8_72, s8_127] (by decide) s7_460_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_72_safe
  · subst z; exact s8_127_safe
def s7_461 : State := ⟨[17,21,67,145], 44601830679428167304950947494010235518124310, 3, 0, 1, 0⟩
theorem s7_461_edges : next config 7 s7_461 = [s8_73, s8_128] := by decide
theorem s7_461_safe : Safe 6 7 s7_461 := by
  apply safe_succ 5 7 s7_461 [s8_73, s8_128] (by decide) s7_461_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_73_safe
  · subst z; exact s8_128_safe
def s7_462 : State := ⟨[17,21,82,145], 44601830679428167226370695432083044324020502, 3, 2, 1, 0⟩
theorem s7_462_edges : next config 7 s7_462 = [s8_74, s8_177] := by decide
theorem s7_462_safe : Safe 6 7 s7_462 := by
  apply safe_succ 5 7 s7_462 [s8_74, s8_177] (by decide) s7_462_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_74_safe
  · subst z; exact s8_177_safe
def s7_463 : State := ⟨[17,21,82,145], 44601830679428167227579547464721378660520214, 3, 2, 1, 0⟩
theorem s7_463_edges : next config 7 s7_463 = [s8_75, s8_178] := by decide
theorem s7_463_safe : Safe 6 7 s7_463 := by
  apply safe_succ 5 7 s7_463 [s8_75, s8_178] (by decide) s7_463_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_75_safe
  · subst z; exact s8_178_safe
def s7_464 : State := ⟨[17,21,82,145], 44601830679428167303741947887419311505211670, 3, 2, 1, 0⟩
theorem s7_464_edges : next config 7 s7_464 = [s8_76, s8_179] := by decide
theorem s7_464_safe : Safe 6 7 s7_464 := by
  apply safe_succ 5 7 s7_464 [s8_76, s8_179] (by decide) s7_464_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_76_safe
  · subst z; exact s8_179_safe
def s7_465 : State := ⟨[17,21,82,145], 44601830679428167304950799920057645841711382, 3, 2, 1, 0⟩
theorem s7_465_edges : next config 7 s7_465 = [s8_77, s8_180] := by decide
theorem s7_465_safe : Safe 6 7 s7_465 := by
  apply safe_succ 5 7 s7_465 [s8_77, s8_180] (by decide) s7_465_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_77_safe
  · subst z; exact s8_180_safe
def s7_466 : State := ⟨[17,21,96,128], 340282367000166625996085689103318978846, 3, 3, 0, 0⟩
theorem s7_466_edges : next config 7 s7_466 = [s8_197, s8_187, s8_181] := by decide
theorem s7_466_safe : Safe 6 7 s7_466 := by
  apply safe_succ 5 7 s7_466 [s8_197, s8_187, s8_181] (by decide) s7_466_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_197_safe
  · subst z; exact s8_187_safe
  · subst z; exact s8_181_safe
def s7_467 : State := ⟨[17,21,96,128], 340282367000166625996085689111908913430, 3, 3, 0, 0⟩
theorem s7_467_edges : next config 7 s7_467 = [s8_188, s8_182] := by decide
theorem s7_467_safe : Safe 6 7 s7_467 := by
  apply safe_succ 5 7 s7_467 [s8_188, s8_182] (by decide) s7_467_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_188_safe
  · subst z; exact s8_182_safe
def s7_468 : State := ⟨[17,21,96,128], 340282367000166626032979177250738082070, 3, 3, 0, 0⟩
theorem s7_468_edges : next config 7 s7_468 = [s8_198, s8_189, s8_183] := by decide
theorem s7_468_safe : Safe 6 7 s7_468 := by
  apply safe_succ 5 7 s7_468 [s8_198, s8_189, s8_183] (by decide) s7_468_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_198_safe
  · subst z; exact s8_189_safe
  · subst z; exact s8_183_safe
def s7_469 : State := ⟨[17,21,96,128], 340282367158622951024614364290406879510, 3, 3, 0, 0⟩
theorem s7_469_edges : next config 7 s7_469 = [s8_190, s8_184] := by decide
theorem s7_469_safe : Safe 6 7 s7_469 := by
  apply safe_succ 5 7 s7_469 [s8_190, s8_184] (by decide) s7_469_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_190_safe
  · subst z; exact s8_184_safe
def s7_470 : State := ⟨[17,21,96,128], 340282368267817226224315090600022180126, 3, 3, 0, 0⟩
theorem s7_470_edges : next config 7 s7_470 = [s8_191, s8_185] := by decide
theorem s7_470_safe : Safe 6 7 s7_470 := by
  apply safe_succ 5 7 s7_470 [s8_191, s8_185] (by decide) s7_470_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_191_safe
  · subst z; exact s8_185_safe
def s7_471 : State := ⟨[17,21,96,128], 340282368267817226261208578747441283350, 3, 3, 0, 0⟩
theorem s7_471_edges : next config 7 s7_471 = [s8_192, s8_186] := by decide
theorem s7_471_safe : Safe 6 7 s7_471 := by
  apply safe_succ 5 7 s7_471 [s8_192, s8_186] (by decide) s7_471_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_192_safe
  · subst z; exact s8_186_safe
def s7_472 : State := ⟨[17,21,97,145], 44601830679428404906022461159661013418840342, 3, 2, 1, 0⟩
theorem s7_472_edges : next config 7 s7_472 = [s8_78] := by decide
theorem s7_472_safe : Safe 6 7 s7_472 := by
  apply safe_succ 5 7 s7_472 [s8_78] (by decide) s7_472_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_78_safe
def s7_473 : State := ⟨[17,21,100,145], 44601830679429514100297660860387323034140958, 3, 1, 1, 0⟩
theorem s7_473_edges : next config 7 s7_473 = [s8_129] := by decide
theorem s7_473_safe : Safe 6 7 s7_473 := by
  apply safe_succ 5 7 s7_473 [s8_129] (by decide) s7_473_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_129_safe
def s7_474 : State := ⟨[17,21,100,145], 44601830679429514100297697753875470453244182, 3, 1, 1, 0⟩
theorem s7_474_edges : next config 7 s7_474 = [s8_130] := by decide
theorem s7_474_safe : Safe 6 7 s7_474 := by
  apply safe_succ 5 7 s7_474 [s8_130] (by decide) s7_474_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_130_safe
def s7_475 : State := ⟨[17,21,104,145], 44601830679448528859301084301409773582221598, 3, 1, 1, 0⟩
theorem s7_475_edges : next config 7 s7_475 = [s8_444, s8_269, s8_342, s8_132, s8_225, s8_208, s8_211, s8_199, s8_201, s8_206] := by decide
theorem s7_475_safe : Safe 6 7 s7_475 := by
  apply safe_succ 5 7 s7_475 [s8_444, s8_269, s8_342, s8_132, s8_225, s8_208, s8_211, s8_199, s8_201, s8_206] (by decide) s7_475_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s8_444_safe
  · subst z; exact s8_269_safe
  · subst z; exact s8_342_safe
  · subst z; exact s8_132_safe
  · subst z; exact s8_225_safe
  · subst z; exact s8_208_safe
  · subst z; exact s8_211_safe
  · subst z; exact s8_199_safe
  · subst z; exact s8_201_safe
  · subst z; exact s8_206_safe
def s7_476 : State := ⟨[17,21,104,145], 44601830679448528859301084301409773582222102, 3, 1, 1, 0⟩
theorem s7_476_edges : next config 7 s7_476 = [s8_133] := by decide
theorem s7_476_safe : Safe 6 7 s7_476 := by
  apply safe_succ 5 7 s7_476 [s8_133] (by decide) s7_476_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_133_safe
def s7_477 : State := ⟨[17,21,104,145], 44601830679448528859301084301409773582225686, 3, 2, 1, 0⟩
theorem s7_477_edges : next config 7 s7_477 = [s8_79, s8_343, s8_226, s8_202] := by decide
theorem s7_477_safe : Safe 6 7 s7_477 := by
  apply safe_succ 5 7 s7_477 [s8_79, s8_343, s8_226, s8_202] (by decide) s7_477_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_79_safe
  · subst z; exact s8_343_safe
  · subst z; exact s8_226_safe
  · subst z; exact s8_202_safe
def s7_478 : State := ⟨[17,21,104,145], 44601830679448528859301084301409782172156182, 3, 1, 1, 0⟩
theorem s7_478_edges : next config 7 s7_478 = [s8_135, s8_227, s8_209, s8_203] := by decide
theorem s7_478_safe : Safe 6 7 s7_478 := by
  apply safe_succ 5 7 s7_478 [s8_135, s8_227, s8_209, s8_203] (by decide) s7_478_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_135_safe
  · subst z; exact s8_227_safe
  · subst z; exact s8_209_safe
  · subst z; exact s8_203_safe
def s7_479 : State := ⟨[17,21,104,145], 44601830679448528859301121194897921001324822, 3, 1, 1, 0⟩
theorem s7_479_edges : next config 7 s7_479 = [s8_445, s8_270, s8_137, s8_228, s8_210, s8_200, s8_204, s8_207] := by decide
theorem s7_479_safe : Safe 6 7 s7_479 := by
  apply safe_succ 5 7 s7_479 [s8_445, s8_270, s8_137, s8_228, s8_210, s8_200, s8_204, s8_207] (by decide) s7_479_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s8_445_safe
  · subst z; exact s8_270_safe
  · subst z; exact s8_137_safe
  · subst z; exact s8_228_safe
  · subst z; exact s8_210_safe
  · subst z; exact s8_200_safe
  · subst z; exact s8_204_safe
  · subst z; exact s8_207_safe
def s7_480 : State := ⟨[17,21,104,145], 44601830679448528859301379449314952935047446, 3, 2, 1, 0⟩
theorem s7_480_edges : next config 7 s7_480 = [s8_80] := by decide
theorem s7_480_safe : Safe 6 7 s7_480 := by
  apply safe_succ 5 7 s7_480 [s8_80] (by decide) s7_480_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_80_safe
def s7_481 : State := ⟨[17,21,104,145], 44601830679448687315626112830084960670122262, 3, 1, 1, 0⟩
theorem s7_481_edges : next config 7 s7_481 = [s8_139, s8_229, s8_205] := by decide
theorem s7_481_safe : Safe 6 7 s7_481 := by
  apply safe_succ 5 7 s7_481 [s8_139, s8_229, s8_205] (by decide) s7_481_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_139_safe
  · subst z; exact s8_229_safe
  · subst z; exact s8_205_safe
def s7_482 : State := ⟨[17,21,104,145], 44601830679449796509901312530811270285426966, 3, 2, 1, 0⟩
theorem s7_482_edges : next config 7 s7_482 = [s8_81] := by decide
theorem s7_482_safe : Safe 6 7 s7_482 := by
  apply safe_succ 5 7 s7_482 [s8_81] (by decide) s7_482_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_81_safe
def s7_483 : State := ⟨[17,21,104,145], 44601830679773047412959511028192929602797846, 3, 2, 1, 0⟩
theorem s7_483_edges : next config 7 s7_483 = [s8_82] := by decide
theorem s7_483_safe : Safe 6 7 s7_483 := by
  apply safe_succ 5 7 s7_483 [s8_82] (by decide) s7_483_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_82_safe
def s7_484 : State := ⟨[17,21,108,128], 340282711801129888074482896206590837022, 3, 1, 0, 0⟩
theorem s7_484_edges : next config 7 s7_484 = [s8_144, s8_195] := by decide
theorem s7_484_safe : Safe 6 7 s7_484 := by
  apply safe_succ 5 7 s7_484 [s8_144, s8_195] (by decide) s7_484_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_144_safe
  · subst z; exact s8_195_safe
def s7_485 : State := ⟨[17,21,108,128], 340282711801129888111376384354009940246, 3, 1, 0, 0⟩
theorem s7_485_edges : next config 7 s7_485 = [s8_145, s8_196] := by decide
theorem s7_485_safe : Safe 6 7 s7_485 := by
  apply safe_succ 5 7 s7_485 [s8_145, s8_196] (by decide) s7_485_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_145_safe
  · subst z; exact s8_196_safe
def s7_486 : State := ⟨[17,21,112,145], 44601830684620543308232260259516322660159766, 3, 2, 1, 0⟩
theorem s7_486_edges : next config 7 s7_486 = [s8_83] := by decide
theorem s7_486_safe : Safe 6 7 s7_486 := by
  apply safe_succ 5 7 s7_486 [s8_83] (by decide) s7_486_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_83_safe
def s7_487 : State := ⟨[17,21,113,145], 44601830689812840166767087888046818989375774, 3, 1, 1, 0⟩
theorem s7_487_edges : next config 7 s7_487 = [s8_147] := by decide
theorem s7_487_safe : Safe 6 7 s7_487 := by
  apply safe_succ 5 7 s7_487 [s8_147] (by decide) s7_487_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_147_safe
def s7_488 : State := ⟨[17,21,113,145], 44601830689812840166767087888046818989379862, 3, 2, 1, 0⟩
theorem s7_488_edges : next config 7 s7_488 = [s8_84] := by decide
theorem s7_488_safe : Safe 6 7 s7_488 := by
  apply safe_succ 5 7 s7_488 [s8_84] (by decide) s7_488_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_84_safe
def s7_489 : State := ⟨[17,21,113,145], 44601830689812840166767124781534966408478998, 3, 1, 1, 0⟩
theorem s7_489_edges : next config 7 s7_489 = [s8_149] := by decide
theorem s7_489_safe : Safe 6 7 s7_489 := by
  apply safe_succ 5 7 s7_489 [s8_149] (by decide) s7_489_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_149_safe
def s7_490 : State := ⟨[17,21,117,145], 44601830845581745922811916743961708865978654, 3, 1, 1, 0⟩
theorem s7_490_edges : next config 7 s7_490 = [s8_150] := by decide
theorem s7_490_safe : Safe 6 7 s7_490 := by
  apply safe_succ 5 7 s7_490 [s8_150] (by decide) s7_490_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_150_safe
def s7_491 : State := ⟨[17,21,117,145], 44601830845581745922811953637449856285081878, 3, 1, 1, 0⟩
theorem s7_491_edges : next config 7 s7_491 = [s8_151] := by decide
theorem s7_491_safe : Safe 6 7 s7_491 := by
  apply safe_succ 5 7 s7_491 [s8_151] (by decide) s7_491_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_151_safe
def s7_492 : State := ⟨[17,21,121,128], 342940843274146061393563727171130949918, 3, 1, 0, 0⟩
theorem s7_492_edges : next config 7 s7_492 = [s8_152, s8_199] := by decide
theorem s7_492_safe : Safe 6 7 s7_492 := by
  apply safe_succ 5 7 s7_492 [s8_152, s8_199] (by decide) s7_492_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_152_safe
  · subst z; exact s8_199_safe
def s7_493 : State := ⟨[17,21,121,128], 342940843274146061430457215318550053142, 3, 1, 0, 0⟩
theorem s7_493_edges : next config 7 s7_493 = [s8_153, s8_200] := by decide
theorem s7_493_safe : Safe 6 7 s7_493 := by
  apply safe_succ 5 7 s7_493 [s8_153, s8_200] (by decide) s7_493_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_153_safe
  · subst z; exact s8_200_safe
def s7_494 : State := ⟨[17,21,125,128], 382817683147693537580677938979541287198, 3, 1, 0, 0⟩
theorem s7_494_edges : next config 7 s7_494 = [s8_154, s8_201] := by decide
theorem s7_494_safe : Safe 6 7 s7_494 := by
  apply safe_succ 5 7 s7_494 [s8_154, s8_201] (by decide) s7_494_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_154_safe
  · subst z; exact s8_201_safe
def s7_495 : State := ⟨[17,21,125,128], 382817683147693537580677938979541291286, 3, 2, 0, 0⟩
theorem s7_495_edges : next config 7 s7_495 = [s8_202] := by decide
theorem s7_495_safe : Safe 6 7 s7_495 := by
  apply safe_succ 5 7 s7_495 [s8_202] (by decide) s7_495_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_202_safe
def s7_496 : State := ⟨[17,21,125,128], 382817683147693537580677938988131221782, 3, 1, 0, 0⟩
theorem s7_496_edges : next config 7 s7_496 = [s8_155, s8_203] := by decide
theorem s7_496_safe : Safe 6 7 s7_496 := by
  apply safe_succ 5 7 s7_496 [s8_155, s8_203] (by decide) s7_496_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_155_safe
  · subst z; exact s8_203_safe
def s7_497 : State := ⟨[17,21,125,128], 382817683147693537617571427126960390422, 3, 1, 0, 0⟩
theorem s7_497_edges : next config 7 s7_497 = [s8_156, s8_204] := by decide
theorem s7_497_safe : Safe 6 7 s7_497 := by
  apply safe_succ 5 7 s7_497 [s8_156, s8_204] (by decide) s7_497_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_156_safe
  · subst z; exact s8_204_safe
def s7_498 : State := ⟨[17,21,125,128], 382817683306149862609206614166629187862, 3, 1, 0, 0⟩
theorem s7_498_edges : next config 7 s7_498 = [s8_157, s8_205] := by decide
theorem s7_498_safe : Safe 6 7 s7_498 := by
  apply safe_succ 5 7 s7_498 [s8_157, s8_205] (by decide) s7_498_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_157_safe
  · subst z; exact s8_205_safe
def s7_499 : State := ⟨[17,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175134, 3, 1, 1, 0⟩
theorem s7_499_edges : next config 7 s7_499 = [s8_159] := by decide
theorem s7_499_safe : Safe 6 7 s7_499 := by
  apply safe_succ 5 7 s7_499 [s8_159] (by decide) s7_499_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_159_safe
def s7_500 : State := ⟨[17,21,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179222, 3, 2, 1, 0⟩
theorem s7_500_edges : next config 7 s7_500 = [s8_85] := by decide
theorem s7_500_safe : Safe 6 7 s7_500 := by
  apply safe_succ 5 7 s7_500 [s8_85] (by decide) s7_500_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_85_safe
def s7_501 : State := ⟨[17,21,241,145], 3533694129556768659166595001530438862334396040200935385767686376335278358, 3, 1, 1, 0⟩
theorem s7_501_edges : next config 7 s7_501 = [s8_161] := by decide
theorem s7_501_safe : Safe 6 7 s7_501 := by
  apply safe_succ 5 7 s7_501 [s8_161] (by decide) s7_501_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_161_safe
def s7_502 : State := ⟨[17,29,67,145], 44601830679428167221535065940600823000269086, 3, 1, 1, 0⟩
theorem s7_502_edges : next config 7 s7_502 = [] := by decide
theorem s7_502_safe : Safe 6 7 s7_502 := by
  apply safe_succ 5 7 s7_502 [] (by decide) s7_502_edges
  simp
def s7_503 : State := ⟨[17,29,96,145], 44601830679428246449697432630985826867806494, 3, 1, 1, 0⟩
theorem s7_503_edges : next config 7 s7_503 = [s8_208] := by decide
theorem s7_503_safe : Safe 6 7 s7_503 := by
  apply safe_succ 5 7 s7_503 [s8_208] (by decide) s7_503_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_208_safe
def s7_504 : State := ⟨[17,29,96,145], 44601830679428246449697432630985835457741078, 3, 1, 1, 0⟩
theorem s7_504_edges : next config 7 s7_504 = [s8_209] := by decide
theorem s7_504_safe : Safe 6 7 s7_504 := by
  apply safe_succ 5 7 s7_504 [s8_209] (by decide) s7_504_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_209_safe
def s7_505 : State := ⟨[17,29,96,145], 44601830679428246449697469524473974286909718, 3, 1, 1, 0⟩
theorem s7_505_edges : next config 7 s7_505 = [s8_210] := by decide
theorem s7_505_safe : Safe 6 7 s7_505 := by
  apply safe_succ 5 7 s7_505 [s8_210] (by decide) s7_505_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_210_safe
def s7_506 : State := ⟨[17,29,104,128], 340282387282576229647756113051107131678, 3, 1, 0, 0⟩
theorem s7_506_edges : next config 7 s7_506 = [s8_208] := by decide
theorem s7_506_safe : Safe 6 7 s7_506 := by
  apply safe_succ 5 7 s7_506 [s8_208] (by decide) s7_506_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_208_safe
def s7_507 : State := ⟨[17,29,104,128], 340282387282576229647756113059697066262, 3, 1, 0, 0⟩
theorem s7_507_edges : next config 7 s7_507 = [s8_209] := by decide
theorem s7_507_safe : Safe 6 7 s7_507 := by
  apply safe_succ 5 7 s7_507 [s8_209] (by decide) s7_507_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_209_safe
def s7_508 : State := ⟨[17,29,104,128], 340282387282576229684649601198526234902, 3, 1, 0, 0⟩
theorem s7_508_edges : next config 7 s7_508 = [s8_210] := by decide
theorem s7_508_safe : Safe 6 7 s7_508 := by
  apply safe_succ 5 7 s7_508 [s8_210] (by decide) s7_508_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_210_safe
def s7_509 : State := ⟨[17,53,67,145], 44601830679428167221535065949608021718139166, 3, 1, 1, 0⟩
theorem s7_509_edges : next config 7 s7_509 = [] := by decide
theorem s7_509_safe : Safe 6 7 s7_509 := by
  apply safe_succ 5 7 s7_509 [] (by decide) s7_509_edges
  simp
def s7_510 : State := ⟨[17,53,96,145], 44601830679428246449697432639993025585676574, 3, 1, 1, 0⟩
theorem s7_510_edges : next config 7 s7_510 = [s8_211] := by decide
theorem s7_510_safe : Safe 6 7 s7_510 := by
  apply safe_succ 5 7 s7_510 [s8_211] (by decide) s7_510_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_211_safe
def s7_511 : State := ⟨[17,53,104,128], 340282387282576229647765120249825001758, 3, 1, 0, 0⟩
theorem s7_511_edges : next config 7 s7_511 = [s8_211] := by decide
theorem s7_511_safe : Safe 6 7 s7_511 := by
  apply safe_succ 5 7 s7_511 [s8_211] (by decide) s7_511_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_211_safe
def s7_512 : State := ⟨[17,68,104,145], 44601830679448528859301379449314952935047446, 3, 2, 1, 0⟩
theorem s7_512_edges : next config 7 s7_512 = [s8_86] := by decide
theorem s7_512_safe : Safe 6 7 s7_512 := by
  apply safe_succ 5 7 s7_512 [s8_86] (by decide) s7_512_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_86_safe
def s7_513 : State := ⟨[17,86,67,128], 340282366921015834918744128514051739926, 3, 2, 0, 0⟩
theorem s7_513_edges : next config 7 s7_513 = [s8_213] := by decide
theorem s7_513_safe : Safe 6 7 s7_513 := by
  apply safe_succ 5 7 s7_513 [s8_213] (by decide) s7_513_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_213_safe
def s7_514 : State := ⟨[17,86,67,128], 340282366921015834955637616661470843158, 3, 2, 0, 0⟩
theorem s7_514_edges : next config 7 s7_514 = [s8_214] := by decide
theorem s7_514_safe : Safe 6 7 s7_514 := by
  apply safe_succ 5 7 s7_514 [s8_214] (by decide) s7_514_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_214_safe
def s7_515 : State := ⟨[17,86,67,128], 340282366921020670658916075178169663766, 3, 2, 0, 0⟩
theorem s7_515_edges : next config 7 s7_515 = [s8_215] := by decide
theorem s7_515_safe : Safe 6 7 s7_515 := by
  apply safe_succ 5 7 s7_515 [s8_215] (by decide) s7_515_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_215_safe
def s7_516 : State := ⟨[17,86,67,128], 340282366921021879510948713512506163478, 3, 2, 0, 0⟩
theorem s7_516_edges : next config 7 s7_516 = [s8_216] := by decide
theorem s7_516_safe : Safe 6 7 s7_516 := by
  apply safe_succ 5 7 s7_516 [s8_216] (by decide) s7_516_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_216_safe
def s7_517 : State := ⟨[17,86,67,145], 44601830679428167298906318395937089644593438, 3, 1, 1, 0⟩
theorem s7_517_edges : next config 7 s7_517 = [s8_389, s8_344] := by decide
theorem s7_517_safe : Safe 6 7 s7_517 := by
  apply safe_succ 5 7 s7_517 [s8_389, s8_344] (by decide) s7_517_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_389_safe
  · subst z; exact s8_344_safe
def s7_518 : State := ⟨[17,86,67,145], 44601830679428167303742095461371901181624598, 3, 0, 1, 0⟩
theorem s7_518_edges : next config 7 s7_518 = [s8_87] := by decide
theorem s7_518_safe : Safe 6 7 s7_518 := by
  apply safe_succ 5 7 s7_518 [s8_87] (by decide) s7_518_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_87_safe
def s7_519 : State := ⟨[17,86,67,145], 44601830679428167304950947494010235518124310, 3, 0, 1, 0⟩
theorem s7_519_edges : next config 7 s7_519 = [s8_88] := by decide
theorem s7_519_safe : Safe 6 7 s7_519 := by
  apply safe_succ 5 7 s7_519 [s8_88] (by decide) s7_519_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_88_safe
def s7_520 : State := ⟨[17,86,82,145], 44601830679428167303741947887419311505211670, 3, 2, 1, 0⟩
theorem s7_520_edges : next config 7 s7_520 = [s8_89, s8_215] := by decide
theorem s7_520_safe : Safe 6 7 s7_520 := by
  apply safe_succ 5 7 s7_520 [s8_89, s8_215] (by decide) s7_520_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_89_safe
  · subst z; exact s8_215_safe
def s7_521 : State := ⟨[17,86,82,145], 44601830679428167304950799920057645841711382, 3, 2, 1, 0⟩
theorem s7_521_edges : next config 7 s7_521 = [s8_90, s8_216] := by decide
theorem s7_521_safe : Safe 6 7 s7_521 := by
  apply safe_succ 5 7 s7_521 [s8_90, s8_216] (by decide) s7_521_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_90_safe
  · subst z; exact s8_216_safe
def s7_522 : State := ⟨[17,100,96,128], 340282368267817226224315090600022180126, 3, 3, 0, 0⟩
theorem s7_522_edges : next config 7 s7_522 = [s8_219, s8_217] := by decide
theorem s7_522_safe : Safe 6 7 s7_522 := by
  apply safe_succ 5 7 s7_522 [s8_219, s8_217] (by decide) s7_522_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_219_safe
  · subst z; exact s8_217_safe
def s7_523 : State := ⟨[17,100,96,128], 340282368267817226261208578747441283350, 3, 3, 0, 0⟩
theorem s7_523_edges : next config 7 s7_523 = [s8_220, s8_218] := by decide
theorem s7_523_safe : Safe 6 7 s7_523 := by
  apply safe_succ 5 7 s7_523 [s8_220, s8_218] (by decide) s7_523_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_220_safe
  · subst z; exact s8_218_safe
def s7_524 : State := ⟨[17,100,104,145], 44601830679449796509901312530811270283329822, 3, 1, 1, 0⟩
theorem s7_524_edges : next config 7 s7_524 = [] := by decide
theorem s7_524_safe : Safe 6 7 s7_524 := by
  apply safe_succ 5 7 s7_524 [] (by decide) s7_524_edges
  simp
def s7_525 : State := ⟨[17,100,104,145], 44601830679449796509901312530811270285426966, 3, 2, 1, 0⟩
theorem s7_525_edges : next config 7 s7_525 = [s8_91] := by decide
theorem s7_525_safe : Safe 6 7 s7_525 := by
  apply safe_succ 5 7 s7_525 [s8_91] (by decide) s7_525_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_91_safe
def s7_526 : State := ⟨[17,100,104,145], 44601830679449796509901349424299417702433046, 3, 1, 1, 0⟩
theorem s7_526_edges : next config 7 s7_526 = [] := by decide
theorem s7_526_safe : Safe 6 7 s7_526 := by
  apply safe_succ 5 7 s7_526 [] (by decide) s7_526_edges
  simp
def s7_527 : State := ⟨[17,108,104,145], 44601830679773047412959511028192929600700702, 3, 1, 1, 0⟩
theorem s7_527_edges : next config 7 s7_527 = [s8_142] := by decide
theorem s7_527_safe : Safe 6 7 s7_527 := by
  apply safe_succ 5 7 s7_527 [s8_142] (by decide) s7_527_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_142_safe
def s7_528 : State := ⟨[17,108,104,145], 44601830679773047412959511028192929602797846, 3, 2, 1, 0⟩
theorem s7_528_edges : next config 7 s7_528 = [s8_92] := by decide
theorem s7_528_safe : Safe 6 7 s7_528 := by
  apply safe_succ 5 7 s7_528 [s8_92] (by decide) s7_528_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_92_safe
def s7_529 : State := ⟨[17,108,104,145], 44601830679773047412959547921681077019803926, 3, 1, 1, 0⟩
theorem s7_529_edges : next config 7 s7_529 = [s8_143] := by decide
theorem s7_529_safe : Safe 6 7 s7_529 := by
  apply safe_succ 5 7 s7_529 [s8_143] (by decide) s7_529_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_143_safe
def s7_530 : State := ⟨[17,117,96,145], 44601830845581745922811916743961708865978654, 3, 1, 1, 0⟩
theorem s7_530_edges : next config 7 s7_530 = [s8_223] := by decide
theorem s7_530_safe : Safe 6 7 s7_530 := by
  apply safe_succ 5 7 s7_530 [s8_223] (by decide) s7_530_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_223_safe
def s7_531 : State := ⟨[17,117,96,145], 44601830845581745922811953637449856285081878, 3, 1, 1, 0⟩
theorem s7_531_edges : next config 7 s7_531 = [s8_224] := by decide
theorem s7_531_safe : Safe 6 7 s7_531 := by
  apply safe_succ 5 7 s7_531 [s8_224] (by decide) s7_531_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_224_safe
def s7_532 : State := ⟨[17,117,104,128], 340448540782049344131869088933105303838, 3, 1, 0, 0⟩
theorem s7_532_edges : next config 7 s7_532 = [s8_223] := by decide
theorem s7_532_safe : Safe 6 7 s7_532 := by
  apply safe_succ 5 7 s7_532 [s8_223] (by decide) s7_532_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_223_safe
def s7_533 : State := ⟨[17,117,104,128], 340448540782049344168762577080524407062, 3, 1, 0, 0⟩
theorem s7_533_edges : next config 7 s7_533 = [s8_224] := by decide
theorem s7_533_safe : Safe 6 7 s7_533 := by
  apply safe_succ 5 7 s7_533 [s8_224] (by decide) s7_533_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_224_safe
def s7_534 : State := ⟨[17,125,104,128], 382817683147693537580677938979541287198, 3, 1, 0, 0⟩
theorem s7_534_edges : next config 7 s7_534 = [s8_225] := by decide
theorem s7_534_safe : Safe 6 7 s7_534 := by
  apply safe_succ 5 7 s7_534 [s8_225] (by decide) s7_534_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_225_safe
def s7_535 : State := ⟨[17,125,104,128], 382817683147693537580677938979541291286, 3, 2, 0, 0⟩
theorem s7_535_edges : next config 7 s7_535 = [s8_226] := by decide
theorem s7_535_safe : Safe 6 7 s7_535 := by
  apply safe_succ 5 7 s7_535 [s8_226] (by decide) s7_535_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_226_safe
def s7_536 : State := ⟨[17,125,104,128], 382817683147693537580677938988131221782, 3, 1, 0, 0⟩
theorem s7_536_edges : next config 7 s7_536 = [s8_227] := by decide
theorem s7_536_safe : Safe 6 7 s7_536 := by
  apply safe_succ 5 7 s7_536 [s8_227] (by decide) s7_536_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_227_safe
def s7_537 : State := ⟨[17,125,104,128], 382817683147693537617571427126960390422, 3, 1, 0, 0⟩
theorem s7_537_edges : next config 7 s7_537 = [s8_228] := by decide
theorem s7_537_safe : Safe 6 7 s7_537 := by
  apply safe_succ 5 7 s7_537 [s8_228] (by decide) s7_537_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_228_safe
def s7_538 : State := ⟨[17,125,104,128], 382817683306149862609206614166629187862, 3, 1, 0, 0⟩
theorem s7_538_edges : next config 7 s7_538 = [s8_229] := by decide
theorem s7_538_safe : Safe 6 7 s7_538 := by
  apply safe_succ 5 7 s7_538 [s8_229] (by decide) s7_538_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_229_safe
def s7_539 : State := ⟨[21,4,64,145], 44601830679428167221534918366648232786989342, 3, 3, 1, 0⟩
theorem s7_539_edges : next config 7 s7_539 = [s8_236] := by decide
theorem s7_539_safe : Safe 6 7 s7_539 := by
  apply safe_succ 5 7 s7_539 [s8_236] (by decide) s7_539_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_236_safe
def s7_540 : State := ⟨[21,4,64,145], 44601830679428167221534918366648241376923926, 3, 3, 1, 0⟩
theorem s7_540_edges : next config 7 s7_540 = [s8_237] := by decide
theorem s7_540_safe : Safe 6 7 s7_540 := by
  apply safe_succ 5 7 s7_540 [s8_237] (by decide) s7_540_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_237_safe
def s7_541 : State := ⟨[21,4,64,145], 44601830679428167221534955260136380206092566, 3, 3, 1, 0⟩
theorem s7_541_edges : next config 7 s7_541 = [s8_238] := by decide
theorem s7_541_safe : Safe 6 7 s7_541 := by
  apply safe_succ 5 7 s7_541 [s8_238] (by decide) s7_541_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_238_safe
def s7_542 : State := ⟨[21,4,67,145], 44601830679428167221535102834088969882505494, 3, 2, 1, 0⟩
theorem s7_542_edges : next config 7 s7_542 = [s8_392] := by decide
theorem s7_542_safe : Safe 6 7 s7_542 := by
  apply safe_succ 5 7 s7_542 [s8_392] (by decide) s7_542_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_392_safe
def s7_543 : State := ⟨[21,4,67,145], 44601830679428167221535139727577117301608726, 3, 2, 1, 0⟩
theorem s7_543_edges : next config 7 s7_543 = [s8_393] := by decide
theorem s7_543_safe : Safe 6 7 s7_543 := by
  apply safe_succ 5 7 s7_543 [s8_393] (by decide) s7_543_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_393_safe
def s7_544 : State := ⟨[21,4,67,145], 44601830679428167303742058567883753762521366, 1, 0, 1, 0⟩
theorem s7_544_edges : next config 7 s7_544 = [] := by decide
theorem s7_544_safe : Safe 6 7 s7_544 := by
  apply safe_succ 5 7 s7_544 [] (by decide) s7_544_edges
  simp
def s7_545 : State := ⟨[21,4,67,145], 44601830679428167303742095461371901181624598, 1, 0, 1, 0⟩
theorem s7_545_edges : next config 7 s7_545 = [] := by decide
theorem s7_545_safe : Safe 6 7 s7_545 := by
  apply safe_succ 5 7 s7_545 [] (by decide) s7_545_edges
  simp
def s7_546 : State := ⟨[21,4,67,145], 44601830679428167304950947494010235518124310, 1, 0, 1, 0⟩
theorem s7_546_edges : next config 7 s7_546 = [] := by decide
theorem s7_546_safe : Safe 6 7 s7_546 := by
  apply safe_succ 5 7 s7_546 [] (by decide) s7_546_edges
  simp
def s7_547 : State := ⟨[21,4,82,145], 44601830679428167226370695432083044324020502, 3, 2, 1, 0⟩
theorem s7_547_edges : next config 7 s7_547 = [] := by decide
theorem s7_547_safe : Safe 6 7 s7_547 := by
  apply safe_succ 5 7 s7_547 [] (by decide) s7_547_edges
  simp
def s7_548 : State := ⟨[21,4,82,145], 44601830679428167227579547464721378660520214, 3, 2, 1, 0⟩
theorem s7_548_edges : next config 7 s7_548 = [] := by decide
theorem s7_548_safe : Safe 6 7 s7_548 := by
  apply safe_succ 5 7 s7_548 [] (by decide) s7_548_edges
  simp
def s7_549 : State := ⟨[21,4,82,145], 44601830679428167303741947887419311505211670, 3, 2, 1, 0⟩
theorem s7_549_edges : next config 7 s7_549 = [] := by decide
theorem s7_549_safe : Safe 6 7 s7_549 := by
  apply safe_succ 5 7 s7_549 [] (by decide) s7_549_edges
  simp
def s7_550 : State := ⟨[21,4,82,145], 44601830679428167304950799920057645841711382, 3, 2, 1, 0⟩
theorem s7_550_edges : next config 7 s7_550 = [] := by decide
theorem s7_550_safe : Safe 6 7 s7_550 := by
  apply safe_succ 5 7 s7_550 [] (by decide) s7_550_edges
  simp
def s7_551 : State := ⟨[21,4,97,145], 44601830679428404906022461159661013418840342, 3, 2, 1, 0⟩
theorem s7_551_edges : next config 7 s7_551 = [] := by decide
theorem s7_551_safe : Safe 6 7 s7_551 := by
  apply safe_succ 5 7 s7_551 [] (by decide) s7_551_edges
  simp
def s7_552 : State := ⟨[21,4,100,145], 44601830679429514100297660860387323034140958, 1, 1, 1, 0⟩
theorem s7_552_edges : next config 7 s7_552 = [] := by decide
theorem s7_552_safe : Safe 6 7 s7_552 := by
  apply safe_succ 5 7 s7_552 [] (by decide) s7_552_edges
  simp
def s7_553 : State := ⟨[21,4,100,145], 44601830679429514100297697753875470453244182, 1, 1, 1, 0⟩
theorem s7_553_edges : next config 7 s7_553 = [] := by decide
theorem s7_553_safe : Safe 6 7 s7_553 := by
  apply safe_succ 5 7 s7_553 [] (by decide) s7_553_edges
  simp
def s7_554 : State := ⟨[21,4,104,145], 44601830679448528859301084301409773582221598, 1, 1, 1, 0⟩
theorem s7_554_edges : next config 7 s7_554 = [s8_446, s8_271, s8_345, s8_263, s8_253, s8_246, s8_242, s8_251] := by decide
theorem s7_554_safe : Safe 6 7 s7_554 := by
  apply safe_succ 5 7 s7_554 [s8_446, s8_271, s8_345, s8_263, s8_253, s8_246, s8_242, s8_251] (by decide) s7_554_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s8_446_safe
  · subst z; exact s8_271_safe
  · subst z; exact s8_345_safe
  · subst z; exact s8_263_safe
  · subst z; exact s8_253_safe
  · subst z; exact s8_246_safe
  · subst z; exact s8_242_safe
  · subst z; exact s8_251_safe
def s7_555 : State := ⟨[21,4,104,145], 44601830679448528859301084301409773582222102, 1, 1, 1, 0⟩
theorem s7_555_edges : next config 7 s7_555 = [] := by decide
theorem s7_555_safe : Safe 6 7 s7_555 := by
  apply safe_succ 5 7 s7_555 [] (by decide) s7_555_edges
  simp
def s7_556 : State := ⟨[21,4,104,145], 44601830679448528859301084301409773582225686, 3, 2, 1, 0⟩
theorem s7_556_edges : next config 7 s7_556 = [s8_447, s8_247] := by decide
theorem s7_556_safe : Safe 6 7 s7_556 := by
  apply safe_succ 5 7 s7_556 [s8_447, s8_247] (by decide) s7_556_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_447_safe
  · subst z; exact s8_247_safe
def s7_557 : State := ⟨[21,4,104,145], 44601830679448528859301084301409782172156182, 1, 1, 1, 0⟩
theorem s7_557_edges : next config 7 s7_557 = [s8_448, s8_272, s8_254, s8_248] := by decide
theorem s7_557_safe : Safe 6 7 s7_557 := by
  apply safe_succ 5 7 s7_557 [s8_448, s8_272, s8_254, s8_248] (by decide) s7_557_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_448_safe
  · subst z; exact s8_272_safe
  · subst z; exact s8_254_safe
  · subst z; exact s8_248_safe
def s7_558 : State := ⟨[21,4,104,145], 44601830679448528859301121194897921001324822, 1, 1, 1, 0⟩
theorem s7_558_edges : next config 7 s7_558 = [s8_449, s8_273, s8_264, s8_255, s8_249, s8_243, s8_252] := by decide
theorem s7_558_safe : Safe 6 7 s7_558 := by
  apply safe_succ 5 7 s7_558 [s8_449, s8_273, s8_264, s8_255, s8_249, s8_243, s8_252] (by decide) s7_558_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s8_449_safe
  · subst z; exact s8_273_safe
  · subst z; exact s8_264_safe
  · subst z; exact s8_255_safe
  · subst z; exact s8_249_safe
  · subst z; exact s8_243_safe
  · subst z; exact s8_252_safe
def s7_559 : State := ⟨[21,4,104,145], 44601830679448528859301379449314952935047446, 3, 2, 1, 0⟩
theorem s7_559_edges : next config 7 s7_559 = [] := by decide
theorem s7_559_safe : Safe 6 7 s7_559 := by
  apply safe_succ 5 7 s7_559 [] (by decide) s7_559_edges
  simp
def s7_560 : State := ⟨[21,4,104,145], 44601830679448687315626112830084960670122262, 1, 1, 1, 0⟩
theorem s7_560_edges : next config 7 s7_560 = [s8_450, s8_256, s8_250] := by decide
theorem s7_560_safe : Safe 6 7 s7_560 := by
  apply safe_succ 5 7 s7_560 [s8_450, s8_256, s8_250] (by decide) s7_560_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_450_safe
  · subst z; exact s8_256_safe
  · subst z; exact s8_250_safe
def s7_561 : State := ⟨[21,4,104,145], 44601830679449796509901312530811270285426966, 3, 2, 1, 0⟩
theorem s7_561_edges : next config 7 s7_561 = [] := by decide
theorem s7_561_safe : Safe 6 7 s7_561 := by
  apply safe_succ 5 7 s7_561 [] (by decide) s7_561_edges
  simp
def s7_562 : State := ⟨[21,4,104,145], 44601830679773047412959511028192929602797846, 3, 2, 1, 0⟩
theorem s7_562_edges : next config 7 s7_562 = [] := by decide
theorem s7_562_safe : Safe 6 7 s7_562 := by
  apply safe_succ 5 7 s7_562 [] (by decide) s7_562_edges
  simp
def s7_563 : State := ⟨[21,4,112,145], 44601830684620543308232260259516322660159766, 3, 2, 1, 0⟩
theorem s7_563_edges : next config 7 s7_563 = [] := by decide
theorem s7_563_safe : Safe 6 7 s7_563 := by
  apply safe_succ 5 7 s7_563 [] (by decide) s7_563_edges
  simp
def s7_564 : State := ⟨[21,4,113,145], 44601830689812840166767087888046818989375774, 1, 1, 1, 0⟩
theorem s7_564_edges : next config 7 s7_564 = [s8_257] := by decide
theorem s7_564_safe : Safe 6 7 s7_564 := by
  apply safe_succ 5 7 s7_564 [s8_257] (by decide) s7_564_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_257_safe
def s7_565 : State := ⟨[21,4,113,145], 44601830689812840166767087888046818989379862, 3, 2, 1, 0⟩
theorem s7_565_edges : next config 7 s7_565 = [] := by decide
theorem s7_565_safe : Safe 6 7 s7_565 := by
  apply safe_succ 5 7 s7_565 [] (by decide) s7_565_edges
  simp
def s7_566 : State := ⟨[21,4,113,145], 44601830689812840166767124781534966408478998, 1, 1, 1, 0⟩
theorem s7_566_edges : next config 7 s7_566 = [s8_258] := by decide
theorem s7_566_safe : Safe 6 7 s7_566 := by
  apply safe_succ 5 7 s7_566 [s8_258] (by decide) s7_566_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_258_safe
def s7_567 : State := ⟨[21,4,117,145], 44601830845581745922811916743961708865978654, 1, 1, 1, 0⟩
theorem s7_567_edges : next config 7 s7_567 = [] := by decide
theorem s7_567_safe : Safe 6 7 s7_567 := by
  apply safe_succ 5 7 s7_567 [] (by decide) s7_567_edges
  simp
def s7_568 : State := ⟨[21,4,117,145], 44601830845581745922811953637449856285081878, 1, 1, 1, 0⟩
theorem s7_568_edges : next config 7 s7_568 = [] := by decide
theorem s7_568_safe : Safe 6 7 s7_568 := by
  apply safe_succ 5 7 s7_568 [] (by decide) s7_568_edges
  simp
def s7_569 : State := ⟨[21,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916175134, 1, 1, 1, 0⟩
theorem s7_569_edges : next config 7 s7_569 = [s8_259] := by decide
theorem s7_569_safe : Safe 6 7 s7_569 := by
  apply safe_succ 5 7 s7_569 [s8_259] (by decide) s7_569_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_259_safe
def s7_570 : State := ⟨[21,4,241,145], 3533694129556768659166595001530438862334396040200935348874198228916179222, 3, 2, 1, 0⟩
theorem s7_570_edges : next config 7 s7_570 = [] := by decide
theorem s7_570_safe : Safe 6 7 s7_570 := by
  apply safe_succ 5 7 s7_570 [] (by decide) s7_570_edges
  simp
def s7_571 : State := ⟨[21,4,241,145], 3533694129556768659166595001530438862334396040200935385767686376335278358, 1, 1, 1, 0⟩
theorem s7_571_edges : next config 7 s7_571 = [s8_260] := by decide
theorem s7_571_safe : Safe 6 7 s7_571 := by
  apply safe_succ 5 7 s7_571 [s8_260] (by decide) s7_571_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_260_safe
def s7_572 : State := ⟨[21,12,67,145], 44601830679428167221535065940600822463402270, 3, 1, 1, 0⟩
theorem s7_572_edges : next config 7 s7_572 = [s8_396, s8_230] := by decide
theorem s7_572_safe : Safe 6 7 s7_572 := by
  apply safe_succ 5 7 s7_572 [s8_396, s8_230] (by decide) s7_572_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_396_safe
  · subst z; exact s8_230_safe
def s7_573 : State := ⟨[21,12,67,145], 44601830679428167226370843006035634000433430, 3, 0, 1, 0⟩
theorem s7_573_edges : next config 7 s7_573 = [s8_231] := by decide
theorem s7_573_safe : Safe 6 7 s7_573 := by
  apply safe_succ 5 7 s7_573 [s8_231] (by decide) s7_573_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_231_safe
def s7_574 : State := ⟨[21,12,67,145], 44601830679428167227579695038673968336933142, 3, 0, 1, 0⟩
theorem s7_574_edges : next config 7 s7_574 = [s8_232] := by decide
theorem s7_574_safe : Safe 6 7 s7_574 := by
  apply safe_succ 5 7 s7_574 [s8_232] (by decide) s7_574_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_232_safe
def s7_575 : State := ⟨[21,12,96,145], 44601830679428246449697432630985826330939678, 3, 1, 1, 0⟩
theorem s7_575_edges : next config 7 s7_575 = [s8_236, s8_259, s8_253] := by decide
theorem s7_575_safe : Safe 6 7 s7_575 := by
  apply safe_succ 5 7 s7_575 [s8_236, s8_259, s8_253] (by decide) s7_575_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_236_safe
  · subst z; exact s8_259_safe
  · subst z; exact s8_253_safe
def s7_576 : State := ⟨[21,12,96,145], 44601830679428246449697432630985834920874262, 3, 1, 1, 0⟩
theorem s7_576_edges : next config 7 s7_576 = [s8_237, s8_254] := by decide
theorem s7_576_safe : Safe 6 7 s7_576 := by
  apply safe_succ 5 7 s7_576 [s8_237, s8_254] (by decide) s7_576_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_237_safe
  · subst z; exact s8_254_safe
def s7_577 : State := ⟨[21,12,96,145], 44601830679428246449697469524473973750042902, 3, 1, 1, 0⟩
theorem s7_577_edges : next config 7 s7_577 = [s8_238, s8_260, s8_255] := by decide
theorem s7_577_safe : Safe 6 7 s7_577 := by
  apply safe_succ 5 7 s7_577 [s8_238, s8_260, s8_255] (by decide) s7_577_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_238_safe
  · subst z; exact s8_260_safe
  · subst z; exact s8_255_safe
def s7_578 : State := ⟨[21,12,96,145], 44601830679428404906022461159661013418840342, 3, 1, 1, 0⟩
theorem s7_578_edges : next config 7 s7_578 = [s8_239, s8_256] := by decide
theorem s7_578_safe : Safe 6 7 s7_578 := by
  apply safe_succ 5 7 s7_578 [s8_239, s8_256] (by decide) s7_578_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_239_safe
  · subst z; exact s8_256_safe
def s7_579 : State := ⟨[21,12,125,145], 44601873214744393976609017223235702553252118, 3, 0, 1, 0⟩
theorem s7_579_edges : next config 7 s7_579 = [s8_247] := by decide
theorem s7_579_safe : Safe 6 7 s7_579 := by
  apply safe_succ 5 7 s7_579 [s8_247] (by decide) s7_579_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_247_safe
def s7_580 : State := ⟨[21,100,96,145], 44601830679429514100297660860387323034140958, 3, 1, 1, 0⟩
theorem s7_580_edges : next config 7 s7_580 = [s8_240, s8_261] := by decide
theorem s7_580_safe : Safe 6 7 s7_580 := by
  apply safe_succ 5 7 s7_580 [s8_240, s8_261] (by decide) s7_580_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_240_safe
  · subst z; exact s8_261_safe
def s7_581 : State := ⟨[21,100,96,145], 44601830679429514100297697753875470453244182, 3, 1, 1, 0⟩
theorem s7_581_edges : next config 7 s7_581 = [s8_241, s8_262] := by decide
theorem s7_581_safe : Safe 6 7 s7_581 := by
  apply safe_succ 5 7 s7_581 [s8_241, s8_262] (by decide) s7_581_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_241_safe
  · subst z; exact s8_262_safe
def s7_582 : State := ⟨[22,21,67,145], 44601830679428167221535065940600822467592478, 3, 1, 1, 0⟩
theorem s7_582_edges : next config 7 s7_582 = [s8_346] := by decide
theorem s7_582_safe : Safe 6 7 s7_582 := by
  apply safe_succ 5 7 s7_582 [s8_346] (by decide) s7_582_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_346_safe
def s7_583 : State := ⟨[22,21,96,145], 44601830679428246449697432630985826335129886, 3, 1, 1, 0⟩
theorem s7_583_edges : next config 7 s7_583 = [s8_348, s8_265] := by decide
theorem s7_583_safe : Safe 6 7 s7_583 := by
  apply safe_succ 5 7 s7_583 [s8_348, s8_265] (by decide) s7_583_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_348_safe
  · subst z; exact s8_265_safe
def s7_584 : State := ⟨[25,4,64,145], 44601830679428167221534918366648232820539678, 3, 3, 1, 0⟩
theorem s7_584_edges : next config 7 s7_584 = [s8_267] := by decide
theorem s7_584_safe : Safe 6 7 s7_584 := by
  apply safe_succ 5 7 s7_584 [s8_267] (by decide) s7_584_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_267_safe
def s7_585 : State := ⟨[25,4,64,145], 44601830679428167221534955260136380239642902, 3, 3, 1, 0⟩
theorem s7_585_edges : next config 7 s7_585 = [s8_268] := by decide
theorem s7_585_safe : Safe 6 7 s7_585 := by
  apply safe_succ 5 7 s7_585 [s8_268] (by decide) s7_585_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_268_safe
def s7_586 : State := ⟨[25,4,67,145], 44601830679428167221535102834088969916055830, 3, 2, 1, 0⟩
theorem s7_586_edges : next config 7 s7_586 = [] := by decide
theorem s7_586_safe : Safe 6 7 s7_586 := by
  apply safe_succ 5 7 s7_586 [] (by decide) s7_586_edges
  simp
def s7_587 : State := ⟨[25,4,67,145], 44601830679428167221535139727577117335159062, 3, 2, 1, 0⟩
theorem s7_587_edges : next config 7 s7_587 = [] := by decide
theorem s7_587_safe : Safe 6 7 s7_587 := by
  apply safe_succ 5 7 s7_587 [] (by decide) s7_587_edges
  simp
def s7_588 : State := ⟨[25,4,104,145], 44601830679448528859301084301409773613678878, 1, 1, 1, 0⟩
theorem s7_588_edges : next config 7 s7_588 = [] := by decide
theorem s7_588_safe : Safe 6 7 s7_588 := by
  apply safe_succ 5 7 s7_588 [] (by decide) s7_588_edges
  simp
def s7_589 : State := ⟨[25,4,104,145], 44601830679448528859301084301409773615776022, 3, 2, 1, 0⟩
theorem s7_589_edges : next config 7 s7_589 = [] := by decide
theorem s7_589_safe : Safe 6 7 s7_589 := by
  apply safe_succ 5 7 s7_589 [] (by decide) s7_589_edges
  simp
def s7_590 : State := ⟨[25,4,104,145], 44601830679448528859301121194897921032782102, 1, 1, 1, 0⟩
theorem s7_590_edges : next config 7 s7_590 = [] := by decide
theorem s7_590_safe : Safe 6 7 s7_590 := by
  apply safe_succ 5 7 s7_590 [] (by decide) s7_590_edges
  simp
def s7_591 : State := ⟨[25,21,67,145], 44601830679428167221535065940600822496952606, 3, 1, 1, 0⟩
theorem s7_591_edges : next config 7 s7_591 = [] := by decide
theorem s7_591_safe : Safe 6 7 s7_591 := by
  apply safe_succ 5 7 s7_591 [] (by decide) s7_591_edges
  simp
def s7_592 : State := ⟨[25,21,96,145], 44601830679428246449697432630985826364490014, 3, 1, 1, 0⟩
theorem s7_592_edges : next config 7 s7_592 = [s8_269] := by decide
theorem s7_592_safe : Safe 6 7 s7_592 := by
  apply safe_succ 5 7 s7_592 [s8_269] (by decide) s7_592_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_269_safe
def s7_593 : State := ⟨[25,21,96,145], 44601830679428246449697469524473973783593238, 3, 1, 1, 0⟩
theorem s7_593_edges : next config 7 s7_593 = [s8_270] := by decide
theorem s7_593_safe : Safe 6 7 s7_593 := by
  apply safe_succ 5 7 s7_593 [s8_270] (by decide) s7_593_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_270_safe
def s7_594 : State := ⟨[29,4,67,145], 44601830679428167221535065940600823000269086, 1, 1, 1, 0⟩
theorem s7_594_edges : next config 7 s7_594 = [] := by decide
theorem s7_594_safe : Safe 6 7 s7_594 := by
  apply safe_succ 5 7 s7_594 [] (by decide) s7_594_edges
  simp
def s7_595 : State := ⟨[29,4,96,145], 44601830679428246449697432630985826867806494, 1, 1, 1, 0⟩
theorem s7_595_edges : next config 7 s7_595 = [s8_271] := by decide
theorem s7_595_safe : Safe 6 7 s7_595 := by
  apply safe_succ 5 7 s7_595 [s8_271] (by decide) s7_595_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_271_safe
def s7_596 : State := ⟨[29,4,96,145], 44601830679428246449697432630985835457741078, 1, 1, 1, 0⟩
theorem s7_596_edges : next config 7 s7_596 = [s8_272] := by decide
theorem s7_596_safe : Safe 6 7 s7_596 := by
  apply safe_succ 5 7 s7_596 [s8_272] (by decide) s7_596_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_272_safe
def s7_597 : State := ⟨[29,4,96,145], 44601830679428246449697469524473974286909718, 1, 1, 1, 0⟩
theorem s7_597_edges : next config 7 s7_597 = [s8_273] := by decide
theorem s7_597_safe : Safe 6 7 s7_597 := by
  apply safe_succ 5 7 s7_597 [s8_273] (by decide) s7_597_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_273_safe
def s7_598 : State := ⟨[33,4,96,145], 44601830679428246449697432630985834918777110, 3, 3, 1, 0⟩
theorem s7_598_edges : next config 7 s7_598 = [s8_289, s8_274] := by decide
theorem s7_598_safe : Safe 6 7 s7_598 := by
  apply safe_succ 5 7 s7_598 [s8_289, s8_274] (by decide) s7_598_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_289_safe
  · subst z; exact s8_274_safe
def s7_599 : State := ⟨[33,4,96,145], 44601830679428246449697432630985834920870166, 3, 3, 1, 0⟩
theorem s7_599_edges : next config 7 s7_599 = [s8_290, s8_276, s8_275] := by decide
theorem s7_599_safe : Safe 6 7 s7_599 := by
  apply safe_succ 5 7 s7_599 [s8_290, s8_276, s8_275] (by decide) s7_599_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_290_safe
  · subst z; exact s8_276_safe
  · subst z; exact s8_275_safe
def s7_600 : State := ⟨[33,4,104,145], 44602511244182370736228011050624645706354966, 3, 2, 1, 0⟩
theorem s7_600_edges : next config 7 s7_600 = [s8_292, s8_13] := by decide
theorem s7_600_safe : Safe 6 7 s7_600 := by
  apply safe_succ 5 7 s7_600 [s8_292, s8_13] (by decide) s7_600_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_292_safe
  · subst z; exact s8_13_safe
def s7_601 : State := ⟨[33,4,104,145], 66902575877979152000836802574058143675912470, 3, 2, 1, 0⟩
theorem s7_601_edges : next config 7 s7_601 = [s8_294, s8_21] := by decide
theorem s7_601_safe : Safe 6 7 s7_601 := by
  apply safe_succ 5 7 s7_601 [s8_294, s8_21] (by decide) s7_601_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_294_safe
  · subst z; exact s8_21_safe
def s7_602 : State := ⟨[33,4,104,163], 11692013100348635200595808745231518700033691160854, 3, 2, 1, 0⟩
theorem s7_602_edges : next config 7 s7_602 = [s8_42] := by decide
theorem s7_602_safe : Safe 6 7 s7_602 := by
  apply safe_succ 5 7 s7_602 [s8_42] (by decide) s7_602_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_42_safe
def s7_603 : State := ⟨[33,4,104,163], 14615016373649311569319424556810586309618483400982, 3, 2, 1, 0⟩
theorem s7_603_edges : next config 7 s7_603 = [s8_45] := by decide
theorem s7_603_safe : Safe 6 7 s7_603 := by
  apply safe_succ 5 7 s7_603 [s8_45] (by decide) s7_603_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_45_safe
def s7_604 : State := ⟨[33,12,64,145], 44601830679428167221534918366648241376923926, 3, 3, 1, 0⟩
theorem s7_604_edges : next config 7 s7_604 = [s8_296, s8_276] := by decide
theorem s7_604_safe : Safe 6 7 s7_604 := by
  apply safe_succ 5 7 s7_604 [s8_296, s8_276] (by decide) s7_604_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_296_safe
  · subst z; exact s8_276_safe
def s7_605 : State := ⟨[33,12,104,145], 44601830679448528859301084301409782170063126, 3, 1, 1, 0⟩
theorem s7_605_edges : next config 7 s7_605 = [s8_300, s8_274] := by decide
theorem s7_605_safe : Safe 6 7 s7_605 := by
  apply safe_succ 5 7 s7_605 [s8_300, s8_274] (by decide) s7_605_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_300_safe
  · subst z; exact s8_274_safe
def s7_606 : State := ⟨[33,21,64,145], 44601830679428167221534918366648241376923926, 3, 3, 1, 0⟩
theorem s7_606_edges : next config 7 s7_606 = [s8_302, s8_277] := by decide
theorem s7_606_safe : Safe 6 7 s7_606 := by
  apply safe_succ 5 7 s7_606 [s8_302, s8_277] (by decide) s7_606_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_302_safe
  · subst z; exact s8_277_safe
def s7_607 : State := ⟨[33,21,104,145], 44601830679448528859301084301409782172156182, 3, 1, 1, 0⟩
theorem s7_607_edges : next config 7 s7_607 = [s8_306, s8_280, s8_279, s8_278] := by decide
theorem s7_607_safe : Safe 6 7 s7_607 := by
  apply safe_succ 5 7 s7_607 [s8_306, s8_280, s8_279, s8_278] (by decide) s7_607_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_306_safe
  · subst z; exact s8_280_safe
  · subst z; exact s8_279_safe
  · subst z; exact s8_278_safe
def s7_608 : State := ⟨[33,29,96,145], 44601830679428246449697432630985835457741078, 3, 1, 1, 0⟩
theorem s7_608_edges : next config 7 s7_608 = [s8_309, s8_279] := by decide
theorem s7_608_safe : Safe 6 7 s7_608 := by
  apply safe_succ 5 7 s7_608 [s8_309, s8_279] (by decide) s7_608_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_309_safe
  · subst z; exact s8_279_safe
def s7_609 : State := ⟨[35,4,64,145], 44601830679428167221534918366648267144630558, 3, 3, 1, 0⟩
theorem s7_609_edges : next config 7 s7_609 = [s8_287] := by decide
theorem s7_609_safe : Safe 6 7 s7_609 := by
  apply safe_succ 5 7 s7_609 [s8_287] (by decide) s7_609_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_287_safe
def s7_610 : State := ⟨[35,4,64,145], 44601830679428167221534918366648267146723614, 3, 3, 1, 0⟩
theorem s7_610_edges : next config 7 s7_610 = [s8_318, s8_295, s8_288] := by decide
theorem s7_610_safe : Safe 6 7 s7_610 := by
  apply safe_succ 5 7 s7_610 [s8_318, s8_295, s8_288] (by decide) s7_610_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_318_safe
  · subst z; exact s8_295_safe
  · subst z; exact s8_288_safe
def s7_611 : State := ⟨[35,4,64,145], 44601830679428167221534918366648275734565142, 3, 3, 1, 0⟩
theorem s7_611_edges : next config 7 s7_611 = [s8_289] := by decide
theorem s7_611_safe : Safe 6 7 s7_611 := by
  apply safe_succ 5 7 s7_611 [s8_289] (by decide) s7_611_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_289_safe
def s7_612 : State := ⟨[35,4,64,145], 44601830679428167221534918366648275736658198, 3, 3, 1, 0⟩
theorem s7_612_edges : next config 7 s7_612 = [s8_319, s8_296, s8_290] := by decide
theorem s7_612_safe : Safe 6 7 s7_612 := by
  apply safe_succ 5 7 s7_612 [s8_319, s8_296, s8_290] (by decide) s7_612_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_319_safe
  · subst z; exact s8_296_safe
  · subst z; exact s8_290_safe
def s7_613 : State := ⟨[35,4,67,129], 1020847100842043553070408856590889324830, 3, 2, 1, 0⟩
theorem s7_613_edges : next config 7 s7_613 = [s8_283] := by decide
theorem s7_613_safe : Safe 6 7 s7_613 := by
  apply safe_succ 5 7 s7_613 [s8_283] (by decide) s7_613_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_283_safe
def s7_614 : State := ⟨[35,4,67,129], 1020847100842043553070408856599479259414, 3, 2, 1, 0⟩
theorem s7_614_edges : next config 7 s7_614 = [s8_284] := by decide
theorem s7_614_safe : Safe 6 7 s7_614 := by
  apply safe_succ 5 7 s7_614 [s8_284] (by decide) s7_614_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_284_safe
def s7_615 : State := ⟨[35,4,67,130], 1701411834683920479997158071454425747742, 3, 2, 1, 0⟩
theorem s7_615_edges : next config 7 s7_615 = [] := by decide
theorem s7_615_safe : Safe 6 7 s7_615 := by
  apply safe_succ 5 7 s7_615 [] (by decide) s7_615_edges
  simp
def s7_616 : State := ⟨[35,4,67,130], 1701411834683920479997158071463015682326, 3, 2, 1, 0⟩
theorem s7_616_edges : next config 7 s7_616 = [] := by decide
theorem s7_616_safe : Safe 6 7 s7_616 := by
  apply safe_succ 5 7 s7_616 [] (by decide) s7_616_edges
  simp
def s7_617 : State := ⟨[35,4,67,131], 3062541302367674333850656501181498593566, 3, 2, 1, 0⟩
theorem s7_617_edges : next config 7 s7_617 = [] := by decide
theorem s7_617_safe : Safe 6 7 s7_617 := by
  apply safe_succ 5 7 s7_617 [] (by decide) s7_617_edges
  simp
def s7_618 : State := ⟨[35,4,67,132], 5784800237735182041557653360635644285214, 3, 2, 1, 0⟩
theorem s7_618_edges : next config 7 s7_618 = [] := by decide
theorem s7_618_safe : Safe 6 7 s7_618 := by
  apply safe_succ 5 7 s7_618 [] (by decide) s7_618_edges
  simp
def s7_619 : State := ⟨[35,4,67,132], 5784800237735182041557653360644234219798, 3, 2, 1, 0⟩
theorem s7_619_edges : next config 7 s7_619 = [] := by decide
theorem s7_619_safe : Safe 6 7 s7_619 := by
  apply safe_succ 5 7 s7_619 [] (by decide) s7_619_edges
  simp
def s7_620 : State := ⟨[35,4,67,136], 87452568298760413272767559144260015034654, 3, 2, 1, 0⟩
theorem s7_620_edges : next config 7 s7_620 = [] := by decide
theorem s7_620_safe : Safe 6 7 s7_620 := by
  apply safe_succ 5 7 s7_620 [] (by decide) s7_620_edges
  simp
def s7_621 : State := ⟨[35,4,67,136], 87452568298760413272767559144268604969238, 3, 2, 1, 0⟩
theorem s7_621_edges : next config 7 s7_621 = [] := by decide
theorem s7_621_safe : Safe 6 7 s7_621 := by
  apply safe_succ 5 7 s7_621 [] (by decide) s7_621_edges
  simp
def s7_622 : State := ⟨[35,4,67,136], 1481249143206924359618749951184782609154334, 3, 2, 1, 0⟩
theorem s7_622_edges : next config 7 s7_622 = [] := by decide
theorem s7_622_safe : Safe 6 7 s7_622 := by
  apply safe_succ 5 7 s7_622 [] (by decide) s7_622_edges
  simp
def s7_623 : State := ⟨[35,4,67,136], 1481249143206924359618749951184791199088918, 3, 2, 1, 0⟩
theorem s7_623_edges : next config 7 s7_623 = [] := by decide
theorem s7_623_safe : Safe 6 7 s7_623 := by
  apply safe_succ 5 7 s7_623 [] (by decide) s7_623_edges
  simp
def s7_624 : State := ⟨[35,4,67,140], 1394136857275164112972126051682249947025694, 3, 2, 1, 0⟩
theorem s7_624_edges : next config 7 s7_624 = [] := by decide
theorem s7_624_safe : Safe 6 7 s7_624 := by
  apply safe_succ 5 7 s7_624 [] (by decide) s7_624_edges
  simp
def s7_625 : State := ⟨[35,4,67,140], 1394136857275164112972126051682258536960278, 3, 2, 1, 0⟩
theorem s7_625_edges : next config 7 s7_625 = [] := by decide
theorem s7_625_safe : Safe 6 7 s7_625 := by
  apply safe_succ 5 7 s7_625 [] (by decide) s7_625_edges
  simp
def s7_626 : State := ⟨[35,4,67,144], 22301085480897623308161861932290088858882334, 3, 2, 1, 0⟩
theorem s7_626_edges : next config 7 s7_626 = [] := by decide
theorem s7_626_safe : Safe 6 7 s7_626 := by
  apply safe_succ 5 7 s7_626 [] (by decide) s7_626_edges
  simp
def s7_627 : State := ⟨[35,4,67,144], 22301085480897623308161861932290097448816918, 3, 2, 1, 0⟩
theorem s7_627_edges : next config 7 s7_627 = [] := by decide
theorem s7_627_safe : Safe 6 7 s7_627 := by
  apply safe_succ 5 7 s7_627 [] (by decide) s7_627_edges
  simp
def s7_628 : State := ⟨[35,4,67,145], 44601830679428246449697580204938450364989726, 1, 1, 1, 0⟩
theorem s7_628_edges : next config 7 s7_628 = [s8_320, s8_297] := by decide
theorem s7_628_safe : Safe 6 7 s7_628 := by
  apply safe_succ 5 7 s7_628 [s8_320, s8_297] (by decide) s7_628_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_320_safe
  · subst z; exact s8_297_safe
def s7_629 : State := ⟨[35,4,67,145], 44601830679428246449697580204938458954924310, 1, 1, 1, 0⟩
theorem s7_629_edges : next config 7 s7_629 = [s8_321, s8_298] := by decide
theorem s7_629_safe : Safe 6 7 s7_629 := by
  apply safe_succ 5 7 s7_629 [s8_321, s8_298] (by decide) s7_629_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_321_safe
  · subst z; exact s8_298_safe
def s7_630 : State := ⟨[35,4,67,145], 44602511244162009098461992689815720357335326, 3, 2, 1, 0⟩
theorem s7_630_edges : next config 7 s7_630 = [s8_398] := by decide
theorem s7_630_safe : Safe 6 7 s7_630 := by
  apply safe_succ 5 7 s7_630 [s8_398] (by decide) s7_630_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_398_safe
def s7_631 : State := ⟨[35,4,67,145], 66902575877958790363070784213249218326892830, 3, 2, 1, 0⟩
theorem s7_631_edges : next config 7 s7_631 = [s8_400] := by decide
theorem s7_631_safe : Safe 6 7 s7_631 := by
  apply safe_succ 5 7 s7_631 [s8_400] (by decide) s7_631_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_400_safe
def s7_632 : State := ⟨[35,4,67,160], 1461501637671185285203851458859942661383285444894, 3, 2, 1, 0⟩
theorem s7_632_edges : next config 7 s7_632 = [] := by decide
theorem s7_632_safe : Safe 6 7 s7_632 := by
  apply safe_succ 5 7 s7_632 [] (by decide) s7_632_edges
  simp
def s7_633 : State := ⟨[35,4,67,160], 1461501637671185285203851458859942661391875379478, 3, 2, 1, 0⟩
theorem s7_633_edges : next config 7 s7_633 = [] := by decide
theorem s7_633_safe : Safe 6 7 s7_633 := by
  apply safe_succ 5 7 s7_633 [] (by decide) s7_633_edges
  simp
def s7_634 : State := ⟨[35,4,67,161], 2923003275002088203407536291576225681047807922454, 3, 2, 1, 0⟩
theorem s7_634_edges : next config 7 s7_634 = [] := by decide
theorem s7_634_safe : Safe 6 7 s7_634 := by
  apply safe_succ 5 7 s7_634 [] (by decide) s7_634_edges
  simp
def s7_635 : State := ⟨[35,4,67,163], 11692013098987505712629645287873923798974813245726, 3, 2, 1, 0⟩
theorem s7_635_edges : next config 7 s7_635 = [] := by decide
theorem s7_635_safe : Safe 6 7 s7_635 := by
  apply safe_succ 5 7 s7_635 [] (by decide) s7_635_edges
  simp
def s7_636 : State := ⟨[35,4,67,163], 11692013098987505712629645287873923798983403180310, 3, 2, 1, 0⟩
theorem s7_636_edges : next config 7 s7_636 = [] := by decide
theorem s7_636_safe : Safe 6 7 s7_636 := by
  apply safe_succ 5 7 s7_636 [] (by decide) s7_636_edges
  simp
def s7_637 : State := ⟨[35,4,67,192], 6277101735386680764176071790207833042246015086191387414814, 3, 2, 1, 0⟩
theorem s7_637_edges : next config 7 s7_637 = [] := by decide
theorem s7_637_safe : Safe 6 7 s7_637 := by
  apply safe_succ 5 7 s7_637 [] (by decide) s7_637_edges
  simp
def s7_638 : State := ⟨[35,4,67,192], 6277101735386680764176071790207833042246015086199977349398, 3, 2, 1, 0⟩
theorem s7_638_edges : next config 7 s7_638 = [] := by decide
theorem s7_638_safe : Safe 6 7 s7_638 := by
  apply safe_succ 5 7 s7_638 [] (by decide) s7_638_edges
  simp
def s7_639 : State := ⟨[35,4,67,195], 50216813883093446111026597752661497954962503197439629005086, 3, 2, 1, 0⟩
theorem s7_639_edges : next config 7 s7_639 = [] := by decide
theorem s7_639_safe : Safe 6 7 s7_639 := by
  apply safe_succ 5 7 s7_639 [] (by decide) s7_639_edges
  simp
def s7_640 : State := ⟨[35,4,67,195], 50216813883093446111026597752661497954962503197448218939670, 3, 2, 1, 0⟩
theorem s7_640_edges : next config 7 s7_640 = [] := by decide
theorem s7_640_safe : Safe 6 7 s7_640 := by
  apply safe_succ 5 7 s7_640 [] (by decide) s7_640_edges
  simp
def s7_641 : State := ⟨[35,4,67,224], 26959946667150639794667015087359913040637311048684232122830963151134, 3, 2, 1, 0⟩
theorem s7_641_edges : next config 7 s7_641 = [] := by decide
theorem s7_641_safe : Safe 6 7 s7_641 := by
  apply safe_succ 5 7 s7_641 [] (by decide) s7_641_edges
  simp
def s7_642 : State := ⟨[35,4,67,224], 26959946667150639794667015087359913040637311048684232122839553085718, 3, 2, 1, 0⟩
theorem s7_642_edges : next config 7 s7_642 = [] := by decide
theorem s7_642_safe : Safe 6 7 s7_642 := by
  apply safe_succ 5 7 s7_642 [] (by decide) s7_642_edges
  simp
def s7_643 : State := ⟨[35,4,96,145], 44602511244162088326624359380200724224872734, 3, 2, 1, 0⟩
theorem s7_643_edges : next config 7 s7_643 = [s8_283, s8_291] := by decide
theorem s7_643_safe : Safe 6 7 s7_643 := by
  apply safe_succ 5 7 s7_643 [s8_283, s8_291] (by decide) s7_643_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_283_safe
  · subst z; exact s8_291_safe
def s7_644 : State := ⟨[35,4,96,145], 44602511244162088326624359380200732814807318, 3, 2, 1, 0⟩
theorem s7_644_edges : next config 7 s7_644 = [s8_284, s8_292] := by decide
theorem s7_644_safe : Safe 6 7 s7_644 := by
  apply safe_succ 5 7 s7_644 [s8_284, s8_292] (by decide) s7_644_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_284_safe
  · subst z; exact s8_292_safe
def s7_645 : State := ⟨[35,4,96,145], 66902575877958869591233150903634222194430238, 3, 2, 1, 0⟩
theorem s7_645_edges : next config 7 s7_645 = [s8_285, s8_293] := by decide
theorem s7_645_safe : Safe 6 7 s7_645 := by
  apply safe_succ 5 7 s7_645 [s8_285, s8_293] (by decide) s7_645_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_285_safe
  · subst z; exact s8_293_safe
def s7_646 : State := ⟨[35,4,96,145], 66902575877958869591233150903634230784364822, 3, 2, 1, 0⟩
theorem s7_646_edges : next config 7 s7_646 = [s8_286, s8_294] := by decide
theorem s7_646_safe : Safe 6 7 s7_646 := by
  apply safe_succ 5 7 s7_646 [s8_286, s8_294] (by decide) s7_646_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_286_safe
  · subst z; exact s8_294_safe
def s7_647 : State := ⟨[35,4,104,129], 1020847121124453156574505327948464197918, 3, 2, 1, 0⟩
theorem s7_647_edges : next config 7 s7_647 = [s8_291] := by decide
theorem s7_647_safe : Safe 6 7 s7_647 := by
  apply safe_succ 5 7 s7_647 [s8_291] (by decide) s7_647_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_291_safe
def s7_648 : State := ⟨[35,4,104,129], 1020847121124453156574505327957054132502, 3, 2, 1, 0⟩
theorem s7_648_edges : next config 7 s7_648 = [s8_292] := by decide
theorem s7_648_safe : Safe 6 7 s7_648 := by
  apply safe_succ 5 7 s7_648 [s8_292] (by decide) s7_648_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_292_safe
def s7_649 : State := ⟨[35,4,104,130], 1701411854966330083501254542812000620830, 3, 2, 1, 0⟩
theorem s7_649_edges : next config 7 s7_649 = [] := by decide
theorem s7_649_safe : Safe 6 7 s7_649 := by
  apply safe_succ 5 7 s7_649 [] (by decide) s7_649_edges
  simp
def s7_650 : State := ⟨[35,4,104,130], 1701411854966330083501254542820590555414, 3, 2, 1, 0⟩
theorem s7_650_edges : next config 7 s7_650 = [] := by decide
theorem s7_650_safe : Safe 6 7 s7_650 := by
  apply safe_succ 5 7 s7_650 [] (by decide) s7_650_edges
  simp
def s7_651 : State := ⟨[35,4,104,131], 3062541322650083937354752972539073466654, 3, 2, 1, 0⟩
theorem s7_651_edges : next config 7 s7_651 = [] := by decide
theorem s7_651_safe : Safe 6 7 s7_651 := by
  apply safe_succ 5 7 s7_651 [] (by decide) s7_651_edges
  simp
def s7_652 : State := ⟨[35,4,104,132], 5784800258017591645061749831993219158302, 3, 2, 1, 0⟩
theorem s7_652_edges : next config 7 s7_652 = [] := by decide
theorem s7_652_safe : Safe 6 7 s7_652 := by
  apply safe_succ 5 7 s7_652 [] (by decide) s7_652_edges
  simp
def s7_653 : State := ⟨[35,4,104,132], 5784800258017591645061749832001809092886, 3, 2, 1, 0⟩
theorem s7_653_edges : next config 7 s7_653 = [] := by decide
theorem s7_653_safe : Safe 6 7 s7_653 := by
  apply safe_succ 5 7 s7_653 [] (by decide) s7_653_edges
  simp
def s7_654 : State := ⟨[35,4,104,136], 87452568319042822876271655615617589907742, 3, 2, 1, 0⟩
theorem s7_654_edges : next config 7 s7_654 = [] := by decide
theorem s7_654_safe : Safe 6 7 s7_654 := by
  apply safe_succ 5 7 s7_654 [] (by decide) s7_654_edges
  simp
def s7_655 : State := ⟨[35,4,104,136], 87452568319042822876271655615626179842326, 3, 2, 1, 0⟩
theorem s7_655_edges : next config 7 s7_655 = [] := by decide
theorem s7_655_safe : Safe 6 7 s7_655 := by
  apply safe_succ 5 7 s7_655 [] (by decide) s7_655_edges
  simp
def s7_656 : State := ⟨[35,4,104,136], 1481249143227206769222254047656140184027422, 3, 2, 1, 0⟩
theorem s7_656_edges : next config 7 s7_656 = [] := by decide
theorem s7_656_safe : Safe 6 7 s7_656 := by
  apply safe_succ 5 7 s7_656 [] (by decide) s7_656_edges
  simp
def s7_657 : State := ⟨[35,4,104,136], 1481249143227206769222254047656148773962006, 3, 2, 1, 0⟩
theorem s7_657_edges : next config 7 s7_657 = [] := by decide
theorem s7_657_safe : Safe 6 7 s7_657 := by
  apply safe_succ 5 7 s7_657 [] (by decide) s7_657_edges
  simp
def s7_658 : State := ⟨[35,4,104,140], 1394136857295446522575630148153607521898782, 3, 2, 1, 0⟩
theorem s7_658_edges : next config 7 s7_658 = [] := by decide
theorem s7_658_safe : Safe 6 7 s7_658 := by
  apply safe_succ 5 7 s7_658 [] (by decide) s7_658_edges
  simp
def s7_659 : State := ⟨[35,4,104,140], 1394136857295446522575630148153616111833366, 3, 2, 1, 0⟩
theorem s7_659_edges : next config 7 s7_659 = [] := by decide
theorem s7_659_safe : Safe 6 7 s7_659 := by
  apply safe_succ 5 7 s7_659 [] (by decide) s7_659_edges
  simp
def s7_660 : State := ⟨[35,4,104,144], 22301085480917905717765366028761446433755422, 3, 2, 1, 0⟩
theorem s7_660_edges : next config 7 s7_660 = [] := by decide
theorem s7_660_safe : Safe 6 7 s7_660 := by
  apply safe_succ 5 7 s7_660 [] (by decide) s7_660_edges
  simp
def s7_661 : State := ⟨[35,4,104,144], 22301085480917905717765366028761455023690006, 3, 2, 1, 0⟩
theorem s7_661_edges : next config 7 s7_661 = [] := by decide
theorem s7_661_safe : Safe 6 7 s7_661 := by
  apply safe_succ 5 7 s7_661 [] (by decide) s7_661_edges
  simp
def s7_662 : State := ⟨[35,4,104,145], 44601830679448528859301084301409807939862814, 1, 1, 1, 0⟩
theorem s7_662_edges : next config 7 s7_662 = [s8_326, s8_299] := by decide
theorem s7_662_safe : Safe 6 7 s7_662 := by
  apply safe_succ 5 7 s7_662 [s8_326, s8_299] (by decide) s7_662_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_326_safe
  · subst z; exact s8_299_safe
def s7_663 : State := ⟨[35,4,104,145], 44601830679448528859301084301409816529797398, 1, 1, 1, 0⟩
theorem s7_663_edges : next config 7 s7_663 = [s8_327, s8_300] := by decide
theorem s7_663_safe : Safe 6 7 s7_663 := by
  apply safe_succ 5 7 s7_663 [s8_327, s8_300] (by decide) s7_663_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_327_safe
  · subst z; exact s8_300_safe
def s7_664 : State := ⟨[35,4,104,160], 1461501637671185305486261062364039132740860317982, 3, 2, 1, 0⟩
theorem s7_664_edges : next config 7 s7_664 = [] := by decide
theorem s7_664_safe : Safe 6 7 s7_664 := by
  apply safe_succ 5 7 s7_664 [] (by decide) s7_664_edges
  simp
def s7_665 : State := ⟨[35,4,104,160], 1461501637671185305486261062364039132749450252566, 3, 2, 1, 0⟩
theorem s7_665_edges : next config 7 s7_665 = [] := by decide
theorem s7_665_safe : Safe 6 7 s7_665 := by
  apply safe_succ 5 7 s7_665 [] (by decide) s7_665_edges
  simp
def s7_666 : State := ⟨[35,4,104,161], 2923003275002088223689945895080322152405382795542, 3, 2, 1, 0⟩
theorem s7_666_edges : next config 7 s7_666 = [] := by decide
theorem s7_666_safe : Safe 6 7 s7_666 := by
  apply safe_succ 5 7 s7_666 [] (by decide) s7_666_edges
  simp
def s7_667 : State := ⟨[35,4,104,163], 11692013098987505732912054891378020270332388118814, 3, 2, 1, 0⟩
theorem s7_667_edges : next config 7 s7_667 = [] := by decide
theorem s7_667_safe : Safe 6 7 s7_667 := by
  apply safe_succ 5 7 s7_667 [] (by decide) s7_667_edges
  simp
def s7_668 : State := ⟨[35,4,104,163], 11692013098987505732912054891378020270340978053398, 3, 2, 1, 0⟩
theorem s7_668_edges : next config 7 s7_668 = [] := by decide
theorem s7_668_safe : Safe 6 7 s7_668 := by
  apply safe_succ 5 7 s7_668 [] (by decide) s7_668_edges
  simp
def s7_669 : State := ⟨[35,4,104,192], 6277101735386680764176071810490242645750111557548962287902, 3, 2, 1, 0⟩
theorem s7_669_edges : next config 7 s7_669 = [] := by decide
theorem s7_669_safe : Safe 6 7 s7_669 := by
  apply safe_succ 5 7 s7_669 [] (by decide) s7_669_edges
  simp
def s7_670 : State := ⟨[35,4,104,192], 6277101735386680764176071810490242645750111557557552222486, 3, 2, 1, 0⟩
theorem s7_670_edges : next config 7 s7_670 = [] := by decide
theorem s7_670_safe : Safe 6 7 s7_670 := by
  apply safe_succ 5 7 s7_670 [] (by decide) s7_670_edges
  simp
def s7_671 : State := ⟨[35,4,104,224], 26959946667150639794667015087359913060919720652188328594188538024222, 3, 2, 1, 0⟩
theorem s7_671_edges : next config 7 s7_671 = [] := by decide
theorem s7_671_safe : Safe 6 7 s7_671 := by
  apply safe_succ 5 7 s7_671 [] (by decide) s7_671_edges
  simp
def s7_672 : State := ⟨[35,4,104,224], 26959946667150639794667015087359913060919720652188328594197127958806, 3, 2, 1, 0⟩
theorem s7_672_edges : next config 7 s7_672 = [] := by decide
theorem s7_672_safe : Safe 6 7 s7_672 := by
  apply safe_succ 5 7 s7_672 [] (by decide) s7_672_edges
  simp
def s7_673 : State := ⟨[35,4,104,232], 6901746346790563787434755862277365734838391548400034311275609151574302, 3, 2, 1, 0⟩
theorem s7_673_edges : next config 7 s7_673 = [] := by decide
theorem s7_673_safe : Safe 6 7 s7_673 := by
  apply safe_succ 5 7 s7_673 [] (by decide) s7_673_edges
  simp
def s7_674 : State := ⟨[35,4,104,232], 6901746346790563787434755862277365734838391548400034311275617741508886, 3, 2, 1, 0⟩
theorem s7_674_edges : next config 7 s7_674 = [] := by decide
theorem s7_674_safe : Safe 6 7 s7_674 := by
  apply safe_succ 5 7 s7_674 [] (by decide) s7_674_edges
  simp
def s7_675 : State := ⟨[35,12,67,145], 44601830679428167221535065940600856821043486, 3, 1, 1, 0⟩
theorem s7_675_edges : next config 7 s7_675 = [s8_402, s8_281] := by decide
theorem s7_675_safe : Safe 6 7 s7_675 := by
  apply safe_succ 5 7 s7_675 [s8_402, s8_281] (by decide) s7_675_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_402_safe
  · subst z; exact s8_281_safe
def s7_676 : State := ⟨[35,12,67,145], 44602511244162088326624506954153313901285662, 3, 0, 1, 0⟩
theorem s7_676_edges : next config 7 s7_676 = [s8_283] := by decide
theorem s7_676_safe : Safe 6 7 s7_676 := by
  apply safe_succ 5 7 s7_676 [s8_283] (by decide) s7_676_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_283_safe
def s7_677 : State := ⟨[35,12,67,145], 44602511244162088326624506954153322491220246, 3, 0, 1, 0⟩
theorem s7_677_edges : next config 7 s7_677 = [s8_284] := by decide
theorem s7_677_safe : Safe 6 7 s7_677 := by
  apply safe_succ 5 7 s7_677 [s8_284] (by decide) s7_677_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_284_safe
def s7_678 : State := ⟨[35,12,67,145], 66902575877958869591233298477586811870843166, 3, 0, 1, 0⟩
theorem s7_678_edges : next config 7 s7_678 = [s8_285] := by decide
theorem s7_678_safe : Safe 6 7 s7_678 := by
  apply safe_succ 5 7 s7_678 [s8_285] (by decide) s7_678_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_285_safe
def s7_679 : State := ⟨[35,12,67,145], 66902575877958869591233298477586820460777750, 3, 0, 1, 0⟩
theorem s7_679_edges : next config 7 s7_679 = [s8_286] := by decide
theorem s7_679_safe : Safe 6 7 s7_679 := by
  apply safe_succ 5 7 s7_679 [s8_286] (by decide) s7_679_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_286_safe
def s7_680 : State := ⟨[35,12,96,145], 44601830679428246449697432630985860688580894, 3, 1, 1, 0⟩
theorem s7_680_edges : next config 7 s7_680 = [s8_287, s8_297, s8_299] := by decide
theorem s7_680_safe : Safe 6 7 s7_680 := by
  apply safe_succ 5 7 s7_680 [s8_287, s8_297, s8_299] (by decide) s7_680_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_287_safe
  · subst z; exact s8_297_safe
  · subst z; exact s8_299_safe
def s7_681 : State := ⟨[35,12,96,145], 44601830679428246449697432630985869278515478, 3, 1, 1, 0⟩
theorem s7_681_edges : next config 7 s7_681 = [s8_289, s8_298, s8_300] := by decide
theorem s7_681_safe : Safe 6 7 s7_681 := by
  apply safe_succ 5 7 s7_681 [s8_289, s8_298, s8_300] (by decide) s7_681_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_289_safe
  · subst z; exact s8_298_safe
  · subst z; exact s8_300_safe
def s7_682 : State := ⟨[35,12,104,145], 44602511244182370736228011050624671476158750, 3, 0, 1, 0⟩
theorem s7_682_edges : next config 7 s7_682 = [s8_291] := by decide
theorem s7_682_safe : Safe 6 7 s7_682 := by
  apply safe_succ 5 7 s7_682 [s8_291] (by decide) s7_682_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_291_safe
def s7_683 : State := ⟨[35,12,104,145], 44602511244182370736228011050624680066093334, 3, 0, 1, 0⟩
theorem s7_683_edges : next config 7 s7_683 = [s8_292] := by decide
theorem s7_683_safe : Safe 6 7 s7_683 := by
  apply safe_succ 5 7 s7_683 [s8_292] (by decide) s7_683_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_292_safe
def s7_684 : State := ⟨[35,12,104,145], 66902575877979152000836802574058169445716254, 3, 0, 1, 0⟩
theorem s7_684_edges : next config 7 s7_684 = [s8_293] := by decide
theorem s7_684_safe : Safe 6 7 s7_684 := by
  apply safe_succ 5 7 s7_684 [s8_293] (by decide) s7_684_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_293_safe
def s7_685 : State := ⟨[35,12,104,145], 66902575877979152000836802574058178035650838, 3, 0, 1, 0⟩
theorem s7_685_edges : next config 7 s7_685 = [s8_294] := by decide
theorem s7_685_safe : Safe 6 7 s7_685 := by
  apply safe_succ 5 7 s7_685 [s8_294] (by decide) s7_685_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_294_safe
def s7_686 : State := ⟨[35,21,67,145], 44601830679428167221535065940600856823136542, 3, 1, 1, 0⟩
theorem s7_686_edges : next config 7 s7_686 = [s8_347, s8_403, s8_328, s8_310, s8_317, s8_307] := by decide
theorem s7_686_safe : Safe 6 7 s7_686 := by
  apply safe_succ 5 7 s7_686 [s8_347, s8_403, s8_328, s8_310, s8_317, s8_307] (by decide) s7_686_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s8_347_safe
  · subst z; exact s8_403_safe
  · subst z; exact s8_328_safe
  · subst z; exact s8_310_safe
  · subst z; exact s8_317_safe
  · subst z; exact s8_307_safe
def s7_687 : State := ⟨[35,21,96,145], 44601830679428246449697432630985860690673950, 3, 1, 1, 0⟩
theorem s7_687_edges : next config 7 s7_687 = [s8_349, s8_329, s8_311, s8_308, s8_303, s8_305] := by decide
theorem s7_687_safe : Safe 6 7 s7_687 := by
  apply safe_succ 5 7 s7_687 [s8_349, s8_329, s8_311, s8_308, s8_303, s8_305] (by decide) s7_687_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s8_349_safe
  · subst z; exact s8_329_safe
  · subst z; exact s8_311_safe
  · subst z; exact s8_308_safe
  · subst z; exact s8_303_safe
  · subst z; exact s8_305_safe
def s7_688 : State := ⟨[35,21,96,145], 44601830679428246449697432630985869280608534, 3, 1, 1, 0⟩
theorem s7_688_edges : next config 7 s7_688 = [s8_350, s8_330, s8_312, s8_309, s8_304, s8_306] := by decide
theorem s7_688_safe : Safe 6 7 s7_688 := by
  apply safe_succ 5 7 s7_688 [s8_350, s8_330, s8_312, s8_309, s8_304, s8_306] (by decide) s7_688_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s8_350_safe
  · subst z; exact s8_330_safe
  · subst z; exact s8_312_safe
  · subst z; exact s8_309_safe
  · subst z; exact s8_304_safe
  · subst z; exact s8_306_safe
def s7_689 : State := ⟨[35,29,64,145], 44601830679428167221534918366648267683594526, 3, 1, 1, 0⟩
theorem s7_689_edges : next config 7 s7_689 = [s8_358, s8_313, s8_308] := by decide
theorem s7_689_safe : Safe 6 7 s7_689 := by
  apply safe_succ 5 7 s7_689 [s8_358, s8_313, s8_308] (by decide) s7_689_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_358_safe
  · subst z; exact s8_313_safe
  · subst z; exact s8_308_safe
def s7_690 : State := ⟨[35,29,64,145], 44601830679428167221534918366648276273529110, 3, 1, 1, 0⟩
theorem s7_690_edges : next config 7 s7_690 = [s8_359, s8_314, s8_309] := by decide
theorem s7_690_safe : Safe 6 7 s7_690 := by
  apply safe_succ 5 7 s7_690 [s8_359, s8_314, s8_309] (by decide) s7_690_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_359_safe
  · subst z; exact s8_314_safe
  · subst z; exact s8_309_safe
def s7_691 : State := ⟨[35,54,64,145], 44601830679428167221534918384662665656205598, 3, 1, 1, 0⟩
theorem s7_691_edges : next config 7 s7_691 = [s8_315, s8_311] := by decide
theorem s7_691_safe : Safe 6 7 s7_691 := by
  apply safe_succ 5 7 s7_691 [s8_315, s8_311] (by decide) s7_691_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_315_safe
  · subst z; exact s8_311_safe
def s7_692 : State := ⟨[35,54,64,145], 44601830679428167221534918384662674246140182, 3, 1, 1, 0⟩
theorem s7_692_edges : next config 7 s7_692 = [s8_316, s8_312] := by decide
theorem s7_692_safe : Safe 6 7 s7_692 := by
  apply safe_succ 5 7 s7_692 [s8_316, s8_312] (by decide) s7_692_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_316_safe
  · subst z; exact s8_312_safe
def s7_693 : State := ⟨[43,4,67,129], 1020847121124453156722079289334233628958, 1, 0, 1, 0⟩
theorem s7_693_edges : next config 7 s7_693 = [s8_322] := by decide
theorem s7_693_safe : Safe 6 7 s7_693 := by
  apply safe_succ 5 7 s7_693 [s8_322] (by decide) s7_693_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_322_safe
def s7_694 : State := ⟨[43,4,67,129], 1020847121124453156722079289342823563542, 1, 0, 1, 0⟩
theorem s7_694_edges : next config 7 s7_694 = [s8_323] := by decide
theorem s7_694_safe : Safe 6 7 s7_694 := by
  apply safe_succ 5 7 s7_694 [s8_323] (by decide) s7_694_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_323_safe
def s7_695 : State := ⟨[43,4,67,130], 1701411854966330083648828504197770051870, 1, 0, 1, 0⟩
theorem s7_695_edges : next config 7 s7_695 = [] := by decide
theorem s7_695_safe : Safe 6 7 s7_695 := by
  apply safe_succ 5 7 s7_695 [] (by decide) s7_695_edges
  simp
def s7_696 : State := ⟨[43,4,67,130], 1701411854966330083648828504206359986454, 1, 0, 1, 0⟩
theorem s7_696_edges : next config 7 s7_696 = [] := by decide
theorem s7_696_safe : Safe 6 7 s7_696 := by
  apply safe_succ 5 7 s7_696 [] (by decide) s7_696_edges
  simp
def s7_697 : State := ⟨[43,4,67,131], 3062541322650083937502326933924842897694, 1, 0, 1, 0⟩
theorem s7_697_edges : next config 7 s7_697 = [] := by decide
theorem s7_697_safe : Safe 6 7 s7_697 := by
  apply safe_succ 5 7 s7_697 [] (by decide) s7_697_edges
  simp
def s7_698 : State := ⟨[43,4,67,132], 5784800258017591645209323793378988589342, 1, 0, 1, 0⟩
theorem s7_698_edges : next config 7 s7_698 = [] := by decide
theorem s7_698_safe : Safe 6 7 s7_698 := by
  apply safe_succ 5 7 s7_698 [] (by decide) s7_698_edges
  simp
def s7_699 : State := ⟨[43,4,67,132], 5784800258017591645209323793387578523926, 1, 0, 1, 0⟩
theorem s7_699_edges : next config 7 s7_699 = [] := by decide
theorem s7_699_safe : Safe 6 7 s7_699 := by
  apply safe_succ 5 7 s7_699 [] (by decide) s7_699_edges
  simp
def s7_700 : State := ⟨[43,4,67,136], 87452568319042822876419229577003359338782, 1, 0, 1, 0⟩
theorem s7_700_edges : next config 7 s7_700 = [] := by decide
theorem s7_700_safe : Safe 6 7 s7_700 := by
  apply safe_succ 5 7 s7_700 [] (by decide) s7_700_edges
  simp
def s7_701 : State := ⟨[43,4,67,136], 87452568319042822876419229577011949273366, 1, 0, 1, 0⟩
theorem s7_701_edges : next config 7 s7_701 = [] := by decide
theorem s7_701_safe : Safe 6 7 s7_701 := by
  apply safe_succ 5 7 s7_701 [] (by decide) s7_701_edges
  simp
def s7_702 : State := ⟨[43,4,67,144], 22301085480917905717765513602722832203186462, 1, 0, 1, 0⟩
theorem s7_702_edges : next config 7 s7_702 = [] := by decide
theorem s7_702_safe : Safe 6 7 s7_702 := by
  apply safe_succ 5 7 s7_702 [] (by decide) s7_702_edges
  simp
def s7_703 : State := ⟨[43,4,67,144], 22301085480917905717765513602722840793121046, 1, 0, 1, 0⟩
theorem s7_703_edges : next config 7 s7_703 = [] := by decide
theorem s7_703_safe : Safe 6 7 s7_703 := by
  apply safe_succ 5 7 s7_703 [] (by decide) s7_703_edges
  simp
def s7_704 : State := ⟨[43,4,67,145], 44601830679428167221535065940609652914061598, 1, 1, 1, 0⟩
theorem s7_704_edges : next config 7 s7_704 = [s8_418] := by decide
theorem s7_704_safe : Safe 6 7 s7_704 := by
  apply safe_succ 5 7 s7_704 [s8_418] (by decide) s7_704_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_418_safe
def s7_705 : State := ⟨[43,4,67,145], 44602511244162088326624506954162109994303774, 1, 0, 1, 0⟩
theorem s7_705_edges : next config 7 s7_705 = [s8_420] := by decide
theorem s7_705_safe : Safe 6 7 s7_705 := by
  apply safe_succ 5 7 s7_705 [s8_420] (by decide) s7_705_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_420_safe
def s7_706 : State := ⟨[43,4,67,145], 44602511244162088326624506954162118584238358, 1, 0, 1, 0⟩
theorem s7_706_edges : next config 7 s7_706 = [s8_421] := by decide
theorem s7_706_safe : Safe 6 7 s7_706 := by
  apply safe_succ 5 7 s7_706 [s8_421] (by decide) s7_706_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_421_safe
def s7_707 : State := ⟨[43,4,67,145], 66902575877958869591233298477595607963861278, 1, 0, 1, 0⟩
theorem s7_707_edges : next config 7 s7_707 = [s8_422] := by decide
theorem s7_707_safe : Safe 6 7 s7_707 := by
  apply safe_succ 5 7 s7_707 [s8_422] (by decide) s7_707_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_422_safe
def s7_708 : State := ⟨[43,4,67,145], 66902575877958869591233298477595616553795862, 1, 0, 1, 0⟩
theorem s7_708_edges : next config 7 s7_708 = [s8_423] := by decide
theorem s7_708_safe : Safe 6 7 s7_708 := by
  apply safe_succ 5 7 s7_708 [s8_423] (by decide) s7_708_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_423_safe
def s7_709 : State := ⟨[43,4,67,160], 1461501637671185305486261062511613094126629749022, 1, 0, 1, 0⟩
theorem s7_709_edges : next config 7 s7_709 = [] := by decide
theorem s7_709_safe : Safe 6 7 s7_709 := by
  apply safe_succ 5 7 s7_709 [] (by decide) s7_709_edges
  simp
def s7_710 : State := ⟨[43,4,67,160], 1461501637671185305486261062511613094135219683606, 1, 0, 1, 0⟩
theorem s7_710_edges : next config 7 s7_710 = [] := by decide
theorem s7_710_safe : Safe 6 7 s7_710 := by
  apply safe_succ 5 7 s7_710 [] (by decide) s7_710_edges
  simp
def s7_711 : State := ⟨[43,4,67,161], 2923003275002088223689945895227896113791152226582, 1, 0, 1, 0⟩
theorem s7_711_edges : next config 7 s7_711 = [] := by decide
theorem s7_711_safe : Safe 6 7 s7_711 := by
  apply safe_succ 5 7 s7_711 [] (by decide) s7_711_edges
  simp
def s7_712 : State := ⟨[43,4,67,163], 11692013098987505732912054891525594231718157549854, 1, 0, 1, 0⟩
theorem s7_712_edges : next config 7 s7_712 = [] := by decide
theorem s7_712_safe : Safe 6 7 s7_712 := by
  apply safe_succ 5 7 s7_712 [] (by decide) s7_712_edges
  simp
def s7_713 : State := ⟨[43,4,67,163], 11692013098987505732912054891525594231726747484438, 1, 0, 1, 0⟩
theorem s7_713_edges : next config 7 s7_713 = [] := by decide
theorem s7_713_safe : Safe 6 7 s7_713 := by
  apply safe_succ 5 7 s7_713 [] (by decide) s7_713_edges
  simp
def s7_714 : State := ⟨[43,4,67,171], 2993155353254029458868429113632742954329820545220894, 1, 0, 1, 0⟩
theorem s7_714_edges : next config 7 s7_714 = [] := by decide
theorem s7_714_safe : Safe 6 7 s7_714 := by
  apply safe_succ 5 7 s7_714 [] (by decide) s7_714_edges
  simp
def s7_715 : State := ⟨[43,4,67,171], 2993155353254029458868429113632742954329829135155478, 1, 0, 1, 0⟩
theorem s7_715_edges : next config 7 s7_715 = [] := by decide
theorem s7_715_safe : Safe 6 7 s7_715 := by
  apply safe_succ 5 7 s7_715 [] (by decide) s7_715_edges
  simp
def s7_716 : State := ⟨[43,4,67,192], 6277101735386680764176071810490242645897685518934731718942, 1, 0, 1, 0⟩
theorem s7_716_edges : next config 7 s7_716 = [] := by decide
theorem s7_716_safe : Safe 6 7 s7_716 := by
  apply safe_succ 5 7 s7_716 [] (by decide) s7_716_edges
  simp
def s7_717 : State := ⟨[43,4,67,192], 6277101735386680764176071810490242645897685518943321653526, 1, 0, 1, 0⟩
theorem s7_717_edges : next config 7 s7_717 = [] := by decide
theorem s7_717_safe : Safe 6 7 s7_717 := by
  apply safe_succ 5 7 s7_717 [] (by decide) s7_717_edges
  simp
def s7_718 : State := ⟨[43,4,67,195], 50216813883093446111026597772943907558614173630182973309214, 1, 0, 1, 0⟩
theorem s7_718_edges : next config 7 s7_718 = [] := by decide
theorem s7_718_safe : Safe 6 7 s7_718 := by
  apply safe_succ 5 7 s7_718 [] (by decide) s7_718_edges
  simp
def s7_719 : State := ⟨[43,4,67,195], 50216813883093446111026597772943907558614173630191563243798, 1, 0, 1, 0⟩
theorem s7_719_edges : next config 7 s7_719 = [] := by decide
theorem s7_719_safe : Safe 6 7 s7_719 := by
  apply safe_succ 5 7 s7_719 [] (by decide) s7_719_edges
  simp
def s7_720 : State := ⟨[43,4,67,224], 26959946667150639794667015087359913060919720652335902555574307455262, 1, 0, 1, 0⟩
theorem s7_720_edges : next config 7 s7_720 = [] := by decide
theorem s7_720_safe : Safe 6 7 s7_720 := by
  apply safe_succ 5 7 s7_720 [] (by decide) s7_720_edges
  simp
def s7_721 : State := ⟨[43,4,67,224], 26959946667150639794667015087359913060919720652335902555582897389846, 1, 0, 1, 0⟩
theorem s7_721_edges : next config 7 s7_721 = [] := by decide
theorem s7_721_safe : Safe 6 7 s7_721 := by
  apply safe_succ 5 7 s7_721 [] (by decide) s7_721_edges
  simp
def s7_722 : State := ⟨[43,4,67,232], 6901746346790563787434755862277365734838391548400181885236994921005342, 1, 0, 1, 0⟩
theorem s7_722_edges : next config 7 s7_722 = [] := by decide
theorem s7_722_safe : Safe 6 7 s7_722 := by
  apply safe_succ 5 7 s7_722 [] (by decide) s7_722_edges
  simp
def s7_723 : State := ⟨[43,4,67,232], 6901746346790563787434755862277365734838391548400181885237003510939926, 1, 0, 1, 0⟩
theorem s7_723_edges : next config 7 s7_723 = [] := by decide
theorem s7_723_safe : Safe 6 7 s7_723 := by
  apply safe_succ 5 7 s7_723 [] (by decide) s7_723_edges
  simp
def s7_724 : State := ⟨[43,4,96,145], 44601830679428246449697432630994656781599006, 1, 1, 1, 0⟩
theorem s7_724_edges : next config 7 s7_724 = [s8_326] := by decide
theorem s7_724_safe : Safe 6 7 s7_724 := by
  apply safe_succ 5 7 s7_724 [s8_326] (by decide) s7_724_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_326_safe
def s7_725 : State := ⟨[43,4,96,145], 44601830679428246449697432630994665371533590, 1, 1, 1, 0⟩
theorem s7_725_edges : next config 7 s7_725 = [s8_327] := by decide
theorem s7_725_safe : Safe 6 7 s7_725 := by
  apply safe_succ 5 7 s7_725 [s8_327] (by decide) s7_725_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_327_safe
def s7_726 : State := ⟨[43,4,104,145], 44602511244182370736228011050633467569176862, 1, 0, 1, 0⟩
theorem s7_726_edges : next config 7 s7_726 = [s8_322] := by decide
theorem s7_726_safe : Safe 6 7 s7_726 := by
  apply safe_succ 5 7 s7_726 [s8_322] (by decide) s7_726_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_322_safe
def s7_727 : State := ⟨[43,4,104,145], 44602511244182370736228011050633476159111446, 1, 0, 1, 0⟩
theorem s7_727_edges : next config 7 s7_727 = [s8_323] := by decide
theorem s7_727_safe : Safe 6 7 s7_727 := by
  apply safe_succ 5 7 s7_727 [s8_323] (by decide) s7_727_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_323_safe
def s7_728 : State := ⟨[43,4,104,145], 66902575877979152000836802574066965538734366, 1, 0, 1, 0⟩
theorem s7_728_edges : next config 7 s7_728 = [s8_324] := by decide
theorem s7_728_safe : Safe 6 7 s7_728 := by
  apply safe_succ 5 7 s7_728 [s8_324] (by decide) s7_728_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_324_safe
def s7_729 : State := ⟨[43,4,104,145], 66902575877979152000836802574066974128668950, 1, 0, 1, 0⟩
theorem s7_729_edges : next config 7 s7_729 = [s8_325] := by decide
theorem s7_729_safe : Safe 6 7 s7_729 := by
  apply safe_succ 5 7 s7_729 [s8_325] (by decide) s7_729_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_325_safe
def s7_730 : State := ⟨[43,21,64,145], 44601830679428167221534918366657063239745822, 3, 1, 1, 0⟩
theorem s7_730_edges : next config 7 s7_730 = [s8_353, s8_331, s8_329] := by decide
theorem s7_730_safe : Safe 6 7 s7_730 := by
  apply safe_succ 5 7 s7_730 [s8_353, s8_331, s8_329] (by decide) s7_730_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_353_safe
  · subst z; exact s8_331_safe
  · subst z; exact s8_329_safe
def s7_731 : State := ⟨[43,21,64,145], 44601830679428167221534918366657071829680406, 3, 1, 1, 0⟩
theorem s7_731_edges : next config 7 s7_731 = [s8_354, s8_332, s8_330] := by decide
theorem s7_731_safe : Safe 6 7 s7_731 := by
  apply safe_succ 5 7 s7_731 [s8_354, s8_332, s8_330] (by decide) s7_731_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_354_safe
  · subst z; exact s8_332_safe
  · subst z; exact s8_330_safe
def s7_732 : State := ⟨[49,4,64,145], 44601830679428167221534918367211182738313502, 3, 3, 1, 0⟩
theorem s7_732_edges : next config 7 s7_732 = [s8_335] := by decide
theorem s7_732_safe : Safe 6 7 s7_732 := by
  apply safe_succ 5 7 s7_732 [s8_335] (by decide) s7_732_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_335_safe
def s7_733 : State := ⟨[49,4,64,145], 44601830679428167221534918367211182740406558, 3, 3, 1, 0⟩
theorem s7_733_edges : next config 7 s7_733 = [s8_338, s8_336] := by decide
theorem s7_733_safe : Safe 6 7 s7_733 := by
  apply safe_succ 5 7 s7_733 [s8_338, s8_336] (by decide) s7_733_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_338_safe
  · subst z; exact s8_336_safe
def s7_734 : State := ⟨[49,4,104,145], 44601830679448528859301084301972723533545758, 1, 1, 1, 0⟩
theorem s7_734_edges : next config 7 s7_734 = [s8_339] := by decide
theorem s7_734_safe : Safe 6 7 s7_734 := by
  apply safe_succ 5 7 s7_734 [s8_339] (by decide) s7_734_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_339_safe
def s7_735 : State := ⟨[49,4,104,145], 44601830679448528859301084301972723533549846, 3, 2, 1, 0⟩
theorem s7_735_edges : next config 7 s7_735 = [] := by decide
theorem s7_735_safe : Safe 6 7 s7_735 := by
  apply safe_succ 5 7 s7_735 [] (by decide) s7_735_edges
  simp
def s7_736 : State := ⟨[49,4,104,145], 44601830679448528859301084301972723535642902, 3, 2, 1, 0⟩
theorem s7_736_edges : next config 7 s7_736 = [s8_340] := by decide
theorem s7_736_safe : Safe 6 7 s7_736 := by
  apply safe_succ 5 7 s7_736 [s8_340] (by decide) s7_736_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_340_safe
def s7_737 : State := ⟨[49,12,67,145], 44601830679428167221535065941163772414726430, 3, 1, 1, 0⟩
theorem s7_737_edges : next config 7 s7_737 = [s8_333] := by decide
theorem s7_737_safe : Safe 6 7 s7_737 := by
  apply safe_succ 5 7 s7_737 [s8_333] (by decide) s7_737_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_333_safe
def s7_738 : State := ⟨[49,12,96,145], 44601830679428246449697432631548776282263838, 3, 1, 1, 0⟩
theorem s7_738_edges : next config 7 s7_738 = [s8_335, s8_339] := by decide
theorem s7_738_safe : Safe 6 7 s7_738 := by
  apply safe_succ 5 7 s7_738 [s8_335, s8_339] (by decide) s7_738_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_335_safe
  · subst z; exact s8_339_safe
def s7_739 : State := ⟨[49,12,96,145], 44601830679428246449697432631548776284360982, 3, 2, 1, 0⟩
theorem s7_739_edges : next config 7 s7_739 = [s8_340] := by decide
theorem s7_739_safe : Safe 6 7 s7_739 := by
  apply safe_succ 5 7 s7_739 [s8_340] (by decide) s7_739_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_340_safe
def s7_740 : State := ⟨[49,21,67,145], 44601830679428167221535065941163772416819486, 3, 1, 1, 0⟩
theorem s7_740_edges : next config 7 s7_740 = [s8_344] := by decide
theorem s7_740_safe : Safe 6 7 s7_740 := by
  apply safe_succ 5 7 s7_740 [s8_344] (by decide) s7_740_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_344_safe
def s7_741 : State := ⟨[49,21,96,145], 44601830679428246449697432631548776284356894, 3, 1, 1, 0⟩
theorem s7_741_edges : next config 7 s7_741 = [s8_342] := by decide
theorem s7_741_safe : Safe 6 7 s7_741 := by
  apply safe_succ 5 7 s7_741 [s8_342] (by decide) s7_741_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_342_safe
def s7_742 : State := ⟨[49,21,96,145], 44601830679428246449697432631548776284360982, 3, 2, 1, 0⟩
theorem s7_742_edges : next config 7 s7_742 = [s8_343] := by decide
theorem s7_742_safe : Safe 6 7 s7_742 := by
  apply safe_succ 5 7 s7_742 [s8_343] (by decide) s7_742_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_343_safe
def s7_743 : State := ⟨[49,21,125,145], 44601873214744393976609017223798652506669334, 3, 0, 1, 0⟩
theorem s7_743_edges : next config 7 s7_743 = [] := by decide
theorem s7_743_safe : Safe 6 7 s7_743 := by
  apply safe_succ 5 7 s7_743 [] (by decide) s7_743_edges
  simp
def s7_744 : State := ⟨[49,125,104,145], 44601873214744393976609017223798652506669334, 3, 0, 1, 0⟩
theorem s7_744_edges : next config 7 s7_744 = [] := by decide
theorem s7_744_safe : Safe 6 7 s7_744 := by
  apply safe_succ 5 7 s7_744 [] (by decide) s7_744_edges
  simp
def s7_745 : State := ⟨[53,4,67,145], 44601830679428167221535065949608021718139166, 1, 1, 1, 0⟩
theorem s7_745_edges : next config 7 s7_745 = [] := by decide
theorem s7_745_safe : Safe 6 7 s7_745 := by
  apply safe_succ 5 7 s7_745 [] (by decide) s7_745_edges
  simp
def s7_746 : State := ⟨[53,4,96,145], 44601830679428246449697432639993025585676574, 1, 1, 1, 0⟩
theorem s7_746_edges : next config 7 s7_746 = [s8_345] := by decide
theorem s7_746_safe : Safe 6 7 s7_746 := by
  apply safe_succ 5 7 s7_746 [s8_345] (by decide) s7_746_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_345_safe
def s7_747 : State := ⟨[54,21,64,145], 44601830679428167221534918384662631300661534, 3, 1, 1, 0⟩
theorem s7_747_edges : next config 7 s7_747 = [s8_355, s8_348] := by decide
theorem s7_747_safe : Safe 6 7 s7_747 := by
  apply safe_succ 5 7 s7_747 [s8_355, s8_348] (by decide) s7_747_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_355_safe
  · subst z; exact s8_348_safe
def s7_748 : State := ⟨[54,21,64,145], 44601830679428167221534918384662665656205598, 3, 1, 1, 0⟩
theorem s7_748_edges : next config 7 s7_748 = [s8_356, s8_349] := by decide
theorem s7_748_safe : Safe 6 7 s7_748 := by
  apply safe_succ 5 7 s7_748 [s8_356, s8_349] (by decide) s7_748_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_356_safe
  · subst z; exact s8_349_safe
def s7_749 : State := ⟨[54,21,64,145], 44601830679428167221534918384662674246140182, 3, 1, 1, 0⟩
theorem s7_749_edges : next config 7 s7_749 = [s8_357, s8_350] := by decide
theorem s7_749_safe : Safe 6 7 s7_749 := by
  apply safe_succ 5 7 s7_749 [s8_357, s8_350] (by decide) s7_749_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_357_safe
  · subst z; exact s8_350_safe
def s7_750 : State := ⟨[54,53,64,145], 44601830679428167221534918393669830551208222, 3, 1, 1, 0⟩
theorem s7_750_edges : next config 7 s7_750 = [s8_360, s8_352] := by decide
theorem s7_750_safe : Safe 6 7 s7_750 := by
  apply safe_succ 5 7 s7_750 [s8_360, s8_352] (by decide) s7_750_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_360_safe
  · subst z; exact s8_352_safe
def s7_751 : State := ⟨[65,4,96,145], 44601830679428246449697469524473973747945750, 3, 3, 1, 0⟩
theorem s7_751_edges : next config 7 s7_751 = [s8_366, s8_362] := by decide
theorem s7_751_safe : Safe 6 7 s7_751 := by
  apply safe_succ 5 7 s7_751 [s8_366, s8_362] (by decide) s7_751_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_366_safe
  · subst z; exact s8_362_safe
def s7_752 : State := ⟨[65,4,96,145], 44601830679428246449697469524473973750038806, 3, 3, 1, 0⟩
theorem s7_752_edges : next config 7 s7_752 = [s8_373, s8_368, s8_361, s8_367, s8_363] := by decide
theorem s7_752_safe : Safe 6 7 s7_752 := by
  apply safe_succ 5 7 s7_752 [s8_373, s8_368, s8_361, s8_367, s8_363] (by decide) s7_752_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s8_373_safe
  · subst z; exact s8_368_safe
  · subst z; exact s8_361_safe
  · subst z; exact s8_367_safe
  · subst z; exact s8_363_safe
def s7_753 : State := ⟨[65,4,96,145], 44601830679429514100297697753875470451147030, 3, 3, 1, 0⟩
theorem s7_753_edges : next config 7 s7_753 = [s8_364] := by decide
theorem s7_753_safe : Safe 6 7 s7_753 := by
  apply safe_succ 5 7 s7_753 [s8_364] (by decide) s7_753_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_364_safe
def s7_754 : State := ⟨[65,4,104,145], 44602511244182370736228047944112784535523606, 3, 2, 1, 0⟩
theorem s7_754_edges : next config 7 s7_754 = [] := by decide
theorem s7_754_safe : Safe 6 7 s7_754 := by
  apply safe_succ 5 7 s7_754 [] (by decide) s7_754_edges
  simp
def s7_755 : State := ⟨[65,4,104,145], 44602511244183638386828276173514281238724886, 3, 2, 1, 0⟩
theorem s7_755_edges : next config 7 s7_755 = [] := by decide
theorem s7_755_safe : Safe 6 7 s7_755 := by
  apply safe_succ 5 7 s7_755 [] (by decide) s7_755_edges
  simp
def s7_756 : State := ⟨[65,4,104,145], 44602511244506889289886474670895940556095766, 3, 2, 1, 0⟩
theorem s7_756_edges : next config 7 s7_756 = [] := by decide
theorem s7_756_safe : Safe 6 7 s7_756 := by
  apply safe_succ 5 7 s7_756 [] (by decide) s7_756_edges
  simp
def s7_757 : State := ⟨[65,4,104,145], 66902575877979152000836839467546282505081110, 3, 2, 1, 0⟩
theorem s7_757_edges : next config 7 s7_757 = [] := by decide
theorem s7_757_safe : Safe 6 7 s7_757 := by
  apply safe_succ 5 7 s7_757 [] (by decide) s7_757_edges
  simp
def s7_758 : State := ⟨[65,4,104,145], 66902575877980419651437067696947779208282390, 3, 2, 1, 0⟩
theorem s7_758_edges : next config 7 s7_758 = [] := by decide
theorem s7_758_safe : Safe 6 7 s7_758 := by
  apply safe_succ 5 7 s7_758 [] (by decide) s7_758_edges
  simp
def s7_759 : State := ⟨[65,4,104,145], 66902575878303670554495266194329438525653270, 3, 2, 1, 0⟩
theorem s7_759_edges : next config 7 s7_759 = [] := by decide
theorem s7_759_safe : Safe 6 7 s7_759 := by
  apply safe_succ 5 7 s7_759 [] (by decide) s7_759_edges
  simp
def s7_760 : State := ⟨[65,4,104,146], 89204682205977458896226411238624371083907350, 3, 2, 1, 0⟩
theorem s7_760_edges : next config 7 s7_760 = [] := by decide
theorem s7_760_safe : Safe 6 7 s7_760 := by
  apply safe_succ 5 7 s7_760 [] (by decide) s7_760_edges
  simp
def s7_761 : State := ⟨[65,4,104,146], 111504066275040398283908276012843005517041942, 3, 2, 1, 0⟩
theorem s7_761_edges : next config 7 s7_761 = [] := by decide
theorem s7_761_safe : Safe 6 7 s7_761 := by
  apply safe_succ 5 7 s7_761 [] (by decide) s7_761_edges
  simp
def s7_762 : State := ⟨[65,4,104,162], 5846006551025023527781069414403280109548790157590, 3, 2, 1, 0⟩
theorem s7_762_edges : next config 7 s7_762 = [] := by decide
theorem s7_762_safe : Safe 6 7 s7_762 := by
  apply safe_succ 5 7 s7_762 [] (by decide) s7_762_edges
  simp
def s7_763 : State := ⟨[65,4,104,162], 7307508186994796978301000393266064699477649854742, 3, 2, 1, 0⟩
theorem s7_763_edges : next config 7 s7_763 = [] := by decide
theorem s7_763_safe : Safe 6 7 s7_763 := by
  apply safe_succ 5 7 s7_763 [] (by decide) s7_763_edges
  simp
def s7_764 : State := ⟨[65,4,104,176], 95780971326419139128314594914659726898420754629595414, 3, 2, 1, 0⟩
theorem s7_764_edges : next config 7 s7_764 = [] := by decide
theorem s7_764_safe : Safe 6 7 s7_764 := by
  apply safe_succ 5 7 s7_764 [] (by decide) s7_764_edges
  simp
def s7_765 : State := ⟨[65,4,104,176], 95782432805755724832702175457956724908792049056157974, 3, 2, 1, 0⟩
theorem s7_765_edges : next config 7 s7_765 = [] := by decide
theorem s7_765_safe : Safe 6 7 s7_765 := by
  apply safe_succ 5 7 s7_765 [] (by decide) s7_765_edges
  simp
def s7_766 : State := ⟨[65,4,108,145], 44601830679773047412959547921681077019803926, 1, 1, 1, 0⟩
theorem s7_766_edges : next config 7 s7_766 = [] := by decide
theorem s7_766_safe : Safe 6 7 s7_766 := by
  apply safe_succ 5 7 s7_766 [] (by decide) s7_766_edges
  simp
def s7_767 : State := ⟨[65,4,241,145], 3533694129556768659166595001530439542899129882077862312516901239869477142, 3, 2, 1, 0⟩
theorem s7_767_edges : next config 7 s7_767 = [] := by decide
theorem s7_767_safe : Safe 6 7 s7_767 := by
  apply safe_succ 5 7 s7_767 [] (by decide) s7_767_edges
  simp
def s7_768 : State := ⟨[65,4,241,145], 3533694129556768659166595001552739607532926663342471104040334737839034646, 3, 2, 1, 0⟩
theorem s7_768_edges : next config 7 s7_768 = [] := by decide
theorem s7_768_safe : Safe 6 7 s7_768 := by
  apply safe_succ 5 7 s7_768 [] (by decide) s7_768_edges
  simp
def s7_769 : State := ⟨[65,4,249,145], 904625697166532776746648320380418881934351203729176207679457272982820552982, 1, 1, 1, 0⟩
theorem s7_769_edges : next config 7 s7_769 = [] := by decide
theorem s7_769_safe : Safe 6 7 s7_769 := by
  apply safe_succ 5 7 s7_769 [] (by decide) s7_769_edges
  simp
def s7_770 : State := ⟨[65,12,64,145], 44601830679428167221534955260136380206092566, 3, 3, 1, 0⟩
theorem s7_770_edges : next config 7 s7_770 = [s8_368] := by decide
theorem s7_770_safe : Safe 6 7 s7_770 := by
  apply safe_succ 5 7 s7_770 [s8_368] (by decide) s7_770_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_368_safe
def s7_771 : State := ⟨[65,12,104,145], 44601830679448528859301121194897920999231766, 3, 1, 1, 0⟩
theorem s7_771_edges : next config 7 s7_771 = [s8_362] := by decide
theorem s7_771_safe : Safe 6 7 s7_771 := by
  apply safe_succ 5 7 s7_771 [s8_362] (by decide) s7_771_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_362_safe
def s7_772 : State := ⟨[65,12,241,145], 3533694129556768659166595001530438862334396040200935385767686376333185302, 3, 1, 1, 0⟩
theorem s7_772_edges : next config 7 s7_772 = [s8_366] := by decide
theorem s7_772_safe : Safe 6 7 s7_772 := by
  apply safe_succ 5 7 s7_772 [s8_366] (by decide) s7_772_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_366_safe
def s7_773 : State := ⟨[65,21,64,145], 44601830679428167221534955260136380206092566, 3, 3, 1, 0⟩
theorem s7_773_edges : next config 7 s7_773 = [s8_369] := by decide
theorem s7_773_safe : Safe 6 7 s7_773 := by
  apply safe_succ 5 7 s7_773 [s8_369] (by decide) s7_773_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_369_safe
def s7_774 : State := ⟨[65,21,104,145], 44601830679448528859301121194897921001324822, 3, 1, 1, 0⟩
theorem s7_774_edges : next config 7 s7_774 = [s8_375, s8_372, s8_370, s8_371] := by decide
theorem s7_774_safe : Safe 6 7 s7_774 := by
  apply safe_succ 5 7 s7_774 [s8_375, s8_372, s8_370, s8_371] (by decide) s7_774_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s8_375_safe
  · subst z; exact s8_372_safe
  · subst z; exact s8_370_safe
  · subst z; exact s8_371_safe
def s7_775 : State := ⟨[65,21,117,145], 44601830845581745922811953637449856285081878, 3, 1, 1, 0⟩
theorem s7_775_edges : next config 7 s7_775 = [] := by decide
theorem s7_775_safe : Safe 6 7 s7_775 := by
  apply safe_succ 5 7 s7_775 [] (by decide) s7_775_edges
  simp
def s7_776 : State := ⟨[65,21,241,145], 3533694129556768659166595001530438862334396040200935385767686376335278358, 3, 1, 1, 0⟩
theorem s7_776_edges : next config 7 s7_776 = [] := by decide
theorem s7_776_safe : Safe 6 7 s7_776 := by
  apply safe_succ 5 7 s7_776 [] (by decide) s7_776_edges
  simp
def s7_777 : State := ⟨[65,29,96,145], 44601830679428246449697469524473974286909718, 3, 1, 1, 0⟩
theorem s7_777_edges : next config 7 s7_777 = [s8_372] := by decide
theorem s7_777_safe : Safe 6 7 s7_777 := by
  apply safe_succ 5 7 s7_777 [s8_372] (by decide) s7_777_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_372_safe
def s7_778 : State := ⟨[65,100,104,145], 44601830679449796509901349424299417702433046, 3, 1, 1, 0⟩
theorem s7_778_edges : next config 7 s7_778 = [] := by decide
theorem s7_778_safe : Safe 6 7 s7_778 := by
  apply safe_succ 5 7 s7_778 [] (by decide) s7_778_edges
  simp
def s7_779 : State := ⟨[65,108,104,145], 44601830679773047412959547921681077019803926, 3, 1, 1, 0⟩
theorem s7_779_edges : next config 7 s7_779 = [s8_365] := by decide
theorem s7_779_safe : Safe 6 7 s7_779 := by
  apply safe_succ 5 7 s7_779 [s8_365] (by decide) s7_779_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_365_safe
def s7_780 : State := ⟨[65,117,96,145], 44601830845581745922811953637449856285081878, 3, 1, 1, 0⟩
theorem s7_780_edges : next config 7 s7_780 = [s8_374] := by decide
theorem s7_780_safe : Safe 6 7 s7_780 := by
  apply safe_succ 5 7 s7_780 [s8_374] (by decide) s7_780_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_374_safe
def s7_781 : State := ⟨[81,4,104,145], 44601830679448528861718935940639031929540886, 3, 2, 1, 0⟩
theorem s7_781_edges : next config 7 s7_781 = [] := by decide
theorem s7_781_safe : Safe 6 7 s7_781 := by
  apply safe_succ 5 7 s7_781 [] (by decide) s7_781_edges
  simp
def s7_782 : State := ⟨[81,4,104,145], 44601830679448528861718935940639031931633942, 3, 2, 1, 0⟩
theorem s7_782_edges : next config 7 s7_782 = [s8_376] := by decide
theorem s7_782_safe : Safe 6 7 s7_782 := by
  apply safe_succ 5 7 s7_782 [s8_376] (by decide) s7_782_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_376_safe
def s7_783 : State := ⟨[81,12,96,145], 44601830679428246452115284270215084680352022, 3, 2, 1, 0⟩
theorem s7_783_edges : next config 7 s7_783 = [s8_376] := by decide
theorem s7_783_safe : Safe 6 7 s7_783 := by
  apply safe_succ 5 7 s7_783 [s8_376] (by decide) s7_783_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_376_safe
def s7_784 : State := ⟨[81,21,96,145], 44601830679428246452115284270215084680352022, 3, 2, 1, 0⟩
theorem s7_784_edges : next config 7 s7_784 = [s8_377] := by decide
theorem s7_784_safe : Safe 6 7 s7_784 := by
  apply safe_succ 5 7 s7_784 [s8_377] (by decide) s7_784_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_377_safe
def s7_785 : State := ⟨[81,21,125,145], 44601873214744393979026868862464960902660374, 3, 0, 1, 0⟩
theorem s7_785_edges : next config 7 s7_785 = [] := by decide
theorem s7_785_safe : Safe 6 7 s7_785 := by
  apply safe_succ 5 7 s7_785 [] (by decide) s7_785_edges
  simp
def s7_786 : State := ⟨[81,125,104,145], 44601873214744393979026868862464960902660374, 3, 0, 1, 0⟩
theorem s7_786_edges : next config 7 s7_786 = [] := by decide
theorem s7_786_safe : Safe 6 7 s7_786 := by
  apply safe_succ 5 7 s7_786 [] (by decide) s7_786_edges
  simp
def s7_787 : State := ⟨[82,4,67,145], 44601830679428167226370806112547486579233046, 3, 2, 1, 0⟩
theorem s7_787_edges : next config 7 s7_787 = [] := by decide
theorem s7_787_safe : Safe 6 7 s7_787 := by
  apply safe_succ 5 7 s7_787 [] (by decide) s7_787_edges
  simp
def s7_788 : State := ⟨[82,4,67,145], 44601830679428167226370806112547486581326102, 3, 2, 1, 0⟩
theorem s7_788_edges : next config 7 s7_788 = [s8_394, s8_390, s8_384] := by decide
theorem s7_788_safe : Safe 6 7 s7_788 := by
  apply safe_succ 5 7 s7_788 [s8_394, s8_390, s8_384] (by decide) s7_788_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_394_safe
  · subst z; exact s8_390_safe
  · subst z; exact s8_384_safe
def s7_789 : State := ⟨[82,4,67,145], 44601830679428167226370843006035633998336278, 3, 2, 1, 0⟩
theorem s7_789_edges : next config 7 s7_789 = [] := by decide
theorem s7_789_safe : Safe 6 7 s7_789 := by
  apply safe_succ 5 7 s7_789 [] (by decide) s7_789_edges
  simp
def s7_790 : State := ⟨[82,4,67,145], 44601830679428167226370843006035634000429334, 3, 2, 1, 0⟩
theorem s7_790_edges : next config 7 s7_790 = [s8_395, s8_391, s8_385] := by decide
theorem s7_790_safe : Safe 6 7 s7_790 := by
  apply safe_succ 5 7 s7_790 [s8_395, s8_391, s8_385] (by decide) s7_790_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_395_safe
  · subst z; exact s8_391_safe
  · subst z; exact s8_385_safe
def s7_791 : State := ⟨[82,4,67,145], 44601830679428167303742058567883753760424214, 3, 2, 1, 0⟩
theorem s7_791_edges : next config 7 s7_791 = [] := by decide
theorem s7_791_safe : Safe 6 7 s7_791 := by
  apply safe_succ 5 7 s7_791 [] (by decide) s7_791_edges
  simp
def s7_792 : State := ⟨[82,4,67,145], 44601830679428167303742058567883753762521366, 1, 0, 1, 0⟩
theorem s7_792_edges : next config 7 s7_792 = [] := by decide
theorem s7_792_safe : Safe 6 7 s7_792 := by
  apply safe_succ 5 7 s7_792 [] (by decide) s7_792_edges
  simp
def s7_793 : State := ⟨[82,4,67,145], 44601830679428167303742095461371901179527446, 3, 2, 1, 0⟩
theorem s7_793_edges : next config 7 s7_793 = [] := by decide
theorem s7_793_safe : Safe 6 7 s7_793 := by
  apply safe_succ 5 7 s7_793 [] (by decide) s7_793_edges
  simp
def s7_794 : State := ⟨[82,4,67,145], 44601830679428167303742095461371901181624598, 1, 0, 1, 0⟩
theorem s7_794_edges : next config 7 s7_794 = [] := by decide
theorem s7_794_safe : Safe 6 7 s7_794 := by
  apply safe_succ 5 7 s7_794 [] (by decide) s7_794_edges
  simp
def s7_795 : State := ⟨[82,12,67,145], 44601830679428167226370769219059339160129822, 3, 1, 1, 0⟩
theorem s7_795_edges : next config 7 s7_795 = [s8_378] := by decide
theorem s7_795_safe : Safe 6 7 s7_795 := by
  apply safe_succ 5 7 s7_795 [s8_378] (by decide) s7_795_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_378_safe
def s7_796 : State := ⟨[82,21,67,145], 44601830679428167226370769219059339162222878, 3, 1, 1, 0⟩
theorem s7_796_edges : next config 7 s7_796 = [s8_389] := by decide
theorem s7_796_safe : Safe 6 7 s7_796 := by
  apply safe_succ 5 7 s7_796 [s8_389] (by decide) s7_796_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_389_safe
def s7_797 : State := ⟨[82,21,67,145], 44601830679428167303742058567883753762521366, 3, 0, 1, 0⟩
theorem s7_797_edges : next config 7 s7_797 = [] := by decide
theorem s7_797_safe : Safe 6 7 s7_797 := by
  apply safe_succ 5 7 s7_797 [] (by decide) s7_797_edges
  simp
def s7_798 : State := ⟨[82,21,67,145], 44601830679428167303742095461371901181624598, 3, 0, 1, 0⟩
theorem s7_798_edges : next config 7 s7_798 = [] := by decide
theorem s7_798_safe : Safe 6 7 s7_798 := by
  apply safe_succ 5 7 s7_798 [] (by decide) s7_798_edges
  simp
def s7_799 : State := ⟨[82,86,67,145], 44601830679428167303742021674395606341320990, 3, 1, 1, 0⟩
theorem s7_799_edges : next config 7 s7_799 = [s8_380, s8_388] := by decide
theorem s7_799_safe : Safe 6 7 s7_799 := by
  apply safe_succ 5 7 s7_799 [s8_380, s8_388] (by decide) s7_799_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_380_safe
  · subst z; exact s8_388_safe
def s7_800 : State := ⟨[82,86,67,145], 44601830679428167303742058567883753762521366, 3, 0, 1, 0⟩
theorem s7_800_edges : next config 7 s7_800 = [s8_382] := by decide
theorem s7_800_safe : Safe 6 7 s7_800 := by
  apply safe_succ 5 7 s7_800 [s8_382] (by decide) s7_800_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_382_safe
def s7_801 : State := ⟨[82,86,67,145], 44601830679428167303742095461371901181624598, 3, 0, 1, 0⟩
theorem s7_801_edges : next config 7 s7_801 = [s8_383] := by decide
theorem s7_801_safe : Safe 6 7 s7_801 := by
  apply safe_succ 5 7 s7_801 [s8_383] (by decide) s7_801_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_383_safe
def s7_802 : State := ⟨[86,4,67,145], 44601830679428167298906318395937089644593438, 1, 1, 1, 0⟩
theorem s7_802_edges : next config 7 s7_802 = [s8_381, s8_397, s8_396] := by decide
theorem s7_802_safe : Safe 6 7 s7_802 := by
  apply safe_succ 5 7 s7_802 [s8_381, s8_397, s8_396] (by decide) s7_802_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s8_381_safe
  · subst z; exact s8_397_safe
  · subst z; exact s8_396_safe
def s7_803 : State := ⟨[86,4,67,145], 44601830679428167303742021674395606341320990, 1, 1, 1, 0⟩
theorem s7_803_edges : next config 7 s7_803 = [s8_233] := by decide
theorem s7_803_safe : Safe 6 7 s7_803 := by
  apply safe_succ 5 7 s7_803 [s8_233] (by decide) s7_803_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_233_safe
def s7_804 : State := ⟨[86,4,67,145], 44601830679428167303742095461371901181624598, 1, 0, 1, 0⟩
theorem s7_804_edges : next config 7 s7_804 = [] := by decide
theorem s7_804_safe : Safe 6 7 s7_804 := by
  apply safe_succ 5 7 s7_804 [] (by decide) s7_804_edges
  simp
def s7_805 : State := ⟨[86,4,67,145], 44601830679428167304950947494010235518124310, 1, 0, 1, 0⟩
theorem s7_805_edges : next config 7 s7_805 = [] := by decide
theorem s7_805_safe : Safe 6 7 s7_805 := by
  apply safe_succ 5 7 s7_805 [] (by decide) s7_805_edges
  simp
def s7_806 : State := ⟨[86,12,67,145], 44601830679428167298906355289425237063700758, 3, 0, 1, 0⟩
theorem s7_806_edges : next config 7 s7_806 = [s8_392] := by decide
theorem s7_806_safe : Safe 6 7 s7_806 := by
  apply safe_succ 5 7 s7_806 [s8_392] (by decide) s7_806_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_392_safe
def s7_807 : State := ⟨[86,12,67,145], 44601830679428167298906392182913384482803990, 3, 0, 1, 0⟩
theorem s7_807_edges : next config 7 s7_807 = [s8_393] := by decide
theorem s7_807_safe : Safe 6 7 s7_807 := by
  apply safe_succ 5 7 s7_807 [s8_393] (by decide) s7_807_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_393_safe
def s7_808 : State := ⟨[86,82,67,145], 44601830679428167303742058567883753762521366, 3, 0, 1, 0⟩
theorem s7_808_edges : next config 7 s7_808 = [s8_394] := by decide
theorem s7_808_safe : Safe 6 7 s7_808 := by
  apply safe_succ 5 7 s7_808 [s8_394] (by decide) s7_808_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_394_safe
def s7_809 : State := ⟨[86,82,67,145], 44601830679428167303742095461371901181624598, 3, 0, 1, 0⟩
theorem s7_809_edges : next config 7 s7_809 = [s8_395] := by decide
theorem s7_809_safe : Safe 6 7 s7_809 := by
  apply safe_succ 5 7 s7_809 [s8_395] (by decide) s7_809_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_395_safe
def s7_810 : State := ⟨[96,4,67,129], 1020847100842043553070408856590889324830, 3, 2, 1, 0⟩
theorem s7_810_edges : next config 7 s7_810 = [s8_410, s8_398] := by decide
theorem s7_810_safe : Safe 6 7 s7_810 := by
  apply safe_succ 5 7 s7_810 [s8_410, s8_398] (by decide) s7_810_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_410_safe
  · subst z; exact s8_398_safe
def s7_811 : State := ⟨[96,4,67,129], 1020847121124453156722079289334233628958, 1, 0, 1, 0⟩
theorem s7_811_edges : next config 7 s7_811 = [s8_399] := by decide
theorem s7_811_safe : Safe 6 7 s7_811 := by
  apply safe_succ 5 7 s7_811 [s8_399] (by decide) s7_811_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_399_safe
def s7_812 : State := ⟨[96,4,67,130], 1701411834683920479997158071454425747742, 3, 2, 1, 0⟩
theorem s7_812_edges : next config 7 s7_812 = [s8_411] := by decide
theorem s7_812_safe : Safe 6 7 s7_812 := by
  apply safe_succ 5 7 s7_812 [s8_411] (by decide) s7_812_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_411_safe
def s7_813 : State := ⟨[96,4,67,130], 1701411854966330083648828504197770051870, 1, 0, 1, 0⟩
theorem s7_813_edges : next config 7 s7_813 = [] := by decide
theorem s7_813_safe : Safe 6 7 s7_813 := by
  apply safe_succ 5 7 s7_813 [] (by decide) s7_813_edges
  simp
def s7_814 : State := ⟨[96,4,67,131], 3062541302367674333850656501181498593566, 3, 2, 1, 0⟩
theorem s7_814_edges : next config 7 s7_814 = [s8_412] := by decide
theorem s7_814_safe : Safe 6 7 s7_814 := by
  apply safe_succ 5 7 s7_814 [s8_412] (by decide) s7_814_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_412_safe
def s7_815 : State := ⟨[96,4,67,131], 3062541322650083937502326933924842897694, 1, 0, 1, 0⟩
theorem s7_815_edges : next config 7 s7_815 = [] := by decide
theorem s7_815_safe : Safe 6 7 s7_815 := by
  apply safe_succ 5 7 s7_815 [] (by decide) s7_815_edges
  simp
def s7_816 : State := ⟨[96,4,67,132], 5784800237735182041557653360635644285214, 3, 2, 1, 0⟩
theorem s7_816_edges : next config 7 s7_816 = [s8_413] := by decide
theorem s7_816_safe : Safe 6 7 s7_816 := by
  apply safe_succ 5 7 s7_816 [s8_413] (by decide) s7_816_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_413_safe
def s7_817 : State := ⟨[96,4,67,132], 5784800258017591645209323793378988589342, 1, 0, 1, 0⟩
theorem s7_817_edges : next config 7 s7_817 = [] := by decide
theorem s7_817_safe : Safe 6 7 s7_817 := by
  apply safe_succ 5 7 s7_817 [] (by decide) s7_817_edges
  simp
def s7_818 : State := ⟨[96,4,67,136], 87452568298760413272767559144260015034654, 3, 2, 1, 0⟩
theorem s7_818_edges : next config 7 s7_818 = [s8_414] := by decide
theorem s7_818_safe : Safe 6 7 s7_818 := by
  apply safe_succ 5 7 s7_818 [s8_414] (by decide) s7_818_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_414_safe
def s7_819 : State := ⟨[96,4,67,136], 87452568319042822876419229577003359338782, 1, 0, 1, 0⟩
theorem s7_819_edges : next config 7 s7_819 = [] := by decide
theorem s7_819_safe : Safe 6 7 s7_819 := by
  apply safe_succ 5 7 s7_819 [] (by decide) s7_819_edges
  simp
def s7_820 : State := ⟨[96,4,67,136], 1481249143206924359618749951184782609154334, 3, 2, 1, 0⟩
theorem s7_820_edges : next config 7 s7_820 = [s8_415] := by decide
theorem s7_820_safe : Safe 6 7 s7_820 := by
  apply safe_succ 5 7 s7_820 [s8_415] (by decide) s7_820_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_415_safe
def s7_821 : State := ⟨[96,4,67,140], 1394136857275164112972126051682249947025694, 3, 2, 1, 0⟩
theorem s7_821_edges : next config 7 s7_821 = [s8_416] := by decide
theorem s7_821_safe : Safe 6 7 s7_821 := by
  apply safe_succ 5 7 s7_821 [s8_416] (by decide) s7_821_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_416_safe
def s7_822 : State := ⟨[96,4,67,144], 22301085480897623308161861932290088858882334, 3, 2, 1, 0⟩
theorem s7_822_edges : next config 7 s7_822 = [s8_417] := by decide
theorem s7_822_safe : Safe 6 7 s7_822 := by
  apply safe_succ 5 7 s7_822 [s8_417] (by decide) s7_822_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_417_safe
def s7_823 : State := ⟨[96,4,67,144], 22301085480917905717765513602722832203186462, 1, 0, 1, 0⟩
theorem s7_823_edges : next config 7 s7_823 = [] := by decide
theorem s7_823_safe : Safe 6 7 s7_823 := by
  apply safe_succ 5 7 s7_823 [] (by decide) s7_823_edges
  simp
def s7_824 : State := ⟨[96,4,67,145], 44601830679428246449697580204938450364989726, 1, 1, 1, 0⟩
theorem s7_824_edges : next config 7 s7_824 = [s8_419, s8_402] := by decide
theorem s7_824_safe : Safe 6 7 s7_824 := by
  apply safe_succ 5 7 s7_824 [s8_419, s8_402] (by decide) s7_824_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_419_safe
  · subst z; exact s8_402_safe
def s7_825 : State := ⟨[96,4,67,160], 1461501637671185285203851458859942661383285444894, 3, 2, 1, 0⟩
theorem s7_825_edges : next config 7 s7_825 = [s8_424] := by decide
theorem s7_825_safe : Safe 6 7 s7_825 := by
  apply safe_succ 5 7 s7_825 [s8_424] (by decide) s7_825_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_424_safe
def s7_826 : State := ⟨[96,4,67,160], 1461501637671185305486261062511613094126629749022, 1, 0, 1, 0⟩
theorem s7_826_edges : next config 7 s7_826 = [] := by decide
theorem s7_826_safe : Safe 6 7 s7_826 := by
  apply safe_succ 5 7 s7_826 [] (by decide) s7_826_edges
  simp
def s7_827 : State := ⟨[96,4,67,163], 11692013098987505712629645287873923798974813245726, 3, 2, 1, 0⟩
theorem s7_827_edges : next config 7 s7_827 = [s8_425] := by decide
theorem s7_827_safe : Safe 6 7 s7_827 := by
  apply safe_succ 5 7 s7_827 [s8_425] (by decide) s7_827_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_425_safe
def s7_828 : State := ⟨[96,4,67,163], 11692013098987505732912054891525594231718157549854, 1, 0, 1, 0⟩
theorem s7_828_edges : next config 7 s7_828 = [] := by decide
theorem s7_828_safe : Safe 6 7 s7_828 := by
  apply safe_succ 5 7 s7_828 [] (by decide) s7_828_edges
  simp
def s7_829 : State := ⟨[96,4,67,171], 2993155353254029458868429113632742954329820545220894, 1, 0, 1, 0⟩
theorem s7_829_edges : next config 7 s7_829 = [] := by decide
theorem s7_829_safe : Safe 6 7 s7_829 := by
  apply safe_succ 5 7 s7_829 [] (by decide) s7_829_edges
  simp
def s7_830 : State := ⟨[96,4,67,192], 6277101735386680764176071790207833042246015086191387414814, 3, 2, 1, 0⟩
theorem s7_830_edges : next config 7 s7_830 = [s8_426] := by decide
theorem s7_830_safe : Safe 6 7 s7_830 := by
  apply safe_succ 5 7 s7_830 [s8_426] (by decide) s7_830_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_426_safe
def s7_831 : State := ⟨[96,4,67,192], 6277101735386680764176071810490242645897685518934731718942, 1, 0, 1, 0⟩
theorem s7_831_edges : next config 7 s7_831 = [] := by decide
theorem s7_831_safe : Safe 6 7 s7_831 := by
  apply safe_succ 5 7 s7_831 [] (by decide) s7_831_edges
  simp
def s7_832 : State := ⟨[96,4,67,195], 50216813883093446111026597752661497954962503197439629005086, 3, 2, 1, 0⟩
theorem s7_832_edges : next config 7 s7_832 = [s8_427] := by decide
theorem s7_832_safe : Safe 6 7 s7_832 := by
  apply safe_succ 5 7 s7_832 [s8_427] (by decide) s7_832_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_427_safe
def s7_833 : State := ⟨[96,4,67,195], 50216813883093446111026597772943907558614173630182973309214, 1, 0, 1, 0⟩
theorem s7_833_edges : next config 7 s7_833 = [] := by decide
theorem s7_833_safe : Safe 6 7 s7_833 := by
  apply safe_succ 5 7 s7_833 [] (by decide) s7_833_edges
  simp
def s7_834 : State := ⟨[96,4,67,224], 26959946667150639794667015087359913040637311048684232122830963151134, 3, 2, 1, 0⟩
theorem s7_834_edges : next config 7 s7_834 = [s8_428] := by decide
theorem s7_834_safe : Safe 6 7 s7_834 := by
  apply safe_succ 5 7 s7_834 [s8_428] (by decide) s7_834_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_428_safe
def s7_835 : State := ⟨[96,4,67,224], 26959946667150639794667015087359913060919720652335902555574307455262, 1, 0, 1, 0⟩
theorem s7_835_edges : next config 7 s7_835 = [] := by decide
theorem s7_835_safe : Safe 6 7 s7_835 := by
  apply safe_succ 5 7 s7_835 [] (by decide) s7_835_edges
  simp
def s7_836 : State := ⟨[96,4,67,232], 6901746346790563787434755862277365734838391548400181885236994921005342, 1, 0, 1, 0⟩
theorem s7_836_edges : next config 7 s7_836 = [] := by decide
theorem s7_836_safe : Safe 6 7 s7_836 := by
  apply safe_succ 5 7 s7_836 [] (by decide) s7_836_edges
  simp
def s7_837 : State := ⟨[96,12,67,145], 44602511244162088326624506954153313901285662, 3, 0, 1, 0⟩
theorem s7_837_edges : next config 7 s7_837 = [s8_430, s8_398] := by decide
theorem s7_837_safe : Safe 6 7 s7_837 := by
  apply safe_succ 5 7 s7_837 [s8_430, s8_398] (by decide) s7_837_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_430_safe
  · subst z; exact s8_398_safe
def s7_838 : State := ⟨[96,12,67,145], 66902575877958869591233298477586811870843166, 3, 0, 1, 0⟩
theorem s7_838_edges : next config 7 s7_838 = [s8_431, s8_400] := by decide
theorem s7_838_safe : Safe 6 7 s7_838 := by
  apply safe_succ 5 7 s7_838 [s8_431, s8_400] (by decide) s7_838_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_431_safe
  · subst z; exact s8_400_safe
def s7_839 : State := ⟨[97,4,96,145], 44601830679428404906022461159661013416743190, 3, 3, 1, 0⟩
theorem s7_839_edges : next config 7 s7_839 = [s8_404] := by decide
theorem s7_839_safe : Safe 6 7 s7_839 := by
  apply safe_succ 5 7 s7_839 [s8_404] (by decide) s7_839_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_404_safe
def s7_840 : State := ⟨[97,4,96,145], 44601830679428404906022461159661013418836246, 3, 3, 1, 0⟩
theorem s7_840_edges : next config 7 s7_840 = [s8_406, s8_405] := by decide
theorem s7_840_safe : Safe 6 7 s7_840 := by
  apply safe_succ 5 7 s7_840 [s8_406, s8_405] (by decide) s7_840_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_406_safe
  · subst z; exact s8_405_safe
def s7_841 : State := ⟨[97,4,104,145], 44602511244182529192553039579299824204321046, 3, 2, 1, 0⟩
theorem s7_841_edges : next config 7 s7_841 = [] := by decide
theorem s7_841_safe : Safe 6 7 s7_841 := by
  apply safe_succ 5 7 s7_841 [] (by decide) s7_841_edges
  simp
def s7_842 : State := ⟨[97,4,104,145], 66902575877979310457161831102733322173878550, 3, 2, 1, 0⟩
theorem s7_842_edges : next config 7 s7_842 = [] := by decide
theorem s7_842_safe : Safe 6 7 s7_842 := by
  apply safe_succ 5 7 s7_842 [] (by decide) s7_842_edges
  simp
def s7_843 : State := ⟨[97,4,104,162], 5846006551025023527939525739394915296588458955030, 3, 2, 1, 0⟩
theorem s7_843_edges : next config 7 s7_843 = [] := by decide
theorem s7_843_safe : Safe 6 7 s7_843 := by
  apply safe_succ 5 7 s7_843 [] (by decide) s7_843_edges
  simp
def s7_844 : State := ⟨[97,4,104,162], 7307508186994796978459456718257699886517318652182, 3, 2, 1, 0⟩
theorem s7_844_edges : next config 7 s7_844 = [] := by decide
theorem s7_844_safe : Safe 6 7 s7_844 := by
  apply safe_succ 5 7 s7_844 [] (by decide) s7_844_edges
  simp
def s7_845 : State := ⟨[97,12,104,145], 44601830679448687315626112830084960668029206, 3, 1, 1, 0⟩
theorem s7_845_edges : next config 7 s7_845 = [s8_404] := by decide
theorem s7_845_safe : Safe 6 7 s7_845 := by
  apply safe_succ 5 7 s7_845 [s8_404] (by decide) s7_845_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_404_safe
def s7_846 : State := ⟨[97,21,104,145], 44601830679448687315626112830084960670122262, 3, 1, 1, 0⟩
theorem s7_846_edges : next config 7 s7_846 = [s8_409, s8_408] := by decide
theorem s7_846_safe : Safe 6 7 s7_846 := by
  apply safe_succ 5 7 s7_846 [s8_409, s8_408] (by decide) s7_846_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_409_safe
  · subst z; exact s8_408_safe
def s7_847 : State := ⟨[104,4,67,128], 340282387282576229795330065674604187934, 3, 2, 0, 0⟩
theorem s7_847_edges : next config 7 s7_847 = [s8_429, s8_413, s8_427, s8_411, s8_414, s8_417, s8_424] := by decide
theorem s7_847_safe : Safe 6 7 s7_847 := by
  apply safe_succ 5 7 s7_847 [s8_429, s8_413, s8_427, s8_411, s8_414, s8_417, s8_424] (by decide) s7_847_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s8_429_safe
  · subst z; exact s8_413_safe
  · subst z; exact s8_427_safe
  · subst z; exact s8_411_safe
  · subst z; exact s8_414_safe
  · subst z; exact s8_417_safe
  · subst z; exact s8_424_safe
def s7_848 : State := ⟨[104,4,67,129], 1020847121124453156722079289334233628958, 1, 0, 1, 0⟩
theorem s7_848_edges : next config 7 s7_848 = [s8_420] := by decide
theorem s7_848_safe : Safe 6 7 s7_848 := by
  apply safe_succ 5 7 s7_848 [s8_420] (by decide) s7_848_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_420_safe
def s7_849 : State := ⟨[104,4,67,129], 1020847121124453156722079289342823563542, 1, 0, 1, 0⟩
theorem s7_849_edges : next config 7 s7_849 = [s8_421] := by decide
theorem s7_849_safe : Safe 6 7 s7_849 := by
  apply safe_succ 5 7 s7_849 [s8_421] (by decide) s7_849_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_421_safe
def s7_850 : State := ⟨[104,4,67,130], 1701411854966330083648828504197770051870, 1, 0, 1, 0⟩
theorem s7_850_edges : next config 7 s7_850 = [] := by decide
theorem s7_850_safe : Safe 6 7 s7_850 := by
  apply safe_succ 5 7 s7_850 [] (by decide) s7_850_edges
  simp
def s7_851 : State := ⟨[104,4,67,130], 1701411854966330083648828504206359986454, 1, 0, 1, 0⟩
theorem s7_851_edges : next config 7 s7_851 = [] := by decide
theorem s7_851_safe : Safe 6 7 s7_851 := by
  apply safe_succ 5 7 s7_851 [] (by decide) s7_851_edges
  simp
def s7_852 : State := ⟨[104,4,67,131], 3062541322650083937502326933924842897694, 1, 0, 1, 0⟩
theorem s7_852_edges : next config 7 s7_852 = [] := by decide
theorem s7_852_safe : Safe 6 7 s7_852 := by
  apply safe_succ 5 7 s7_852 [] (by decide) s7_852_edges
  simp
def s7_853 : State := ⟨[104,4,67,132], 5784800258017591645209323793378988589342, 1, 0, 1, 0⟩
theorem s7_853_edges : next config 7 s7_853 = [] := by decide
theorem s7_853_safe : Safe 6 7 s7_853 := by
  apply safe_succ 5 7 s7_853 [] (by decide) s7_853_edges
  simp
def s7_854 : State := ⟨[104,4,67,132], 5784800258017591645209323793387578523926, 1, 0, 1, 0⟩
theorem s7_854_edges : next config 7 s7_854 = [] := by decide
theorem s7_854_safe : Safe 6 7 s7_854 := by
  apply safe_succ 5 7 s7_854 [] (by decide) s7_854_edges
  simp
def s7_855 : State := ⟨[104,4,67,136], 87452568319042822876419229577003359338782, 1, 0, 1, 0⟩
theorem s7_855_edges : next config 7 s7_855 = [] := by decide
theorem s7_855_safe : Safe 6 7 s7_855 := by
  apply safe_succ 5 7 s7_855 [] (by decide) s7_855_edges
  simp
def s7_856 : State := ⟨[104,4,67,136], 87452568319042822876419229577011949273366, 1, 0, 1, 0⟩
theorem s7_856_edges : next config 7 s7_856 = [] := by decide
theorem s7_856_safe : Safe 6 7 s7_856 := by
  apply safe_succ 5 7 s7_856 [] (by decide) s7_856_edges
  simp
def s7_857 : State := ⟨[104,4,67,140], 1399581375166181537991191715825105489690910, 1, 0, 1, 0⟩
theorem s7_857_edges : next config 7 s7_857 = [] := by decide
theorem s7_857_safe : Safe 6 7 s7_857 := by
  apply safe_succ 5 7 s7_857 [] (by decide) s7_857_edges
  simp
def s7_858 : State := ⟨[104,4,67,140], 1481249143227206769222401621608729860440350, 1, 0, 1, 0⟩
theorem s7_858_edges : next config 7 s7_858 = [] := by decide
theorem s7_858_safe : Safe 6 7 s7_858 := by
  apply safe_succ 5 7 s7_858 [] (by decide) s7_858_edges
  simp
def s7_859 : State := ⟨[104,4,67,144], 22301085480917905717765513602722832203186462, 1, 0, 1, 0⟩
theorem s7_859_edges : next config 7 s7_859 = [] := by decide
theorem s7_859_safe : Safe 6 7 s7_859 := by
  apply safe_succ 5 7 s7_859 [] (by decide) s7_859_edges
  simp
def s7_860 : State := ⟨[104,4,67,144], 22301085480917905717765513602722840793121046, 1, 0, 1, 0⟩
theorem s7_860_edges : next config 7 s7_860 = [] := by decide
theorem s7_860_safe : Safe 6 7 s7_860 := by
  apply safe_succ 5 7 s7_860 [] (by decide) s7_860_edges
  simp
def s7_861 : State := ⟨[104,4,67,145], 44602511244182291508065644360248463701639454, 1, 0, 1, 0⟩
theorem s7_861_edges : next config 7 s7_861 = [s8_399] := by decide
theorem s7_861_safe : Safe 6 7 s7_861 := by
  apply safe_succ 5 7 s7_861 [s8_399] (by decide) s7_861_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_399_safe
def s7_862 : State := ⟨[104,4,67,145], 44602511244182370736228158624577261152567582, 1, 0, 1, 0⟩
theorem s7_862_edges : next config 7 s7_862 = [s8_322, s8_430] := by decide
theorem s7_862_safe : Safe 6 7 s7_862 := by
  apply safe_succ 5 7 s7_862 [s8_322, s8_430] (by decide) s7_862_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_322_safe
  · subst z; exact s8_430_safe
def s7_863 : State := ⟨[104,4,67,145], 66902575877979072772674435883681961671196958, 1, 0, 1, 0⟩
theorem s7_863_edges : next config 7 s7_863 = [s8_401] := by decide
theorem s7_863_safe : Safe 6 7 s7_863 := by
  apply safe_succ 5 7 s7_863 [s8_401] (by decide) s7_863_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_401_safe
def s7_864 : State := ⟨[104,4,67,145], 66902575877979152000836950148010759122125086, 1, 0, 1, 0⟩
theorem s7_864_edges : next config 7 s7_864 = [s8_324, s8_431] := by decide
theorem s7_864_safe : Safe 6 7 s7_864 := by
  apply safe_succ 5 7 s7_864 [s8_324, s8_431] (by decide) s7_864_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_324_safe
  · subst z; exact s8_431_safe
def s7_865 : State := ⟨[104,4,67,160], 1461501637671185305486261062511613094126629749022, 1, 0, 1, 0⟩
theorem s7_865_edges : next config 7 s7_865 = [] := by decide
theorem s7_865_safe : Safe 6 7 s7_865 := by
  apply safe_succ 5 7 s7_865 [] (by decide) s7_865_edges
  simp
def s7_866 : State := ⟨[104,4,67,160], 1461501637671185305486261062511613094135219683606, 1, 0, 1, 0⟩
theorem s7_866_edges : next config 7 s7_866 = [] := by decide
theorem s7_866_safe : Safe 6 7 s7_866 := by
  apply safe_succ 5 7 s7_866 [] (by decide) s7_866_edges
  simp
def s7_867 : State := ⟨[104,4,67,161], 2923003275002088223689945895227896113791152226582, 1, 0, 1, 0⟩
theorem s7_867_edges : next config 7 s7_867 = [] := by decide
theorem s7_867_safe : Safe 6 7 s7_867 := by
  apply safe_succ 5 7 s7_867 [] (by decide) s7_867_edges
  simp
def s7_868 : State := ⟨[104,4,67,163], 11692013098987505732912054891525594231718157549854, 1, 0, 1, 0⟩
theorem s7_868_edges : next config 7 s7_868 = [] := by decide
theorem s7_868_safe : Safe 6 7 s7_868 := by
  apply safe_succ 5 7 s7_868 [] (by decide) s7_868_edges
  simp
def s7_869 : State := ⟨[104,4,67,163], 11692013098987505732912054891525594231726747484438, 1, 0, 1, 0⟩
theorem s7_869_edges : next config 7 s7_869 = [] := by decide
theorem s7_869_safe : Safe 6 7 s7_869 := by
  apply safe_succ 5 7 s7_869 [] (by decide) s7_869_edges
  simp
def s7_870 : State := ⟨[104,4,67,171], 2993155353254029458868429113632742954329820545220894, 1, 0, 1, 0⟩
theorem s7_870_edges : next config 7 s7_870 = [] := by decide
theorem s7_870_safe : Safe 6 7 s7_870 := by
  apply safe_succ 5 7 s7_870 [] (by decide) s7_870_edges
  simp
def s7_871 : State := ⟨[104,4,67,171], 2993155353254029458868429113632742954329829135155478, 1, 0, 1, 0⟩
theorem s7_871_edges : next config 7 s7_871 = [] := by decide
theorem s7_871_safe : Safe 6 7 s7_871 := by
  apply safe_succ 5 7 s7_871 [] (by decide) s7_871_edges
  simp
def s7_872 : State := ⟨[104,4,67,171], 2993155353341141744800189360279366853823557114331422, 1, 0, 1, 0⟩
theorem s7_872_edges : next config 7 s7_872 = [] := by decide
theorem s7_872_safe : Safe 6 7 s7_872 := by
  apply safe_succ 5 7 s7_872 [] (by decide) s7_872_edges
  simp
def s7_873 : State := ⟨[104,4,67,171], 3004847366352676682214058592294473218478271912542494, 1, 0, 1, 0⟩
theorem s7_873_edges : next config 7 s7_873 = [] := by decide
theorem s7_873_safe : Safe 6 7 s7_873 := by
  apply safe_succ 5 7 s7_873 [] (by decide) s7_873_edges
  simp
def s7_874 : State := ⟨[104,4,67,171], 50216816876248799364715774254090444961561797876736728301854, 1, 0, 1, 0⟩
theorem s7_874_edges : next config 7 s7_874 = [] := by decide
theorem s7_874_safe : Safe 6 7 s7_874 := by
  apply safe_succ 5 7 s7_874 [] (by decide) s7_874_edges
  simp
def s7_875 : State := ⟨[104,4,67,171], 6901746346790563790427911215531054911319538085803129509483548675997982, 1, 0, 1, 0⟩
theorem s7_875_edges : next config 7 s7_875 = [] := by decide
theorem s7_875_safe : Safe 6 7 s7_875 := by
  apply safe_succ 5 7 s7_875 [] (by decide) s7_875_edges
  simp
def s7_876 : State := ⟨[104,4,67,192], 6277101735386680764176071810490242645897685518934731718942, 1, 0, 1, 0⟩
theorem s7_876_edges : next config 7 s7_876 = [] := by decide
theorem s7_876_safe : Safe 6 7 s7_876 := by
  apply safe_succ 5 7 s7_876 [] (by decide) s7_876_edges
  simp
def s7_877 : State := ⟨[104,4,67,192], 6277101735386680764176071810490242645897685518943321653526, 1, 0, 1, 0⟩
theorem s7_877_edges : next config 7 s7_877 = [] := by decide
theorem s7_877_safe : Safe 6 7 s7_877 := by
  apply safe_succ 5 7 s7_877 [] (by decide) s7_877_edges
  simp
def s7_878 : State := ⟨[104,4,67,195], 50216813883093446111026597772943907558614173630182973309214, 1, 0, 1, 0⟩
theorem s7_878_edges : next config 7 s7_878 = [] := by decide
theorem s7_878_safe : Safe 6 7 s7_878 := by
  apply safe_succ 5 7 s7_878 [] (by decide) s7_878_edges
  simp
def s7_879 : State := ⟨[104,4,67,195], 50216813883093446111026597772943907558614173630191563243798, 1, 0, 1, 0⟩
theorem s7_879_edges : next config 7 s7_879 = [] := by decide
theorem s7_879_safe : Safe 6 7 s7_879 := by
  apply safe_succ 5 7 s7_879 [] (by decide) s7_879_edges
  simp
def s7_880 : State := ⟨[104,4,67,224], 26959946667150639794667015087359913060919720652335902555574307455262, 1, 0, 1, 0⟩
theorem s7_880_edges : next config 7 s7_880 = [] := by decide
theorem s7_880_safe : Safe 6 7 s7_880 := by
  apply safe_succ 5 7 s7_880 [] (by decide) s7_880_edges
  simp
def s7_881 : State := ⟨[104,4,67,224], 26959946667150639794667015087359913060919720652335902555582897389846, 1, 0, 1, 0⟩
theorem s7_881_edges : next config 7 s7_881 = [] := by decide
theorem s7_881_safe : Safe 6 7 s7_881 := by
  apply safe_succ 5 7 s7_881 [] (by decide) s7_881_edges
  simp
def s7_882 : State := ⟨[104,4,67,232], 6901746346790563787434755862277365734838391548400181885236994921005342, 1, 0, 1, 0⟩
theorem s7_882_edges : next config 7 s7_882 = [] := by decide
theorem s7_882_safe : Safe 6 7 s7_882 := by
  apply safe_succ 5 7 s7_882 [] (by decide) s7_882_edges
  simp
def s7_883 : State := ⟨[104,4,67,232], 6901746346790563787434755862277365734838391548400181885237003510939926, 1, 0, 1, 0⟩
theorem s7_883_edges : next config 7 s7_883 = [] := by decide
theorem s7_883_safe : Safe 6 7 s7_883 := by
  apply safe_succ 5 7 s7_883 [] (by decide) s7_883_edges
  simp
def s7_884 : State := ⟨[104,12,67,129], 1020847121124453156722079280538140610846, 3, 0, 1, 0⟩
theorem s7_884_edges : next config 7 s7_884 = [s8_410, s8_430] := by decide
theorem s7_884_safe : Safe 6 7 s7_884 := by
  apply safe_succ 5 7 s7_884 [s8_410, s8_430] (by decide) s7_884_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_410_safe
  · subst z; exact s8_430_safe
def s7_885 : State := ⟨[104,12,67,130], 1701411854966330083648828495401677033758, 3, 0, 1, 0⟩
theorem s7_885_edges : next config 7 s7_885 = [s8_411] := by decide
theorem s7_885_safe : Safe 6 7 s7_885 := by
  apply safe_succ 5 7 s7_885 [s8_411] (by decide) s7_885_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_411_safe
def s7_886 : State := ⟨[104,12,67,131], 3062541322650083937502326925128749879582, 3, 0, 1, 0⟩
theorem s7_886_edges : next config 7 s7_886 = [s8_412] := by decide
theorem s7_886_safe : Safe 6 7 s7_886 := by
  apply safe_succ 5 7 s7_886 [s8_412] (by decide) s7_886_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_412_safe
def s7_887 : State := ⟨[104,12,67,132], 5784800258017591645209323784582895571230, 3, 0, 1, 0⟩
theorem s7_887_edges : next config 7 s7_887 = [s8_413] := by decide
theorem s7_887_safe : Safe 6 7 s7_887 := by
  apply safe_succ 5 7 s7_887 [s8_413] (by decide) s7_887_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_413_safe
def s7_888 : State := ⟨[104,12,67,136], 87452568319042822876419229568207266320670, 3, 0, 1, 0⟩
theorem s7_888_edges : next config 7 s7_888 = [s8_414] := by decide
theorem s7_888_safe : Safe 6 7 s7_888 := by
  apply safe_succ 5 7 s7_888 [s8_414] (by decide) s7_888_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_414_safe
def s7_889 : State := ⟨[104,12,67,140], 1394136857295446522575777722106197198311710, 3, 0, 1, 0⟩
theorem s7_889_edges : next config 7 s7_889 = [s8_416] := by decide
theorem s7_889_safe : Safe 6 7 s7_889 := by
  apply safe_succ 5 7 s7_889 [s8_416] (by decide) s7_889_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_416_safe
def s7_890 : State := ⟨[104,12,67,144], 22301085480917905717765513602714036110168350, 3, 0, 1, 0⟩
theorem s7_890_edges : next config 7 s7_890 = [s8_417] := by decide
theorem s7_890_safe : Safe 6 7 s7_890 := by
  apply safe_succ 5 7 s7_890 [s8_417] (by decide) s7_890_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_417_safe
def s7_891 : State := ⟨[104,12,67,160], 1461501637671185305486261062511613085330536730910, 3, 0, 1, 0⟩
theorem s7_891_edges : next config 7 s7_891 = [s8_424] := by decide
theorem s7_891_safe : Safe 6 7 s7_891 := by
  apply safe_succ 5 7 s7_891 [s8_424] (by decide) s7_891_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_424_safe
def s7_892 : State := ⟨[104,12,67,163], 11692013098987505732912054891525594222922064531742, 3, 0, 1, 0⟩
theorem s7_892_edges : next config 7 s7_892 = [s8_425] := by decide
theorem s7_892_safe : Safe 6 7 s7_892 := by
  apply safe_succ 5 7 s7_892 [s8_425] (by decide) s7_892_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_425_safe
def s7_893 : State := ⟨[104,12,67,192], 6277101735386680764176071810490242645897685510138638700830, 3, 0, 1, 0⟩
theorem s7_893_edges : next config 7 s7_893 = [s8_426] := by decide
theorem s7_893_safe : Safe 6 7 s7_893 := by
  apply safe_succ 5 7 s7_893 [s8_426] (by decide) s7_893_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_426_safe
def s7_894 : State := ⟨[104,12,67,195], 50216813883093446111026597772943907558614173621386880291102, 3, 0, 1, 0⟩
theorem s7_894_edges : next config 7 s7_894 = [s8_427] := by decide
theorem s7_894_safe : Safe 6 7 s7_894 := by
  apply safe_succ 5 7 s7_894 [s8_427] (by decide) s7_894_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_427_safe
def s7_895 : State := ⟨[104,12,67,224], 26959946667150639794667015087359913060919720652335902546778214437150, 3, 0, 1, 0⟩
theorem s7_895_edges : next config 7 s7_895 = [s8_428] := by decide
theorem s7_895_safe : Safe 6 7 s7_895 := by
  apply safe_succ 5 7 s7_895 [s8_428] (by decide) s7_895_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_428_safe
def s7_896 : State := ⟨[104,12,67,232], 6901746346790563787434755862277365734838391548400181885228198827987230, 3, 0, 1, 0⟩
theorem s7_896_edges : next config 7 s7_896 = [s8_429] := by decide
theorem s7_896_safe : Safe 6 7 s7_896 := by
  apply safe_succ 5 7 s7_896 [s8_429] (by decide) s7_896_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_429_safe
def s7_897 : State := ⟨[104,140,67,136], 1481249143227206769222401621608729860440350, 3, 0, 1, 0⟩
theorem s7_897_edges : next config 7 s7_897 = [s8_415] := by decide
theorem s7_897_safe : Safe 6 7 s7_897 := by
  apply safe_succ 5 7 s7_897 [s8_415] (by decide) s7_897_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_415_safe
def s7_898 : State := ⟨[113,4,104,145], 44601830689833122576370739558470766238564638, 1, 1, 1, 0⟩
theorem s7_898_edges : next config 7 s7_898 = [s8_436] := by decide
theorem s7_898_safe : Safe 6 7 s7_898 := by
  apply safe_succ 5 7 s7_898 [s8_436] (by decide) s7_898_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_436_safe
def s7_899 : State := ⟨[113,4,104,145], 44601830689833122576370739558470766238568726, 3, 2, 1, 0⟩
theorem s7_899_edges : next config 7 s7_899 = [] := by decide
theorem s7_899_safe : Safe 6 7 s7_899 := by
  apply safe_succ 5 7 s7_899 [] (by decide) s7_899_edges
  simp
def s7_900 : State := ⟨[113,4,104,145], 44601830689833122576370739558470766240661782, 3, 2, 1, 0⟩
theorem s7_900_edges : next config 7 s7_900 = [s8_437] := by decide
theorem s7_900_safe : Safe 6 7 s7_900 := by
  apply safe_succ 5 7 s7_900 [s8_437] (by decide) s7_900_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_437_safe
def s7_901 : State := ⟨[113,4,104,145], 44601830689833122576370776451958913657667862, 1, 1, 1, 0⟩
theorem s7_901_edges : next config 7 s7_901 = [s8_438] := by decide
theorem s7_901_safe : Safe 6 7 s7_901 := by
  apply safe_succ 5 7 s7_901 [s8_438] (by decide) s7_901_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_438_safe
def s7_902 : State := ⟨[113,12,96,145], 44601830689812840166767087888046818987282718, 3, 1, 1, 0⟩
theorem s7_902_edges : next config 7 s7_902 = [s8_432, s8_436] := by decide
theorem s7_902_safe : Safe 6 7 s7_902 := by
  apply safe_succ 5 7 s7_902 [s8_432, s8_436] (by decide) s7_902_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_432_safe
  · subst z; exact s8_436_safe
def s7_903 : State := ⟨[113,12,96,145], 44601830689812840166767087888046818989379862, 3, 2, 1, 0⟩
theorem s7_903_edges : next config 7 s7_903 = [s8_437] := by decide
theorem s7_903_safe : Safe 6 7 s7_903 := by
  apply safe_succ 5 7 s7_903 [s8_437] (by decide) s7_903_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_437_safe
def s7_904 : State := ⟨[113,12,96,145], 44601830689812840166767124781534966406385942, 3, 1, 1, 0⟩
theorem s7_904_edges : next config 7 s7_904 = [s8_434, s8_438] := by decide
theorem s7_904_safe : Safe 6 7 s7_904 := by
  apply safe_succ 5 7 s7_904 [s8_434, s8_438] (by decide) s7_904_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_434_safe
  · subst z; exact s8_438_safe
def s7_905 : State := ⟨[113,21,96,145], 44601830689812840166767087888046818989375774, 3, 1, 1, 0⟩
theorem s7_905_edges : next config 7 s7_905 = [s8_439] := by decide
theorem s7_905_safe : Safe 6 7 s7_905 := by
  apply safe_succ 5 7 s7_905 [s8_439] (by decide) s7_905_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_439_safe
def s7_906 : State := ⟨[113,21,96,145], 44601830689812840166767087888046818989379862, 3, 2, 1, 0⟩
theorem s7_906_edges : next config 7 s7_906 = [s8_440] := by decide
theorem s7_906_safe : Safe 6 7 s7_906 := by
  apply safe_succ 5 7 s7_906 [s8_440] (by decide) s7_906_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_440_safe
def s7_907 : State := ⟨[113,21,96,145], 44601830689812840166767124781534966408478998, 3, 1, 1, 0⟩
theorem s7_907_edges : next config 7 s7_907 = [s8_441] := by decide
theorem s7_907_safe : Safe 6 7 s7_907 := by
  apply safe_succ 5 7 s7_907 [s8_441] (by decide) s7_907_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_441_safe
def s7_908 : State := ⟨[113,21,125,145], 44601873225128987693678672480296695211688214, 3, 0, 1, 0⟩
theorem s7_908_edges : next config 7 s7_908 = [] := by decide
theorem s7_908_safe : Safe 6 7 s7_908 := by
  apply safe_succ 5 7 s7_908 [] (by decide) s7_908_edges
  simp
def s7_909 : State := ⟨[113,125,104,145], 44601873225128987693678672480296695211688214, 3, 0, 1, 0⟩
theorem s7_909_edges : next config 7 s7_909 = [] := by decide
theorem s7_909_safe : Safe 6 7 s7_909 := by
  apply safe_succ 5 7 s7_909 [] (by decide) s7_909_edges
  simp
def s7_910 : State := ⟨[117,4,96,145], 44601830845581745922811916743961708865978654, 1, 1, 1, 0⟩
theorem s7_910_edges : next config 7 s7_910 = [s8_442] := by decide
theorem s7_910_safe : Safe 6 7 s7_910 := by
  apply safe_succ 5 7 s7_910 [s8_442] (by decide) s7_910_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_442_safe
def s7_911 : State := ⟨[117,4,96,145], 44601830845581745922811953637449856285081878, 1, 1, 1, 0⟩
theorem s7_911_edges : next config 7 s7_911 = [s8_443] := by decide
theorem s7_911_safe : Safe 6 7 s7_911 := by
  apply safe_succ 5 7 s7_911 [s8_443] (by decide) s7_911_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_443_safe
def s7_912 : State := ⟨[121,4,104,145], 44601833337904520429132830109023894140813598, 1, 1, 1, 0⟩
theorem s7_912_edges : next config 7 s7_912 = [] := by decide
theorem s7_912_safe : Safe 6 7 s7_912 := by
  apply safe_succ 5 7 s7_912 [] (by decide) s7_912_edges
  simp
def s7_913 : State := ⟨[121,4,104,145], 44601833337904520429132830109023894142910742, 3, 2, 1, 0⟩
theorem s7_913_edges : next config 7 s7_913 = [] := by decide
theorem s7_913_safe : Safe 6 7 s7_913 := by
  apply safe_succ 5 7 s7_913 [] (by decide) s7_913_edges
  simp
def s7_914 : State := ⟨[121,4,104,145], 44601833337904520429132867002512041559916822, 1, 1, 1, 0⟩
theorem s7_914_edges : next config 7 s7_914 = [] := by decide
theorem s7_914_safe : Safe 6 7 s7_914 := by
  apply safe_succ 5 7 s7_914 [] (by decide) s7_914_edges
  simp
def s7_915 : State := ⟨[125,12,104,145], 44601873214744393976609017223235702553252118, 3, 0, 1, 0⟩
theorem s7_915_edges : next config 7 s7_915 = [s8_447] := by decide
theorem s7_915_safe : Safe 6 7 s7_915 := by
  apply safe_succ 5 7 s7_915 [s8_447] (by decide) s7_915_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_447_safe
def s7_916 : State := ⟨[131,4,104,146], 89207404464912826403934081341995677810495766, 3, 2, 1, 0⟩
theorem s7_916_edges : next config 7 s7_916 = [] := by decide
theorem s7_916_safe : Safe 6 7 s7_916 := by
  apply safe_succ 5 7 s7_916 [] (by decide) s7_916_edges
  simp
def s7_917 : State := ⟨[131,4,104,162], 5846006553747282463148577122073383480855516746006, 3, 2, 1, 0⟩
theorem s7_917_edges : next config 7 s7_917 = [] := by decide
theorem s7_917_safe : Safe 6 7 s7_917 := by
  apply safe_succ 5 7 s7_917 [] (by decide) s7_917_edges
  simp
def s7_918 : State := ⟨[146,4,64,145], 133804811473550659787677791457241678808813854, 3, 3, 1, 0⟩
theorem s7_918_edges : next config 7 s7_918 = [s8_453] := by decide
theorem s7_918_safe : Safe 6 7 s7_918 := by
  apply safe_succ 5 7 s7_918 [s8_453] (by decide) s7_918_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_453_safe
def s7_919 : State := ⟨[146,4,64,145], 133804811473550659787677791457241678810906910, 3, 3, 1, 0⟩
theorem s7_919_edges : next config 7 s7_919 = [s8_457, s8_454] := by decide
theorem s7_919_safe : Safe 6 7 s7_919 := by
  apply safe_succ 5 7 s7_919 [s8_457, s8_454] (by decide) s7_919_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_457_safe
  · subst z; exact s8_454_safe
def s7_920 : State := ⟨[146,4,67,145], 133805492038284501664604865780409132021518622, 3, 2, 1, 0⟩
theorem s7_920_edges : next config 7 s7_920 = [] := by decide
theorem s7_920_safe : Safe 6 7 s7_920 := by
  apply safe_succ 5 7 s7_920 [] (by decide) s7_920_edges
  simp
def s7_921 : State := ⟨[146,4,67,145], 156105556672081282929213657303842629991076126, 3, 2, 1, 0⟩
theorem s7_921_edges : next config 7 s7_921 = [] := by decide
theorem s7_921_safe : Safe 6 7 s7_921 := by
  apply safe_succ 5 7 s7_921 [] (by decide) s7_921_edges
  simp
def s7_922 : State := ⟨[146,4,96,145], 133805492038284580892767232470794135889056030, 3, 2, 1, 0⟩
theorem s7_922_edges : next config 7 s7_922 = [s8_455] := by decide
theorem s7_922_safe : Safe 6 7 s7_922 := by
  apply safe_succ 5 7 s7_922 [s8_455] (by decide) s7_922_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_455_safe
def s7_923 : State := ⟨[146,4,96,145], 156105556672081362157376023994227633858613534, 3, 2, 1, 0⟩
theorem s7_923_edges : next config 7 s7_923 = [s8_456] := by decide
theorem s7_923_safe : Safe 6 7 s7_923 := by
  apply safe_succ 5 7 s7_923 [s8_456] (by decide) s7_923_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_456_safe
def s7_924 : State := ⟨[146,4,104,145], 133804811473571021425443957392003219604046110, 1, 1, 1, 0⟩
theorem s7_924_edges : next config 7 s7_924 = [s8_458] := by decide
theorem s7_924_safe : Safe 6 7 s7_924 := by
  apply safe_succ 5 7 s7_924 [s8_458] (by decide) s7_924_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_458_safe
def s7_925 : State := ⟨[146,12,67,145], 133804811473550659787677939031194268485226782, 3, 1, 1, 0⟩
theorem s7_925_edges : next config 7 s7_925 = [s8_451] := by decide
theorem s7_925_safe : Safe 6 7 s7_925 := by
  apply safe_succ 5 7 s7_925 [s8_451] (by decide) s7_925_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_451_safe
def s7_926 : State := ⟨[146,12,96,145], 133804811473550739015840305721579272352764190, 3, 1, 1, 0⟩
theorem s7_926_edges : next config 7 s7_926 = [s8_453, s8_458] := by decide
theorem s7_926_safe : Safe 6 7 s7_926 := by
  apply safe_succ 5 7 s7_926 [s8_453, s8_458] (by decide) s7_926_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s8_453_safe
  · subst z; exact s8_458_safe
def s7_927 : State := ⟨[146,12,104,145], 133805492038304863302370884141218083140342046, 3, 0, 1, 0⟩
theorem s7_927_edges : next config 7 s7_927 = [s8_455] := by decide
theorem s7_927_safe : Safe 6 7 s7_927 := by
  apply safe_succ 5 7 s7_927 [s8_455] (by decide) s7_927_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_455_safe
def s7_928 : State := ⟨[146,12,104,145], 156105556672101644566979675664651581109899550, 3, 0, 1, 0⟩
theorem s7_928_edges : next config 7 s7_928 = [s8_456] := by decide
theorem s7_928_safe : Safe 6 7 s7_928 := by
  apply safe_succ 5 7 s7_928 [s8_456] (by decide) s7_928_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_456_safe
def s7_929 : State := ⟨[146,21,67,145], 133804811473550659787677939031194268487319838, 3, 1, 1, 0⟩
theorem s7_929_edges : next config 7 s7_929 = [s8_461] := by decide
theorem s7_929_safe : Safe 6 7 s7_929 := by
  apply safe_succ 5 7 s7_929 [s8_461] (by decide) s7_929_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_461_safe
def s7_930 : State := ⟨[146,21,96,145], 133804811473550739015840305721579272354857246, 3, 1, 1, 0⟩
theorem s7_930_edges : next config 7 s7_930 = [s8_460] := by decide
theorem s7_930_safe : Safe 6 7 s7_930 := by
  apply safe_succ 5 7 s7_930 [s8_460] (by decide) s7_930_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_460_safe
def s7_931 : State := ⟨[163,4,104,130], 11692013100348635200595808745231518700033691160854, 3, 2, 1, 0⟩
theorem s7_931_edges : next config 7 s7_931 = [] := by decide
theorem s7_931_safe : Safe 6 7 s7_931 := by
  apply safe_succ 5 7 s7_931 [] (by decide) s7_931_edges
  simp
def s7_932 : State := ⟨[163,4,104,130], 11692013103070894135963316452938515559479246917910, 3, 2, 1, 0⟩
theorem s7_932_edges : next config 7 s7_932 = [] := by decide
theorem s7_932_safe : Safe 6 7 s7_932 := by
  apply safe_succ 5 7 s7_932 [] (by decide) s7_932_edges
  simp
def s7_933 : State := ⟨[163,4,104,160], 13153514736318408651115739724094303289953960923422, 3, 2, 1, 0⟩
theorem s7_933_edges : next config 7 s7_933 = [] := by decide
theorem s7_933_safe : Safe 6 7 s7_933 := by
  apply safe_succ 5 7 s7_933 [] (by decide) s7_933_edges
  simp
def s7_934 : State := ⟨[163,4,104,160], 16076518010980214487523109389526869329265826009366, 3, 2, 1, 0⟩
theorem s7_934_edges : next config 7 s7_934 = [] := by decide
theorem s7_934_safe : Safe 6 7 s7_934 := by
  apply safe_succ 5 7 s7_934 [] (by decide) s7_934_edges
  simp
def s7_935 : State := ⟨[163,4,104,162], 17538019649672246873410548076096650778648831398166, 3, 2, 1, 0⟩
theorem s7_935_edges : next config 7 s7_935 = [s8_40] := by decide
theorem s7_935_safe : Safe 6 7 s7_935 := by
  apply safe_succ 5 7 s7_935 [s8_40] (by decide) s7_935_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_40_safe
def s7_936 : State := ⟨[163,4,104,162], 18999521285642020323930479054959435368577691095318, 3, 2, 1, 0⟩
theorem s7_936_edges : next config 7 s7_936 = [s8_41] := by decide
theorem s7_936_safe : Safe 6 7 s7_936 := by
  apply safe_succ 5 7 s7_936 [s8_41] (by decide) s7_936_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s8_41_safe
def s7_937 : State := ⟨[171,4,67,195], 50216816876248799364715774254090444961561797876736728301854, 1, 0, 1, 0⟩
theorem s7_937_edges : next config 7 s7_937 = [] := by decide
theorem s7_937_safe : Safe 6 7 s7_937 := by
  apply safe_succ 5 7 s7_937 [] (by decide) s7_937_edges
  simp
end HGP13.SectorGraph234
