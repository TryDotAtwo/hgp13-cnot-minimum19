import Graph234Base
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def s11_0 : State := ⟨[43,4,67,145], 44601830679448528859301231875371193711395102, 3, 3, 1, 0⟩
theorem s11_0_edges : next config 11 s11_0 = [] := by decide
theorem s11_0_safe : Safe 2 11 s11_0 := by
  apply safe_succ 1 11 s11_0 [] (by decide) s11_0_edges
  simp
def s11_1 : State := ⟨[43,4,67,145], 44601830679448528859301231875371202301329686, 3, 3, 1, 0⟩
theorem s11_1_edges : next config 11 s11_1 = [] := by decide
theorem s11_1_safe : Safe 2 11 s11_1 := by
  apply safe_succ 1 11 s11_1 [] (by decide) s11_1_edges
  simp
def s11_2 : State := ⟨[96,4,67,145], 44601830679448528859301231875371193711395102, 3, 3, 1, 0⟩
theorem s11_2_edges : next config 11 s11_2 = [] := by decide
theorem s11_2_safe : Safe 2 11 s11_2 := by
  apply safe_succ 1 11 s11_2 [] (by decide) s11_2_edges
  simp
def s11_3 : State := ⟨[104,4,67,145], 44601830679448528859301231875371193711395102, 3, 3, 1, 0⟩
theorem s11_3_edges : next config 11 s11_3 = [] := by decide
theorem s11_3_safe : Safe 2 11 s11_3 := by
  apply safe_succ 1 11 s11_3 [] (by decide) s11_3_edges
  simp
def s11_4 : State := ⟨[104,4,67,145], 44601830679448528859301231875371202301329686, 3, 3, 1, 0⟩
theorem s11_4_edges : next config 11 s11_4 = [] := by decide
theorem s11_4_safe : Safe 2 11 s11_4 := by
  apply safe_succ 1 11 s11_4 [] (by decide) s11_4_edges
  simp
end HGP13.SectorGraph234
