import Graph234Layer0
import Sector234Potentials
namespace HGP13.SectorCost234
open SharedSearch SectorGraph234
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
def decode (h : Nat) : List Row :=
  ((List.range 256).filter (fun v => PackedRows.has h v)).map
    (fun v => Sector234Encoding.liftMask (BitVec.ofNat 8 v))
theorem decode0 : decode 44601830679428167221535102834088969880408342 = Sector234Potentials.history0 := by decide
theorem decode1 : decode 44601830679428167221535102834088969882501398 = Sector234Potentials.history1 := by decide
theorem decode2 : decode 44601830679428167221535139727577117299511574 = Sector234Potentials.history2 := by decide
theorem decode3 : decode 44601830679428167221535139727577117301604630 = Sector234Potentials.history3 := by decide
theorem decode4 : decode 44602511244162009098461992689815685997596958 = Sector234Potentials.history4 := by decide
theorem decode5 : decode 66902575877958790363070784213249183967154462 = Sector234Potentials.history5 := by decide
theorem decode6 : decode 44601830679428167226370843006035633998336278 = Sector234Potentials.history6 := by decide
theorem decode7 : decode 44601830679428167226370843006035634000429334 = Sector234Potentials.history7 := by decide
theorem decode8 : decode 44601830679428167227579695038673968334835990 = Sector234Potentials.history8 := by decide
theorem decode9 : decode 44601830679428167227579695038673968336929046 = Sector234Potentials.history9 := by decide
theorem decode10 : decode 44601830679428167303742095461371901179527446 = Sector234Potentials.history10 := by decide
theorem decode11 : decode 44601830679428167304950947494010235516027158 = Sector234Potentials.history11 := by decide
theorem decode12 : decode 133806172603018343541531792529623995557941534 = Sector234Potentials.history12 := by decide
theorem decode13 : decode 156105556672081282929213657303842629991076126 = Sector234Potentials.history13 := by decide
theorem decode14 : decode 44601830679428167303742095461371901181624598 = Sector234Potentials.history14 := by decide
theorem decode15 : decode 44601830679428167304950947494010235518124310 = Sector234Potentials.history15 := by decide
theorem key_cost (depth history : Nat) (costs : Row → Nat)
    (hk : (depth,history) ∈ SectorGraph234.keys)
    (hc : ∀ z ∈ Sector234Potentials.targets,
      PassiveCost.cost (decode history) z = some (costs z)) :
    18 < depth + (Sector234Potentials.targets.map costs).sum := by
  simp only [SectorGraph234.keys,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes0 costs (by simpa only [decode0] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes1 costs (by simpa only [decode1] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes2 costs (by simpa only [decode2] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes3 costs (by simpa only [decode3] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes4 costs (by simpa only [decode4] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes5 costs (by simpa only [decode5] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes6 costs (by simpa only [decode6] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes7 costs (by simpa only [decode7] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes8 costs (by simpa only [decode8] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes9 costs (by simpa only [decode9] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes10 costs (by simpa only [decode10] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes11 costs (by simpa only [decode11] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes12 costs (by simpa only [decode12] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes13 costs (by simpa only [decode13] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes14 costs (by simpa only [decode14] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact Sector234Potentials.excludes15 costs (by simpa only [decode15] using hc)
theorem no_cheap_terminal {k : Nat} {z : State}
    (reach : SectorGraph234.Reach 0 (initial SectorGraph234.config) k z)
    (length : k ≤ 13)
    (terminal : SharedSearch.terminal SectorGraph234.config z = true)
    (costs : Row → Nat)
    (hc : ∀ r ∈ Sector234Potentials.targets,
      PassiveCost.cost (decode z.history) r = some (costs r)) :
    18 < k + (Sector234Potentials.targets.map costs).sum :=
  key_cost k z.history costs (reachable_terminal_key reach length terminal) hc
end HGP13.SectorCost234
