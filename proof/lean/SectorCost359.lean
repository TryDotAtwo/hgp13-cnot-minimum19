import SectorGraph359
import SectorTerminal359
namespace HGP13.SectorCost359
open SharedSearch SectorGraph359
set_option maxRecDepth 20000
def decode (h : Nat) : List Row :=
  ((List.range 128).filter (fun v => PackedRows.has h v)).map
    (fun v => BitVec.ofNat 13 ((v &&& 63) ||| ((v &&& 64) <<< 2)))
theorem decode0 : decode 534955578141872029974 = SectorTerminal359.history0 := by decide
theorem decode1 : decode 498062089994452926742 = SectorTerminal359.history1 := by decide
theorem decode2 : decode 239807672962519204150 = SectorTerminal359.history2 := by decide
theorem decode3 : decode 239807672962520252694 = SectorTerminal359.history3 := by decide
theorem decode4 : decode 202914184815101149462 = SectorTerminal359.history4 := by decide
theorem decode5 : decode 239807672962519208214 = SectorTerminal359.history5 := by decide
theorem decode6 : decode 239807672962519204182 = SectorTerminal359.history6 := by decide
theorem decode7 : decode 2600990914397341810966 = SectorTerminal359.history7 := by decide
theorem decode8 : decode 239807673031238680854 = SectorTerminal359.history8 := by decide
theorem decode9 : decode 793209995173805752598 = SectorTerminal359.history9 := by decide
theorem decode10 : decode 202914184883819577622 = SectorTerminal359.history10 := by decide
theorem decode11 : decode 202914184815100100950 = SectorTerminal359.history11 := by decide
theorem decode12 : decode 1420399293679930507542 = SectorTerminal359.history12 := by decide
theorem decode13 : decode 202914184815100104982 = SectorTerminal359.history13 := by decide
theorem decode14 : decode 2564097426249922707734 = SectorTerminal359.history14 := by decide
theorem decode15 : decode 202914184815100100918 = SectorTerminal359.history15 := by decide
theorem decode16 : decode 1346878762945407923905347256598 = SectorTerminal359.history16 := by decide
theorem decode17 : decode 1346878762982301412052766359830 = SectorTerminal359.history17 := by decide
theorem decode18 : decode 2297616713079686486880455557398 = SectorTerminal359.history18 := by decide
theorem decode19 : decode 2139160388051157811693367656726 = SectorTerminal359.history19 := by decide
theorem decode20 : decode 79228162754072010556063158550 = SectorTerminal359.history20 := by decide
theorem decode21 : decode 91878602098384779796873494 = SectorTerminal359.history21 := by decide
theorem decode22 : decode 82207195541467746399224086 = SectorTerminal359.history22 := by decide
theorem decode23 : decode 871509787822928410196664455446 = SectorTerminal359.history23 := by decide
theorem decode24 : decode 396140812811129360930238959894 = SectorTerminal359.history24 := by decide
theorem decode25 : decode 79228162717178522408644055318 = SectorTerminal359.history25 := by decide
theorem decode26 : decode 1505335087973936599092435157270 = SectorTerminal359.history26 := by decide
theorem decode27 : decode 14507349643048512615682326 = SectorTerminal359.history27 := by decide
theorem decode28 : decode 1029966112851457085383752356118 = SectorTerminal359.history28 := by decide
theorem decode29 : decode 4835943086131479218032918 = SectorTerminal359.history29 := by decide
theorem decode30 : decode 93087454131023114133373206 = SectorTerminal359.history30 := by decide
theorem decode31 : decode 83416121361082375573930262 = SectorTerminal359.history31 := by decide
theorem decode32 : decode 1663791413039358762426942161174 = SectorTerminal359.history32 := by decide
theorem decode33 : decode 15716201675686846952182038 = SectorTerminal359.history33 := by decide
theorem decode34 : decode 6044868905746108392739094 = SectorTerminal359.history34 := by decide
theorem decode35 : decode 237684487745707197595731955990 = SectorTerminal359.history35 := by decide
theorem key_cost (depth history : Nat) (costs : Row → Nat)
    (hk : (depth,history) ∈ SectorGraph359.keys)
    (hc : ∀ z ∈ SectorTerminal359.targets, PassiveCost.cost (decode history) z = some (costs z)) :
    18 < depth + (SectorTerminal359.targets.map costs).sum := by
  simp only [SectorGraph359.keys,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes0 costs (by simpa only [decode0] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes1 costs (by simpa only [decode1] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes2 costs (by simpa only [decode2] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes3 costs (by simpa only [decode3] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes4 costs (by simpa only [decode4] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes5 costs (by simpa only [decode5] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes6 costs (by simpa only [decode6] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes7 costs (by simpa only [decode7] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes8 costs (by simpa only [decode8] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes9 costs (by simpa only [decode9] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes10 costs (by simpa only [decode10] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes11 costs (by simpa only [decode11] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes12 costs (by simpa only [decode12] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes13 costs (by simpa only [decode13] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes14 costs (by simpa only [decode14] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes15 costs (by simpa only [decode15] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes16 costs (by simpa only [decode16] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes17 costs (by simpa only [decode17] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes18 costs (by simpa only [decode18] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes19 costs (by simpa only [decode19] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes20 costs (by simpa only [decode20] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes21 costs (by simpa only [decode21] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes22 costs (by simpa only [decode22] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes23 costs (by simpa only [decode23] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes24 costs (by simpa only [decode24] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes25 costs (by simpa only [decode25] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes26 costs (by simpa only [decode26] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes27 costs (by simpa only [decode27] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes28 costs (by simpa only [decode28] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes29 costs (by simpa only [decode29] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes30 costs (by simpa only [decode30] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes31 costs (by simpa only [decode31] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes32 costs (by simpa only [decode32] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes33 costs (by simpa only [decode33] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes34 costs (by simpa only [decode34] using hc)
  · have hd := congrArg Prod.fst hk
    have hh := congrArg Prod.snd hk
    simp only [Prod.fst,Prod.snd] at hd hh
    subst depth
    subst history
    exact SectorTerminal359.excludes35 costs (by simpa only [decode35] using hc)
theorem no_cheap_terminal {k : Nat} {z : State}
    (reach : SectorGraph359.Reach 0 (initial SectorGraph359.config) k z)
    (length : k ≤ 12) (terminal : SharedSearch.terminal SectorGraph359.config z = true)
    (costs : Row → Nat)
    (hc : ∀ r ∈ SectorTerminal359.targets, PassiveCost.cost (decode z.history) r = some (costs r)) :
    18 < k + (SectorTerminal359.targets.map costs).sum :=
  key_cost k z.history costs (reachable_terminal_key reach length terminal) hc
end HGP13.SectorCost359
