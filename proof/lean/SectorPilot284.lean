import Std
namespace HGP13.SectorPilot284
/- Experimental finite graph. Its correspondence to all short full words is OPEN.
   Transpose orientation, active sources [2,3], relay [5], depth cap 13.
   Catalogue prefix completeness and pruning soundness are NOT assumed proved. -/
structure State where
  a : Nat
  b : Nat
  c : Nat
  r : Nat
  hist : Nat
  changed : Nat
  returned : Nat
  copied : Nat
  deriving DecidableEq, Repr
inductive Tree where
  | nil
  | node (left : Tree) (key : Nat) (right : Tree)
def lookup : Tree → Nat → Bool
  | .nil, _ => false
  | .node l k r, x => if x < k then lookup l x else if x = k then true else lookup r x
def has (h v : Nat) : Bool := ((h >>> v) &&& 1) == 1
def set (h v : Nat) : Nat := h ||| (1 <<< v)
def rows (s : State) := [s.a,s.b,s.c,s.r]
def projected (h : Nat) := (h ||| (h >>> 128)) &&& ((1 <<< 128)-1)
def base := [0,1,2,4,8,16,32,64]
def goals := [21,62,104,17,50,96,67]
def want := [4,8,67,224]
def fixed := [1,2,16,32]
def passive := [21,62,104,17,50]
def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a :: r => if x ≤ a then x :: a :: r else a :: ins x r
def sort : List Nat → List Nat
  | [] => []
  | a :: r => ins a (sort r)
def encode (l : List Nat) := l.foldl (fun a b => a*128+b) 0
def prefixes : Tree := (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node .nil 0 .nil) 3 .nil) 9 (.node .nil 12 .nil)) 18 (.node (.node .nil 22 .nil) 25 (.node .nil 29 .nil))) 33 (.node (.node (.node .nil 34 .nil) 35 (.node .nil 42 .nil)) 43 (.node (.node .nil 48 .nil) 49 (.node .nil 53 .nil)))) 54 (.node (.node (.node (.node .nil 58 .nil) 65 (.node .nil 66 .nil)) 68 (.node (.node .nil 80 .nil) 81 (.node .nil 82 .nil))) 86 (.node (.node (.node .nil 97 .nil) 100 (.node .nil 108 .nil)) 112 (.node (.node .nil 113 .nil) 117 (.node .nil 120 .nil))))) 121 (.node (.node (.node (.node (.node (.node .nil 125 .nil) 396 .nil) 402 (.node .nil 406 .nil)) 409 (.node (.node .nil 413 .nil) 418 (.node .nil 419 .nil))) 427 (.node (.node (.node .nil 432 .nil) 433 (.node .nil 437 .nil)) 438 (.node (.node .nil 442 .nil) 466 (.node .nil 470 .nil)))) 484 (.node (.node (.node (.node .nil 492 .nil) 497 (.node .nil 501 .nil)) 505 (.node (.node .nil 509 .nil) 1186 (.node .nil 1195 .nil))) 1554 (.node (.node (.node .nil 1569 .nil) 1570 (.node .nil 1571 .nil)) 1579 (.node (.node .nil 1584 .nil) 1585 (.node .nil 1601 .nil)))))) 1602 (.node (.node (.node (.node (.node (.node (.node .nil 1616 .nil) 1617 .nil) 1618 (.node .nil 1622 .nil)) 1633 (.node (.node .nil 1648 .nil) 1649 (.node .nil 1661 .nil))) 2326 (.node (.node (.node .nil 2329 .nil) 2333 (.node .nil 2339 .nil)) 2347 (.node (.node .nil 2358 .nil) 2362 (.node .nil 2369 .nil)))) 2370 (.node (.node (.node (.node .nil 2372 .nil) 2385 (.node .nil 2386 .nil)) 2390 (.node (.node .nil 2404 .nil) 2412 (.node .nil 2417 .nil))) 2421 (.node (.node (.node .nil 2425 .nil) 2429 (.node .nil 2870 .nil)) 2902 (.node (.node .nil 3234 .nil) 3243 (.node .nil 3248 .nil))))) 3265 (.node (.node (.node (.node (.node (.node .nil 3266 .nil) 3745 .nil) 3746 (.node .nil 3747 .nil)) 3760 (.node (.node .nil 3777 .nil) 3778 (.node .nil 4259 .nil))) 4267 (.node (.node (.node .nil 4278 .nil) 4282 (.node .nil 4310 .nil)) 4349 (.node (.node .nil 4387 .nil) 4394 (.node .nil 4395 .nil)))) 4406 (.node (.node (.node (.node .nil 4410 .nil) 4417 (.node .nil 4418 .nil)) 4434 (.node (.node .nil 4438 .nil) 4449 (.node .nil 4452 .nil))) 4460 (.node (.node (.node .nil 4465 .nil) 4469 (.node .nil 4473 .nil)) 4477 (.node (.node .nil 4523 .nil) 4528 (.node .nil 4534 .nil))))))) 4538 (.node (.node (.node (.node (.node (.node (.node (.node .nil 4545 .nil) 4546 .nil) 4566 (.node .nil 4605 .nil)) 5419 (.node (.node .nil 5434 .nil) 5442 (.node .nil 5552 .nil))) 5553 (.node (.node (.node .nil 5558 .nil) 5562 (.node .nil 5569 .nil)) 5570 (.node (.node .nil 5584 .nil) 5585 (.node .nil 5586 .nil)))) 5601 (.node (.node (.node (.node .nil 5616 .nil) 5617 (.node .nil 6198 .nil)) 6202 (.node (.node .nil 6209 .nil) 6210 (.node .nil 6226 .nil))) 6230 (.node (.node (.node .nil 6244 .nil) 6252 (.node .nil 6257 .nil)) 6261 (.node (.node .nil 6265 .nil) 6269 (.node .nil 6326 .nil))))) 6330 (.node (.node (.node (.node (.node (.node .nil 6358 .nil) 6397 .nil) 6838 (.node .nil 6977 .nil)) 6978 (.node (.node .nil 6992 .nil) 6993 (.node .nil 6994 .nil))) 6998 (.node (.node (.node .nil 7009 .nil) 7024 (.node .nil 7025 .nil)) 7029 (.node (.node .nil 7037 .nil) 7489 (.node .nil 7490 .nil)))) 7504 (.node (.node (.node (.node .nil 7505 .nil) 7506 (.node .nil 7510 .nil)) 7521 (.node (.node .nil 7536 .nil) 7537 (.node .nil 7544 .nil))) 7545 (.node (.node (.node .nil 7549 .nil) 8402 (.node .nil 8406 .nil)) 8420 (.node (.node .nil 8428 .nil) 8433 (.node .nil 8437 .nil)))))) 8441 (.node (.node (.node (.node (.node (.node (.node .nil 8445 .nil) 8530 .nil) 8534 (.node .nil 8548 .nil)) 8556 (.node (.node .nil 8560 .nil) 8561 (.node .nil 8565 .nil))) 8568 (.node (.node (.node .nil 8569 .nil) 8573 (.node .nil 8790 .nil)) 10322 (.node (.node .nil 10326 .nil) 10348 (.node .nil 10365 .nil)))) 10454 (.node (.node (.node (.node .nil 10493 .nil) 10582 (.node .nil 10604 .nil)) 10621 (.node (.node .nil 11105 .nil) 11108 (.node .nil 11120 .nil))) 11121 (.node (.node (.node .nil 12541 .nil) 14461 (.node .nil 14589 .nil)) 50706 (.node (.node .nil 50722 .nil) 50723 (.node .nil 50731 .nil))))) 50736 (.node (.node (.node (.node (.node .nil 50737 .nil) 50770 (.node .nil 50774 .nil)) 50801 (.node (.node .nil 50813 .nil) 51499 (.node .nil 51510 .nil))) 51514 (.node (.node (.node .nil 51542 .nil) 51581 (.node .nil 52022 .nil)) 52395 (.node (.node .nil 52899 .nil) 53547 (.node .nil 53558 .nil)))) 53562 (.node (.node (.node (.node .nil 53590 .nil) 53629 (.node .nil 53675 .nil)) 53686 (.node (.node .nil 53690 .nil) 53718 (.node .nil 53757 .nil))) 54704 (.node (.node (.node .nil 54705 .nil) 54710 (.node .nil 54714 .nil)) 54738 (.node (.node .nil 54769 .nil) 55350 (.node .nil 55354 .nil)))))))) 55382 (.node (.node (.node (.node (.node (.node (.node (.node (.node .nil 55421 .nil) 55478 .nil) 55482 (.node .nil 55510 .nil)) 55549 (.node (.node .nil 55990 .nil) 56146 (.node .nil 56150 .nil))) 56177 (.node (.node (.node .nil 56181 .nil) 56189 (.node .nil 56658 .nil)) 56662 (.node (.node .nil 56689 .nil) 56697 (.node .nil 56701 .nil)))) 59734 (.node (.node (.node (.node .nil 59756 .nil) 59773 (.node .nil 60260 .nil)) 60273 (.node (.node .nil 63741 .nil) 151851 (.node .nil 198947 .nil))) 198955 (.node (.node (.node .nil 198977 .nil) 198978 (.node .nil 198993 .nil)) 198994 (.node (.node .nil 198998 .nil) 199025 (.node .nil 199037 .nil))))) 200867 (.node (.node (.node (.node (.node (.node .nil 200995 .nil) 201003 .nil) 201025 (.node .nil 201026 .nil)) 201042 (.node (.node .nil 201046 .nil) 201057 (.node .nil 201073 .nil))) 201085 (.node (.node (.node .nil 201136 .nil) 201153 (.node .nil 201154 .nil)) 202160 (.node (.node .nil 202177 .nil) 202178 (.node .nil 202817 .nil)))) 202818 (.node (.node (.node (.node .nil 202834 .nil) 202838 (.node .nil 202865 .nil)) 202877 (.node (.node .nil 205010 .nil) 205014 (.node .nil 205041 .nil))) 205053 (.node (.node (.node .nil 205138 .nil) 205142 (.node .nil 205168 .nil)) 205169 (.node (.node .nil 205181 .nil) 206930 (.node .nil 297814 .nil)))))) 298155 (.node (.node (.node (.node (.node (.node (.node .nil 298659 .nil) 299435 .nil) 299446 (.node .nil 299450 .nil)) 299478 (.node (.node .nil 299517 .nil) 300470 (.node .nil 300474 .nil))) 300481 (.node (.node (.node .nil 300482 .nil) 300497 (.node .nil 300498 .nil)) 300529 (.node (.node .nil 301889 .nil) 301890 (.node .nil 301905 .nil)))) 301906 (.node (.node (.node (.node .nil 301910 .nil) 301937 (.node .nil 301941 .nil)) 301949 (.node (.node .nil 302401 .nil) 302402 (.node .nil 302417 .nil))) 302418 (.node (.node (.node .nil 302422 .nil) 302449 (.node .nil 302457 .nil)) 302461 (.node (.node .nil 303318 .nil) 303357 (.node .nil 303446 .nil))))) 303485 (.node (.node (.node (.node (.node .nil 303702 .nil) 305366 (.node .nil 305405 .nil)) 305494 (.node (.node .nil 305516 .nil) 305533 (.node .nil 306020 .nil))) 306033 (.node (.node (.node .nil 309501 .nil) 413995 (.node .nil 415152 .nil)) 415169 (.node (.node .nil 415170 .nil) 479395 (.node .nil 479523 .nil)))) 479664 (.node (.node (.node (.node .nil 479681 .nil) 479682 (.node .nil 545195 .nil)) 545206 (.node (.node .nil 545210 .nil) 545238 (.node .nil 545277 .nil))) 561579 (.node (.node (.node .nil 561590 .nil) 561594 (.node .nil 561622 .nil)) 561661 (.node (.node .nil 562475 .nil) 562614 (.node .nil 562618 .nil))))))) 562625 (.node (.node (.node (.node (.node (.node (.node (.node .nil 562626 .nil) 562642 .nil) 562657 (.node .nil 562673 .nil)) 564033 (.node (.node .nil 564034 .nil) 564050 (.node .nil 564054 .nil))) 564065 (.node (.node (.node .nil 564081 .nil) 564085 (.node .nil 564093 .nil)) 564545 (.node (.node .nil 564546 .nil) 564562 (.node .nil 564566 .nil)))) 564577 (.node (.node (.node (.node .nil 564593 .nil) 564601 (.node .nil 564605 .nil)) 565462 (.node (.node .nil 565501 .nil) 565590 (.node .nil 565629 .nil))) 567638 (.node (.node (.node .nil 567660 .nil) 567677 (.node .nil 568161 .nil)) 568164 (.node (.node .nil 568177 .nil) 569597 (.node .nil 571645 .nil))))) 578992 (.node (.node (.node (.node (.node (.node .nil 579009 .nil) 579010 .nil) 579638 (.node .nil 579642 .nil)) 579670 (.node (.node .nil 579709 .nil) 580417 (.node .nil 580418 .nil))) 580929 (.node (.node (.node .nil 580930 .nil) 581846 (.node .nil 581885 .nil)) 581974 (.node (.node .nil 582013 .nil) 695618 (.node .nil 710710 .nil)))) 710714 (.node (.node (.node (.node .nil 710721 .nil) 710722 (.node .nil 710738 .nil)) 710769 (.node (.node .nil 711489 .nil) 711490 (.node .nil 712001 .nil))) 712002 (.node (.node (.node .nil 712914 .nil) 712945 (.node .nil 713042 .nil)) 713072 (.node (.node .nil 713073 .nil) 714834 (.node .nil 793409 .nil)))))) 793410 (.node (.node (.node (.node (.node (.node (.node .nil 793426 .nil) 793430 .nil) 793457 (.node .nil 793461 .nil)) 793469 (.node (.node .nil 793921 .nil) 793922 (.node .nil 793938 .nil))) 793942 (.node (.node (.node .nil 793969 .nil) 793977 (.node .nil 793981 .nil)) 794838 (.node (.node .nil 794877 .nil) 794966 (.node .nil 795005 .nil)))) 797014 (.node (.node (.node (.node .nil 797036 .nil) 797053 (.node .nil 797540 .nil)) 797553 (.node (.node .nil 801021 .nil) 893138 (.node .nil 893142 .nil))) 893169 (.node (.node (.node .nil 893173 .nil) 893181 (.node .nil 893266 .nil)) 893270 (.node (.node .nil 893296 .nil) 893297 (.node .nil 893301 .nil))))) 893309 (.node (.node (.node (.node (.node .nil 895058 .nil) 958674 (.node .nil 958678 .nil)) 958705 (.node (.node .nil 958713 .nil) 958717 (.node .nil 958802 .nil))) 958806 (.node (.node (.node .nil 958832 .nil) 958833 (.node .nil 958840 .nil)) 958841 (.node (.node .nil 958845 .nil) 960594 (.node .nil 1075542 .nil)))) 1075564 (.node (.node (.node (.node .nil 1075581 .nil) 1076068 (.node .nil 1076081 .nil)) 1079549 (.node (.node .nil 1091926 .nil) 1091948 (.node .nil 1091965 .nil))) 1092452 (.node (.node (.node .nil 1092464 .nil) 1092465 (.node .nil 1095805 .nil)) 1095933 (.node (.node .nil 1321302 .nil) 1321324 (.node .nil 1321341 .nil)))))))))
def move (depth : Nat) (s : State) (t j : Nat) : Option State := Id.run do
  if j == t then return none
  let rs := rows s
  let control := if j < 4 then rs[j]! else fixed[j-4]!
  let v := rs[t]! ^^^ control
  let p := v &&& 127
  if v == 0 then return none
  let changed := if t < 2 then set s.changed t else s.changed
  let ret := t < 2 && v == [4,8][t]! && has s.changed t && !has s.returned t
  let copy := t == 3 && rs[t]! &&& 127 == 0 && p != 0 && s.copied == 0
  let returned := if ret then set s.returned t else s.returned
  let copied := if copy then 1 else s.copied
  let old := projected s.hist
  let seen := base.contains p || has old p
  if seen && !(ret || copy) then return none
  let aux := (List.range 128).filter (fun a => a != 0 && has old a && !base.contains a && !goals.contains a)
  let enlarged := if !seen && !goals.contains p then p :: aux else aux
  if enlarged.length > 3 || !lookup prefixes (encode (sort enlarged)) then return none
  let rs := rs.set t v
  let hist := set s.hist v
  let known := projected hist
  if ([2,3].any fun i =>
      let f := want[i]! &&& 127
      has known f && rs[i]! != want[i]! &&
        (i == 2 || rs[i]! &&& 127 != 0 || !rs.contains f)) then return none
  if passive.any (fun f => has known f && !has hist f) then return none
  let delta := ((List.range 4).filter (fun i => rs[i]! != want[i]!)).map (fun i => rs[i]! ^^^ want[i]!)
  let missing := (delta.filter (fun v => !(rs ++ want ++ fixed).contains v)).eraseDups
  let untouched := ((List.range 2).filter (fun i => !has changed i)).length
  let bound := max (delta.length+2*untouched) (delta.length+(missing.length+1)/2)
  if depth+1+bound > 13 then return none
  return some ⟨rs[0]!,rs[1]!,rs[2]!,rs[3]!,hist,changed,returned,copied⟩
def next (d : Nat) (s : State) : List State :=
  (List.range 4).flatMap fun t => (List.range 8).filterMap fun j => move d s t j
def terminal (s : State) : Bool := s.changed == 3 && rows s == want
def Safe : Nat → Nat → State → Prop
  | 0, _, s => terminal s = false
  | k+1, d, s => terminal s = false ∧ ∀ z ∈ next d s, Safe k (d+1) z

theorem safe_succ (k d : Nat) (s : State) (zs : List State)
    (ht : terminal s = false) (he : next d s = zs)
    (hs : ∀ z ∈ zs, Safe k (d+1) z) : Safe (k+1) d s := by
  exact ⟨ht, fun z hz => hs z (he ▸ hz)⟩

inductive Reach : Nat → State → Nat → State → Prop where
  | refl (d s) : Reach d s 0 s
  | step {d s t k z} : t ∈ next d s → Reach (d+1) t k z → Reach d s (k+1) z

theorem safe_reach {d s k z} (h : Reach d s k z) :
    ∀ fuel, k ≤ fuel → Safe fuel d s → terminal z = false := by
  induction h with
  | refl d s =>
    intro fuel _ hs
    cases fuel with
    | zero => exact hs
    | succ n => exact hs.1
  | step ht hr ih =>
    intro fuel hk hs
    cases fuel with
    | zero => omega
    | succ n => exact ih n (by omega) (hs.2 _ ht)

def s7_0 : State := ⟨4, 8, 67, 224, 26959946667150639800513021638044654181056576070962385269848700686614, 1, 1, 1⟩
theorem s7_0_edges : next 7 s7_0 = [] := by decide
theorem s7_0_safe : Safe 6 7 s7_0 := by
  apply safe_succ 5 7 s7_0 [] (by decide) s7_0_edges
  simp
def s7_1 : State := ⟨4, 8, 67, 224, 26959946667150639800513021638044654181056576070962385269848700686614, 2, 2, 1⟩
theorem s7_1_edges : next 7 s7_1 = [] := by decide
theorem s7_1_safe : Safe 6 7 s7_1 := by
  apply safe_succ 5 7 s7_1 [] (by decide) s7_1_edges
  simp
def s7_2 : State := ⟨4, 8, 67, 224, 26959946667150639801974523274014427631576507049825169859777560383766, 1, 1, 1⟩
theorem s7_2_edges : next 7 s7_2 = [] := by decide
theorem s7_2_safe : Safe 6 7 s7_2 := by
  apply safe_succ 5 7 s7_2 [] (by decide) s7_2_edges
  simp
def s7_3 : State := ⟨4, 8, 67, 224, 26959946667150639801974523274014427631576507049825169859777560383766, 2, 2, 1⟩
theorem s7_3_edges : next 7 s7_3 = [] := by decide
theorem s7_3_safe : Safe 6 7 s7_3 := by
  apply safe_succ 5 7 s7_3 [] (by decide) s7_3_edges
  simp
def s7_4 : State := ⟨4, 8, 97, 224, 26959946667150639794667015087359913061078176977216857269341266186518, 3, 3, 1⟩
theorem s7_4_edges : next 7 s7_4 = [] := by decide
theorem s7_4_safe : Safe 6 7 s7_4 := by
  apply safe_succ 5 7 s7_4 [] (by decide) s7_4_edges
  simp
def s7_5 : State := ⟨4, 8, 112, 224, 26959946667150639794667015087359918253216579187015957124650507505942, 3, 3, 1⟩
theorem s7_5_edges : next 7 s7_5 = [] := by decide
theorem s7_5_safe : Safe 6 7 s7_5 := by
  apply safe_succ 5 7 s7_5 [] (by decide) s7_5_edges
  simp
def s6_0 : State := ⟨4, 8, 66, 224, 26959946667150639800513021638044654181056576070814811317259024273686, 1, 1, 1⟩
theorem s6_0_edges : next 6 s6_0 = [s7_0] := by decide
theorem s6_0_safe : Safe 7 6 s6_0 := by
  apply safe_succ 6 6 s6_0 [s7_0] (by decide) s6_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_0_safe
def s6_1 : State := ⟨4, 8, 66, 224, 26959946667150639800513021638044654181056576070814811317259024273686, 2, 2, 1⟩
theorem s6_1_edges : next 6 s6_1 = [s7_1] := by decide
theorem s6_1_safe : Safe 7 6 s6_1 := by
  apply safe_succ 6 6 s6_1 [s7_1] (by decide) s6_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_1_safe
def s6_2 : State := ⟨4, 8, 66, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 1, 1, 1⟩
theorem s6_2_edges : next 6 s6_2 = [s7_2] := by decide
theorem s6_2_safe : Safe 7 6 s6_2 := by
  apply safe_succ 6 6 s6_2 [s7_2] (by decide) s6_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_2_safe
def s6_3 : State := ⟨4, 8, 66, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 2, 2, 1⟩
theorem s6_3_edges : next 6 s6_3 = [s7_3] := by decide
theorem s6_3_safe : Safe 7 6 s6_3 := by
  apply safe_succ 6 6 s6_3 [s7_3] (by decide) s6_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_3_safe
def s6_4 : State := ⟨4, 8, 67, 146, 89204682205957097258460392877815419965083926, 1, 1, 1⟩
theorem s6_4_edges : next 6 s6_4 = [] := by decide
theorem s6_4_safe : Safe 7 6 s6_4 := by
  apply safe_succ 6 6 s6_4 [] (by decide) s6_4_edges
  simp
def s6_5 : State := ⟨4, 8, 67, 146, 89204682205957097258460392877815419965083926, 2, 2, 1⟩
theorem s6_5_edges : next 6 s6_5 = [] := by decide
theorem s6_5_safe : Safe 7 6 s6_5 := by
  apply safe_succ 6 6 s6_5 [] (by decide) s6_5_edges
  simp
def s6_6 : State := ⟨4, 8, 67, 146, 89204682205957097258460429771303567384187158, 1, 1, 1⟩
theorem s6_6_edges : next 6 s6_6 = [] := by decide
theorem s6_6_safe : Safe 7 6 s6_6 := by
  apply safe_succ 6 6 s6_6 [] (by decide) s6_6_edges
  simp
def s6_7 : State := ⟨4, 8, 67, 146, 89204682205957097258460429771303567384187158, 2, 2, 1⟩
theorem s6_7_edges : next 6 s6_7 = [] := by decide
theorem s6_7_safe : Safe 7 6 s6_7 := by
  apply safe_succ 6 6 s6_7 [] (by decide) s6_7_edges
  simp
def s6_8 : State := ⟨4, 8, 67, 146, 111504066275020036646142257652034054398218518, 1, 1, 1⟩
theorem s6_8_edges : next 6 s6_8 = [] := by decide
theorem s6_8_safe : Safe 7 6 s6_8 := by
  apply safe_succ 6 6 s6_8 [] (by decide) s6_8_edges
  simp
def s6_9 : State := ⟨4, 8, 67, 146, 111504066275020036646142257652034054398218518, 2, 2, 1⟩
theorem s6_9_edges : next 6 s6_9 = [] := by decide
theorem s6_9_safe : Safe 7 6 s6_9 := by
  apply safe_succ 6 6 s6_9 [] (by decide) s6_9_edges
  simp
def s6_10 : State := ⟨4, 8, 67, 146, 111504066275020036646142294545522201817321750, 1, 1, 1⟩
theorem s6_10_edges : next 6 s6_10 = [] := by decide
theorem s6_10_safe : Safe 7 6 s6_10 := by
  apply safe_succ 6 6 s6_10 [] (by decide) s6_10_edges
  simp
def s6_11 : State := ⟨4, 8, 67, 146, 111504066275020036646142294545522201817321750, 2, 2, 1⟩
theorem s6_11_edges : next 6 s6_11 = [] := by decide
theorem s6_11_safe : Safe 7 6 s6_11 := by
  apply safe_succ 6 6 s6_11 [] (by decide) s6_11_edges
  simp
def s6_12 : State := ⟨4, 8, 67, 162, 5846006551025023507419431648384919300597671334166, 1, 1, 1⟩
theorem s6_12_edges : next 6 s6_12 = [] := by decide
theorem s6_12_safe : Safe 7 6 s6_12 := by
  apply safe_succ 6 6 s6_12 [] (by decide) s6_12_edges
  simp
def s6_13 : State := ⟨4, 8, 67, 162, 5846006551025023507419431648384919300597671334166, 2, 2, 1⟩
theorem s6_13_edges : next 6 s6_13 = [] := by decide
theorem s6_13_safe : Safe 7 6 s6_13 := by
  apply safe_succ 6 6 s6_13 [] (by decide) s6_13_edges
  simp
def s6_14 : State := ⟨4, 8, 67, 162, 5846006551025023507419431648421812788745090437398, 1, 1, 1⟩
theorem s6_14_edges : next 6 s6_14 = [] := by decide
theorem s6_14_safe : Safe 7 6 s6_14 := by
  apply safe_succ 6 6 s6_14 [] (by decide) s6_14_edges
  simp
def s6_15 : State := ⟨4, 8, 67, 162, 5846006551025023507419431648421812788745090437398, 2, 2, 1⟩
theorem s6_15_edges : next 6 s6_15 = [] := by decide
theorem s6_15_safe : Safe 7 6 s6_15 := by
  apply safe_succ 6 6 s6_15 [] (by decide) s6_15_edges
  simp
def s6_16 : State := ⟨4, 8, 67, 162, 7307508186994796957939362627247703890526531031318, 1, 1, 1⟩
theorem s6_16_edges : next 6 s6_16 = [] := by decide
theorem s6_16_safe : Safe 7 6 s6_16 := by
  apply safe_succ 6 6 s6_16 [] (by decide) s6_16_edges
  simp
def s6_17 : State := ⟨4, 8, 67, 162, 7307508186994796957939362627247703890526531031318, 2, 2, 1⟩
theorem s6_17_edges : next 6 s6_17 = [] := by decide
theorem s6_17_safe : Safe 7 6 s6_17 := by
  apply safe_succ 6 6 s6_17 [] (by decide) s6_17_edges
  simp
def s6_18 : State := ⟨4, 8, 67, 162, 7307508186994796957939362627284597378673950134550, 1, 1, 1⟩
theorem s6_18_edges : next 6 s6_18 = [] := by decide
theorem s6_18_safe : Safe 7 6 s6_18 := by
  apply safe_succ 6 6 s6_18 [] (by decide) s6_18_edges
  simp
def s6_19 : State := ⟨4, 8, 67, 162, 7307508186994796957939362627284597378673950134550, 2, 2, 1⟩
theorem s6_19_edges : next 6 s6_19 = [] := by decide
theorem s6_19_safe : Safe 7 6 s6_19 := by
  apply safe_succ 6 6 s6_19 [] (by decide) s6_19_edges
  simp
def s6_20 : State := ⟨4, 8, 67, 176, 95780971326419139128294233276893708537611803510771990, 1, 1, 1⟩
theorem s6_20_edges : next 6 s6_20 = [] := by decide
theorem s6_20_safe : Safe 7 6 s6_20 := by
  apply safe_succ 6 6 s6_20 [] (by decide) s6_20_edges
  simp
def s6_21 : State := ⟨4, 8, 67, 176, 95780971326419139128294233276893708537611803510771990, 2, 2, 1⟩
theorem s6_21_edges : next 6 s6_21 = [] := by decide
theorem s6_21_safe : Safe 7 6 s6_21 := by
  apply safe_succ 6 6 s6_21 [] (by decide) s6_21_edges
  simp
def s6_22 : State := ⟨4, 8, 67, 176, 95780971326419139128294233276893745431099950929875222, 1, 1, 1⟩
theorem s6_22_edges : next 6 s6_22 = [] := by decide
theorem s6_22_safe : Safe 7 6 s6_22 := by
  apply safe_succ 6 6 s6_22 [] (by decide) s6_22_edges
  simp
def s6_23 : State := ⟨4, 8, 67, 176, 95780971326419139128294233276893745431099950929875222, 2, 2, 1⟩
theorem s6_23_edges : next 6 s6_23 = [] := by decide
theorem s6_23_safe : Safe 7 6 s6_23 := by
  apply safe_succ 6 6 s6_23 [] (by decide) s6_23_edges
  simp
def s6_24 : State := ⟨4, 8, 67, 176, 95782432805755724832681813820190706547983097937334550, 1, 1, 1⟩
theorem s6_24_edges : next 6 s6_24 = [] := by decide
theorem s6_24_safe : Safe 7 6 s6_24 := by
  apply safe_succ 6 6 s6_24 [] (by decide) s6_24_edges
  simp
def s6_25 : State := ⟨4, 8, 67, 176, 95782432805755724832681813820190706547983097937334550, 2, 2, 1⟩
theorem s6_25_edges : next 6 s6_25 = [] := by decide
theorem s6_25_safe : Safe 7 6 s6_25 := by
  apply safe_succ 6 6 s6_25 [] (by decide) s6_25_edges
  simp
def s6_26 : State := ⟨4, 8, 67, 176, 95782432805755724832681813820190743441471245356437782, 1, 1, 1⟩
theorem s6_26_edges : next 6 s6_26 = [] := by decide
theorem s6_26_safe : Safe 7 6 s6_26 := by
  apply safe_succ 6 6 s6_26 [] (by decide) s6_26_edges
  simp
def s6_27 : State := ⟨4, 8, 67, 176, 95782432805755724832681813820190743441471245356437782, 2, 2, 1⟩
theorem s6_27_edges : next 6 s6_27 = [] := by decide
theorem s6_27_safe : Safe 7 6 s6_27 := by
  apply safe_succ 6 6 s6_27 [] (by decide) s6_27_edges
  simp
def s6_28 : State := ⟨4, 8, 67, 210, 1645504557321206042177270268038248049062735287088508619142009110, 1, 1, 1⟩
theorem s6_28_edges : next 6 s6_28 = [] := by decide
theorem s6_28_safe : Safe 7 6 s6_28 := by
  apply safe_succ 6 6 s6_28 [] (by decide) s6_28_edges
  simp
def s6_29 : State := ⟨4, 8, 67, 210, 1645504557321206042177270268038248049062735287088508619142009110, 2, 2, 1⟩
theorem s6_29_edges : next 6 s6_29 = [] := by decide
theorem s6_29_safe : Safe 7 6 s6_29 := by
  apply safe_succ 6 6 s6_29 [] (by decide) s6_29_edges
  simp
def s6_30 : State := ⟨4, 8, 67, 210, 1645529665728147588878024865997410256586863978237638113774080278, 1, 1, 1⟩
theorem s6_30_edges : next 6 s6_30 = [] := by decide
theorem s6_30_safe : Safe 7 6 s6_30 := by
  apply safe_succ 6 6 s6_30 [] (by decide) s6_30_edges
  simp
def s6_31 : State := ⟨4, 8, 67, 210, 1645529665728147588878024865997410256586863978237638113774080278, 2, 2, 1⟩
theorem s6_31_edges : next 6 s6_31 = [] := by decide
theorem s6_31_safe : Safe 7 6 s6_31 := by
  apply safe_succ 6 6 s6_31 [] (by decide) s6_31_edges
  simp
def s6_32 : State := ⟨4, 8, 67, 210, 27973577474460502716656777188955856128786509137225786432719749398, 1, 1, 1⟩
theorem s6_32_edges : next 6 s6_32 = [] := by decide
theorem s6_32_safe : Safe 7 6 s6_32 := by
  apply safe_succ 6 6 s6_32 [] (by decide) s6_32_edges
  simp
def s6_33 : State := ⟨4, 8, 67, 210, 27973602582867444263357531786915018336310637828374915927351820566, 1, 1, 1⟩
theorem s6_33_edges : next 6 s6_33 = [] := by decide
theorem s6_33_safe : Safe 7 6 s6_33 := by
  apply safe_succ 6 6 s6_33 [] (by decide) s6_33_edges
  simp
def s6_34 : State := ⟨4, 8, 67, 224, 26959946667150639796128516724690815958761767718923144293006411108630, 1, 1, 1⟩
theorem s6_34_edges : next 6 s6_34 = [] := by decide
theorem s6_34_safe : Safe 7 6 s6_34 := by
  apply safe_succ 6 6 s6_34 [] (by decide) s6_34_edges
  simp
def s6_35 : State := ⟨4, 8, 67, 224, 26959946667150639796128516724690815958761767718923144293006411108630, 2, 2, 1⟩
theorem s6_35_edges : next 6 s6_35 = [] := by decide
theorem s6_35_safe : Safe 7 6 s6_35 := by
  apply safe_succ 6 6 s6_35 [] (by decide) s6_35_edges
  simp
def s6_36 : State := ⟨4, 8, 67, 224, 26959946667150639796128516724690815958761767718960037781153830211862, 1, 1, 1⟩
theorem s6_36_edges : next 6 s6_36 = [] := by decide
theorem s6_36_safe : Safe 7 6 s6_36 := by
  apply safe_succ 6 6 s6_36 [] (by decide) s6_36_edges
  simp
def s6_37 : State := ⟨4, 8, 67, 224, 26959946667150639796128516724690815958761767718960037781153830211862, 2, 2, 1⟩
theorem s6_37_edges : next 6 s6_37 = [] := by decide
theorem s6_37_safe : Safe 7 6 s6_37 := by
  apply safe_succ 6 6 s6_37 [] (by decide) s6_37_edges
  simp
def s6_38 : State := ⟨4, 8, 67, 224, 26959946673427741530053695851195702463765749302309216717814513078550, 1, 1, 1⟩
theorem s6_38_edges : next 6 s6_38 = [] := by decide
theorem s6_38_safe : Safe 7 6 s6_38 := by
  apply safe_succ 6 6 s6_38 [] (by decide) s6_38_edges
  simp
def s6_39 : State := ⟨4, 8, 67, 224, 26959946673427741530053695851195702463765749302309216717814513078550, 2, 2, 1⟩
theorem s6_39_edges : next 6 s6_39 = [] := by decide
theorem s6_39_safe : Safe 7 6 s6_39 := by
  apply safe_succ 6 6 s6_39 [] (by decide) s6_39_edges
  simp
def s6_40 : State := ⟨4, 8, 67, 224, 26959946673427741530053695851195702463765749302346110205961932181782, 1, 1, 1⟩
theorem s6_40_edges : next 6 s6_40 = [] := by decide
theorem s6_40_safe : Safe 7 6 s6_40 := by
  apply safe_succ 6 6 s6_40 [] (by decide) s6_40_edges
  simp
def s6_41 : State := ⟨4, 8, 67, 224, 26959946673427741530053695851195702463765749302346110205961932181782, 2, 2, 1⟩
theorem s6_41_edges : next 6 s6_41 = [] := by decide
theorem s6_41_safe : Safe 7 6 s6_41 := by
  apply safe_succ 6 6 s6_41 [] (by decide) s6_41_edges
  simp
def s6_42 : State := ⟨4, 8, 67, 224, 458319093341560876510800758117004906736956078479572303990664175091990, 1, 1, 1⟩
theorem s6_42_edges : next 6 s6_42 = [] := by decide
theorem s6_42_safe : Safe 7 6 s6_42 := by
  apply safe_succ 6 6 s6_42 [] (by decide) s6_42_edges
  simp
def s6_43 : State := ⟨4, 8, 67, 224, 458319093341560876510800758117004906736956078479609197478811594195222, 1, 1, 1⟩
theorem s6_43_edges : next 6 s6_43 = [] := by decide
theorem s6_43_safe : Safe 7 6 s6_43 := by
  apply safe_succ 6 6 s6_43 [] (by decide) s6_43_edges
  simp
def s6_44 : State := ⟨4, 8, 67, 224, 458319093347837978244725937243509793241960060062958376415472277061910, 1, 1, 1⟩
theorem s6_44_edges : next 6 s6_44 = [] := by decide
theorem s6_44_safe : Safe 7 6 s6_44 := by
  apply safe_succ 6 6 s6_44 [] (by decide) s6_44_edges
  simp
def s6_45 : State := ⟨4, 8, 67, 224, 458319093347837978244725937243509793241960060062995269903619696165142, 1, 1, 1⟩
theorem s6_45_edges : next 6 s6_45 = [] := by decide
theorem s6_45_safe : Safe 7 6 s6_45 := by
  apply safe_succ 6 6 s6_45 [] (by decide) s6_45_edges
  simp
def s6_46 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761772554515742287080852623638, 1, 1, 1⟩
theorem s6_46_edges : next 6 s6_46 = [] := by decide
theorem s6_46_safe : Safe 7 6 s6_46 := by
  apply safe_succ 6 6 s6_46 [] (by decide) s6_46_edges
  simp
def s6_47 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761772554515742287080852623638, 2, 2, 1⟩
theorem s6_47_edges : next 6 s6_47 = [] := by decide
theorem s6_47_safe : Safe 7 6 s6_47 := by
  apply safe_succ 6 6 s6_47 [] (by decide) s6_47_edges
  simp
def s6_48 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761773763367774925415189123350, 1, 1, 1⟩
theorem s6_48_edges : next 6 s6_48 = [] := by decide
theorem s6_48_safe : Safe 7 6 s6_48 := by
  apply safe_succ 6 6 s6_48 [] (by decide) s6_48_edges
  simp
def s6_49 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761773763367774925415189123350, 2, 2, 1⟩
theorem s6_49_edges : next 6 s6_49 = [] := by decide
theorem s6_49_safe : Safe 7 6 s6_49 := by
  apply safe_succ 6 6 s6_49 [] (by decide) s6_49_edges
  simp
def s6_50 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761849925768197623348033814806, 1, 1, 1⟩
theorem s6_50_edges : next 6 s6_50 = [] := by decide
theorem s6_50_safe : Safe 7 6 s6_50 := by
  apply safe_succ 6 6 s6_50 [] (by decide) s6_50_edges
  simp
def s6_51 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761851134620230261682370314518, 1, 1, 1⟩
theorem s6_51_edges : next 6 s6_51 = [] := by decide
theorem s6_51_safe : Safe 7 6 s6_51 := by
  apply safe_succ 6 6 s6_51 [] (by decide) s6_51_edges
  simp
def s6_52 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765754137901814711888954593558, 1, 1, 1⟩
theorem s6_52_edges : next 6 s6_52 = [] := by decide
theorem s6_52_safe : Safe 7 6 s6_52 := by
  apply safe_succ 6 6 s6_52 [] (by decide) s6_52_edges
  simp
def s6_53 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765754137901814711888954593558, 2, 2, 1⟩
theorem s6_53_edges : next 6 s6_53 = [] := by decide
theorem s6_53_safe : Safe 7 6 s6_53 := by
  apply safe_succ 6 6 s6_53 [] (by decide) s6_53_edges
  simp
def s6_54 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765755346753847350223291093270, 1, 1, 1⟩
theorem s6_54_edges : next 6 s6_54 = [] := by decide
theorem s6_54_safe : Safe 7 6 s6_54 := by
  apply safe_succ 6 6 s6_54 [] (by decide) s6_54_edges
  simp
def s6_55 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765755346753847350223291093270, 2, 2, 1⟩
theorem s6_55_edges : next 6 s6_55 = [] := by decide
theorem s6_55_safe : Safe 7 6 s6_55 := by
  apply safe_succ 6 6 s6_55 [] (by decide) s6_55_edges
  simp
def s6_56 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765831509154270048156135784726, 1, 1, 1⟩
theorem s6_56_edges : next 6 s6_56 = [] := by decide
theorem s6_56_safe : Safe 7 6 s6_56 := by
  apply safe_succ 6 6 s6_56 [] (by decide) s6_56_edges
  simp
def s6_57 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765832718006302686490472284438, 1, 1, 1⟩
theorem s6_57_edges : next 6 s6_57 = [] := by decide
theorem s6_57_safe : Safe 7 6 s6_57 := by
  apply safe_succ 6 6 s6_57 [] (by decide) s6_57_edges
  simp
def s6_58 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 3, 3, 1⟩
theorem s6_58_edges : next 6 s6_58 = [s7_4, s7_5] := by decide
theorem s6_58_safe : Safe 7 6 s6_58 := by
  apply safe_succ 6 6 s6_58 [s7_4, s7_5] (by decide) s6_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s7_4_safe
  · subst z; exact s7_5_safe
def s6_59 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913060919720652483476499333531107606, 3, 3, 1⟩
theorem s6_59_edges : next 6 s6_59 = [] := by decide
theorem s6_59_safe : Safe 7 6 s6_59 := by
  apply safe_succ 6 6 s6_59 [] (by decide) s6_59_edges
  simp
def s6_60 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 3, 3, 1⟩
theorem s6_60_edges : next 6 s6_60 = [] := by decide
theorem s6_60_safe : Safe 7 6 s6_60 := by
  apply safe_succ 6 6 s6_60 [] (by decide) s6_60_edges
  simp
def s6_61 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 3, 3, 1⟩
theorem s6_61_edges : next 6 s6_61 = [] := by decide
theorem s6_61_safe : Safe 7 6 s6_61 := by
  apply safe_succ 6 6 s6_61 [] (by decide) s6_61_edges
  simp
def s6_62 : State := ⟨4, 8, 96, 224, 458319093341560876509339256479674003839114031412837488291811942269206, 3, 3, 1⟩
theorem s6_62_edges : next 6 s6_62 = [] := by decide
theorem s6_62_safe : Safe 7 6 s6_62 := by
  apply safe_succ 6 6 s6_62 [] (by decide) s6_62_edges
  simp
def s6_63 : State := ⟨4, 8, 162, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 1, 1, 1⟩
theorem s6_63_edges : next 6 s6_63 = [] := by decide
theorem s6_63_safe : Safe 7 6 s6_63 := by
  apply safe_succ 6 6 s6_63 [] (by decide) s6_63_edges
  simp
def s6_64 : State := ⟨4, 8, 162, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 2, 2, 1⟩
theorem s6_64_edges : next 6 s6_64 = [] := by decide
theorem s6_64_safe : Safe 7 6 s6_64 := by
  apply safe_succ 6 6 s6_64 [] (by decide) s6_64_edges
  simp
def s6_65 : State := ⟨4, 8, 162, 224, 26959946673427741535899702400519314136580488633063668331995985940758, 1, 1, 1⟩
theorem s6_65_edges : next 6 s6_65 = [] := by decide
theorem s6_65_safe : Safe 7 6 s6_65 := by
  apply safe_succ 6 6 s6_65 [] (by decide) s6_65_edges
  simp
def s6_66 : State := ⟨4, 8, 162, 224, 26959946673427741535899702400519314136580488633063668331995985940758, 2, 2, 1⟩
theorem s6_66_edges : next 6 s6_66 = [] := by decide
theorem s6_66_safe : Safe 7 6 s6_66 := by
  apply safe_succ 6 6 s6_66 [] (by decide) s6_66_edges
  simp
def s6_67 : State := ⟨4, 12, 67, 224, 26959946667150639800513021638044654181056576070962385269848700686614, 2, 0, 1⟩
theorem s6_67_edges : next 6 s6_67 = [s7_1] := by decide
theorem s6_67_safe : Safe 7 6 s6_67 := by
  apply safe_succ 6 6 s6_67 [s7_1] (by decide) s6_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_1_safe
def s6_68 : State := ⟨4, 12, 67, 224, 26959946667150639801974523274014427631576507049825169859777560383766, 2, 0, 1⟩
theorem s6_68_edges : next 6 s6_68 = [s7_3] := by decide
theorem s6_68_safe : Safe 7 6 s6_68 := by
  apply safe_succ 6 6 s6_68 [s7_3] (by decide) s6_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_3_safe
def s6_69 : State := ⟨4, 12, 97, 224, 26959946667150639794667015087359913061078176977216857269341266186518, 2, 2, 1⟩
theorem s6_69_edges : next 6 s6_69 = [] := by decide
theorem s6_69_safe : Safe 7 6 s6_69 := by
  apply safe_succ 6 6 s6_69 [] (by decide) s6_69_edges
  simp
def s6_70 : State := ⟨4, 12, 112, 224, 26959946667150639794667015087359918253216579187015957124650507505942, 2, 2, 1⟩
theorem s6_70_edges : next 6 s6_70 = [] := by decide
theorem s6_70_safe : Safe 7 6 s6_70 := by
  apply safe_succ 6 6 s6_70 [] (by decide) s6_70_edges
  simp
def s6_71 : State := ⟨4, 104, 97, 224, 26959946667150639794667015087359913061078176977216857269341266186518, 2, 2, 1⟩
theorem s6_71_edges : next 6 s6_71 = [] := by decide
theorem s6_71_safe : Safe 7 6 s6_71 := by
  apply safe_succ 6 6 s6_71 [] (by decide) s6_71_edges
  simp
def s6_72 : State := ⟨4, 104, 97, 224, 26959946667150639794667015087359913061078176977216857269341266186518, 3, 1, 1⟩
theorem s6_72_edges : next 6 s6_72 = [] := by decide
theorem s6_72_safe : Safe 7 6 s6_72 := by
  apply safe_succ 6 6 s6_72 [] (by decide) s6_72_edges
  simp
def s6_73 : State := ⟨4, 104, 112, 224, 26959946667150639794667015087359918253216579187015957124650507505942, 2, 2, 1⟩
theorem s6_73_edges : next 6 s6_73 = [] := by decide
theorem s6_73_safe : Safe 7 6 s6_73 := by
  apply safe_succ 6 6 s6_73 [] (by decide) s6_73_edges
  simp
def s6_74 : State := ⟨4, 104, 112, 224, 26959946667150639794667015087359918253216579187015957124650507505942, 3, 1, 1⟩
theorem s6_74_edges : next 6 s6_74 = [] := by decide
theorem s6_74_safe : Safe 7 6 s6_74 := by
  apply safe_succ 6 6 s6_74 [] (by decide) s6_74_edges
  simp
def s6_75 : State := ⟨12, 8, 67, 224, 26959946667150639800513021638044654181056576070962385269848700686614, 1, 0, 1⟩
theorem s6_75_edges : next 6 s6_75 = [s7_0] := by decide
theorem s6_75_safe : Safe 7 6 s6_75 := by
  apply safe_succ 6 6 s6_75 [s7_0] (by decide) s6_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_0_safe
def s6_76 : State := ⟨12, 8, 67, 224, 26959946667150639801974523274014427631576507049825169859777560383766, 1, 0, 1⟩
theorem s6_76_edges : next 6 s6_76 = [s7_2] := by decide
theorem s6_76_safe : Safe 7 6 s6_76 := by
  apply safe_succ 6 6 s6_76 [s7_2] (by decide) s6_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_2_safe
def s6_77 : State := ⟨12, 8, 97, 224, 26959946667150639794667015087359913061078176977216857269341266186518, 3, 2, 1⟩
theorem s6_77_edges : next 6 s6_77 = [s7_4] := by decide
theorem s6_77_safe : Safe 7 6 s6_77 := by
  apply safe_succ 6 6 s6_77 [s7_4] (by decide) s6_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_4_safe
def s6_78 : State := ⟨12, 8, 112, 224, 26959946667150639794667015087359918253216579187015957124650507505942, 3, 2, 1⟩
theorem s6_78_edges : next 6 s6_78 = [s7_5] := by decide
theorem s6_78_safe : Safe 7 6 s6_78 := by
  apply safe_succ 6 6 s6_78 [s7_5] (by decide) s6_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s7_5_safe
def s5_0 : State := ⟨4, 8, 64, 163, 11692013102390329381759801759845831583074915258646, 1, 1, 1⟩
theorem s5_0_edges : next 5 s5_0 = [] := by decide
theorem s5_0_safe : Safe 8 5 s5_0 := by
  apply safe_succ 7 5 s5_0 [] (by decide) s5_0_edges
  simp
def s5_1 : State := ⟨4, 8, 64, 163, 11692013102390329381759801759845831583074915258646, 2, 2, 1⟩
theorem s5_1_edges : next 5 s5_1 = [] := by decide
theorem s5_1_safe : Safe 8 5 s5_1 := by
  apply safe_succ 7 5 s5_1 [] (by decide) s5_1_edges
  simp
def s5_2 : State := ⟨4, 8, 64, 163, 11692013103070894115601678686772580797938451681558, 1, 1, 1⟩
theorem s5_2_edges : next 5 s5_2 = [] := by decide
theorem s5_2_safe : Safe 8 5 s5_2 := by
  apply safe_succ 7 5 s5_2 [] (by decide) s5_2_edges
  simp
def s5_3 : State := ⟨4, 8, 64, 163, 11692013103070894115601678686772580797938451681558, 2, 2, 1⟩
theorem s5_3_edges : next 5 s5_3 = [] := by decide
theorem s5_3_safe : Safe 8 5 s5_3 := by
  apply safe_succ 7 5 s5_3 [] (by decide) s5_3_edges
  simp
def s5_4 : State := ⟨4, 8, 64, 163, 14615016374329876282799663717571400762932634652950, 1, 1, 1⟩
theorem s5_4_edges : next 5 s5_4 = [] := by decide
theorem s5_4_safe : Safe 8 5 s5_4 := by
  apply safe_succ 7 5 s5_4 [] (by decide) s5_4_edges
  simp
def s5_5 : State := ⟨4, 8, 64, 163, 14615016374329876282799663717571400762932634652950, 2, 2, 1⟩
theorem s5_5_edges : next 5 s5_5 = [] := by decide
theorem s5_5_safe : Safe 8 5 s5_5 := by
  apply safe_succ 7 5 s5_5 [] (by decide) s5_5_edges
  simp
def s5_6 : State := ⟨4, 8, 64, 163, 16076518010980214467161471623360934567725030773014, 1, 1, 1⟩
theorem s5_6_edges : next 5 s5_6 = [] := by decide
theorem s5_6_safe : Safe 8 5 s5_6 := by
  apply safe_succ 7 5 s5_6 [] (by decide) s5_6_edges
  simp
def s5_7 : State := ⟨4, 8, 64, 163, 16076518010980214467161471623360934567725030773014, 2, 2, 1⟩
theorem s5_7_edges : next 5 s5_7 = [] := by decide
theorem s5_7_safe : Safe 8 5 s5_7 := by
  apply safe_succ 7 5 s5_7 [] (by decide) s5_7_edges
  simp
def s5_8 : State := ⟨4, 8, 64, 163, 17538019649672246853048910309930716017108036161814, 1, 1, 1⟩
theorem s5_8_edges : next 5 s5_8 = [] := by decide
theorem s5_8_safe : Safe 8 5 s5_8 := by
  apply safe_succ 7 5 s5_8 [] (by decide) s5_8_edges
  simp
def s5_9 : State := ⟨4, 8, 64, 163, 17538019649672246853048910309930716017108036161814, 2, 2, 1⟩
theorem s5_9_edges : next 5 s5_9 = [] := by decide
theorem s5_9_safe : Safe 8 5 s5_9 := by
  apply safe_succ 7 5 s5_9 [] (by decide) s5_9_edges
  simp
def s5_10 : State := ⟨4, 8, 64, 163, 18999521285642020303568841288793500607036895858966, 1, 1, 1⟩
theorem s5_10_edges : next 5 s5_10 = [] := by decide
theorem s5_10_safe : Safe 8 5 s5_10 := by
  apply safe_succ 7 5 s5_10 [] (by decide) s5_10_edges
  simp
def s5_11 : State := ⟨4, 8, 64, 163, 18999521285642020303568841288793500607036895858966, 2, 2, 1⟩
theorem s5_11_edges : next 5 s5_11 = [] := by decide
theorem s5_11_safe : Safe 8 5 s5_11 := by
  apply safe_succ 7 5 s5_11 [] (by decide) s5_11_edges
  simp
def s5_12 : State := ⟨4, 8, 64, 163, 3004847366356079505862906339162793455838424763269398, 2, 2, 1⟩
theorem s5_12_edges : next 5 s5_12 = [] := by decide
theorem s5_12_safe : Safe 8 5 s5_12 := by
  apply safe_succ 7 5 s5_12 [] (by decide) s5_12_edges
  simp
def s5_13 : State := ⟨4, 8, 64, 163, 3004847366356760070596748216089720205053288299692310, 2, 2, 1⟩
theorem s5_13_edges : next 5 s5_13 = [] := by decide
theorem s5_13_safe : Safe 8 5 s5_13 := by
  apply safe_succ 7 5 s5_13 [] (by decide) s5_13_edges
  simp
def s5_14 : State := ⟨4, 8, 64, 163, 3007770369628019052763946201120519025018282482663702, 2, 2, 1⟩
theorem s5_14_edges : next 5 s5_14 = [] := by decide
theorem s5_14_safe : Safe 8 5 s5_14 := by
  apply safe_succ 7 5 s5_14 [] (by decide) s5_14_edges
  simp
def s5_15 : State := ⟨4, 8, 64, 163, 3009231871264669390948308009026308558823074878783766, 2, 2, 1⟩
theorem s5_15_edges : next 5 s5_15 = [] := by decide
theorem s5_15_safe : Safe 8 5 s5_15 := by
  apply safe_succ 7 5 s5_15 [] (by decide) s5_15_edges
  simp
def s5_16 : State := ⟨4, 8, 64, 163, 3010693372903361423334195447712878340272457884172566, 2, 2, 1⟩
theorem s5_16_edges : next 5 s5_16 = [] := by decide
theorem s5_16_safe : Safe 8 5 s5_16 := by
  apply safe_succ 7 5 s5_16 [] (by decide) s5_16_edges
  simp
def s5_17 : State := ⟨4, 8, 64, 163, 3012154874539331196784715378691741124862386743869718, 2, 2, 1⟩
theorem s5_17_edges : next 5 s5_17 = [] := by decide
theorem s5_17_safe : Safe 8 5 s5_17 := by
  apply safe_succ 7 5 s5_17 [] (by decide) s5_17_edges
  simp
def s5_18 : State := ⟨4, 8, 64, 171, 2999001359804714199988565969051148076115210423829270, 2, 2, 1⟩
theorem s5_18_edges : next 5 s5_18 = [] := by decide
theorem s5_18_safe : Safe 8 5 s5_18 := by
  apply safe_succ 7 5 s5_18 [] (by decide) s5_18_edges
  simp
def s5_19 : State := ⟨4, 8, 64, 171, 3000462861440683973439085900030010860705139283526422, 2, 2, 1⟩
theorem s5_19_edges : next 5 s5_19 = [] := by decide
theorem s5_19_safe : Safe 8 5 s5_19 := by
  apply safe_succ 7 5 s5_19 [] (by decide) s5_19_edges
  simp
def s5_20 : State := ⟨4, 8, 64, 210, 1645504557321206042244173864763307602241196074043954546218176790, 1, 1, 1⟩
theorem s5_20_edges : next 5 s5_20 = [] := by decide
theorem s5_20_safe : Safe 8 5 s5_20 := by
  apply safe_succ 7 5 s5_20 [] (by decide) s5_20_edges
  simp
def s5_21 : State := ⟨4, 8, 64, 210, 1645504557321206042244173864763307602241196074043954546218176790, 2, 2, 1⟩
theorem s5_21_edges : next 5 s5_21 = [] := by decide
theorem s5_21_safe : Safe 8 5 s5_21 := by
  apply safe_succ 7 5 s5_21 [] (by decide) s5_21_edges
  simp
def s5_22 : State := ⟨4, 8, 64, 210, 1645504557321206042266473248832370541628877938818173180651311382, 1, 1, 1⟩
theorem s5_22_edges : next 5 s5_22 = [] := by decide
theorem s5_22_safe : Safe 8 5 s5_22 := by
  apply safe_succ 7 5 s5_22 [] (by decide) s5_22_edges
  simp
def s5_23 : State := ⟨4, 8, 64, 210, 1645504557321206042266473248832370541628877938818173180651311382, 2, 2, 1⟩
theorem s5_23_edges : next 5 s5_23 = [] := by decide
theorem s5_23_safe : Safe 8 5 s5_23 := by
  apply safe_succ 7 5 s5_23 [] (by decide) s5_23_edges
  simp
def s5_24 : State := ⟨4, 8, 64, 210, 1645529665728147588878026227126877940340717610375138956332306710, 1, 1, 1⟩
theorem s5_24_edges : next 5 s5_24 = [] := by decide
theorem s5_24_safe : Safe 8 5 s5_24 := by
  apply safe_succ 7 5 s5_24 [] (by decide) s5_24_edges
  simp
def s5_25 : State := ⟨4, 8, 64, 210, 1645529665728147588878026227126877940340717610375138956332306710, 2, 2, 1⟩
theorem s5_25_edges : next 5 s5_25 = [] := by decide
theorem s5_25_safe : Safe 8 5 s5_25 := by
  apply safe_succ 7 5 s5_25 [] (by decide) s5_25_edges
  simp
def s5_26 : State := ⟨4, 8, 64, 210, 1645535942829882975558788701786833464253279859232153693293973782, 1, 1, 1⟩
theorem s5_26_edges : next 5 s5_26 = [] := by decide
theorem s5_26_safe : Safe 8 5 s5_26 := by
  apply safe_succ 7 5 s5_26 [] (by decide) s5_26_edges
  simp
def s5_27 : State := ⟨4, 8, 64, 210, 1645535942829882975558788701786833464253279859232153693293973782, 2, 2, 1⟩
theorem s5_27_edges : next 5 s5_27 = [] := by decide
theorem s5_27_safe : Safe 8 5 s5_27 := by
  apply safe_succ 7 5 s5_27 [] (by decide) s5_27_edges
  simp
def s5_28 : State := ⟨4, 8, 64, 210, 2056880696651507552716012563677585675308419032135974700464541974, 1, 1, 1⟩
theorem s5_28_edges : next 5 s5_28 = [] := by decide
theorem s5_28_safe : Safe 8 5 s5_28 := by
  apply safe_succ 7 5 s5_28 [] (by decide) s5_28_edges
  simp
def s5_29 : State := ⟨4, 8, 64, 210, 2056880696651507552716012563677585675308419032135974700464541974, 2, 2, 1⟩
theorem s5_29_edges : next 5 s5_29 = [] := by decide
theorem s5_29_safe : Safe 8 5 s5_29 := by
  apply safe_succ 7 5 s5_29 [] (by decide) s5_29_edges
  simp
def s5_30 : State := ⟨4, 8, 64, 210, 2056886973753242939374475654268478259833299416218770802993074454, 1, 1, 1⟩
theorem s5_30_edges : next 5 s5_30 = [] := by decide
theorem s5_30_safe : Safe 8 5 s5_30 := by
  apply safe_succ 7 5 s5_30 [] (by decide) s5_30_edges
  simp
def s5_31 : State := ⟨4, 8, 64, 210, 2056886973753242939374475654268478259833299416218770802993074454, 2, 2, 1⟩
theorem s5_31_edges : next 5 s5_31 = [] := by decide
theorem s5_31_safe : Safe 8 5 s5_31 := by
  apply safe_succ 7 5 s5_31 [] (by decide) s5_31_edges
  simp
def s5_32 : State := ⟨4, 8, 64, 210, 27973577474460502716723680785680915681964969924181232359795917078, 1, 1, 1⟩
theorem s5_32_edges : next 5 s5_32 = [] := by decide
theorem s5_32_safe : Safe 8 5 s5_32 := by
  apply safe_succ 7 5 s5_32 [] (by decide) s5_32_edges
  simp
def s5_33 : State := ⟨4, 8, 64, 210, 27973577474460502716745980169749978621352651788955450994229051670, 1, 1, 1⟩
theorem s5_33_edges : next 5 s5_33 = [] := by decide
theorem s5_33_safe : Safe 8 5 s5_33 := by
  apply safe_succ 7 5 s5_33 [] (by decide) s5_33_edges
  simp
def s5_34 : State := ⟨4, 8, 64, 210, 27973602582867444263357533148044486020064491460512416769910046998, 1, 1, 1⟩
theorem s5_34_edges : next 5 s5_34 = [] := by decide
theorem s5_34_safe : Safe 8 5 s5_34 := by
  apply safe_succ 7 5 s5_34 [] (by decide) s5_34_edges
  simp
def s5_35 : State := ⟨4, 8, 64, 210, 27973608859969179650038295622704441543977053709369431506871714070, 1, 1, 1⟩
theorem s5_35_edges : next 5 s5_35 = [] := by decide
theorem s5_35_safe : Safe 8 5 s5_35 := by
  apply safe_succ 7 5 s5_35 [] (by decide) s5_35_edges
  simp
def s5_36 : State := ⟨4, 8, 64, 210, 28384953613790804227195519484595193755032192882273252514042282262, 1, 1, 1⟩
theorem s5_36_edges : next 5 s5_36 = [] := by decide
theorem s5_36_safe : Safe 8 5 s5_36 := by
  apply safe_succ 7 5 s5_36 [] (by decide) s5_36_edges
  simp
def s5_37 : State := ⟨4, 8, 64, 210, 28384959890892539613853982575186086339557073266356048616570814742, 1, 1, 1⟩
theorem s5_37_edges : next 5 s5_37 = [] := by decide
theorem s5_37_safe : Safe 8 5 s5_37 := by
  apply safe_succ 7 5 s5_37 [] (by decide) s5_37_edges
  simp
def s5_38 : State := ⟨4, 8, 64, 214, 26328072917139296674568711603123565176982234353695557675800133910, 1, 1, 1⟩
theorem s5_38_edges : next 5 s5_38 = [] := by decide
theorem s5_38_safe : Safe 8 5 s5_38 := by
  apply safe_succ 7 5 s5_38 [] (by decide) s5_38_edges
  simp
def s5_39 : State := ⟨4, 8, 64, 214, 26328072917139296674591010987192628116369916218469776310233268502, 1, 1, 1⟩
theorem s5_39_edges : next 5 s5_39 = [] := by decide
theorem s5_39_safe : Safe 8 5 s5_39 := by
  apply safe_succ 7 5 s5_39 [] (by decide) s5_39_edges
  simp
def s5_40 : State := ⟨4, 8, 65, 146, 89204682205957097258460245303862830288670998, 1, 1, 1⟩
theorem s5_40_edges : next 5 s5_40 = [s6_4] := by decide
theorem s5_40_safe : Safe 8 5 s5_40 := by
  apply safe_succ 7 5 s5_40 [s6_4] (by decide) s5_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_4_safe
def s5_41 : State := ⟨4, 8, 65, 146, 89204682205957097258460245303862830288670998, 2, 2, 1⟩
theorem s5_41_edges : next 5 s5_41 = [s6_5] := by decide
theorem s5_41_safe : Safe 8 5 s5_41 := by
  apply safe_succ 7 5 s5_41 [s6_5] (by decide) s5_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_5_safe
def s5_42 : State := ⟨4, 8, 65, 146, 111504066275020036646142110078081464721805590, 1, 1, 1⟩
theorem s5_42_edges : next 5 s5_42 = [s6_8] := by decide
theorem s5_42_safe : Safe 8 5 s5_42 := by
  apply safe_succ 7 5 s5_42 [s6_8] (by decide) s5_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_8_safe
def s5_43 : State := ⟨4, 8, 65, 146, 111504066275020036646142110078081464721805590, 2, 2, 1⟩
theorem s5_43_edges : next 5 s5_43 = [s6_9] := by decide
theorem s5_43_safe : Safe 8 5 s5_43 := by
  apply safe_succ 7 5 s5_43 [s6_9] (by decide) s5_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_9_safe
def s5_44 : State := ⟨4, 8, 65, 162, 5846006551025023507419431648237345348007994921238, 1, 1, 1⟩
theorem s5_44_edges : next 5 s5_44 = [s6_12] := by decide
theorem s5_44_safe : Safe 8 5 s5_44 := by
  apply safe_succ 7 5 s5_44 [s6_12] (by decide) s5_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_12_safe
def s5_45 : State := ⟨4, 8, 65, 162, 5846006551025023507419431648237345348007994921238, 2, 2, 1⟩
theorem s5_45_edges : next 5 s5_45 = [s6_13] := by decide
theorem s5_45_safe : Safe 8 5 s5_45 := by
  apply safe_succ 7 5 s5_45 [s6_13] (by decide) s5_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_13_safe
def s5_46 : State := ⟨4, 8, 65, 162, 7307508186994796957939362627100129937936854618390, 1, 1, 1⟩
theorem s5_46_edges : next 5 s5_46 = [s6_16] := by decide
theorem s5_46_safe : Safe 8 5 s5_46 := by
  apply safe_succ 7 5 s5_46 [s6_16] (by decide) s5_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_16_safe
def s5_47 : State := ⟨4, 8, 65, 162, 7307508186994796957939362627100129937936854618390, 2, 2, 1⟩
theorem s5_47_edges : next 5 s5_47 = [s6_17] := by decide
theorem s5_47_safe : Safe 8 5 s5_47 := by
  apply safe_succ 7 5 s5_47 [s6_17] (by decide) s5_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_17_safe
def s5_48 : State := ⟨4, 8, 65, 176, 95780971326419139128294233276893560963659213834359062, 1, 1, 1⟩
theorem s5_48_edges : next 5 s5_48 = [s6_20] := by decide
theorem s5_48_safe : Safe 8 5 s5_48 := by
  apply safe_succ 7 5 s5_48 [s6_20] (by decide) s5_48_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_20_safe
def s5_49 : State := ⟨4, 8, 65, 176, 95780971326419139128294233276893560963659213834359062, 2, 2, 1⟩
theorem s5_49_edges : next 5 s5_49 = [s6_21] := by decide
theorem s5_49_safe : Safe 8 5 s5_49 := by
  apply safe_succ 7 5 s5_49 [s6_21] (by decide) s5_49_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_21_safe
def s5_50 : State := ⟨4, 8, 65, 176, 95782432805755724832681813820190558974030508260921622, 1, 1, 1⟩
theorem s5_50_edges : next 5 s5_50 = [s6_24] := by decide
theorem s5_50_safe : Safe 8 5 s5_50 := by
  apply safe_succ 7 5 s5_50 [s6_24] (by decide) s5_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_24_safe
def s5_51 : State := ⟨4, 8, 65, 176, 95782432805755724832681813820190558974030508260921622, 2, 2, 1⟩
theorem s5_51_edges : next 5 s5_51 = [s6_25] := by decide
theorem s5_51_safe : Safe 8 5 s5_51 := by
  apply safe_succ 7 5 s5_51 [s6_25] (by decide) s5_51_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_25_safe
def s5_52 : State := ⟨4, 8, 65, 224, 26959946667150639796128516724690815958761767718775570340416734695702, 1, 1, 1⟩
theorem s5_52_edges : next 5 s5_52 = [s6_34] := by decide
theorem s5_52_safe : Safe 8 5 s5_52 := by
  apply safe_succ 7 5 s5_52 [s6_34] (by decide) s5_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_34_safe
def s5_53 : State := ⟨4, 8, 65, 224, 26959946667150639796128516724690815958761767718775570340416734695702, 2, 2, 1⟩
theorem s5_53_edges : next 5 s5_53 = [s6_35] := by decide
theorem s5_53_safe : Safe 8 5 s5_53 := by
  apply safe_succ 7 5 s5_53 [s6_35] (by decide) s5_53_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_35_safe
def s5_54 : State := ⟨4, 8, 65, 224, 26959946673427741530053695851195702463765749302161642765224836665622, 1, 1, 1⟩
theorem s5_54_edges : next 5 s5_54 = [s6_38] := by decide
theorem s5_54_safe : Safe 8 5 s5_54 := by
  apply safe_succ 7 5 s5_54 [s6_38] (by decide) s5_54_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_38_safe
def s5_55 : State := ⟨4, 8, 65, 224, 26959946673427741530053695851195702463765749302161642765224836665622, 2, 2, 1⟩
theorem s5_55_edges : next 5 s5_55 = [s6_39] := by decide
theorem s5_55_safe : Safe 8 5 s5_55 := by
  apply safe_succ 7 5 s5_55 [s6_39] (by decide) s5_55_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_39_safe
def s5_56 : State := ⟨4, 8, 65, 224, 458319093341560876510800758117004906736956078479424730038074498679062, 1, 1, 1⟩
theorem s5_56_edges : next 5 s5_56 = [s6_42] := by decide
theorem s5_56_safe : Safe 8 5 s5_56 := by
  apply safe_succ 7 5 s5_56 [s6_42] (by decide) s5_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_42_safe
def s5_57 : State := ⟨4, 8, 65, 224, 458319093347837978244725937243509793241960060062810802462882600648982, 1, 1, 1⟩
theorem s5_57_edges : next 5 s5_57 = [s6_44] := by decide
theorem s5_57_safe : Safe 8 5 s5_57 := by
  apply safe_succ 7 5 s5_57 [s6_44] (by decide) s5_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_44_safe
def s5_58 : State := ⟨4, 8, 66, 146, 89204682205957097258460282197350977707774230, 1, 1, 1⟩
theorem s5_58_edges : next 5 s5_58 = [s6_6] := by decide
theorem s5_58_safe : Safe 8 5 s5_58 := by
  apply safe_succ 7 5 s5_58 [s6_6] (by decide) s5_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_6_safe
def s5_59 : State := ⟨4, 8, 66, 146, 89204682205957097258460282197350977707774230, 2, 2, 1⟩
theorem s5_59_edges : next 5 s5_59 = [s6_7] := by decide
theorem s5_59_safe : Safe 8 5 s5_59 := by
  apply safe_succ 7 5 s5_59 [s6_7] (by decide) s5_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_7_safe
def s5_60 : State := ⟨4, 8, 66, 146, 111504066275020036646142146971569612140908822, 1, 1, 1⟩
theorem s5_60_edges : next 5 s5_60 = [s6_10] := by decide
theorem s5_60_safe : Safe 8 5 s5_60 := by
  apply safe_succ 7 5 s5_60 [s6_10] (by decide) s5_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_10_safe
def s5_61 : State := ⟨4, 8, 66, 146, 111504066275020036646142146971569612140908822, 2, 2, 1⟩
theorem s5_61_edges : next 5 s5_61 = [s6_11] := by decide
theorem s5_61_safe : Safe 8 5 s5_61 := by
  apply safe_succ 7 5 s5_61 [s6_11] (by decide) s5_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_11_safe
def s5_62 : State := ⟨4, 8, 66, 162, 5846006551025023507419431648274238836155414024470, 1, 1, 1⟩
theorem s5_62_edges : next 5 s5_62 = [s6_14, s6_0] := by decide
theorem s5_62_safe : Safe 8 5 s5_62 := by
  apply safe_succ 7 5 s5_62 [s6_14, s6_0] (by decide) s5_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_14_safe
  · subst z; exact s6_0_safe
def s5_63 : State := ⟨4, 8, 66, 162, 5846006551025023507419431648274238836155414024470, 2, 2, 1⟩
theorem s5_63_edges : next 5 s5_63 = [s6_15, s6_1] := by decide
theorem s5_63_safe : Safe 8 5 s5_63 := by
  apply safe_succ 7 5 s5_63 [s6_15, s6_1] (by decide) s5_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_15_safe
  · subst z; exact s6_1_safe
def s5_64 : State := ⟨4, 8, 66, 162, 7307508186994796957939362627137023426084273721622, 1, 1, 1⟩
theorem s5_64_edges : next 5 s5_64 = [s6_18, s6_2] := by decide
theorem s5_64_safe : Safe 8 5 s5_64 := by
  apply safe_succ 7 5 s5_64 [s6_18, s6_2] (by decide) s5_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_18_safe
  · subst z; exact s6_2_safe
def s5_65 : State := ⟨4, 8, 66, 162, 7307508186994796957939362627137023426084273721622, 2, 2, 1⟩
theorem s5_65_edges : next 5 s5_65 = [s6_19, s6_3] := by decide
theorem s5_65_safe : Safe 8 5 s5_65 := by
  apply safe_succ 7 5 s5_65 [s6_19, s6_3] (by decide) s5_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_19_safe
  · subst z; exact s6_3_safe
def s5_66 : State := ⟨4, 8, 66, 176, 95780971326419139128294233276893597857147361253462294, 1, 1, 1⟩
theorem s5_66_edges : next 5 s5_66 = [s6_22] := by decide
theorem s5_66_safe : Safe 8 5 s5_66 := by
  apply safe_succ 7 5 s5_66 [s6_22] (by decide) s5_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_22_safe
def s5_67 : State := ⟨4, 8, 66, 176, 95780971326419139128294233276893597857147361253462294, 2, 2, 1⟩
theorem s5_67_edges : next 5 s5_67 = [s6_23] := by decide
theorem s5_67_safe : Safe 8 5 s5_67 := by
  apply safe_succ 7 5 s5_67 [s6_23] (by decide) s5_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_23_safe
def s5_68 : State := ⟨4, 8, 66, 176, 95782432805755724832681813820190595867518655680024854, 1, 1, 1⟩
theorem s5_68_edges : next 5 s5_68 = [s6_26] := by decide
theorem s5_68_safe : Safe 8 5 s5_68 := by
  apply safe_succ 7 5 s5_68 [s6_26] (by decide) s5_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_26_safe
def s5_69 : State := ⟨4, 8, 66, 176, 95782432805755724832681813820190595867518655680024854, 2, 2, 1⟩
theorem s5_69_edges : next 5 s5_69 = [s6_27] := by decide
theorem s5_69_safe : Safe 8 5 s5_69 := by
  apply safe_succ 7 5 s5_69 [s6_27] (by decide) s5_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_27_safe
def s5_70 : State := ⟨4, 8, 66, 210, 1645504557321206042177270268038248049062735139514556029465596182, 1, 1, 1⟩
theorem s5_70_edges : next 5 s5_70 = [s6_28] := by decide
theorem s5_70_safe : Safe 8 5 s5_70 := by
  apply safe_succ 7 5 s5_70 [s6_28] (by decide) s5_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_28_safe
def s5_71 : State := ⟨4, 8, 66, 210, 1645504557321206042177270268038248049062735139514556029465596182, 2, 2, 1⟩
theorem s5_71_edges : next 5 s5_71 = [s6_29] := by decide
theorem s5_71_safe : Safe 8 5 s5_71 := by
  apply safe_succ 7 5 s5_71 [s6_29] (by decide) s5_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_29_safe
def s5_72 : State := ⟨4, 8, 66, 210, 1645529665728147588878024865997410256586863830663685524097667350, 1, 1, 1⟩
theorem s5_72_edges : next 5 s5_72 = [s6_30] := by decide
theorem s5_72_safe : Safe 8 5 s5_72 := by
  apply safe_succ 7 5 s5_72 [s6_30] (by decide) s5_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_30_safe
def s5_73 : State := ⟨4, 8, 66, 210, 1645529665728147588878024865997410256586863830663685524097667350, 2, 2, 1⟩
theorem s5_73_edges : next 5 s5_73 = [s6_31] := by decide
theorem s5_73_safe : Safe 8 5 s5_73 := by
  apply safe_succ 7 5 s5_73 [s6_31] (by decide) s5_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_31_safe
def s5_74 : State := ⟨4, 8, 66, 210, 27973577474460502716656777188955856128786508989651833843043336470, 1, 1, 1⟩
theorem s5_74_edges : next 5 s5_74 = [s6_32] := by decide
theorem s5_74_safe : Safe 8 5 s5_74 := by
  apply safe_succ 7 5 s5_74 [s6_32] (by decide) s5_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_32_safe
def s5_75 : State := ⟨4, 8, 66, 210, 27973602582867444263357531786915018336310637680800963337675407638, 1, 1, 1⟩
theorem s5_75_edges : next 5 s5_75 = [s6_33] := by decide
theorem s5_75_safe : Safe 8 5 s5_75 := by
  apply safe_succ 7 5 s5_75 [s6_33] (by decide) s5_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_33_safe
def s5_76 : State := ⟨4, 8, 66, 224, 26959946667150639796128516724690815958761767718812463828564153798934, 1, 1, 1⟩
theorem s5_76_edges : next 5 s5_76 = [s6_63, s6_36, s6_46] := by decide
theorem s5_76_safe : Safe 8 5 s5_76 := by
  apply safe_succ 7 5 s5_76 [s6_63, s6_36, s6_46] (by decide) s5_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_63_safe
  · subst z; exact s6_36_safe
  · subst z; exact s6_46_safe
def s5_77 : State := ⟨4, 8, 66, 224, 26959946667150639796128516724690815958761767718812463828564153798934, 2, 2, 1⟩
theorem s5_77_edges : next 5 s5_77 = [s6_64, s6_37, s6_47] := by decide
theorem s5_77_safe : Safe 8 5 s5_77 := by
  apply safe_succ 7 5 s5_77 [s6_64, s6_37, s6_47] (by decide) s5_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_64_safe
  · subst z; exact s6_37_safe
  · subst z; exact s6_47_safe
def s5_78 : State := ⟨4, 8, 66, 224, 26959946673427741530053695851195702463765749302198536253372255768854, 1, 1, 1⟩
theorem s5_78_edges : next 5 s5_78 = [s6_65, s6_40, s6_52] := by decide
theorem s5_78_safe : Safe 8 5 s5_78 := by
  apply safe_succ 7 5 s5_78 [s6_65, s6_40, s6_52] (by decide) s5_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_65_safe
  · subst z; exact s6_40_safe
  · subst z; exact s6_52_safe
def s5_79 : State := ⟨4, 8, 66, 224, 26959946673427741530053695851195702463765749302198536253372255768854, 2, 2, 1⟩
theorem s5_79_edges : next 5 s5_79 = [s6_66, s6_41, s6_53] := by decide
theorem s5_79_safe : Safe 8 5 s5_79 := by
  apply safe_succ 7 5 s5_79 [s6_66, s6_41, s6_53] (by decide) s5_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_66_safe
  · subst z; exact s6_41_safe
  · subst z; exact s6_53_safe
def s5_80 : State := ⟨4, 8, 66, 224, 458319093341560876510800758117004906736956078479461623526221917782294, 1, 1, 1⟩
theorem s5_80_edges : next 5 s5_80 = [s6_43] := by decide
theorem s5_80_safe : Safe 8 5 s5_80 := by
  apply safe_succ 7 5 s5_80 [s6_43] (by decide) s5_80_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_43_safe
def s5_81 : State := ⟨4, 8, 66, 224, 458319093347837978244725937243509793241960060062847695951030019752214, 1, 1, 1⟩
theorem s5_81_edges : next 5 s5_81 = [s6_45] := by decide
theorem s5_81_safe : Safe 8 5 s5_81 := by
  apply safe_succ 7 5 s5_81 [s6_45] (by decide) s5_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_45_safe
def s5_82 : State := ⟨4, 8, 67, 129, 1020847100762815390593038007110404739350, 1, 1, 1⟩
theorem s5_82_edges : next 5 s5_82 = [] := by decide
theorem s5_82_safe : Safe 8 5 s5_82 := by
  apply safe_succ 7 5 s5_82 [] (by decide) s5_82_edges
  simp
def s5_83 : State := ⟨4, 8, 67, 129, 1020847100762815390593038007110404739350, 2, 2, 1⟩
theorem s5_83_edges : next 5 s5_83 = [] := by decide
theorem s5_83_safe : Safe 8 5 s5_83 := by
  apply safe_succ 7 5 s5_83 [] (by decide) s5_83_edges
  simp
def s5_84 : State := ⟨4, 8, 67, 129, 1020847100762815390629931495257823842582, 1, 1, 1⟩
theorem s5_84_edges : next 5 s5_84 = [] := by decide
theorem s5_84_safe : Safe 8 5 s5_84 := by
  apply safe_succ 7 5 s5_84 [] (by decide) s5_84_edges
  simp
def s5_85 : State := ⟨4, 8, 67, 129, 1020847100762815390629931495257823842582, 2, 2, 1⟩
theorem s5_85_edges : next 5 s5_85 = [] := by decide
theorem s5_85_safe : Safe 8 5 s5_85 := by
  apply safe_succ 7 5 s5_85 [] (by decide) s5_85_edges
  simp
def s5_86 : State := ⟨4, 8, 67, 130, 1701411834604692317519787221973941162262, 1, 1, 1⟩
theorem s5_86_edges : next 5 s5_86 = [s6_4, s6_12] := by decide
theorem s5_86_safe : Safe 8 5 s5_86 := by
  apply safe_succ 7 5 s5_86 [s6_4, s6_12] (by decide) s5_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_4_safe
  · subst z; exact s6_12_safe
def s5_87 : State := ⟨4, 8, 67, 130, 1701411834604692317519787221973941162262, 2, 2, 1⟩
theorem s5_87_edges : next 5 s5_87 = [s6_5, s6_13] := by decide
theorem s5_87_safe : Safe 8 5 s5_87 := by
  apply safe_succ 7 5 s5_87 [s6_5, s6_13] (by decide) s5_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_5_safe
  · subst z; exact s6_13_safe
def s5_88 : State := ⟨4, 8, 67, 130, 1701411834604692317556680710121360265494, 1, 1, 1⟩
theorem s5_88_edges : next 5 s5_88 = [s6_6, s6_14] := by decide
theorem s5_88_safe : Safe 8 5 s5_88 := by
  apply safe_succ 7 5 s5_88 [s6_6, s6_14] (by decide) s5_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_6_safe
  · subst z; exact s6_14_safe
def s5_89 : State := ⟨4, 8, 67, 130, 1701411834604692317556680710121360265494, 2, 2, 1⟩
theorem s5_89_edges : next 5 s5_89 = [s6_7, s6_15] := by decide
theorem s5_89_safe : Safe 8 5 s5_89 := by
  apply safe_succ 7 5 s5_89 [s6_7, s6_15] (by decide) s5_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_7_safe
  · subst z; exact s6_15_safe
def s5_90 : State := ⟨4, 8, 67, 132, 5784800237655953879080282511155159699734, 1, 1, 1⟩
theorem s5_90_edges : next 5 s5_90 = [] := by decide
theorem s5_90_safe : Safe 8 5 s5_90 := by
  apply safe_succ 7 5 s5_90 [] (by decide) s5_90_edges
  simp
def s5_91 : State := ⟨4, 8, 67, 132, 5784800237655953879080282511155159699734, 2, 2, 1⟩
theorem s5_91_edges : next 5 s5_91 = [] := by decide
theorem s5_91_safe : Safe 8 5 s5_91 := by
  apply safe_succ 7 5 s5_91 [] (by decide) s5_91_edges
  simp
def s5_92 : State := ⟨4, 8, 67, 132, 5784800237655953879117175999302578802966, 1, 1, 1⟩
theorem s5_92_edges : next 5 s5_92 = [] := by decide
theorem s5_92_safe : Safe 8 5 s5_92 := by
  apply safe_succ 7 5 s5_92 [] (by decide) s5_92_edges
  simp
def s5_93 : State := ⟨4, 8, 67, 132, 5784800237655953879117175999302578802966, 2, 2, 1⟩
theorem s5_93_edges : next 5 s5_93 = [] := by decide
theorem s5_93_safe : Safe 8 5 s5_93 := by
  apply safe_succ 7 5 s5_93 [] (by decide) s5_93_edges
  simp
def s5_94 : State := ⟨4, 8, 67, 132, 1399581375145819900225062674551677753819414, 2, 2, 1⟩
theorem s5_94_edges : next 5 s5_94 = [] := by decide
theorem s5_94_safe : Safe 8 5 s5_94 := by
  apply safe_succ 7 5 s5_94 [] (by decide) s5_94_edges
  simp
def s5_95 : State := ⟨4, 8, 67, 132, 1399581375145819900225099568039825172922646, 2, 2, 1⟩
theorem s5_95_edges : next 5 s5_95 = [] := by decide
theorem s5_95_safe : Safe 8 5 s5_95 := by
  apply safe_succ 7 5 s5_95 [] (by decide) s5_95_edges
  simp
def s5_96 : State := ⟨4, 8, 67, 136, 87452568298681185110290188294779530449174, 1, 1, 1⟩
theorem s5_96_edges : next 5 s5_96 = [] := by decide
theorem s5_96_safe : Safe 8 5 s5_96 := by
  apply safe_succ 7 5 s5_96 [] (by decide) s5_96_edges
  simp
def s5_97 : State := ⟨4, 8, 67, 136, 87452568298681185110290188294779530449174, 2, 2, 1⟩
theorem s5_97_edges : next 5 s5_97 = [] := by decide
theorem s5_97_safe : Safe 8 5 s5_97 := by
  apply safe_succ 7 5 s5_97 [] (by decide) s5_97_edges
  simp
def s5_98 : State := ⟨4, 8, 67, 136, 87452568298681185110327081782926949552406, 1, 1, 1⟩
theorem s5_98_edges : next 5 s5_98 = [] := by decide
theorem s5_98_safe : Safe 8 5 s5_98 := by
  apply safe_succ 7 5 s5_98 [] (by decide) s5_98_edges
  simp
def s5_99 : State := ⟨4, 8, 67, 136, 87452568298681185110327081782926949552406, 2, 2, 1⟩
theorem s5_99_edges : next 5 s5_99 = [] := by decide
theorem s5_99_safe : Safe 8 5 s5_99 := by
  apply safe_succ 7 5 s5_99 [] (by decide) s5_99_edges
  simp
def s5_100 : State := ⟨4, 8, 67, 136, 1481249143206845131456272580335302124568854, 1, 1, 1⟩
theorem s5_100_edges : next 5 s5_100 = [] := by decide
theorem s5_100_safe : Safe 8 5 s5_100 := by
  apply safe_succ 7 5 s5_100 [] (by decide) s5_100_edges
  simp
def s5_101 : State := ⟨4, 8, 67, 136, 1481249143206845131456309473823449543672086, 1, 1, 1⟩
theorem s5_101_edges : next 5 s5_101 = [] := by decide
theorem s5_101_safe : Safe 8 5 s5_101 := by
  apply safe_succ 7 5 s5_101 [] (by decide) s5_101_edges
  simp
def s5_102 : State := ⟨4, 8, 67, 140, 1394136857275084884809648680832769462440214, 1, 1, 1⟩
theorem s5_102_edges : next 5 s5_102 = [] := by decide
theorem s5_102_safe : Safe 8 5 s5_102 := by
  apply safe_succ 7 5 s5_102 [] (by decide) s5_102_edges
  simp
def s5_103 : State := ⟨4, 8, 67, 140, 1394136857275084884809648680832769462440214, 2, 2, 1⟩
theorem s5_103_edges : next 5 s5_103 = [] := by decide
theorem s5_103_safe : Safe 8 5 s5_103 := by
  apply safe_succ 7 5 s5_103 [] (by decide) s5_103_edges
  simp
def s5_104 : State := ⟨4, 8, 67, 140, 1394136857275084884809685574320916881543446, 1, 1, 1⟩
theorem s5_104_edges : next 5 s5_104 = [] := by decide
theorem s5_104_safe : Safe 8 5 s5_104 := by
  apply safe_succ 7 5 s5_104 [] (by decide) s5_104_edges
  simp
def s5_105 : State := ⟨4, 8, 67, 140, 1394136857275084884809685574320916881543446, 2, 2, 1⟩
theorem s5_105_edges : next 5 s5_105 = [] := by decide
theorem s5_105_safe : Safe 8 5 s5_105 := by
  apply safe_succ 7 5 s5_105 [] (by decide) s5_105_edges
  simp
def s5_106 : State := ⟨4, 8, 67, 144, 22301085480897544079999384561440608374296854, 1, 1, 1⟩
theorem s5_106_edges : next 5 s5_106 = [s6_8, s6_20] := by decide
theorem s5_106_safe : Safe 8 5 s5_106 := by
  apply safe_succ 7 5 s5_106 [s6_8, s6_20] (by decide) s5_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_8_safe
  · subst z; exact s6_20_safe
def s5_107 : State := ⟨4, 8, 67, 144, 22301085480897544079999384561440608374296854, 2, 2, 1⟩
theorem s5_107_edges : next 5 s5_107 = [s6_9, s6_21] := by decide
theorem s5_107_safe : Safe 8 5 s5_107 := by
  apply safe_succ 7 5 s5_107 [s6_9, s6_21] (by decide) s5_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_9_safe
  · subst z; exact s6_21_safe
def s5_108 : State := ⟨4, 8, 67, 144, 22301085480897544079999421454928755793400086, 1, 1, 1⟩
theorem s5_108_edges : next 5 s5_108 = [s6_10, s6_22] := by decide
theorem s5_108_safe : Safe 8 5 s5_108 := by
  apply safe_succ 7 5 s5_108 [s6_10, s6_22] (by decide) s5_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_10_safe
  · subst z; exact s6_22_safe
def s5_109 : State := ⟨4, 8, 67, 144, 22301085480897544079999421454928755793400086, 2, 2, 1⟩
theorem s5_109_edges : next 5 s5_109 = [s6_11, s6_23] := by decide
theorem s5_109_safe : Safe 8 5 s5_109 := by
  apply safe_succ 7 5 s5_109 [s6_11, s6_23] (by decide) s5_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_11_safe
  · subst z; exact s6_23_safe
def s5_110 : State := ⟨4, 8, 67, 160, 1461501637671185285124623296382571811902800859414, 1, 1, 1⟩
theorem s5_110_edges : next 5 s5_110 = [s6_16, s6_24] := by decide
theorem s5_110_safe : Safe 8 5 s5_110 := by
  apply safe_succ 7 5 s5_110 [s6_16, s6_24] (by decide) s5_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_16_safe
  · subst z; exact s6_24_safe
def s5_111 : State := ⟨4, 8, 67, 160, 1461501637671185285124623296382571811902800859414, 2, 2, 1⟩
theorem s5_111_edges : next 5 s5_111 = [s6_17, s6_25] := by decide
theorem s5_111_safe : Safe 8 5 s5_111 := by
  apply safe_succ 7 5 s5_111 [s6_17, s6_25] (by decide) s5_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_17_safe
  · subst z; exact s6_25_safe
def s5_112 : State := ⟨4, 8, 67, 160, 1461501637671185285124623296419465300050219962646, 1, 1, 1⟩
theorem s5_112_edges : next 5 s5_112 = [s6_18, s6_26] := by decide
theorem s5_112_safe : Safe 8 5 s5_112 := by
  apply safe_succ 7 5 s5_112 [s6_18, s6_26] (by decide) s5_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_18_safe
  · subst z; exact s6_26_safe
def s5_113 : State := ⟨4, 8, 67, 160, 1461501637671185285124623296419465300050219962646, 2, 2, 1⟩
theorem s5_113_edges : next 5 s5_113 = [s6_19, s6_27] := by decide
theorem s5_113_safe : Safe 8 5 s5_113 := by
  apply safe_succ 7 5 s5_113 [s6_19, s6_27] (by decide) s5_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_19_safe
  · subst z; exact s6_27_safe
def s5_114 : State := ⟨4, 8, 67, 192, 6277101735386680764176071790128604879768644236710902829334, 1, 1, 1⟩
theorem s5_114_edges : next 5 s5_114 = [s6_38] := by decide
theorem s5_114_safe : Safe 8 5 s5_114 := by
  apply safe_succ 7 5 s5_114 [s6_38] (by decide) s5_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_38_safe
def s5_115 : State := ⟨4, 8, 67, 192, 6277101735386680764176071790128604879768644236710902829334, 2, 2, 1⟩
theorem s5_115_edges : next 5 s5_115 = [s6_39] := by decide
theorem s5_115_safe : Safe 8 5 s5_115 := by
  apply safe_succ 7 5 s5_115 [s6_39] (by decide) s5_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_39_safe
def s5_116 : State := ⟨4, 8, 67, 192, 6277101735386680764176071790128604879805537724858321932566, 1, 1, 1⟩
theorem s5_116_edges : next 5 s5_116 = [s6_40] := by decide
theorem s5_116_safe : Safe 8 5 s5_116 := by
  apply safe_succ 7 5 s5_116 [s6_40] (by decide) s5_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_40_safe
def s5_117 : State := ⟨4, 8, 67, 192, 6277101735386680764176071790128604879805537724858321932566, 2, 2, 1⟩
theorem s5_117_edges : next 5 s5_117 = [s6_41] := by decide
theorem s5_117_safe : Safe 8 5 s5_117 := by
  apply safe_succ 7 5 s5_117 [s6_41] (by decide) s5_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_41_safe
def s5_118 : State := ⟨4, 8, 67, 193, 12554203470773361528011861213336271295870999681174937342230, 1, 1, 1⟩
theorem s5_118_edges : next 5 s5_118 = [] := by decide
theorem s5_118_safe : Safe 8 5 s5_118 := by
  apply safe_succ 7 5 s5_118 [] (by decide) s5_118_edges
  simp
def s5_119 : State := ⟨4, 8, 67, 193, 12554203470773361528011861213336271295870999681174937342230, 2, 2, 1⟩
theorem s5_119_edges : next 5 s5_119 = [] := by decide
theorem s5_119_safe : Safe 8 5 s5_119 := by
  apply safe_succ 7 5 s5_119 [] (by decide) s5_119_edges
  simp
def s5_120 : State := ⟨4, 8, 67, 194, 25108406941546723055683440059751604128112604058250425471254, 1, 1, 1⟩
theorem s5_120_edges : next 5 s5_120 = [s6_30] := by decide
theorem s5_120_safe : Safe 8 5 s5_120 := by
  apply safe_succ 7 5 s5_120 [s6_30] (by decide) s5_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_30_safe
def s5_121 : State := ⟨4, 8, 67, 194, 25108406941546723055683440059751604128112604058250425471254, 2, 2, 1⟩
theorem s5_121_edges : next 5 s5_121 = [s6_31] := by decide
theorem s5_121_safe : Safe 8 5 s5_121 := by
  apply safe_succ 7 5 s5_121 [s6_31] (by decide) s5_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_31_safe
def s5_122 : State := ⟨4, 8, 67, 195, 50216813883093446111026597752582269792485132347959144419606, 1, 1, 1⟩
theorem s5_122_edges : next 5 s5_122 = [] := by decide
theorem s5_122_safe : Safe 8 5 s5_122 := by
  apply safe_succ 7 5 s5_122 [] (by decide) s5_122_edges
  simp
def s5_123 : State := ⟨4, 8, 67, 195, 50216813883093446111026597752582269792485132347959144419606, 2, 2, 1⟩
theorem s5_123_edges : next 5 s5_123 = [] := by decide
theorem s5_123_safe : Safe 8 5 s5_123 := by
  apply safe_succ 7 5 s5_123 [] (by decide) s5_123_edges
  simp
def s5_124 : State := ⟨4, 8, 67, 195, 50216813883093446111026597752582269792522025836106563522838, 1, 1, 1⟩
theorem s5_124_edges : next 5 s5_124 = [] := by decide
theorem s5_124_safe : Safe 8 5 s5_124 := by
  apply safe_succ 7 5 s5_124 [] (by decide) s5_124_edges
  simp
def s5_125 : State := ⟨4, 8, 67, 195, 50216813883093446111026597752582269792522025836106563522838, 2, 2, 1⟩
theorem s5_125_edges : next 5 s5_125 = [] := by decide
theorem s5_125_safe : Safe 8 5 s5_125 := by
  apply safe_succ 7 5 s5_125 [] (by decide) s5_125_edges
  simp
def s5_126 : State := ⟨4, 8, 67, 214, 27973577474460502716656777188955856128786509137225786432719749398, 0, 0, 1⟩
theorem s5_126_edges : next 5 s5_126 = [] := by decide
theorem s5_126_safe : Safe 8 5 s5_126 := by
  apply safe_succ 7 5 s5_126 [] (by decide) s5_126_edges
  simp
def s5_127 : State := ⟨4, 8, 67, 214, 27973602582867444263357531786915018336310637828374915927351820566, 0, 0, 1⟩
theorem s5_127_edges : next 5 s5_127 = [] := by decide
theorem s5_127_safe : Safe 8 5 s5_127 := by
  apply safe_succ 7 5 s5_127 [] (by decide) s5_127_edges
  simp
def s5_128 : State := ⟨4, 8, 67, 224, 26959946667150639800513021638044654181056576070962385269848700682518, 0, 0, 1⟩
theorem s5_128_edges : next 5 s5_128 = [s6_75, s6_67] := by decide
theorem s5_128_safe : Safe 8 5 s5_128 := by
  apply safe_succ 7 5 s5_128 [s6_75, s6_67] (by decide) s5_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_75_safe
  · subst z; exact s6_67_safe
def s5_129 : State := ⟨4, 8, 67, 224, 26959946667150639801974523274014427631576507049825169859777560379670, 0, 0, 1⟩
theorem s5_129_edges : next 5 s5_129 = [s6_76, s6_68] := by decide
theorem s5_129_safe : Safe 8 5 s5_129 := by
  apply safe_succ 7 5 s5_129 [s6_76, s6_68] (by decide) s5_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_76_safe
  · subst z; exact s6_68_safe
def s5_130 : State := ⟨4, 8, 80, 210, 1645504557321206042154970883969185109676262126772975729368961302, 1, 1, 1⟩
theorem s5_130_edges : next 5 s5_130 = [] := by decide
theorem s5_130_safe : Safe 8 5 s5_130 := by
  apply safe_succ 7 5 s5_130 [] (by decide) s5_130_edges
  simp
def s5_131 : State := ⟨4, 8, 80, 210, 1645504557321206042154970883969185109676262126772975729368961302, 2, 2, 1⟩
theorem s5_131_edges : next 5 s5_131 = [] := by decide
theorem s5_131_safe : Safe 8 5 s5_131 := by
  apply safe_succ 7 5 s5_131 [] (by decide) s5_131_edges
  simp
def s5_132 : State := ⟨4, 8, 80, 210, 2056880696651507552693711818479055052168092239682940968133267734, 1, 1, 1⟩
theorem s5_132_edges : next 5 s5_132 = [] := by decide
theorem s5_132_safe : Safe 8 5 s5_132 := by
  apply safe_succ 7 5 s5_132 [] (by decide) s5_132_edges
  simp
def s5_133 : State := ⟨4, 8, 80, 210, 2056880696651507552693711818479055052168092239682940968133267734, 2, 2, 1⟩
theorem s5_133_edges : next 5 s5_133 = [] := by decide
theorem s5_133_safe : Safe 8 5 s5_133 := by
  apply safe_succ 7 5 s5_133 [] (by decide) s5_133_edges
  simp
def s5_134 : State := ⟨4, 8, 80, 210, 27973577474460502716634477804886793189400035976910253542946701590, 1, 1, 1⟩
theorem s5_134_edges : next 5 s5_134 = [] := by decide
theorem s5_134_safe : Safe 8 5 s5_134 := by
  apply safe_succ 7 5 s5_134 [] (by decide) s5_134_edges
  simp
def s5_135 : State := ⟨4, 8, 80, 210, 28384953613790804227173218739396663131891866089820218781711008022, 1, 1, 1⟩
theorem s5_135_edges : next 5 s5_135 = [] := by decide
theorem s5_135_safe : Safe 8 5 s5_135 := by
  apply safe_succ 7 5 s5_135 [] (by decide) s5_135_edges
  simp
def s5_136 : State := ⟨4, 8, 80, 224, 26959946667150639796128516724690815958761768927664496466898490298646, 1, 1, 1⟩
theorem s5_136_edges : next 5 s5_136 = [s6_48] := by decide
theorem s5_136_safe : Safe 8 5 s5_136 := by
  apply safe_succ 7 5 s5_136 [s6_48] (by decide) s5_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_48_safe
def s5_137 : State := ⟨4, 8, 80, 224, 26959946667150639796128516724690815958761768927664496466898490298646, 2, 2, 1⟩
theorem s5_137_edges : next 5 s5_137 = [s6_49] := by decide
theorem s5_137_safe : Safe 8 5 s5_137 := by
  apply safe_succ 7 5 s5_137 [s6_49] (by decide) s5_137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_49_safe
def s5_138 : State := ⟨4, 8, 80, 224, 26959946673427741530053695851195702463765750511050568891706592268566, 1, 1, 1⟩
theorem s5_138_edges : next 5 s5_138 = [s6_54] := by decide
theorem s5_138_safe : Safe 8 5 s5_138 := by
  apply safe_succ 7 5 s5_138 [s6_54] (by decide) s5_138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_54_safe
def s5_139 : State := ⟨4, 8, 80, 224, 26959946673427741530053695851195702463765750511050568891706592268566, 2, 2, 1⟩
theorem s5_139_edges : next 5 s5_139 = [s6_55] := by decide
theorem s5_139_safe : Safe 8 5 s5_139 := by
  apply safe_succ 7 5 s5_139 [s6_55] (by decide) s5_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_55_safe
def s5_140 : State := ⟨4, 8, 82, 129, 1020847100762820226185636001184846254358, 1, 1, 1⟩
theorem s5_140_edges : next 5 s5_140 = [] := by decide
theorem s5_140_safe : Safe 8 5 s5_140 := by
  apply safe_succ 7 5 s5_140 [] (by decide) s5_140_edges
  simp
def s5_141 : State := ⟨4, 8, 82, 129, 1020847100762820226185636001184846254358, 2, 2, 1⟩
theorem s5_141_edges : next 5 s5_141 = [] := by decide
theorem s5_141_safe : Safe 8 5 s5_141 := by
  apply safe_succ 7 5 s5_141 [] (by decide) s5_141_edges
  simp
def s5_142 : State := ⟨4, 8, 82, 129, 1020847100762821435037668639519182754070, 1, 1, 1⟩
theorem s5_142_edges : next 5 s5_142 = [] := by decide
theorem s5_142_safe : Safe 8 5 s5_142 := by
  apply safe_succ 7 5 s5_142 [] (by decide) s5_142_edges
  simp
def s5_143 : State := ⟨4, 8, 82, 129, 1020847100762821435037668639519182754070, 2, 2, 1⟩
theorem s5_143_edges : next 5 s5_143 = [] := by decide
theorem s5_143_safe : Safe 8 5 s5_143 := by
  apply safe_succ 7 5 s5_143 [] (by decide) s5_143_edges
  simp
def s5_144 : State := ⟨4, 8, 82, 129, 1020847100762897597438091337452027445526, 1, 1, 1⟩
theorem s5_144_edges : next 5 s5_144 = [] := by decide
theorem s5_144_safe : Safe 8 5 s5_144 := by
  apply safe_succ 7 5 s5_144 [] (by decide) s5_144_edges
  simp
def s5_145 : State := ⟨4, 8, 82, 129, 1020847100762898806290123975786363945238, 1, 1, 1⟩
theorem s5_145_edges : next 5 s5_145 = [] := by decide
theorem s5_145_safe : Safe 8 5 s5_145 := by
  apply safe_succ 7 5 s5_145 [] (by decide) s5_145_edges
  simp
def s5_146 : State := ⟨4, 8, 82, 130, 1701411834604697153112385216048382677270, 1, 1, 1⟩
theorem s5_146_edges : next 5 s5_146 = [] := by decide
theorem s5_146_safe : Safe 8 5 s5_146 := by
  apply safe_succ 7 5 s5_146 [] (by decide) s5_146_edges
  simp
def s5_147 : State := ⟨4, 8, 82, 130, 1701411834604697153112385216048382677270, 2, 2, 1⟩
theorem s5_147_edges : next 5 s5_147 = [] := by decide
theorem s5_147_safe : Safe 8 5 s5_147 := by
  apply safe_succ 7 5 s5_147 [] (by decide) s5_147_edges
  simp
def s5_148 : State := ⟨4, 8, 82, 130, 1701411834604698361964417854382719176982, 1, 1, 1⟩
theorem s5_148_edges : next 5 s5_148 = [] := by decide
theorem s5_148_safe : Safe 8 5 s5_148 := by
  apply safe_succ 7 5 s5_148 [] (by decide) s5_148_edges
  simp
def s5_149 : State := ⟨4, 8, 82, 130, 1701411834604698361964417854382719176982, 2, 2, 1⟩
theorem s5_149_edges : next 5 s5_149 = [] := by decide
theorem s5_149_safe : Safe 8 5 s5_149 := by
  apply safe_succ 7 5 s5_149 [] (by decide) s5_149_edges
  simp
def s5_150 : State := ⟨4, 8, 82, 130, 1701411834604774524364840552315563868438, 1, 1, 1⟩
theorem s5_150_edges : next 5 s5_150 = [] := by decide
theorem s5_150_safe : Safe 8 5 s5_150 := by
  apply safe_succ 7 5 s5_150 [] (by decide) s5_150_edges
  simp
def s5_151 : State := ⟨4, 8, 82, 130, 1701411834604775733216873190649900368150, 1, 1, 1⟩
theorem s5_151_edges : next 5 s5_151 = [] := by decide
theorem s5_151_safe : Safe 8 5 s5_151 := by
  apply safe_succ 7 5 s5_151 [] (by decide) s5_151_edges
  simp
def s5_152 : State := ⟨4, 8, 82, 132, 5784800237655958714672880505229601214742, 1, 1, 1⟩
theorem s5_152_edges : next 5 s5_152 = [] := by decide
theorem s5_152_safe : Safe 8 5 s5_152 := by
  apply safe_succ 7 5 s5_152 [] (by decide) s5_152_edges
  simp
def s5_153 : State := ⟨4, 8, 82, 132, 5784800237655958714672880505229601214742, 2, 2, 1⟩
theorem s5_153_edges : next 5 s5_153 = [] := by decide
theorem s5_153_safe : Safe 8 5 s5_153 := by
  apply safe_succ 7 5 s5_153 [] (by decide) s5_153_edges
  simp
def s5_154 : State := ⟨4, 8, 82, 132, 5784800237655959923524913143563937714454, 1, 1, 1⟩
theorem s5_154_edges : next 5 s5_154 = [] := by decide
theorem s5_154_safe : Safe 8 5 s5_154 := by
  apply safe_succ 7 5 s5_154 [] (by decide) s5_154_edges
  simp
def s5_155 : State := ⟨4, 8, 82, 132, 5784800237655959923524913143563937714454, 2, 2, 1⟩
theorem s5_155_edges : next 5 s5_155 = [] := by decide
theorem s5_155_safe : Safe 8 5 s5_155 := by
  apply safe_succ 7 5 s5_155 [] (by decide) s5_155_edges
  simp
def s5_156 : State := ⟨4, 8, 82, 132, 5784800237656036085925335841496782405910, 1, 1, 1⟩
theorem s5_156_edges : next 5 s5_156 = [] := by decide
theorem s5_156_safe : Safe 8 5 s5_156 := by
  apply safe_succ 7 5 s5_156 [] (by decide) s5_156_edges
  simp
def s5_157 : State := ⟨4, 8, 82, 132, 5784800237656037294777368479831118905622, 1, 1, 1⟩
theorem s5_157_edges : next 5 s5_157 = [] := by decide
theorem s5_157_safe : Safe 8 5 s5_157 := by
  apply safe_succ 7 5 s5_157 [] (by decide) s5_157_edges
  simp
def s5_158 : State := ⟨4, 8, 82, 132, 1399581375145819905060655272545752195334422, 2, 2, 1⟩
theorem s5_158_edges : next 5 s5_158 = [] := by decide
theorem s5_158_safe : Safe 8 5 s5_158 := by
  apply safe_succ 7 5 s5_158 [] (by decide) s5_158_edges
  simp
def s5_159 : State := ⟨4, 8, 82, 132, 1399581375145819906269507305184086531834134, 2, 2, 1⟩
theorem s5_159_edges : next 5 s5_159 = [] := by decide
theorem s5_159_safe : Safe 8 5 s5_159 := by
  apply safe_succ 7 5 s5_159 [] (by decide) s5_159_edges
  simp
def s5_160 : State := ⟨4, 8, 82, 136, 87452568298681189945882786288853971964182, 1, 1, 1⟩
theorem s5_160_edges : next 5 s5_160 = [] := by decide
theorem s5_160_safe : Safe 8 5 s5_160 := by
  apply safe_succ 7 5 s5_160 [] (by decide) s5_160_edges
  simp
def s5_161 : State := ⟨4, 8, 82, 136, 87452568298681189945882786288853971964182, 2, 2, 1⟩
theorem s5_161_edges : next 5 s5_161 = [] := by decide
theorem s5_161_safe : Safe 8 5 s5_161 := by
  apply safe_succ 7 5 s5_161 [] (by decide) s5_161_edges
  simp
def s5_162 : State := ⟨4, 8, 82, 136, 87452568298681191154734818927188308463894, 1, 1, 1⟩
theorem s5_162_edges : next 5 s5_162 = [] := by decide
theorem s5_162_safe : Safe 8 5 s5_162 := by
  apply safe_succ 7 5 s5_162 [] (by decide) s5_162_edges
  simp
def s5_163 : State := ⟨4, 8, 82, 136, 87452568298681191154734818927188308463894, 2, 2, 1⟩
theorem s5_163_edges : next 5 s5_163 = [] := by decide
theorem s5_163_safe : Safe 8 5 s5_163 := by
  apply safe_succ 7 5 s5_163 [] (by decide) s5_163_edges
  simp
def s5_164 : State := ⟨4, 8, 82, 136, 87452568298681267317135241625121153155350, 1, 1, 1⟩
theorem s5_164_edges : next 5 s5_164 = [] := by decide
theorem s5_164_safe : Safe 8 5 s5_164 := by
  apply safe_succ 7 5 s5_164 [] (by decide) s5_164_edges
  simp
def s5_165 : State := ⟨4, 8, 82, 136, 87452568298681268525987274263455489655062, 1, 1, 1⟩
theorem s5_165_edges : next 5 s5_165 = [] := by decide
theorem s5_165_safe : Safe 8 5 s5_165 := by
  apply safe_succ 7 5 s5_165 [] (by decide) s5_165_edges
  simp
def s5_166 : State := ⟨4, 8, 82, 136, 1481249143206845136291865178329376566083862, 1, 1, 1⟩
theorem s5_166_edges : next 5 s5_166 = [] := by decide
theorem s5_166_safe : Safe 8 5 s5_166 := by
  apply safe_succ 7 5 s5_166 [] (by decide) s5_166_edges
  simp
def s5_167 : State := ⟨4, 8, 82, 136, 1481249143206845137500717210967710902583574, 1, 1, 1⟩
theorem s5_167_edges : next 5 s5_167 = [] := by decide
theorem s5_167_safe : Safe 8 5 s5_167 := by
  apply safe_succ 7 5 s5_167 [] (by decide) s5_167_edges
  simp
def s5_168 : State := ⟨4, 8, 82, 140, 1394136857275084889645241278826843903955222, 1, 1, 1⟩
theorem s5_168_edges : next 5 s5_168 = [] := by decide
theorem s5_168_safe : Safe 8 5 s5_168 := by
  apply safe_succ 7 5 s5_168 [] (by decide) s5_168_edges
  simp
def s5_169 : State := ⟨4, 8, 82, 140, 1394136857275084889645241278826843903955222, 2, 2, 1⟩
theorem s5_169_edges : next 5 s5_169 = [] := by decide
theorem s5_169_safe : Safe 8 5 s5_169 := by
  apply safe_succ 7 5 s5_169 [] (by decide) s5_169_edges
  simp
def s5_170 : State := ⟨4, 8, 82, 140, 1394136857275084890854093311465178240454934, 1, 1, 1⟩
theorem s5_170_edges : next 5 s5_170 = [] := by decide
theorem s5_170_safe : Safe 8 5 s5_170 := by
  apply safe_succ 7 5 s5_170 [] (by decide) s5_170_edges
  simp
def s5_171 : State := ⟨4, 8, 82, 140, 1394136857275084890854093311465178240454934, 2, 2, 1⟩
theorem s5_171_edges : next 5 s5_171 = [] := by decide
theorem s5_171_safe : Safe 8 5 s5_171 := by
  apply safe_succ 7 5 s5_171 [] (by decide) s5_171_edges
  simp
def s5_172 : State := ⟨4, 8, 82, 144, 22301085480897544084834977159434682815811862, 1, 1, 1⟩
theorem s5_172_edges : next 5 s5_172 = [] := by decide
theorem s5_172_safe : Safe 8 5 s5_172 := by
  apply safe_succ 7 5 s5_172 [] (by decide) s5_172_edges
  simp
def s5_173 : State := ⟨4, 8, 82, 144, 22301085480897544084834977159434682815811862, 2, 2, 1⟩
theorem s5_173_edges : next 5 s5_173 = [] := by decide
theorem s5_173_safe : Safe 8 5 s5_173 := by
  apply safe_succ 7 5 s5_173 [] (by decide) s5_173_edges
  simp
def s5_174 : State := ⟨4, 8, 82, 144, 22301085480897544086043829192073017152311574, 1, 1, 1⟩
theorem s5_174_edges : next 5 s5_174 = [] := by decide
theorem s5_174_safe : Safe 8 5 s5_174 := by
  apply safe_succ 7 5 s5_174 [] (by decide) s5_174_edges
  simp
def s5_175 : State := ⟨4, 8, 82, 144, 22301085480897544086043829192073017152311574, 2, 2, 1⟩
theorem s5_175_edges : next 5 s5_175 = [] := by decide
theorem s5_175_safe : Safe 8 5 s5_175 := by
  apply safe_succ 7 5 s5_175 [] (by decide) s5_175_edges
  simp
def s5_176 : State := ⟨4, 8, 82, 144, 22301085480897544162206229614770949997003030, 1, 1, 1⟩
theorem s5_176_edges : next 5 s5_176 = [] := by decide
theorem s5_176_safe : Safe 8 5 s5_176 := by
  apply safe_succ 7 5 s5_176 [] (by decide) s5_176_edges
  simp
def s5_177 : State := ⟨4, 8, 82, 144, 22301085480897544163415081647409284333502742, 1, 1, 1⟩
theorem s5_177_edges : next 5 s5_177 = [] := by decide
theorem s5_177_safe : Safe 8 5 s5_177 := by
  apply safe_succ 7 5 s5_177 [] (by decide) s5_177_edges
  simp
def s5_178 : State := ⟨4, 8, 82, 160, 1461501637671185285124628131975169805977242374422, 1, 1, 1⟩
theorem s5_178_edges : next 5 s5_178 = [] := by decide
theorem s5_178_safe : Safe 8 5 s5_178 := by
  apply safe_succ 7 5 s5_178 [] (by decide) s5_178_edges
  simp
def s5_179 : State := ⟨4, 8, 82, 160, 1461501637671185285124628131975169805977242374422, 2, 2, 1⟩
theorem s5_179_edges : next 5 s5_179 = [] := by decide
theorem s5_179_safe : Safe 8 5 s5_179 := by
  apply safe_succ 7 5 s5_179 [] (by decide) s5_179_edges
  simp
def s5_180 : State := ⟨4, 8, 82, 160, 1461501637671185285124629340827202444311578874134, 1, 1, 1⟩
theorem s5_180_edges : next 5 s5_180 = [] := by decide
theorem s5_180_safe : Safe 8 5 s5_180 := by
  apply safe_succ 7 5 s5_180 [] (by decide) s5_180_edges
  simp
def s5_181 : State := ⟨4, 8, 82, 160, 1461501637671185285124629340827202444311578874134, 2, 2, 1⟩
theorem s5_181_edges : next 5 s5_181 = [] := by decide
theorem s5_181_safe : Safe 8 5 s5_181 := by
  apply safe_succ 7 5 s5_181 [] (by decide) s5_181_edges
  simp
def s5_182 : State := ⟨4, 8, 82, 160, 1461501637671185285124705503227625142244423565590, 1, 1, 1⟩
theorem s5_182_edges : next 5 s5_182 = [] := by decide
theorem s5_182_safe : Safe 8 5 s5_182 := by
  apply safe_succ 7 5 s5_182 [] (by decide) s5_182_edges
  simp
def s5_183 : State := ⟨4, 8, 82, 160, 1461501637671185285124706712079657780578760065302, 1, 1, 1⟩
theorem s5_183_edges : next 5 s5_183 = [] := by decide
theorem s5_183_safe : Safe 8 5 s5_183 := by
  apply safe_succ 7 5 s5_183 [] (by decide) s5_183_edges
  simp
def s5_184 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128609715361242230785344344342, 1, 1, 1⟩
theorem s5_184_edges : next 5 s5_184 = [s6_52] := by decide
theorem s5_184_safe : Safe 8 5 s5_184 := by
  apply safe_succ 7 5 s5_184 [s6_52] (by decide) s5_184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_52_safe
def s5_185 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128609715361242230785344344342, 2, 2, 1⟩
theorem s5_185_edges : next 5 s5_185 = [s6_53] := by decide
theorem s5_185_safe : Safe 8 5 s5_185 := by
  apply safe_succ 7 5 s5_185 [s6_53] (by decide) s5_185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_53_safe
def s5_186 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128610924213274869119680844054, 1, 1, 1⟩
theorem s5_186_edges : next 5 s5_186 = [s6_54] := by decide
theorem s5_186_safe : Safe 8 5 s5_186 := by
  apply safe_succ 7 5 s5_186 [s6_54] (by decide) s5_186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_54_safe
def s5_187 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128610924213274869119680844054, 2, 2, 1⟩
theorem s5_187_edges : next 5 s5_187 = [s6_55] := by decide
theorem s5_187_safe : Safe 8 5 s5_187 := by
  apply safe_succ 7 5 s5_187 [s6_55] (by decide) s5_187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_55_safe
def s5_188 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128687086613697567052525535510, 1, 1, 1⟩
theorem s5_188_edges : next 5 s5_188 = [s6_56] := by decide
theorem s5_188_safe : Safe 8 5 s5_188 := by
  apply safe_succ 7 5 s5_188 [s6_56] (by decide) s5_188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_56_safe
def s5_189 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128688295465730205386862035222, 1, 1, 1⟩
theorem s5_189_edges : next 5 s5_189 = [s6_57] := by decide
theorem s5_189_safe : Safe 8 5 s5_189 := by
  apply safe_succ 7 5 s5_189 [s6_57] (by decide) s5_189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_57_safe
def s5_190 : State := ⟨4, 8, 82, 194, 25108406941546723055683440059751608963668308564177447883030, 1, 1, 1⟩
theorem s5_190_edges : next 5 s5_190 = [] := by decide
theorem s5_190_safe : Safe 8 5 s5_190 := by
  apply safe_succ 7 5 s5_190 [] (by decide) s5_190_edges
  simp
def s5_191 : State := ⟨4, 8, 82, 194, 25108406941546723055683440059751608963668308564177447883030, 2, 2, 1⟩
theorem s5_191_edges : next 5 s5_191 = [] := by decide
theorem s5_191_safe : Safe 8 5 s5_191 := by
  apply safe_succ 7 5 s5_191 [] (by decide) s5_191_edges
  simp
def s5_192 : State := ⟨4, 8, 82, 194, 25108406941546723055683440059751686334920763900444629074198, 1, 1, 1⟩
theorem s5_192_edges : next 5 s5_192 = [] := by decide
theorem s5_192_safe : Safe 8 5 s5_192 := by
  apply safe_succ 7 5 s5_192 [] (by decide) s5_192_edges
  simp
def s5_193 : State := ⟨4, 8, 82, 208, 411376139330301510538742635921704547190192077327819621483483414, 1, 1, 1⟩
theorem s5_193_edges : next 5 s5_193 = [] := by decide
theorem s5_193_safe : Safe 8 5 s5_193 := by
  apply safe_succ 7 5 s5_193 [] (by decide) s5_193_edges
  simp
def s5_194 : State := ⟨4, 8, 82, 208, 411376139330301510538742635921704547190192077327819621483483414, 2, 2, 1⟩
theorem s5_194_edges : next 5 s5_194 = [] := by decide
theorem s5_194_safe : Safe 8 5 s5_194 := by
  apply safe_succ 7 5 s5_194 [] (by decide) s5_194_edges
  simp
def s5_195 : State := ⟨4, 8, 82, 208, 411376139330301510538742635921704547267563329783155888664674582, 1, 1, 1⟩
theorem s5_195_edges : next 5 s5_195 = [] := by decide
theorem s5_195_safe : Safe 8 5 s5_195 := by
  apply safe_succ 7 5 s5_195 [] (by decide) s5_195_edges
  simp
def s5_196 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717425926035124520366184658440470, 1, 1, 1⟩
theorem s5_196_edges : next 5 s5_196 = [] := by decide
theorem s5_196_safe : Safe 8 5 s5_196 := by
  apply safe_succ 7 5 s5_196 [] (by decide) s5_196_edges
  simp
def s5_197 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717425926035124520366184658440470, 2, 2, 1⟩
theorem s5_197_edges : next 5 s5_197 = [] := by decide
theorem s5_197_safe : Safe 8 5 s5_197 := by
  apply safe_succ 7 5 s5_197 [] (by decide) s5_197_edges
  simp
def s5_198 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717425927243976553004518994940182, 1, 1, 1⟩
theorem s5_198_edges : next 5 s5_198 = [] := by decide
theorem s5_198_safe : Safe 8 5 s5_198 := by
  apply safe_succ 7 5 s5_198 [] (by decide) s5_198_edges
  simp
def s5_199 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717425927243976553004518994940182, 2, 2, 1⟩
theorem s5_199_edges : next 5 s5_199 = [] := by decide
theorem s5_199_safe : Safe 8 5 s5_199 := by
  apply safe_succ 7 5 s5_199 [] (by decide) s5_199_edges
  simp
def s5_200 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717426003406376975702451839631638, 1, 1, 1⟩
theorem s5_200_edges : next 5 s5_200 = [] := by decide
theorem s5_200_safe : Safe 8 5 s5_200 := by
  apply safe_succ 7 5 s5_200 [] (by decide) s5_200_edges
  simp
def s5_201 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717426004615229008340786176131350, 1, 1, 1⟩
theorem s5_201_edges : next 5 s5_201 = [] := by decide
theorem s5_201_safe : Safe 8 5 s5_201 := by
  apply safe_succ 7 5 s5_201 [] (by decide) s5_201_edges
  simp
def s5_202 : State := ⟨4, 8, 82, 210, 27973577474460502716634476443757325505649808974657643998236180758, 1, 1, 1⟩
theorem s5_202_edges : next 5 s5_202 = [] := by decide
theorem s5_202_safe : Safe 8 5 s5_202 := by
  apply safe_succ 7 5 s5_202 [] (by decide) s5_202_edges
  simp
def s5_203 : State := ⟨4, 8, 82, 210, 27973577474460502716634476443757325505651017826690282332572680470, 1, 1, 1⟩
theorem s5_203_edges : next 5 s5_203 = [] := by decide
theorem s5_203_safe : Safe 8 5 s5_203 := by
  apply safe_succ 7 5 s5_203 [] (by decide) s5_203_edges
  simp
def s5_204 : State := ⟨4, 8, 82, 214, 26328072917139296674479507261199975000744444361479400402068766998, 1, 1, 1⟩
theorem s5_204_edges : next 5 s5_204 = [] := by decide
theorem s5_204_safe : Safe 8 5 s5_204 := by
  apply safe_succ 7 5 s5_204 [] (by decide) s5_204_edges
  simp
def s5_205 : State := ⟨4, 8, 82, 214, 26328072917139296674479507261199975000745653213512038736405266710, 1, 1, 1⟩
theorem s5_205_edges : next 5 s5_205 = [] := by decide
theorem s5_205_safe : Safe 8 5 s5_205 := by
  apply safe_succ 7 5 s5_205 [] (by decide) s5_205_edges
  simp
def s5_206 : State := ⟨4, 8, 86, 224, 26959946667150639796128516724690815958761849925768197623348033814806, 0, 0, 1⟩
theorem s5_206_edges : next 5 s5_206 = [] := by decide
theorem s5_206_safe : Safe 8 5 s5_206 := by
  apply safe_succ 7 5 s5_206 [] (by decide) s5_206_edges
  simp
def s5_207 : State := ⟨4, 8, 86, 224, 26959946667150639796128516724690815958761851134620230261682370314518, 0, 0, 1⟩
theorem s5_207_edges : next 5 s5_207 = [] := by decide
theorem s5_207_safe : Safe 8 5 s5_207 := by
  apply safe_succ 7 5 s5_207 [] (by decide) s5_207_edges
  simp
def s5_208 : State := ⟨4, 8, 86, 224, 26959946673427741530053695851195702463765831509154270048156135784726, 0, 0, 1⟩
theorem s5_208_edges : next 5 s5_208 = [] := by decide
theorem s5_208_safe : Safe 8 5 s5_208 := by
  apply safe_succ 7 5 s5_208 [] (by decide) s5_208_edges
  simp
def s5_209 : State := ⟨4, 8, 86, 224, 26959946673427741530053695851195702463765832718006302686490472284438, 0, 0, 1⟩
theorem s5_209_edges : next 5 s5_209 = [] := by decide
theorem s5_209_safe : Safe 8 5 s5_209 := by
  apply safe_succ 7 5 s5_209 [] (by decide) s5_209_edges
  simp
def s5_210 : State := ⟨4, 8, 96, 128, 340282387282576229647756113050568036630, 3, 3, 0⟩
theorem s5_210_edges : next 5 s5_210 = [s6_58] := by decide
theorem s5_210_safe : Safe 8 5 s5_210 := by
  apply safe_succ 7 5 s5_210 [s6_58] (by decide) s5_210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_58_safe
def s5_211 : State := ⟨4, 8, 96, 128, 340282387282576229942904018229920858390, 3, 3, 0⟩
theorem s5_211_edges : next 5 s5_211 = [s6_59] := by decide
theorem s5_211_safe : Safe 8 5 s5_211 := by
  apply safe_succ 7 5 s5_211 [s6_59] (by decide) s5_211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_59_safe
def s5_212 : State := ⟨4, 8, 96, 128, 340282388550226829875985514547271237910, 3, 3, 0⟩
theorem s5_212_edges : next 5 s5_212 = [s6_60] := by decide
theorem s5_212_safe : Safe 8 5 s5_212 := by
  apply safe_succ 7 5 s5_212 [s6_60] (by decide) s5_212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_60_safe
def s5_213 : State := ⟨4, 8, 96, 128, 340282711801129888074482896206588608790, 3, 3, 0⟩
theorem s5_213_edges : next 5 s5_213 = [s6_61] := by decide
theorem s5_213_safe : Safe 8 5 s5_213 := by
  apply safe_succ 7 5 s5_213 [s6_61] (by decide) s5_213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_61_safe
def s5_214 : State := ⟨4, 8, 97, 224, 26959946667150639794667015087359913040795767373565186845394014900502, 1, 1, 1⟩
theorem s5_214_edges : next 5 s5_214 = [] := by decide
theorem s5_214_safe : Safe 8 5 s5_214 := by
  apply safe_succ 7 5 s5_214 [] (by decide) s5_214_edges
  simp
def s5_215 : State := ⟨4, 8, 97, 224, 26959946667150639794667015087359913040795767373565186845394014900502, 2, 2, 1⟩
theorem s5_215_edges : next 5 s5_215 = [] := by decide
theorem s5_215_safe : Safe 8 5 s5_215 := by
  apply safe_succ 7 5 s5_215 [] (by decide) s5_215_edges
  simp
def s5_216 : State := ⟨4, 8, 97, 224, 26959946667150639794667015087359913061078176977216857269341266182422, 2, 2, 1⟩
theorem s5_216_edges : next 5 s5_216 = [s6_77, s6_69] := by decide
theorem s5_216_safe : Safe 8 5 s5_216 := by
  apply safe_succ 7 5 s5_216 [s6_77, s6_69] (by decide) s5_216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_77_safe
  · subst z; exact s6_69_safe
def s5_217 : State := ⟨4, 8, 100, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 2, 2, 1⟩
theorem s5_217_edges : next 5 s5_217 = [] := by decide
theorem s5_217_safe : Safe 8 5 s5_217 := by
  apply safe_succ 7 5 s5_217 [] (by decide) s5_217_edges
  simp
def s5_218 : State := ⟨4, 8, 104, 224, 26959946667150639794667015087359913060919720652188328594154178282262, 2, 2, 1⟩
theorem s5_218_edges : next 5 s5_218 = [] := by decide
theorem s5_218_safe : Safe 8 5 s5_218 := by
  apply safe_succ 7 5 s5_218 [] (by decide) s5_218_edges
  simp
def s5_219 : State := ⟨4, 8, 104, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 1, 1, 1⟩
theorem s5_219_edges : next 5 s5_219 = [] := by decide
theorem s5_219_safe : Safe 8 5 s5_219 := by
  apply safe_succ 7 5 s5_219 [] (by decide) s5_219_edges
  simp
def s5_220 : State := ⟨4, 8, 104, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 2, 2, 1⟩
theorem s5_220_edges : next 5 s5_220 = [] := by decide
theorem s5_220_safe : Safe 8 5 s5_220 := by
  apply safe_succ 7 5 s5_220 [] (by decide) s5_220_edges
  simp
def s5_221 : State := ⟨4, 8, 104, 224, 26959946667150639794667015087359913060919720652483476499333531107606, 1, 1, 1⟩
theorem s5_221_edges : next 5 s5_221 = [] := by decide
theorem s5_221_safe : Safe 8 5 s5_221 := by
  apply safe_succ 7 5 s5_221 [] (by decide) s5_221_edges
  simp
def s5_222 : State := ⟨4, 8, 104, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 1, 1, 1⟩
theorem s5_222_edges : next 5 s5_222 = [] := by decide
theorem s5_222_safe : Safe 8 5 s5_222 := by
  apply safe_succ 7 5 s5_222 [] (by decide) s5_222_edges
  simp
def s5_223 : State := ⟨4, 8, 104, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 1, 1, 1⟩
theorem s5_223_edges : next 5 s5_223 = [] := by decide
theorem s5_223_safe : Safe 8 5 s5_223 := by
  apply safe_succ 7 5 s5_223 [] (by decide) s5_223_edges
  simp
def s5_224 : State := ⟨4, 8, 104, 224, 458319093341560876509339256479674003839114031412837488291811942269206, 1, 1, 1⟩
theorem s5_224_edges : next 5 s5_224 = [] := by decide
theorem s5_224_safe : Safe 8 5 s5_224 := by
  apply safe_succ 7 5 s5_224 [] (by decide) s5_224_edges
  simp
def s5_225 : State := ⟨4, 8, 112, 224, 26959946667150639794667015087359918232934169583364286700703256219926, 1, 1, 1⟩
theorem s5_225_edges : next 5 s5_225 = [] := by decide
theorem s5_225_safe : Safe 8 5 s5_225 := by
  apply safe_succ 7 5 s5_225 [] (by decide) s5_225_edges
  simp
def s5_226 : State := ⟨4, 8, 112, 224, 26959946667150639794667015087359918232934169583364286700703256219926, 2, 2, 1⟩
theorem s5_226_edges : next 5 s5_226 = [] := by decide
theorem s5_226_safe : Safe 8 5 s5_226 := by
  apply safe_succ 7 5 s5_226 [] (by decide) s5_226_edges
  simp
def s5_227 : State := ⟨4, 8, 112, 224, 26959946667150639794667015087359918253216579187015957124650507501846, 2, 2, 1⟩
theorem s5_227_edges : next 5 s5_227 = [s6_78, s6_70] := by decide
theorem s5_227_safe : Safe 8 5 s5_227 := by
  apply safe_succ 7 5 s5_227 [s6_78, s6_70] (by decide) s5_227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_78_safe
  · subst z; exact s6_70_safe
def s5_228 : State := ⟨4, 8, 194, 146, 25108406941546812260025363649927924124617832152539007619350, 1, 1, 1⟩
theorem s5_228_edges : next 5 s5_228 = [] := by decide
theorem s5_228_safe : Safe 8 5 s5_228 := by
  apply safe_succ 7 5 s5_228 [] (by decide) s5_228_edges
  simp
def s5_229 : State := ⟨4, 8, 194, 146, 25108406941546812260025363649927924124617832152539007619350, 2, 2, 1⟩
theorem s5_229_edges : next 5 s5_229 = [] := by decide
theorem s5_229_safe : Safe 8 5 s5_229 := by
  apply safe_succ 7 5 s5_229 [] (by decide) s5_229_edges
  simp
def s5_230 : State := ⟨4, 8, 194, 162, 25108406947392729606368181200250097312609873637716713869590, 1, 1, 1⟩
theorem s5_230_edges : next 5 s5_230 = [] := by decide
theorem s5_230_safe : Safe 8 5 s5_230 := by
  apply safe_succ 7 5 s5_230 [] (by decide) s5_230_edges
  simp
def s5_231 : State := ⟨4, 8, 194, 162, 25108406947392729606368181200250097312609873637716713869590, 2, 2, 1⟩
theorem s5_231_edges : next 5 s5_231 = [] := by decide
theorem s5_231_safe : Safe 8 5 s5_231 := by
  apply safe_succ 7 5 s5_231 [] (by decide) s5_231_edges
  simp
def s5_232 : State := ⟨4, 8, 210, 130, 1645504557321206042154970883969185109676262126772975729368961302, 1, 1, 1⟩
theorem s5_232_edges : next 5 s5_232 = [] := by decide
theorem s5_232_safe : Safe 8 5 s5_232 := by
  apply safe_succ 7 5 s5_232 [] (by decide) s5_232_edges
  simp
def s5_233 : State := ⟨4, 8, 210, 130, 1645504557321206042154970883969185109676262126772975729368961302, 2, 2, 1⟩
theorem s5_233_edges : next 5 s5_233 = [] := by decide
theorem s5_233_safe : Safe 8 5 s5_233 := by
  apply safe_succ 7 5 s5_233 [] (by decide) s5_233_edges
  simp
def s5_234 : State := ⟨4, 8, 210, 130, 1645529665728147588878026227126877940340717610375138956332306710, 1, 1, 1⟩
theorem s5_234_edges : next 5 s5_234 = [] := by decide
theorem s5_234_safe : Safe 8 5 s5_234 := by
  apply safe_succ 7 5 s5_234 [] (by decide) s5_234_edges
  simp
def s5_235 : State := ⟨4, 8, 210, 130, 1645529665728147588878026227126877940340717610375138956332306710, 2, 2, 1⟩
theorem s5_235_edges : next 5 s5_235 = [] := by decide
theorem s5_235_safe : Safe 8 5 s5_235 := by
  apply safe_succ 7 5 s5_235 [] (by decide) s5_235_edges
  simp
def s5_236 : State := ⟨4, 8, 210, 130, 27973577474460502716634477804886793189400035976910253542946701590, 1, 1, 1⟩
theorem s5_236_edges : next 5 s5_236 = [] := by decide
theorem s5_236_safe : Safe 8 5 s5_236 := by
  apply safe_succ 7 5 s5_236 [] (by decide) s5_236_edges
  simp
def s5_237 : State := ⟨4, 8, 210, 130, 27973602582867444263357533148044486020064491460512416769910046998, 1, 1, 1⟩
theorem s5_237_edges : next 5 s5_237 = [] := by decide
theorem s5_237_safe : Safe 8 5 s5_237 := by
  apply safe_succ 7 5 s5_237 [] (by decide) s5_237_edges
  simp
def s5_238 : State := ⟨4, 8, 210, 144, 1645504557321206042177270268038248049062735139514556029465596182, 1, 1, 1⟩
theorem s5_238_edges : next 5 s5_238 = [] := by decide
theorem s5_238_safe : Safe 8 5 s5_238 := by
  apply safe_succ 7 5 s5_238 [] (by decide) s5_238_edges
  simp
def s5_239 : State := ⟨4, 8, 210, 144, 1645504557321206042177270268038248049062735139514556029465596182, 2, 2, 1⟩
theorem s5_239_edges : next 5 s5_239 = [] := by decide
theorem s5_239_safe : Safe 8 5 s5_239 := by
  apply safe_succ 7 5 s5_239 [] (by decide) s5_239_edges
  simp
def s5_240 : State := ⟨4, 8, 210, 144, 2056880696651507552716012563677585675308419032135974700464541974, 1, 1, 1⟩
theorem s5_240_edges : next 5 s5_240 = [] := by decide
theorem s5_240_safe : Safe 8 5 s5_240 := by
  apply safe_succ 7 5 s5_240 [] (by decide) s5_240_edges
  simp
def s5_241 : State := ⟨4, 8, 210, 144, 2056880696651507552716012563677585675308419032135974700464541974, 2, 2, 1⟩
theorem s5_241_edges : next 5 s5_241 = [] := by decide
theorem s5_241_safe : Safe 8 5 s5_241 := by
  apply safe_succ 7 5 s5_241 [] (by decide) s5_241_edges
  simp
def s5_242 : State := ⟨4, 8, 210, 144, 27973577474460502716656777188955856128786508989651833843043336470, 1, 1, 1⟩
theorem s5_242_edges : next 5 s5_242 = [] := by decide
theorem s5_242_safe : Safe 8 5 s5_242 := by
  apply safe_succ 7 5 s5_242 [] (by decide) s5_242_edges
  simp
def s5_243 : State := ⟨4, 8, 210, 144, 28384953613790804227195519484595193755032192882273252514042282262, 1, 1, 1⟩
theorem s5_243_edges : next 5 s5_243 = [] := by decide
theorem s5_243_safe : Safe 8 5 s5_243 := by
  apply safe_succ 7 5 s5_243 [] (by decide) s5_243_edges
  simp
def s5_244 : State := ⟨4, 8, 210, 146, 1645504557321206042244173864763307602241196074043954546218176790, 1, 1, 1⟩
theorem s5_244_edges : next 5 s5_244 = [] := by decide
theorem s5_244_safe : Safe 8 5 s5_244 := by
  apply safe_succ 7 5 s5_244 [] (by decide) s5_244_edges
  simp
def s5_245 : State := ⟨4, 8, 210, 146, 1645504557321206042244173864763307602241196074043954546218176790, 2, 2, 1⟩
theorem s5_245_edges : next 5 s5_245 = [] := by decide
theorem s5_245_safe : Safe 8 5 s5_245 := by
  apply safe_succ 7 5 s5_245 [] (by decide) s5_245_edges
  simp
def s5_246 : State := ⟨4, 8, 210, 146, 1645504557321206042266473248832370541628877938818173180651311382, 1, 1, 1⟩
theorem s5_246_edges : next 5 s5_246 = [] := by decide
theorem s5_246_safe : Safe 8 5 s5_246 := by
  apply safe_succ 7 5 s5_246 [] (by decide) s5_246_edges
  simp
def s5_247 : State := ⟨4, 8, 210, 146, 1645504557321206042266473248832370541628877938818173180651311382, 2, 2, 1⟩
theorem s5_247_edges : next 5 s5_247 = [] := by decide
theorem s5_247_safe : Safe 8 5 s5_247 := by
  apply safe_succ 7 5 s5_247 [] (by decide) s5_247_edges
  simp
def s5_248 : State := ⟨4, 8, 210, 146, 27973577474460502716723680785680915681964969924181232359795917078, 1, 1, 1⟩
theorem s5_248_edges : next 5 s5_248 = [] := by decide
theorem s5_248_safe : Safe 8 5 s5_248 := by
  apply safe_succ 7 5 s5_248 [] (by decide) s5_248_edges
  simp
def s5_249 : State := ⟨4, 8, 210, 146, 27973577474460502716745980169749978621352651788955450994229051670, 1, 1, 1⟩
theorem s5_249_edges : next 5 s5_249 = [] := by decide
theorem s5_249_safe : Safe 8 5 s5_249 := by
  apply safe_succ 7 5 s5_249 [] (by decide) s5_249_edges
  simp
def s5_250 : State := ⟨4, 8, 214, 146, 26328072917139296675995959295829525058040520027997147632830054678, 1, 1, 1⟩
theorem s5_250_edges : next 5 s5_250 = [] := by decide
theorem s5_250_safe : Safe 8 5 s5_250 := by
  apply safe_succ 7 5 s5_250 [] (by decide) s5_250_edges
  simp
def s5_251 : State := ⟨4, 8, 214, 146, 26328072917139296676018258679898587997428201892771366267263189270, 1, 1, 1⟩
theorem s5_251_edges : next 5 s5_251 = [] := by decide
theorem s5_251_safe : Safe 8 5 s5_251 := by
  apply safe_succ 7 5 s5_251 [] (by decide) s5_251_edges
  simp
def s5_252 : State := ⟨4, 9, 96, 224, 26959946667150639794667015087359913060919720652188328594154178282262, 2, 2, 1⟩
theorem s5_252_edges : next 5 s5_252 = [] := by decide
theorem s5_252_safe : Safe 8 5 s5_252 := by
  apply safe_succ 7 5 s5_252 [] (by decide) s5_252_edges
  simp
def s5_253 : State := ⟨4, 12, 66, 224, 26959946667150639800513021638044654181056576070814811317259024273686, 2, 0, 1⟩
theorem s5_253_edges : next 5 s5_253 = [s6_1, s6_67] := by decide
theorem s5_253_safe : Safe 8 5 s5_253 := by
  apply safe_succ 7 5 s5_253 [s6_1, s6_67] (by decide) s5_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_1_safe
  · subst z; exact s6_67_safe
def s5_254 : State := ⟨4, 12, 66, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 2, 0, 1⟩
theorem s5_254_edges : next 5 s5_254 = [s6_3, s6_68] := by decide
theorem s5_254_safe : Safe 8 5 s5_254 := by
  apply safe_succ 7 5 s5_254 [s6_3, s6_68] (by decide) s5_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_3_safe
  · subst z; exact s6_68_safe
def s5_255 : State := ⟨4, 12, 67, 146, 89204682205957097258460392877815419965083926, 2, 0, 1⟩
theorem s5_255_edges : next 5 s5_255 = [s6_5] := by decide
theorem s5_255_safe : Safe 8 5 s5_255 := by
  apply safe_succ 7 5 s5_255 [s6_5] (by decide) s5_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_5_safe
def s5_256 : State := ⟨4, 12, 67, 146, 89204682205957097258460429771303567384187158, 2, 0, 1⟩
theorem s5_256_edges : next 5 s5_256 = [s6_7] := by decide
theorem s5_256_safe : Safe 8 5 s5_256 := by
  apply safe_succ 7 5 s5_256 [s6_7] (by decide) s5_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_7_safe
def s5_257 : State := ⟨4, 12, 67, 146, 111504066275020036646142257652034054398218518, 2, 0, 1⟩
theorem s5_257_edges : next 5 s5_257 = [s6_9] := by decide
theorem s5_257_safe : Safe 8 5 s5_257 := by
  apply safe_succ 7 5 s5_257 [s6_9] (by decide) s5_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_9_safe
def s5_258 : State := ⟨4, 12, 67, 146, 111504066275020036646142294545522201817321750, 2, 0, 1⟩
theorem s5_258_edges : next 5 s5_258 = [s6_11] := by decide
theorem s5_258_safe : Safe 8 5 s5_258 := by
  apply safe_succ 7 5 s5_258 [s6_11] (by decide) s5_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_11_safe
def s5_259 : State := ⟨4, 12, 67, 162, 5846006551025023507419431648384919300597671334166, 2, 0, 1⟩
theorem s5_259_edges : next 5 s5_259 = [s6_13] := by decide
theorem s5_259_safe : Safe 8 5 s5_259 := by
  apply safe_succ 7 5 s5_259 [s6_13] (by decide) s5_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_13_safe
def s5_260 : State := ⟨4, 12, 67, 162, 5846006551025023507419431648421812788745090437398, 2, 0, 1⟩
theorem s5_260_edges : next 5 s5_260 = [s6_15] := by decide
theorem s5_260_safe : Safe 8 5 s5_260 := by
  apply safe_succ 7 5 s5_260 [s6_15] (by decide) s5_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_15_safe
def s5_261 : State := ⟨4, 12, 67, 162, 7307508186994796957939362627247703890526531031318, 2, 0, 1⟩
theorem s5_261_edges : next 5 s5_261 = [s6_17] := by decide
theorem s5_261_safe : Safe 8 5 s5_261 := by
  apply safe_succ 7 5 s5_261 [s6_17] (by decide) s5_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_17_safe
def s5_262 : State := ⟨4, 12, 67, 162, 7307508186994796957939362627284597378673950134550, 2, 0, 1⟩
theorem s5_262_edges : next 5 s5_262 = [s6_19] := by decide
theorem s5_262_safe : Safe 8 5 s5_262 := by
  apply safe_succ 7 5 s5_262 [s6_19] (by decide) s5_262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_19_safe
def s5_263 : State := ⟨4, 12, 67, 176, 95780971326419139128294233276893708537611803510771990, 2, 0, 1⟩
theorem s5_263_edges : next 5 s5_263 = [s6_21] := by decide
theorem s5_263_safe : Safe 8 5 s5_263 := by
  apply safe_succ 7 5 s5_263 [s6_21] (by decide) s5_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_21_safe
def s5_264 : State := ⟨4, 12, 67, 176, 95780971326419139128294233276893745431099950929875222, 2, 0, 1⟩
theorem s5_264_edges : next 5 s5_264 = [s6_23] := by decide
theorem s5_264_safe : Safe 8 5 s5_264 := by
  apply safe_succ 7 5 s5_264 [s6_23] (by decide) s5_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_23_safe
def s5_265 : State := ⟨4, 12, 67, 176, 95782432805755724832681813820190706547983097937334550, 2, 0, 1⟩
theorem s5_265_edges : next 5 s5_265 = [s6_25] := by decide
theorem s5_265_safe : Safe 8 5 s5_265 := by
  apply safe_succ 7 5 s5_265 [s6_25] (by decide) s5_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_25_safe
def s5_266 : State := ⟨4, 12, 67, 176, 95782432805755724832681813820190743441471245356437782, 2, 0, 1⟩
theorem s5_266_edges : next 5 s5_266 = [s6_27] := by decide
theorem s5_266_safe : Safe 8 5 s5_266 := by
  apply safe_succ 7 5 s5_266 [s6_27] (by decide) s5_266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_27_safe
def s5_267 : State := ⟨4, 12, 67, 210, 1645504557321206042177270268038248049062735287088508619142009110, 2, 0, 1⟩
theorem s5_267_edges : next 5 s5_267 = [s6_29] := by decide
theorem s5_267_safe : Safe 8 5 s5_267 := by
  apply safe_succ 7 5 s5_267 [s6_29] (by decide) s5_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_29_safe
def s5_268 : State := ⟨4, 12, 67, 210, 1645529665728147588878024865997410256586863978237638113774080278, 2, 0, 1⟩
theorem s5_268_edges : next 5 s5_268 = [s6_31] := by decide
theorem s5_268_safe : Safe 8 5 s5_268 := by
  apply safe_succ 7 5 s5_268 [s6_31] (by decide) s5_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_31_safe
def s5_269 : State := ⟨4, 12, 67, 224, 26959946667150639796128516724690815958761767718923144293006411108630, 2, 0, 1⟩
theorem s5_269_edges : next 5 s5_269 = [s6_35] := by decide
theorem s5_269_safe : Safe 8 5 s5_269 := by
  apply safe_succ 7 5 s5_269 [s6_35] (by decide) s5_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_35_safe
def s5_270 : State := ⟨4, 12, 67, 224, 26959946667150639796128516724690815958761767718960037781153830211862, 2, 0, 1⟩
theorem s5_270_edges : next 5 s5_270 = [s6_37] := by decide
theorem s5_270_safe : Safe 8 5 s5_270 := by
  apply safe_succ 7 5 s5_270 [s6_37] (by decide) s5_270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_37_safe
def s5_271 : State := ⟨4, 12, 67, 224, 26959946673427741530053695851195702463765749302309216717814513078550, 2, 0, 1⟩
theorem s5_271_edges : next 5 s5_271 = [s6_39] := by decide
theorem s5_271_safe : Safe 8 5 s5_271 := by
  apply safe_succ 7 5 s5_271 [s6_39] (by decide) s5_271_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_39_safe
def s5_272 : State := ⟨4, 12, 67, 224, 26959946673427741530053695851195702463765749302346110205961932181782, 2, 0, 1⟩
theorem s5_272_edges : next 5 s5_272 = [s6_41] := by decide
theorem s5_272_safe : Safe 8 5 s5_272 := by
  apply safe_succ 7 5 s5_272 [s6_41] (by decide) s5_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_41_safe
def s5_273 : State := ⟨4, 12, 82, 224, 26959946667150639796128516724690815958761772554515742287080852623638, 2, 0, 1⟩
theorem s5_273_edges : next 5 s5_273 = [s6_47] := by decide
theorem s5_273_safe : Safe 8 5 s5_273 := by
  apply safe_succ 7 5 s5_273 [s6_47] (by decide) s5_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_47_safe
def s5_274 : State := ⟨4, 12, 82, 224, 26959946667150639796128516724690815958761773763367774925415189123350, 2, 0, 1⟩
theorem s5_274_edges : next 5 s5_274 = [s6_49] := by decide
theorem s5_274_safe : Safe 8 5 s5_274 := by
  apply safe_succ 7 5 s5_274 [s6_49] (by decide) s5_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_49_safe
def s5_275 : State := ⟨4, 12, 82, 224, 26959946673427741530053695851195702463765754137901814711888954593558, 2, 0, 1⟩
theorem s5_275_edges : next 5 s5_275 = [s6_53] := by decide
theorem s5_275_safe : Safe 8 5 s5_275 := by
  apply safe_succ 7 5 s5_275 [s6_53] (by decide) s5_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_53_safe
def s5_276 : State := ⟨4, 12, 82, 224, 26959946673427741530053695851195702463765755346753847350223291093270, 2, 0, 1⟩
theorem s5_276_edges : next 5 s5_276 = [s6_55] := by decide
theorem s5_276_safe : Safe 8 5 s5_276 := by
  apply safe_succ 7 5 s5_276 [s6_55] (by decide) s5_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_55_safe
def s5_277 : State := ⟨4, 12, 96, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 2, 2, 1⟩
theorem s5_277_edges : next 5 s5_277 = [s6_69, s6_70] := by decide
theorem s5_277_safe : Safe 8 5 s5_277 := by
  apply safe_succ 7 5 s5_277 [s6_69, s6_70] (by decide) s5_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_69_safe
  · subst z; exact s6_70_safe
def s5_278 : State := ⟨4, 12, 162, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 2, 0, 1⟩
theorem s5_278_edges : next 5 s5_278 = [s6_64] := by decide
theorem s5_278_safe : Safe 8 5 s5_278 := by
  apply safe_succ 7 5 s5_278 [s6_64] (by decide) s5_278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_64_safe
def s5_279 : State := ⟨4, 12, 162, 224, 26959946673427741535899702400519314136580488633063668331995985940758, 2, 0, 1⟩
theorem s5_279_edges : next 5 s5_279 = [s6_66] := by decide
theorem s5_279_safe : Safe 8 5 s5_279 := by
  apply safe_succ 7 5 s5_279 [s6_66] (by decide) s5_279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_66_safe
def s5_280 : State := ⟨4, 104, 96, 224, 26959946667150639794667015087359913060919720652188328594154178282262, 2, 2, 1⟩
theorem s5_280_edges : next 5 s5_280 = [] := by decide
theorem s5_280_safe : Safe 8 5 s5_280 := by
  apply safe_succ 7 5 s5_280 [] (by decide) s5_280_edges
  simp
def s5_281 : State := ⟨4, 104, 96, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 2, 2, 1⟩
theorem s5_281_edges : next 5 s5_281 = [s6_71, s6_73] := by decide
theorem s5_281_safe : Safe 8 5 s5_281 := by
  apply safe_succ 7 5 s5_281 [s6_71, s6_73] (by decide) s5_281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_71_safe
  · subst z; exact s6_73_safe
def s5_282 : State := ⟨4, 104, 96, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 3, 1, 1⟩
theorem s5_282_edges : next 5 s5_282 = [s6_58, s6_72, s6_74] := by decide
theorem s5_282_safe : Safe 8 5 s5_282 := by
  apply safe_succ 7 5 s5_282 [s6_58, s6_72, s6_74] (by decide) s5_282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_58_safe
  · subst z; exact s6_72_safe
  · subst z; exact s6_74_safe
def s5_283 : State := ⟨4, 104, 96, 224, 26959946667150639794667015087359913060919720652483476499333531107606, 3, 1, 1⟩
theorem s5_283_edges : next 5 s5_283 = [s6_59] := by decide
theorem s5_283_safe : Safe 8 5 s5_283 := by
  apply safe_succ 7 5 s5_283 [s6_59] (by decide) s5_283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_59_safe
def s5_284 : State := ⟨4, 104, 96, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 3, 1, 1⟩
theorem s5_284_edges : next 5 s5_284 = [s6_60] := by decide
theorem s5_284_safe : Safe 8 5 s5_284 := by
  apply safe_succ 7 5 s5_284 [s6_60] (by decide) s5_284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_60_safe
def s5_285 : State := ⟨4, 104, 96, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 3, 1, 1⟩
theorem s5_285_edges : next 5 s5_285 = [s6_61] := by decide
theorem s5_285_safe : Safe 8 5 s5_285 := by
  apply safe_succ 7 5 s5_285 [s6_61] (by decide) s5_285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_61_safe
def s5_286 : State := ⟨4, 104, 96, 224, 458319093341560876509339256479674003839114031412837488291811942269206, 3, 1, 1⟩
theorem s5_286_edges : next 5 s5_286 = [s6_62] := by decide
theorem s5_286_safe : Safe 8 5 s5_286 := by
  apply safe_succ 7 5 s5_286 [s6_62] (by decide) s5_286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_62_safe
def s5_287 : State := ⟨12, 8, 66, 224, 26959946667150639800513021638044654181056576070814811317259024273686, 1, 0, 1⟩
theorem s5_287_edges : next 5 s5_287 = [s6_0, s6_75] := by decide
theorem s5_287_safe : Safe 8 5 s5_287 := by
  apply safe_succ 7 5 s5_287 [s6_0, s6_75] (by decide) s5_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_0_safe
  · subst z; exact s6_75_safe
def s5_288 : State := ⟨12, 8, 66, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 1, 0, 1⟩
theorem s5_288_edges : next 5 s5_288 = [s6_2, s6_76] := by decide
theorem s5_288_safe : Safe 8 5 s5_288 := by
  apply safe_succ 7 5 s5_288 [s6_2, s6_76] (by decide) s5_288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s6_2_safe
  · subst z; exact s6_76_safe
def s5_289 : State := ⟨12, 8, 67, 146, 89204682205957097258460392877815419965083926, 1, 0, 1⟩
theorem s5_289_edges : next 5 s5_289 = [s6_4] := by decide
theorem s5_289_safe : Safe 8 5 s5_289 := by
  apply safe_succ 7 5 s5_289 [s6_4] (by decide) s5_289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_4_safe
def s5_290 : State := ⟨12, 8, 67, 146, 89204682205957097258460429771303567384187158, 1, 0, 1⟩
theorem s5_290_edges : next 5 s5_290 = [s6_6] := by decide
theorem s5_290_safe : Safe 8 5 s5_290 := by
  apply safe_succ 7 5 s5_290 [s6_6] (by decide) s5_290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_6_safe
def s5_291 : State := ⟨12, 8, 67, 146, 111504066275020036646142257652034054398218518, 1, 0, 1⟩
theorem s5_291_edges : next 5 s5_291 = [s6_8] := by decide
theorem s5_291_safe : Safe 8 5 s5_291 := by
  apply safe_succ 7 5 s5_291 [s6_8] (by decide) s5_291_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_8_safe
def s5_292 : State := ⟨12, 8, 67, 146, 111504066275020036646142294545522201817321750, 1, 0, 1⟩
theorem s5_292_edges : next 5 s5_292 = [s6_10] := by decide
theorem s5_292_safe : Safe 8 5 s5_292 := by
  apply safe_succ 7 5 s5_292 [s6_10] (by decide) s5_292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_10_safe
def s5_293 : State := ⟨12, 8, 67, 162, 5846006551025023507419431648384919300597671334166, 1, 0, 1⟩
theorem s5_293_edges : next 5 s5_293 = [s6_12] := by decide
theorem s5_293_safe : Safe 8 5 s5_293 := by
  apply safe_succ 7 5 s5_293 [s6_12] (by decide) s5_293_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_12_safe
def s5_294 : State := ⟨12, 8, 67, 162, 5846006551025023507419431648421812788745090437398, 1, 0, 1⟩
theorem s5_294_edges : next 5 s5_294 = [s6_14] := by decide
theorem s5_294_safe : Safe 8 5 s5_294 := by
  apply safe_succ 7 5 s5_294 [s6_14] (by decide) s5_294_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_14_safe
def s5_295 : State := ⟨12, 8, 67, 162, 7307508186994796957939362627247703890526531031318, 1, 0, 1⟩
theorem s5_295_edges : next 5 s5_295 = [s6_16] := by decide
theorem s5_295_safe : Safe 8 5 s5_295 := by
  apply safe_succ 7 5 s5_295 [s6_16] (by decide) s5_295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_16_safe
def s5_296 : State := ⟨12, 8, 67, 162, 7307508186994796957939362627284597378673950134550, 1, 0, 1⟩
theorem s5_296_edges : next 5 s5_296 = [s6_18] := by decide
theorem s5_296_safe : Safe 8 5 s5_296 := by
  apply safe_succ 7 5 s5_296 [s6_18] (by decide) s5_296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_18_safe
def s5_297 : State := ⟨12, 8, 67, 176, 95780971326419139128294233276893708537611803510771990, 1, 0, 1⟩
theorem s5_297_edges : next 5 s5_297 = [s6_20] := by decide
theorem s5_297_safe : Safe 8 5 s5_297 := by
  apply safe_succ 7 5 s5_297 [s6_20] (by decide) s5_297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_20_safe
def s5_298 : State := ⟨12, 8, 67, 176, 95780971326419139128294233276893745431099950929875222, 1, 0, 1⟩
theorem s5_298_edges : next 5 s5_298 = [s6_22] := by decide
theorem s5_298_safe : Safe 8 5 s5_298 := by
  apply safe_succ 7 5 s5_298 [s6_22] (by decide) s5_298_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_22_safe
def s5_299 : State := ⟨12, 8, 67, 176, 95782432805755724832681813820190706547983097937334550, 1, 0, 1⟩
theorem s5_299_edges : next 5 s5_299 = [s6_24] := by decide
theorem s5_299_safe : Safe 8 5 s5_299 := by
  apply safe_succ 7 5 s5_299 [s6_24] (by decide) s5_299_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_24_safe
def s5_300 : State := ⟨12, 8, 67, 176, 95782432805755724832681813820190743441471245356437782, 1, 0, 1⟩
theorem s5_300_edges : next 5 s5_300 = [s6_26] := by decide
theorem s5_300_safe : Safe 8 5 s5_300 := by
  apply safe_succ 7 5 s5_300 [s6_26] (by decide) s5_300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_26_safe
def s5_301 : State := ⟨12, 8, 67, 210, 1645504557321206042177270268038248049062735287088508619142009110, 1, 0, 1⟩
theorem s5_301_edges : next 5 s5_301 = [s6_28] := by decide
theorem s5_301_safe : Safe 8 5 s5_301 := by
  apply safe_succ 7 5 s5_301 [s6_28] (by decide) s5_301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_28_safe
def s5_302 : State := ⟨12, 8, 67, 210, 1645529665728147588878024865997410256586863978237638113774080278, 1, 0, 1⟩
theorem s5_302_edges : next 5 s5_302 = [s6_30] := by decide
theorem s5_302_safe : Safe 8 5 s5_302 := by
  apply safe_succ 7 5 s5_302 [s6_30] (by decide) s5_302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_30_safe
def s5_303 : State := ⟨12, 8, 67, 224, 26959946667150639796128516724690815958761767718923144293006411108630, 1, 0, 1⟩
theorem s5_303_edges : next 5 s5_303 = [s6_34] := by decide
theorem s5_303_safe : Safe 8 5 s5_303 := by
  apply safe_succ 7 5 s5_303 [s6_34] (by decide) s5_303_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_34_safe
def s5_304 : State := ⟨12, 8, 67, 224, 26959946667150639796128516724690815958761767718960037781153830211862, 1, 0, 1⟩
theorem s5_304_edges : next 5 s5_304 = [s6_36] := by decide
theorem s5_304_safe : Safe 8 5 s5_304 := by
  apply safe_succ 7 5 s5_304 [s6_36] (by decide) s5_304_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_36_safe
def s5_305 : State := ⟨12, 8, 67, 224, 26959946673427741530053695851195702463765749302309216717814513078550, 1, 0, 1⟩
theorem s5_305_edges : next 5 s5_305 = [s6_38] := by decide
theorem s5_305_safe : Safe 8 5 s5_305 := by
  apply safe_succ 7 5 s5_305 [s6_38] (by decide) s5_305_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_38_safe
def s5_306 : State := ⟨12, 8, 67, 224, 26959946673427741530053695851195702463765749302346110205961932181782, 1, 0, 1⟩
theorem s5_306_edges : next 5 s5_306 = [s6_40] := by decide
theorem s5_306_safe : Safe 8 5 s5_306 := by
  apply safe_succ 7 5 s5_306 [s6_40] (by decide) s5_306_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_40_safe
def s5_307 : State := ⟨12, 8, 82, 224, 26959946667150639796128516724690815958761772554515742287080852623638, 1, 0, 1⟩
theorem s5_307_edges : next 5 s5_307 = [s6_46] := by decide
theorem s5_307_safe : Safe 8 5 s5_307 := by
  apply safe_succ 7 5 s5_307 [s6_46] (by decide) s5_307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_46_safe
def s5_308 : State := ⟨12, 8, 82, 224, 26959946667150639796128516724690815958761773763367774925415189123350, 1, 0, 1⟩
theorem s5_308_edges : next 5 s5_308 = [s6_48] := by decide
theorem s5_308_safe : Safe 8 5 s5_308 := by
  apply safe_succ 7 5 s5_308 [s6_48] (by decide) s5_308_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_48_safe
def s5_309 : State := ⟨12, 8, 82, 224, 26959946673427741530053695851195702463765754137901814711888954593558, 1, 0, 1⟩
theorem s5_309_edges : next 5 s5_309 = [s6_52] := by decide
theorem s5_309_safe : Safe 8 5 s5_309 := by
  apply safe_succ 7 5 s5_309 [s6_52] (by decide) s5_309_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_52_safe
def s5_310 : State := ⟨12, 8, 82, 224, 26959946673427741530053695851195702463765755346753847350223291093270, 1, 0, 1⟩
theorem s5_310_edges : next 5 s5_310 = [s6_54] := by decide
theorem s5_310_safe : Safe 8 5 s5_310 := by
  apply safe_succ 7 5 s5_310 [s6_54] (by decide) s5_310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_54_safe
def s5_311 : State := ⟨12, 8, 96, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 3, 2, 1⟩
theorem s5_311_edges : next 5 s5_311 = [s6_58, s6_77, s6_78] := by decide
theorem s5_311_safe : Safe 8 5 s5_311 := by
  apply safe_succ 7 5 s5_311 [s6_58, s6_77, s6_78] (by decide) s5_311_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s6_58_safe
  · subst z; exact s6_77_safe
  · subst z; exact s6_78_safe
def s5_312 : State := ⟨12, 8, 162, 224, 26959946667150639801974523274014427631576507049677595907187883970838, 1, 0, 1⟩
theorem s5_312_edges : next 5 s5_312 = [s6_63] := by decide
theorem s5_312_safe : Safe 8 5 s5_312 := by
  apply safe_succ 7 5 s5_312 [s6_63] (by decide) s5_312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_63_safe
def s5_313 : State := ⟨12, 8, 162, 224, 26959946673427741535899702400519314136580488633063668331995985940758, 1, 0, 1⟩
theorem s5_313_edges : next 5 s5_313 = [s6_65] := by decide
theorem s5_313_safe : Safe 8 5 s5_313 := by
  apply safe_succ 7 5 s5_313 [s6_65] (by decide) s5_313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_65_safe
def s5_314 : State := ⟨12, 104, 97, 224, 26959946667150639794667015087359913061078176977216857269341266186518, 3, 0, 1⟩
theorem s5_314_edges : next 5 s5_314 = [] := by decide
theorem s5_314_safe : Safe 8 5 s5_314 := by
  apply safe_succ 7 5 s5_314 [] (by decide) s5_314_edges
  simp
def s5_315 : State := ⟨12, 104, 112, 224, 26959946667150639794667015087359918253216579187015957124650507505942, 3, 0, 1⟩
theorem s5_315_edges : next 5 s5_315 = [] := by decide
theorem s5_315_safe : Safe 8 5 s5_315 := by
  apply safe_succ 7 5 s5_315 [] (by decide) s5_315_edges
  simp
def s5_316 : State := ⟨68, 8, 96, 224, 26959946667150639794667015087359913060919720652483476499333531107606, 3, 2, 1⟩
theorem s5_316_edges : next 5 s5_316 = [] := by decide
theorem s5_316_safe : Safe 8 5 s5_316 := by
  apply safe_succ 7 5 s5_316 [] (by decide) s5_316_edges
  simp
def s5_317 : State := ⟨86, 8, 82, 224, 26959946667150639796128516724690815958761849925768197623348033814806, 1, 0, 1⟩
theorem s5_317_edges : next 5 s5_317 = [s6_50] := by decide
theorem s5_317_safe : Safe 8 5 s5_317 := by
  apply safe_succ 7 5 s5_317 [s6_50] (by decide) s5_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_50_safe
def s5_318 : State := ⟨86, 8, 82, 224, 26959946667150639796128516724690815958761851134620230261682370314518, 1, 0, 1⟩
theorem s5_318_edges : next 5 s5_318 = [s6_51] := by decide
theorem s5_318_safe : Safe 8 5 s5_318 := by
  apply safe_succ 7 5 s5_318 [s6_51] (by decide) s5_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_51_safe
def s5_319 : State := ⟨86, 8, 82, 224, 26959946673427741530053695851195702463765831509154270048156135784726, 1, 0, 1⟩
theorem s5_319_edges : next 5 s5_319 = [s6_56] := by decide
theorem s5_319_safe : Safe 8 5 s5_319 := by
  apply safe_succ 7 5 s5_319 [s6_56] (by decide) s5_319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_56_safe
def s5_320 : State := ⟨86, 8, 82, 224, 26959946673427741530053695851195702463765832718006302686490472284438, 1, 0, 1⟩
theorem s5_320_edges : next 5 s5_320 = [s6_57] := by decide
theorem s5_320_safe : Safe 8 5 s5_320 := by
  apply safe_succ 7 5 s5_320 [s6_57] (by decide) s5_320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_57_safe
def s5_321 : State := ⟨100, 8, 96, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 3, 2, 1⟩
theorem s5_321_edges : next 5 s5_321 = [s6_60] := by decide
theorem s5_321_safe : Safe 8 5 s5_321 := by
  apply safe_succ 7 5 s5_321 [s6_60] (by decide) s5_321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_60_safe
def s5_322 : State := ⟨108, 8, 96, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 3, 2, 1⟩
theorem s5_322_edges : next 5 s5_322 = [] := by decide
theorem s5_322_safe : Safe 8 5 s5_322 := by
  apply safe_succ 7 5 s5_322 [] (by decide) s5_322_edges
  simp
def s5_323 : State := ⟨214, 8, 67, 210, 27973577474460502716656777188955856128786509137225786432719749398, 1, 0, 1⟩
theorem s5_323_edges : next 5 s5_323 = [s6_32] := by decide
theorem s5_323_safe : Safe 8 5 s5_323 := by
  apply safe_succ 7 5 s5_323 [s6_32] (by decide) s5_323_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_32_safe
def s5_324 : State := ⟨214, 8, 67, 210, 27973602582867444263357531786915018336310637828374915927351820566, 1, 0, 1⟩
theorem s5_324_edges : next 5 s5_324 = [s6_33] := by decide
theorem s5_324_safe : Safe 8 5 s5_324 := by
  apply safe_succ 7 5 s5_324 [s6_33] (by decide) s5_324_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_33_safe
def s5_325 : State := ⟨228, 8, 67, 224, 458319093341560876510800758117004906736956078479572303990664175091990, 1, 0, 1⟩
theorem s5_325_edges : next 5 s5_325 = [s6_42] := by decide
theorem s5_325_safe : Safe 8 5 s5_325 := by
  apply safe_succ 7 5 s5_325 [s6_42] (by decide) s5_325_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_42_safe
def s5_326 : State := ⟨228, 8, 67, 224, 458319093341560876510800758117004906736956078479609197478811594195222, 1, 0, 1⟩
theorem s5_326_edges : next 5 s5_326 = [s6_43] := by decide
theorem s5_326_safe : Safe 8 5 s5_326 := by
  apply safe_succ 7 5 s5_326 [s6_43] (by decide) s5_326_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_43_safe
def s5_327 : State := ⟨228, 8, 67, 224, 458319093347837978244725937243509793241960060062958376415472277061910, 1, 0, 1⟩
theorem s5_327_edges : next 5 s5_327 = [s6_44] := by decide
theorem s5_327_safe : Safe 8 5 s5_327 := by
  apply safe_succ 7 5 s5_327 [s6_44] (by decide) s5_327_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_44_safe
def s5_328 : State := ⟨228, 8, 67, 224, 458319093347837978244725937243509793241960060062995269903619696165142, 1, 0, 1⟩
theorem s5_328_edges : next 5 s5_328 = [s6_45] := by decide
theorem s5_328_safe : Safe 8 5 s5_328 := by
  apply safe_succ 7 5 s5_328 [s6_45] (by decide) s5_328_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_45_safe
def s5_329 : State := ⟨228, 8, 96, 224, 458319093341560876509339256479674003839114031412837488291811942269206, 3, 2, 1⟩
theorem s5_329_edges : next 5 s5_329 = [s6_62] := by decide
theorem s5_329_safe : Safe 8 5 s5_329 := by
  apply safe_succ 7 5 s5_329 [s6_62] (by decide) s5_329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s6_62_safe
def s4_0 : State := ⟨4, 8, 64, 131, 3743106036130323098115567425827454914838, 1, 1, 1⟩
theorem s4_0_edges : next 4 s4_0 = [s5_0] := by decide
theorem s4_0_safe : Safe 9 4 s4_0 := by
  apply safe_succ 8 4 s4_0 [s5_0] (by decide) s4_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_0_safe
def s4_1 : State := ⟨4, 8, 64, 131, 3743106036130323098115567425827454914838, 2, 2, 1⟩
theorem s4_1_edges : next 4 s4_1 = [s5_1] := by decide
theorem s4_1_safe : Safe 9 4 s4_1 := by
  apply safe_succ 8 4 s4_1 [s5_1] (by decide) s4_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1_safe
def s4_2 : State := ⟨4, 8, 64, 131, 4423670769972200025042316640690991337750, 1, 1, 1⟩
theorem s4_2_edges : next 4 s4_2 = [s5_2] := by decide
theorem s4_2_safe : Safe 9 4 s4_2 := by
  apply safe_succ 8 4 s4_2 [s5_2] (by decide) s4_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_2_safe
def s4_3 : State := ⟨4, 8, 64, 131, 4423670769972200025042316640690991337750, 2, 2, 1⟩
theorem s4_3_edges : next 4 s4_3 = [s5_3] := by decide
theorem s4_3_safe : Safe 9 4 s4_3 := by
  apply safe_succ 8 4 s4_3 [s5_3] (by decide) s4_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_3_safe
def s4_4 : State := ⟨4, 8, 64, 146, 89204682205957097258460208410374682869567766, 1, 1, 1⟩
theorem s4_4_edges : next 4 s4_4 = [s5_244, s5_40, s5_58, s5_20] := by decide
theorem s4_4_safe : Safe 9 4 s4_4 := by
  apply safe_succ 8 4 s4_4 [s5_244, s5_40, s5_58, s5_20] (by decide) s4_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_244_safe
  · subst z; exact s5_40_safe
  · subst z; exact s5_58_safe
  · subst z; exact s5_20_safe
def s4_5 : State := ⟨4, 8, 64, 146, 89204682205957097258460208410374682869567766, 2, 2, 1⟩
theorem s4_5_edges : next 4 s4_5 = [s5_245, s5_41, s5_59, s5_21] := by decide
theorem s4_5_safe : Safe 9 4 s4_5 := by
  apply safe_succ 8 4 s4_5 [s5_245, s5_41, s5_59, s5_21] (by decide) s4_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_245_safe
  · subst z; exact s5_41_safe
  · subst z; exact s5_59_safe
  · subst z; exact s5_21_safe
def s4_6 : State := ⟨4, 8, 64, 146, 89204682205957097258460503558279862222389526, 1, 1, 1⟩
theorem s4_6_edges : next 4 s4_6 = [] := by decide
theorem s4_6_safe : Safe 9 4 s4_6 := by
  apply safe_succ 8 4 s4_6 [] (by decide) s4_6_edges
  simp
def s4_7 : State := ⟨4, 8, 64, 146, 111504066275020036646142073184593317302702358, 1, 1, 1⟩
theorem s4_7_edges : next 4 s4_7 = [s5_246, s5_42, s5_60, s5_22] := by decide
theorem s4_7_safe : Safe 9 4 s4_7 := by
  apply safe_succ 8 4 s4_7 [s5_246, s5_42, s5_60, s5_22] (by decide) s4_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_246_safe
  · subst z; exact s5_42_safe
  · subst z; exact s5_60_safe
  · subst z; exact s5_22_safe
def s4_8 : State := ⟨4, 8, 64, 146, 111504066275020036646142073184593317302702358, 2, 2, 1⟩
theorem s4_8_edges : next 4 s4_8 = [s5_247, s5_43, s5_61, s5_23] := by decide
theorem s4_8_safe : Safe 9 4 s4_8 := by
  apply safe_succ 8 4 s4_8 [s5_247, s5_43, s5_61, s5_23] (by decide) s4_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_247_safe
  · subst z; exact s5_43_safe
  · subst z; exact s5_61_safe
  · subst z; exact s5_23_safe
def s4_9 : State := ⟨4, 8, 64, 146, 111504066275020036646142368332498496655524118, 1, 1, 1⟩
theorem s4_9_edges : next 4 s4_9 = [] := by decide
theorem s4_9_safe : Safe 9 4 s4_9 := by
  apply safe_succ 8 4 s4_9 [] (by decide) s4_9_edges
  simp
def s4_10 : State := ⟨4, 8, 64, 146, 1516452374911916978316746177859869819252310294, 1, 1, 1⟩
theorem s4_10_edges : next 4 s4_10 = [] := by decide
theorem s4_10_safe : Safe 9 4 s4_10 := by
  apply safe_succ 8 4 s4_10 [] (by decide) s4_10_edges
  simp
def s4_11 : State := ⟨4, 8, 64, 146, 1538751758980979917704428042634088453685444886, 1, 1, 1⟩
theorem s4_11_edges : next 4 s4_11 = [] := by decide
theorem s4_11_safe : Safe 9 4 s4_11 := by
  apply safe_succ 8 4 s4_11 [] (by decide) s4_11_edges
  simp
def s4_12 : State := ⟨4, 8, 64, 161, 2923003275682652937170185055841136605685174309142, 1, 1, 1⟩
theorem s4_12_edges : next 4 s4_12 = [s5_4] := by decide
theorem s4_12_safe : Safe 9 4 s4_12 := by
  apply safe_succ 8 4 s4_12 [s5_4] (by decide) s4_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_4_safe
def s4_13 : State := ⟨4, 8, 64, 161, 2923003275682652937170185055841136605685174309142, 2, 2, 1⟩
theorem s4_13_edges : next 4 s4_13 = [s5_5] := by decide
theorem s4_13_safe : Safe 9 4 s4_13 := by
  apply safe_succ 8 4 s4_13 [s5_5] (by decide) s4_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_5_safe
def s4_14 : State := ⟨4, 8, 64, 161, 4384504912332991121531992961630670410477570429206, 1, 1, 1⟩
theorem s4_14_edges : next 4 s4_14 = [s5_6] := by decide
theorem s4_14_safe : Safe 9 4 s4_14 := by
  apply safe_succ 8 4 s4_14 [s5_6] (by decide) s4_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_6_safe
def s4_15 : State := ⟨4, 8, 64, 161, 4384504912332991121531992961630670410477570429206, 2, 2, 1⟩
theorem s4_15_edges : next 4 s4_15 = [s5_7] := by decide
theorem s4_15_safe : Safe 9 4 s4_15 := by
  apply safe_succ 8 4 s4_15 [s5_7] (by decide) s4_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_7_safe
def s4_16 : State := ⟨4, 8, 64, 162, 5846006551025023507419431648200451859860575814422, 2, 2, 1⟩
theorem s4_16_edges : next 4 s4_16 = [] := by decide
theorem s4_16_safe : Safe 9 4 s4_16 := by
  apply safe_succ 8 4 s4_16 [] (by decide) s4_16_edges
  simp
def s4_17 : State := ⟨4, 8, 64, 162, 5846006551025023507419431648200451859860575818006, 1, 1, 1⟩
theorem s4_17_edges : next 4 s4_17 = [s5_44, s5_62, s5_8] := by decide
theorem s4_17_safe : Safe 9 4 s4_17 := by
  apply safe_succ 8 4 s4_17 [s5_44, s5_62, s5_8] (by decide) s4_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_44_safe
  · subst z; exact s5_62_safe
  · subst z; exact s5_8_safe
def s4_18 : State := ⟨4, 8, 64, 162, 5846006551025023507419431648200451859860575818006, 2, 2, 1⟩
theorem s4_18_edges : next 4 s4_18 = [s5_45, s5_63, s5_9] := by decide
theorem s4_18_safe : Safe 9 4 s4_18 := by
  apply safe_succ 8 4 s4_18 [s5_45, s5_63, s5_9] (by decide) s4_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_45_safe
  · subst z; exact s5_63_safe
  · subst z; exact s5_9_safe
def s4_19 : State := ⟨4, 8, 64, 162, 7307508186994796957939362627063236449789435511574, 2, 2, 1⟩
theorem s4_19_edges : next 4 s4_19 = [] := by decide
theorem s4_19_safe : Safe 9 4 s4_19 := by
  apply safe_succ 8 4 s4_19 [] (by decide) s4_19_edges
  simp
def s4_20 : State := ⟨4, 8, 64, 162, 7307508186994796957939362627063236449789435515158, 1, 1, 1⟩
theorem s4_20_edges : next 4 s4_20 = [s5_46, s5_64, s5_10] := by decide
theorem s4_20_safe : Safe 9 4 s4_20 := by
  apply safe_succ 8 4 s4_20 [s5_46, s5_64, s5_10] (by decide) s4_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_46_safe
  · subst z; exact s5_64_safe
  · subst z; exact s5_10_safe
def s4_21 : State := ⟨4, 8, 64, 162, 7307508186994796957939362627063236449789435515158, 2, 2, 1⟩
theorem s4_21_edges : next 4 s4_21 = [s5_47, s5_65, s5_11] := by decide
theorem s4_21_safe : Safe 9 4 s4_21 := by
  apply safe_succ 8 4 s4_21 [s5_47, s5_65, s5_11] (by decide) s4_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_47_safe
  · subst z; exact s5_65_safe
  · subst z; exact s5_11_safe
def s4_22 : State := ⟨4, 8, 64, 162, 1502423683177869611747992700349674263987535499821334, 2, 2, 1⟩
theorem s4_22_edges : next 4 s4_22 = [] := by decide
theorem s4_22_safe : Safe 9 4 s4_22 := by
  apply safe_succ 8 4 s4_22 [] (by decide) s4_22_edges
  simp
def s4_23 : State := ⟨4, 8, 64, 162, 1503885184813839385198512631328537048577464359518486, 2, 2, 1⟩
theorem s4_23_edges : next 4 s4_23 = [] := by decide
theorem s4_23_safe : Safe 9 4 s4_23 := by
  apply safe_succ 8 4 s4_23 [] (by decide) s4_23_edges
  simp
def s4_24 : State := ⟨4, 8, 64, 171, 3004847366356079505862906339162793455838424763269398, 0, 0, 1⟩
theorem s4_24_edges : next 4 s4_24 = [] := by decide
theorem s4_24_safe : Safe 9 4 s4_24 := by
  apply safe_succ 8 4 s4_24 [] (by decide) s4_24_edges
  simp
def s4_25 : State := ⟨4, 8, 64, 171, 3004847366356760070596748216089720205053288299692310, 0, 0, 1⟩
theorem s4_25_edges : next 4 s4_25 = [] := by decide
theorem s4_25_safe : Safe 9 4 s4_25 := by
  apply safe_succ 8 4 s4_25 [] (by decide) s4_25_edges
  simp
def s4_26 : State := ⟨4, 8, 64, 171, 3007770369628019052763946201120519025018282482663702, 0, 0, 1⟩
theorem s4_26_edges : next 4 s4_26 = [] := by decide
theorem s4_26_safe : Safe 9 4 s4_26 := by
  apply safe_succ 8 4 s4_26 [] (by decide) s4_26_edges
  simp
def s4_27 : State := ⟨4, 8, 64, 171, 3009231871264669390948308009026308558823074878783766, 0, 0, 1⟩
theorem s4_27_edges : next 4 s4_27 = [] := by decide
theorem s4_27_safe : Safe 9 4 s4_27 := by
  apply safe_succ 8 4 s4_27 [] (by decide) s4_27_edges
  simp
def s4_28 : State := ⟨4, 8, 64, 171, 3010693372903361423334195447712878340272457884172566, 0, 0, 1⟩
theorem s4_28_edges : next 4 s4_28 = [] := by decide
theorem s4_28_safe : Safe 9 4 s4_28 := by
  apply safe_succ 8 4 s4_28 [] (by decide) s4_28_edges
  simp
def s4_29 : State := ⟨4, 8, 64, 171, 3012154874539331196784715378691741124862386743869718, 0, 0, 1⟩
theorem s4_29_edges : next 4 s4_29 = [] := by decide
theorem s4_29_safe : Safe 9 4 s4_29 := by
  apply safe_succ 8 4 s4_29 [] (by decide) s4_29_edges
  simp
def s4_30 : State := ⟨4, 8, 64, 171, 4495579036431558788229139237752621888242885347836182, 0, 0, 1⟩
theorem s4_30_edges : next 4 s4_30 = [] := by decide
theorem s4_30_safe : Safe 9 4 s4_30 := by
  apply safe_succ 8 4 s4_30 [] (by decide) s4_30_edges
  simp
def s4_31 : State := ⟨4, 8, 64, 171, 4497040538067528561679659168731484672832814207533334, 0, 0, 1⟩
theorem s4_31_edges : next 4 s4_31 = [] := by decide
theorem s4_31_safe : Safe 9 4 s4_31 := by
  apply safe_succ 8 4 s4_31 [] (by decide) s4_31_edges
  simp
def s4_32 : State := ⟨4, 8, 64, 176, 95780971326419139128294233276893524070171066415255830, 1, 1, 1⟩
theorem s4_32_edges : next 4 s4_32 = [s5_48, s5_66] := by decide
theorem s4_32_safe : Safe 9 4 s4_32 := by
  apply safe_succ 8 4 s4_32 [s5_48, s5_66] (by decide) s4_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_48_safe
  · subst z; exact s5_66_safe
def s4_33 : State := ⟨4, 8, 64, 176, 95780971326419139128294233276893524070171066415255830, 2, 2, 1⟩
theorem s4_33_edges : next 4 s4_33 = [s5_49, s5_67] := by decide
theorem s4_33_safe : Safe 9 4 s4_33 := by
  apply safe_succ 8 4 s4_33 [s5_49, s5_67] (by decide) s4_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_49_safe
  · subst z; exact s5_67_safe
def s4_34 : State := ⟨4, 8, 64, 176, 95782432805755724832681813820190522080542360841818390, 1, 1, 1⟩
theorem s4_34_edges : next 4 s4_34 = [s5_50, s5_68] := by decide
theorem s4_34_safe : Safe 9 4 s4_34 := by
  apply safe_succ 8 4 s4_34 [s5_50, s5_68] (by decide) s4_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_50_safe
  · subst z; exact s5_68_safe
def s4_35 : State := ⟨4, 8, 64, 176, 95782432805755724832681813820190522080542360841818390, 2, 2, 1⟩
theorem s4_35_edges : next 4 s4_35 = [s5_51, s5_69] := by decide
theorem s4_35_safe : Safe 9 4 s4_35 := by
  apply safe_succ 8 4 s4_35 [s5_51, s5_69] (by decide) s4_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_51_safe
  · subst z; exact s5_69_safe
def s4_36 : State := ⟨4, 8, 64, 193, 12554203470773361528692425947178148222613281455301378248982, 1, 1, 1⟩
theorem s4_36_edges : next 4 s4_36 = [] := by decide
theorem s4_36_safe : Safe 9 4 s4_36 := by
  apply safe_succ 8 4 s4_36 [] (by decide) s4_36_edges
  simp
def s4_37 : State := ⟨4, 8, 64, 193, 12554203470773361528692425947178148222613281455301378248982, 2, 2, 1⟩
theorem s4_37_edges : next 4 s4_37 = [] := by decide
theorem s4_37_safe : Safe 9 4 s4_37 := by
  apply safe_succ 8 4 s4_37 [] (by decide) s4_37_edges
  simp
def s4_38 : State := ⟨4, 8, 64, 193, 18831305206160042291847650636543937711788887684901876338966, 1, 1, 1⟩
theorem s4_38_edges : next 4 s4_38 = [] := by decide
theorem s4_38_safe : Safe 9 4 s4_38 := by
  apply safe_succ 8 4 s4_38 [] (by decide) s4_38_edges
  simp
def s4_39 : State := ⟨4, 8, 64, 193, 18831305206160042291847650636543937711788887684901876338966, 2, 2, 1⟩
theorem s4_39_edges : next 4 s4_39 = [] := by decide
theorem s4_39_safe : Safe 9 4 s4_39 := by
  apply safe_succ 8 4 s4_39 [] (by decide) s4_39_edges
  simp
def s4_40 : State := ⟨4, 8, 64, 194, 25108406941546723057044569527435357981744741559092983697686, 1, 1, 1⟩
theorem s4_40_edges : next 4 s4_40 = [s5_24] := by decide
theorem s4_40_safe : Safe 9 4 s4_40 := by
  apply safe_succ 8 4 s4_40 [s5_24] (by decide) s4_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_24_safe
def s4_41 : State := ⟨4, 8, 64, 194, 25108406941546723057044569527435357981744741559092983697686, 2, 2, 1⟩
theorem s4_41_edges : next 4 s4_41 = [s5_25] := by decide
theorem s4_41_safe : Safe 9 4 s4_41 := by
  apply safe_succ 8 4 s4_41 [s5_25] (by decide) s4_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_25_safe
def s4_42 : State := ⟨4, 8, 64, 194, 31385508676933403819519229482959270543993598573829945364758, 1, 1, 1⟩
theorem s4_42_edges : next 4 s4_42 = [s5_26] := by decide
theorem s4_42_safe : Safe 9 4 s4_42 := by
  apply safe_succ 8 4 s4_42 [s5_26] (by decide) s4_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_26_safe
def s4_43 : State := ⟨4, 8, 64, 194, 31385508676933403819519229482959270543993598573829945364758, 2, 2, 1⟩
theorem s4_43_edges : next 4 s4_43 = [s5_27] := by decide
theorem s4_43_safe : Safe 9 4 s4_43 := by
  apply safe_succ 8 4 s4_43 [s5_27] (by decide) s4_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_27_safe
def s4_44 : State := ⟨4, 8, 64, 208, 411376139330301510561043381120235170325683166502394837115932950, 1, 1, 1⟩
theorem s4_44_edges : next 4 s4_44 = [s5_28] := by decide
theorem s4_44_safe : Safe 9 4 s4_44 := by
  apply safe_succ 8 4 s4_44 [s5_28] (by decide) s4_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_28_safe
def s4_45 : State := ⟨4, 8, 64, 208, 411376139330301510561043381120235170325683166502394837115932950, 2, 2, 1⟩
theorem s4_45_edges : next 4 s4_45 = [s5_29] := by decide
theorem s4_45_safe : Safe 9 4 s4_45 := by
  apply safe_succ 8 4 s4_45 [s5_29] (by decide) s4_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_29_safe
def s4_46 : State := ⟨4, 8, 64, 208, 411382416432036897219506471711127754850563550585190939644465430, 1, 1, 1⟩
theorem s4_46_edges : next 4 s4_46 = [s5_30] := by decide
theorem s4_46_safe : Safe 9 4 s4_46 := by
  apply safe_succ 8 4 s4_46 [s5_30] (by decide) s4_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_30_safe
def s4_47 : State := ⟨4, 8, 64, 208, 411382416432036897219506471711127754850563550585190939644465430, 2, 2, 1⟩
theorem s4_47_edges : next 4 s4_47 = [s5_31] := by decide
theorem s4_47_safe : Safe 9 4 s4_47 := by
  apply safe_succ 8 4 s4_47 [s5_31] (by decide) s4_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_31_safe
def s4_48 : State := ⟨4, 8, 64, 214, 26328072917139296675995959295829525058040520027997147632830054678, 0, 0, 1⟩
theorem s4_48_edges : next 4 s4_48 = [] := by decide
theorem s4_48_safe : Safe 9 4 s4_48 := by
  apply safe_succ 8 4 s4_48 [] (by decide) s4_48_edges
  simp
def s4_49 : State := ⟨4, 8, 64, 214, 26328072917139296676018258679898587997428201892771366267263189270, 0, 0, 1⟩
theorem s4_49_edges : next 4 s4_49 = [] := by decide
theorem s4_49_safe : Safe 9 4 s4_49 := by
  apply safe_succ 8 4 s4_49 [] (by decide) s4_49_edges
  simp
def s4_50 : State := ⟨4, 8, 64, 214, 27973577474460502716723680785680915681964969924181232359795917078, 0, 0, 1⟩
theorem s4_50_edges : next 4 s4_50 = [] := by decide
theorem s4_50_safe : Safe 9 4 s4_50 := by
  apply safe_succ 8 4 s4_50 [] (by decide) s4_50_edges
  simp
def s4_51 : State := ⟨4, 8, 64, 214, 27973577474460502716745980169749978621352651788955450994229051670, 0, 0, 1⟩
theorem s4_51_edges : next 4 s4_51 = [] := by decide
theorem s4_51_safe : Safe 9 4 s4_51 := by
  apply safe_succ 8 4 s4_51 [] (by decide) s4_51_edges
  simp
def s4_52 : State := ⟨4, 8, 64, 214, 27973602582867444263357533148044486020064491460512416769910046998, 0, 0, 1⟩
theorem s4_52_edges : next 4 s4_52 = [] := by decide
theorem s4_52_safe : Safe 9 4 s4_52 := by
  apply safe_succ 8 4 s4_52 [] (by decide) s4_52_edges
  simp
def s4_53 : State := ⟨4, 8, 64, 214, 27973608859969179650038295622704441543977053709369431506871714070, 0, 0, 1⟩
theorem s4_53_edges : next 4 s4_53 = [] := by decide
theorem s4_53_safe : Safe 9 4 s4_53 := by
  apply safe_succ 8 4 s4_53 [] (by decide) s4_53_edges
  simp
def s4_54 : State := ⟨4, 8, 64, 214, 28384953613790804227195519484595193755032192882273252514042282262, 0, 0, 1⟩
theorem s4_54_edges : next 4 s4_54 = [] := by decide
theorem s4_54_safe : Safe 9 4 s4_54 := by
  apply safe_succ 8 4 s4_54 [] (by decide) s4_54_edges
  simp
def s4_55 : State := ⟨4, 8, 64, 214, 28384959890892539613853982575186086339557073266356048616570814742, 0, 0, 1⟩
theorem s4_55_edges : next 4 s4_55 = [] := by decide
theorem s4_55_safe : Safe 9 4 s4_55 := by
  apply safe_succ 8 4 s4_55 [] (by decide) s4_55_edges
  simp
def s4_56 : State := ⟨4, 8, 64, 224, 26959946667150639796128516724690815958761767718738676852269315588886, 2, 2, 1⟩
theorem s4_56_edges : next 4 s4_56 = [] := by decide
theorem s4_56_safe : Safe 9 4 s4_56 := by
  apply safe_succ 8 4 s4_56 [] (by decide) s4_56_edges
  simp
def s4_57 : State := ⟨4, 8, 64, 224, 26959946667150639796128516724690815958761767718738676852269315592470, 1, 1, 1⟩
theorem s4_57_edges : next 4 s4_57 = [s5_52, s5_76, s5_136] := by decide
theorem s4_57_safe : Safe 9 4 s4_57 := by
  apply safe_succ 8 4 s4_57 [s5_52, s5_76, s5_136] (by decide) s4_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_52_safe
  · subst z; exact s5_76_safe
  · subst z; exact s5_136_safe
def s4_58 : State := ⟨4, 8, 64, 224, 26959946667150639796128516724690815958761767718738676852269315592470, 2, 2, 1⟩
theorem s4_58_edges : next 4 s4_58 = [s5_53, s5_77, s5_137] := by decide
theorem s4_58_safe : Safe 9 4 s4_58 := by
  apply safe_succ 8 4 s4_58 [s5_53, s5_77, s5_137] (by decide) s4_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_53_safe
  · subst z; exact s5_77_safe
  · subst z; exact s5_137_safe
def s4_59 : State := ⟨4, 8, 64, 224, 26959946667150639796128516724690815958761767719033824757448668414230, 1, 1, 1⟩
theorem s4_59_edges : next 4 s4_59 = [] := by decide
theorem s4_59_safe : Safe 9 4 s4_59 := by
  apply safe_succ 8 4 s4_59 [] (by decide) s4_59_edges
  simp
def s4_60 : State := ⟨4, 8, 64, 224, 26959946673427741530053695851195702463765749302124749277077417558806, 2, 2, 1⟩
theorem s4_60_edges : next 4 s4_60 = [] := by decide
theorem s4_60_safe : Safe 9 4 s4_60 := by
  apply safe_succ 8 4 s4_60 [] (by decide) s4_60_edges
  simp
def s4_61 : State := ⟨4, 8, 64, 224, 26959946673427741530053695851195702463765749302124749277077417562390, 1, 1, 1⟩
theorem s4_61_edges : next 4 s4_61 = [s5_54, s5_78, s5_138] := by decide
theorem s4_61_safe : Safe 9 4 s4_61 := by
  apply safe_succ 8 4 s4_61 [s5_54, s5_78, s5_138] (by decide) s4_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_54_safe
  · subst z; exact s5_78_safe
  · subst z; exact s5_138_safe
def s4_62 : State := ⟨4, 8, 64, 224, 26959946673427741530053695851195702463765749302124749277077417562390, 2, 2, 1⟩
theorem s4_62_edges : next 4 s4_62 = [s5_55, s5_79, s5_139] := by decide
theorem s4_62_safe : Safe 9 4 s4_62 := by
  apply safe_succ 8 4 s4_62 [s5_55, s5_79, s5_139] (by decide) s4_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_55_safe
  · subst z; exact s5_79_safe
  · subst z; exact s5_139_safe
def s4_63 : State := ⟨4, 8, 64, 224, 26959946673427741530053695851195702463765749302419897182256770384150, 1, 1, 1⟩
theorem s4_63_edges : next 4 s4_63 = [] := by decide
theorem s4_63_safe : Safe 9 4 s4_63 := by
  apply safe_succ 8 4 s4_63 [] (by decide) s4_63_edges
  simp
def s4_64 : State := ⟨4, 8, 64, 224, 26959946773861369296240588072568333235088411959762436388501969764630, 1, 1, 1⟩
theorem s4_64_edges : next 4 s4_64 = [] := by decide
theorem s4_64_safe : Safe 9 4 s4_64 := by
  apply safe_succ 8 4 s4_64 [] (by decide) s4_64_edges
  simp
def s4_65 : State := ⟨4, 8, 64, 224, 458319093341560876510800758117004906736956078479387836549927079575830, 1, 1, 1⟩
theorem s4_65_edges : next 4 s4_65 = [s5_56, s5_80] := by decide
theorem s4_65_safe : Safe 9 4 s4_65 := by
  apply safe_succ 8 4 s4_65 [s5_56, s5_80] (by decide) s4_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_56_safe
  · subst z; exact s5_80_safe
def s4_66 : State := ⟨4, 8, 64, 224, 458319093347837978244725937243509793241960060062773908974735181545750, 1, 1, 1⟩
theorem s4_66_edges : next 4 s4_66 = [s5_57, s5_81] := by decide
theorem s4_66_safe : Safe 9 4 s4_66 := by
  apply safe_succ 8 4 s4_66 [s5_57, s5_81] (by decide) s4_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_57_safe
  · subst z; exact s5_81_safe
def s4_67 : State := ⟨4, 8, 65, 129, 1020847100762815390445464054520728326422, 1, 1, 1⟩
theorem s4_67_edges : next 4 s4_67 = [s5_82] := by decide
theorem s4_67_safe : Safe 9 4 s4_67 := by
  apply safe_succ 8 4 s4_67 [s5_82] (by decide) s4_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_82_safe
def s4_68 : State := ⟨4, 8, 65, 129, 1020847100762815390445464054520728326422, 2, 2, 1⟩
theorem s4_68_edges : next 4 s4_68 = [s5_83] := by decide
theorem s4_68_safe : Safe 9 4 s4_68 := by
  apply safe_succ 8 4 s4_68 [s5_83] (by decide) s4_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_83_safe
def s4_69 : State := ⟨4, 8, 65, 130, 1701411834604692317372213269384264749334, 1, 1, 1⟩
theorem s4_69_edges : next 4 s4_69 = [s5_86, s5_40, s5_44] := by decide
theorem s4_69_safe : Safe 9 4 s4_69 := by
  apply safe_succ 8 4 s4_69 [s5_86, s5_40, s5_44] (by decide) s4_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_86_safe
  · subst z; exact s5_40_safe
  · subst z; exact s5_44_safe
def s4_70 : State := ⟨4, 8, 65, 130, 1701411834604692317372213269384264749334, 2, 2, 1⟩
theorem s4_70_edges : next 4 s4_70 = [s5_87, s5_41, s5_45] := by decide
theorem s4_70_safe : Safe 9 4 s4_70 := by
  apply safe_succ 8 4 s4_70 [s5_87, s5_41, s5_45] (by decide) s4_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_87_safe
  · subst z; exact s5_41_safe
  · subst z; exact s5_45_safe
def s4_71 : State := ⟨4, 8, 65, 132, 5784800237655953878932708558565483286806, 1, 1, 1⟩
theorem s4_71_edges : next 4 s4_71 = [s5_90] := by decide
theorem s4_71_safe : Safe 9 4 s4_71 := by
  apply safe_succ 8 4 s4_71 [s5_90] (by decide) s4_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_90_safe
def s4_72 : State := ⟨4, 8, 65, 132, 5784800237655953878932708558565483286806, 2, 2, 1⟩
theorem s4_72_edges : next 4 s4_72 = [s5_91] := by decide
theorem s4_72_safe : Safe 9 4 s4_72 := by
  apply safe_succ 8 4 s4_72 [s5_91] (by decide) s4_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_91_safe
def s4_73 : State := ⟨4, 8, 65, 132, 1399581375145819900224915100599088077406486, 2, 2, 1⟩
theorem s4_73_edges : next 4 s4_73 = [s5_94] := by decide
theorem s4_73_safe : Safe 9 4 s4_73 := by
  apply safe_succ 8 4 s4_73 [s5_94] (by decide) s4_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_94_safe
def s4_74 : State := ⟨4, 8, 65, 136, 87452568298681185110142614342189854036246, 1, 1, 1⟩
theorem s4_74_edges : next 4 s4_74 = [s5_96] := by decide
theorem s4_74_safe : Safe 9 4 s4_74 := by
  apply safe_succ 8 4 s4_74 [s5_96] (by decide) s4_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_96_safe
def s4_75 : State := ⟨4, 8, 65, 136, 87452568298681185110142614342189854036246, 2, 2, 1⟩
theorem s4_75_edges : next 4 s4_75 = [s5_97] := by decide
theorem s4_75_safe : Safe 9 4 s4_75 := by
  apply safe_succ 8 4 s4_75 [s5_97] (by decide) s4_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_97_safe
def s4_76 : State := ⟨4, 8, 65, 136, 1481249143206845131456125006382712448155926, 1, 1, 1⟩
theorem s4_76_edges : next 4 s4_76 = [s5_100] := by decide
theorem s4_76_safe : Safe 9 4 s4_76 := by
  apply safe_succ 8 4 s4_76 [s5_100] (by decide) s4_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_100_safe
def s4_77 : State := ⟨4, 8, 65, 140, 1394136857275084884809501106880179786027286, 1, 1, 1⟩
theorem s4_77_edges : next 4 s4_77 = [s5_102] := by decide
theorem s4_77_safe : Safe 9 4 s4_77 := by
  apply safe_succ 8 4 s4_77 [s5_102] (by decide) s4_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_102_safe
def s4_78 : State := ⟨4, 8, 65, 140, 1394136857275084884809501106880179786027286, 2, 2, 1⟩
theorem s4_78_edges : next 4 s4_78 = [s5_103] := by decide
theorem s4_78_safe : Safe 9 4 s4_78 := by
  apply safe_succ 8 4 s4_78 [s5_103] (by decide) s4_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_103_safe
def s4_79 : State := ⟨4, 8, 65, 144, 22301085480897544079999236987488018697883926, 1, 1, 1⟩
theorem s4_79_edges : next 4 s4_79 = [s5_106, s5_42, s5_48] := by decide
theorem s4_79_safe : Safe 9 4 s4_79 := by
  apply safe_succ 8 4 s4_79 [s5_106, s5_42, s5_48] (by decide) s4_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_106_safe
  · subst z; exact s5_42_safe
  · subst z; exact s5_48_safe
def s4_80 : State := ⟨4, 8, 65, 144, 22301085480897544079999236987488018697883926, 2, 2, 1⟩
theorem s4_80_edges : next 4 s4_80 = [s5_107, s5_43, s5_49] := by decide
theorem s4_80_safe : Safe 9 4 s4_80 := by
  apply safe_succ 8 4 s4_80 [s5_107, s5_43, s5_49] (by decide) s4_80_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_107_safe
  · subst z; exact s5_43_safe
  · subst z; exact s5_49_safe
def s4_81 : State := ⟨4, 8, 65, 160, 1461501637671185285124623296234997859313124446486, 1, 1, 1⟩
theorem s4_81_edges : next 4 s4_81 = [s5_110, s5_46, s5_50] := by decide
theorem s4_81_safe : Safe 9 4 s4_81 := by
  apply safe_succ 8 4 s4_81 [s5_110, s5_46, s5_50] (by decide) s4_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_110_safe
  · subst z; exact s5_46_safe
  · subst z; exact s5_50_safe
def s4_82 : State := ⟨4, 8, 65, 160, 1461501637671185285124623296234997859313124446486, 2, 2, 1⟩
theorem s4_82_edges : next 4 s4_82 = [s5_111, s5_47, s5_51] := by decide
theorem s4_82_safe : Safe 9 4 s4_82 := by
  apply safe_succ 8 4 s4_82 [s5_111, s5_47, s5_51] (by decide) s4_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_111_safe
  · subst z; exact s5_47_safe
  · subst z; exact s5_51_safe
def s4_83 : State := ⟨4, 8, 65, 192, 6277101735386680764176071790128604879621070284121226416406, 1, 1, 1⟩
theorem s4_83_edges : next 4 s4_83 = [s5_114, s5_54] := by decide
theorem s4_83_safe : Safe 9 4 s4_83 := by
  apply safe_succ 8 4 s4_83 [s5_114, s5_54] (by decide) s4_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_114_safe
  · subst z; exact s5_54_safe
def s4_84 : State := ⟨4, 8, 65, 192, 6277101735386680764176071790128604879621070284121226416406, 2, 2, 1⟩
theorem s4_84_edges : next 4 s4_84 = [s5_115, s5_55] := by decide
theorem s4_84_safe : Safe 9 4 s4_84 := by
  apply safe_succ 8 4 s4_84 [s5_115, s5_55] (by decide) s4_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_115_safe
  · subst z; exact s5_55_safe
def s4_85 : State := ⟨4, 8, 65, 193, 12554203470773361528011861213336271295723425728585260929302, 1, 1, 1⟩
theorem s4_85_edges : next 4 s4_85 = [s5_118] := by decide
theorem s4_85_safe : Safe 9 4 s4_85 := by
  apply safe_succ 8 4 s4_85 [s5_118] (by decide) s4_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_118_safe
def s4_86 : State := ⟨4, 8, 65, 193, 12554203470773361528011861213336271295723425728585260929302, 2, 2, 1⟩
theorem s4_86_edges : next 4 s4_86 = [s5_119] := by decide
theorem s4_86_safe : Safe 9 4 s4_86 := by
  apply safe_succ 8 4 s4_86 [s5_119] (by decide) s4_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_119_safe
def s4_87 : State := ⟨4, 8, 66, 129, 1020847100762815390482357542668147429654, 1, 1, 1⟩
theorem s4_87_edges : next 4 s4_87 = [s5_84, s5_140] := by decide
theorem s4_87_safe : Safe 9 4 s4_87 := by
  apply safe_succ 8 4 s4_87 [s5_84, s5_140] (by decide) s4_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_84_safe
  · subst z; exact s5_140_safe
def s4_88 : State := ⟨4, 8, 66, 129, 1020847100762815390482357542668147429654, 2, 2, 1⟩
theorem s4_88_edges : next 4 s4_88 = [s5_85, s5_141] := by decide
theorem s4_88_safe : Safe 9 4 s4_88 := by
  apply safe_succ 8 4 s4_88 [s5_85, s5_141] (by decide) s4_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_85_safe
  · subst z; exact s5_141_safe
def s4_89 : State := ⟨4, 8, 66, 130, 1701411834604692317409106757531683852566, 1, 1, 1⟩
theorem s4_89_edges : next 4 s4_89 = [s5_88, s5_146, s5_58, s5_62] := by decide
theorem s4_89_safe : Safe 9 4 s4_89 := by
  apply safe_succ 8 4 s4_89 [s5_88, s5_146, s5_58, s5_62] (by decide) s4_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_88_safe
  · subst z; exact s5_146_safe
  · subst z; exact s5_58_safe
  · subst z; exact s5_62_safe
def s4_90 : State := ⟨4, 8, 66, 130, 1701411834604692317409106757531683852566, 2, 2, 1⟩
theorem s4_90_edges : next 4 s4_90 = [s5_89, s5_147, s5_59, s5_63] := by decide
theorem s4_90_safe : Safe 9 4 s4_90 := by
  apply safe_succ 8 4 s4_90 [s5_89, s5_147, s5_59, s5_63] (by decide) s4_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_89_safe
  · subst z; exact s5_147_safe
  · subst z; exact s5_59_safe
  · subst z; exact s5_63_safe
def s4_91 : State := ⟨4, 8, 66, 132, 5784800237655953878969602046712902390038, 1, 1, 1⟩
theorem s4_91_edges : next 4 s4_91 = [s5_92, s5_152] := by decide
theorem s4_91_safe : Safe 9 4 s4_91 := by
  apply safe_succ 8 4 s4_91 [s5_92, s5_152] (by decide) s4_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_92_safe
  · subst z; exact s5_152_safe
def s4_92 : State := ⟨4, 8, 66, 132, 5784800237655953878969602046712902390038, 2, 2, 1⟩
theorem s4_92_edges : next 4 s4_92 = [s5_93, s5_153] := by decide
theorem s4_92_safe : Safe 9 4 s4_92 := by
  apply safe_succ 8 4 s4_92 [s5_93, s5_153] (by decide) s4_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_93_safe
  · subst z; exact s5_153_safe
def s4_93 : State := ⟨4, 8, 66, 132, 1399581375145819900224951994087235496509718, 2, 2, 1⟩
theorem s4_93_edges : next 4 s4_93 = [s5_95, s5_158] := by decide
theorem s4_93_safe : Safe 9 4 s4_93 := by
  apply safe_succ 8 4 s4_93 [s5_95, s5_158] (by decide) s4_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_95_safe
  · subst z; exact s5_158_safe
def s4_94 : State := ⟨4, 8, 66, 136, 87452568298681185110179507830337273139478, 1, 1, 1⟩
theorem s4_94_edges : next 4 s4_94 = [s5_98, s5_160] := by decide
theorem s4_94_safe : Safe 9 4 s4_94 := by
  apply safe_succ 8 4 s4_94 [s5_98, s5_160] (by decide) s4_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_98_safe
  · subst z; exact s5_160_safe
def s4_95 : State := ⟨4, 8, 66, 136, 87452568298681185110179507830337273139478, 2, 2, 1⟩
theorem s4_95_edges : next 4 s4_95 = [s5_99, s5_161] := by decide
theorem s4_95_safe : Safe 9 4 s4_95 := by
  apply safe_succ 8 4 s4_95 [s5_99, s5_161] (by decide) s4_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_99_safe
  · subst z; exact s5_161_safe
def s4_96 : State := ⟨4, 8, 66, 136, 1481249143206845131456161899870859867259158, 1, 1, 1⟩
theorem s4_96_edges : next 4 s4_96 = [s5_101, s5_166] := by decide
theorem s4_96_safe : Safe 9 4 s4_96 := by
  apply safe_succ 8 4 s4_96 [s5_101, s5_166] (by decide) s4_96_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_101_safe
  · subst z; exact s5_166_safe
def s4_97 : State := ⟨4, 8, 66, 140, 1394136857275084884809538000368327205130518, 1, 1, 1⟩
theorem s4_97_edges : next 4 s4_97 = [s5_104, s5_168] := by decide
theorem s4_97_safe : Safe 9 4 s4_97 := by
  apply safe_succ 8 4 s4_97 [s5_104, s5_168] (by decide) s4_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_104_safe
  · subst z; exact s5_168_safe
def s4_98 : State := ⟨4, 8, 66, 140, 1394136857275084884809538000368327205130518, 2, 2, 1⟩
theorem s4_98_edges : next 4 s4_98 = [s5_105, s5_169] := by decide
theorem s4_98_safe : Safe 9 4 s4_98 := by
  apply safe_succ 8 4 s4_98 [s5_105, s5_169] (by decide) s4_98_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_105_safe
  · subst z; exact s5_169_safe
def s4_99 : State := ⟨4, 8, 66, 144, 22301085480897544079999273880976166116987158, 1, 1, 1⟩
theorem s4_99_edges : next 4 s4_99 = [s5_238, s5_108, s5_172, s5_70, s5_60, s5_66] := by decide
theorem s4_99_safe : Safe 9 4 s4_99 := by
  apply safe_succ 8 4 s4_99 [s5_238, s5_108, s5_172, s5_70, s5_60, s5_66] (by decide) s4_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_238_safe
  · subst z; exact s5_108_safe
  · subst z; exact s5_172_safe
  · subst z; exact s5_70_safe
  · subst z; exact s5_60_safe
  · subst z; exact s5_66_safe
def s4_100 : State := ⟨4, 8, 66, 144, 22301085480897544079999273880976166116987158, 2, 2, 1⟩
theorem s4_100_edges : next 4 s4_100 = [s5_239, s5_109, s5_173, s5_71, s5_61, s5_67] := by decide
theorem s4_100_safe : Safe 9 4 s4_100 := by
  apply safe_succ 8 4 s4_100 [s5_239, s5_109, s5_173, s5_71, s5_61, s5_67] (by decide) s4_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s5_239_safe
  · subst z; exact s5_109_safe
  · subst z; exact s5_173_safe
  · subst z; exact s5_71_safe
  · subst z; exact s5_61_safe
  · subst z; exact s5_67_safe
def s4_101 : State := ⟨4, 8, 66, 160, 1461501637671185285124623296271891347460543549718, 1, 1, 1⟩
theorem s4_101_edges : next 4 s4_101 = [s5_112, s5_178, s5_64, s5_68] := by decide
theorem s4_101_safe : Safe 9 4 s4_101 := by
  apply safe_succ 8 4 s4_101 [s5_112, s5_178, s5_64, s5_68] (by decide) s4_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_112_safe
  · subst z; exact s5_178_safe
  · subst z; exact s5_64_safe
  · subst z; exact s5_68_safe
def s4_102 : State := ⟨4, 8, 66, 160, 1461501637671185285124623296271891347460543549718, 2, 2, 1⟩
theorem s4_102_edges : next 4 s4_102 = [s5_113, s5_179, s5_65, s5_69] := by decide
theorem s4_102_safe : Safe 9 4 s4_102 := by
  apply safe_succ 8 4 s4_102 [s5_113, s5_179, s5_65, s5_69] (by decide) s4_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_113_safe
  · subst z; exact s5_179_safe
  · subst z; exact s5_65_safe
  · subst z; exact s5_69_safe
def s4_103 : State := ⟨4, 8, 66, 192, 6277101735386680764176071790128604879657963772268645519638, 1, 1, 1⟩
theorem s4_103_edges : next 4 s4_103 = [s5_116, s5_184, s5_78] := by decide
theorem s4_103_safe : Safe 9 4 s4_103 := by
  apply safe_succ 8 4 s4_103 [s5_116, s5_184, s5_78] (by decide) s4_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_116_safe
  · subst z; exact s5_184_safe
  · subst z; exact s5_78_safe
def s4_104 : State := ⟨4, 8, 66, 192, 6277101735386680764176071790128604879657963772268645519638, 2, 2, 1⟩
theorem s4_104_edges : next 4 s4_104 = [s5_117, s5_185, s5_79] := by decide
theorem s4_104_safe : Safe 9 4 s4_104 := by
  apply safe_succ 8 4 s4_104 [s5_117, s5_185, s5_79] (by decide) s4_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_117_safe
  · subst z; exact s5_185_safe
  · subst z; exact s5_79_safe
def s4_105 : State := ⟨4, 8, 66, 194, 25108406941546723055683440059751604127965030105660749058326, 1, 1, 1⟩
theorem s4_105_edges : next 4 s4_105 = [s5_120, s5_190, s5_72] := by decide
theorem s4_105_safe : Safe 9 4 s4_105 := by
  apply safe_succ 8 4 s4_105 [s5_120, s5_190, s5_72] (by decide) s4_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_120_safe
  · subst z; exact s5_190_safe
  · subst z; exact s5_72_safe
def s4_106 : State := ⟨4, 8, 66, 194, 25108406941546723055683440059751604127965030105660749058326, 2, 2, 1⟩
theorem s4_106_edges : next 4 s4_106 = [s5_121, s5_191, s5_73] := by decide
theorem s4_106_safe : Safe 9 4 s4_106 := by
  apply safe_succ 8 4 s4_106 [s5_121, s5_191, s5_73] (by decide) s4_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_121_safe
  · subst z; exact s5_191_safe
  · subst z; exact s5_73_safe
def s4_107 : State := ⟨4, 8, 66, 214, 27973577474460502716656777188955856128786508989651833843043336470, 0, 0, 1⟩
theorem s4_107_edges : next 4 s4_107 = [s5_126] := by decide
theorem s4_107_safe : Safe 9 4 s4_107 := by
  apply safe_succ 8 4 s4_107 [s5_126] (by decide) s4_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_126_safe
def s4_108 : State := ⟨4, 8, 66, 214, 27973602582867444263357531786915018336310637680800963337675407638, 0, 0, 1⟩
theorem s4_108_edges : next 4 s4_108 = [s5_127] := by decide
theorem s4_108_safe : Safe 9 4 s4_108 := by
  apply safe_succ 8 4 s4_108 [s5_127] (by decide) s4_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_127_safe
def s4_109 : State := ⟨4, 8, 66, 224, 26959946667150639800513021638044654181056576070814811317259024269590, 0, 0, 1⟩
theorem s4_109_edges : next 4 s4_109 = [s5_287, s5_253, s5_128] := by decide
theorem s4_109_safe : Safe 9 4 s4_109 := by
  apply safe_succ 8 4 s4_109 [s5_287, s5_253, s5_128] (by decide) s4_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_287_safe
  · subst z; exact s5_253_safe
  · subst z; exact s5_128_safe
def s4_110 : State := ⟨4, 8, 66, 224, 26959946667150639801974523274014427631576507049677595907187883966742, 0, 0, 1⟩
theorem s4_110_edges : next 4 s4_110 = [s5_288, s5_254, s5_129] := by decide
theorem s4_110_safe : Safe 9 4 s4_110 := by
  apply safe_succ 8 4 s4_110 [s5_288, s5_254, s5_129] (by decide) s4_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_288_safe
  · subst z; exact s5_254_safe
  · subst z; exact s5_129_safe
def s4_111 : State := ⟨4, 8, 67, 128, 340282366920938463666288792246868316438, 1, 1, 0⟩
theorem s4_111_edges : next 4 s4_111 = [s5_90, s5_96, s5_122, s5_82, s5_86, s5_106, s5_110] := by decide
theorem s4_111_safe : Safe 9 4 s4_111 := by
  apply safe_succ 8 4 s4_111 [s5_90, s5_96, s5_122, s5_82, s5_86, s5_106, s5_110] (by decide) s4_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_90_safe
  · subst z; exact s5_96_safe
  · subst z; exact s5_122_safe
  · subst z; exact s5_82_safe
  · subst z; exact s5_86_safe
  · subst z; exact s5_106_safe
  · subst z; exact s5_110_safe
def s4_112 : State := ⟨4, 8, 67, 128, 340282366920938463666288792246868316438, 2, 2, 0⟩
theorem s4_112_edges : next 4 s4_112 = [s5_91, s5_97, s5_123, s5_83, s5_87, s5_107, s5_111] := by decide
theorem s4_112_safe : Safe 9 4 s4_112 := by
  apply safe_succ 8 4 s4_112 [s5_91, s5_97, s5_123, s5_83, s5_87, s5_107, s5_111] (by decide) s4_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_91_safe
  · subst z; exact s5_97_safe
  · subst z; exact s5_123_safe
  · subst z; exact s5_83_safe
  · subst z; exact s5_87_safe
  · subst z; exact s5_107_safe
  · subst z; exact s5_111_safe
def s4_113 : State := ⟨4, 8, 67, 128, 340282366920938463703182280394287419670, 1, 1, 0⟩
theorem s4_113_edges : next 4 s4_113 = [s5_92, s5_98, s5_124, s5_84, s5_88, s5_108, s5_112] := by decide
theorem s4_113_safe : Safe 9 4 s4_113 := by
  apply safe_succ 8 4 s4_113 [s5_92, s5_98, s5_124, s5_84, s5_88, s5_108, s5_112] (by decide) s4_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_92_safe
  · subst z; exact s5_98_safe
  · subst z; exact s5_124_safe
  · subst z; exact s5_84_safe
  · subst z; exact s5_88_safe
  · subst z; exact s5_108_safe
  · subst z; exact s5_112_safe
def s4_114 : State := ⟨4, 8, 67, 128, 340282366920938463703182280394287419670, 2, 2, 0⟩
theorem s4_114_edges : next 4 s4_114 = [s5_93, s5_99, s5_125, s5_85, s5_89, s5_109, s5_113] := by decide
theorem s4_114_safe : Safe 9 4 s4_114 := by
  apply safe_succ 8 4 s4_114 [s5_93, s5_99, s5_125, s5_85, s5_89, s5_109, s5_113] (by decide) s4_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_93_safe
  · subst z; exact s5_99_safe
  · subst z; exact s5_125_safe
  · subst z; exact s5_85_safe
  · subst z; exact s5_89_safe
  · subst z; exact s5_109_safe
  · subst z; exact s5_113_safe
def s4_115 : State := ⟨4, 8, 67, 140, 1399581375145819900225062674551677753819414, 0, 0, 1⟩
theorem s4_115_edges : next 4 s4_115 = [] := by decide
theorem s4_115_safe : Safe 9 4 s4_115 := by
  apply safe_succ 8 4 s4_115 [] (by decide) s4_115_edges
  simp
def s4_116 : State := ⟨4, 8, 67, 140, 1399581375145819900225099568039825172922646, 0, 0, 1⟩
theorem s4_116_edges : next 4 s4_116 = [] := by decide
theorem s4_116_safe : Safe 9 4 s4_116 := by
  apply safe_succ 8 4 s4_116 [] (by decide) s4_116_edges
  simp
def s4_117 : State := ⟨4, 8, 67, 140, 1481249143206845131456272580335302124568854, 0, 0, 1⟩
theorem s4_117_edges : next 4 s4_117 = [] := by decide
theorem s4_117_safe : Safe 9 4 s4_117 := by
  apply safe_succ 8 4 s4_117 [] (by decide) s4_117_edges
  simp
def s4_118 : State := ⟨4, 8, 67, 140, 1481249143206845131456309473823449543672086, 0, 0, 1⟩
theorem s4_118_edges : next 4 s4_118 = [] := by decide
theorem s4_118_safe : Safe 9 4 s4_118 := by
  apply safe_succ 8 4 s4_118 [] (by decide) s4_118_edges
  simp
def s4_119 : State := ⟨4, 8, 67, 146, 89204682205957097258460392877815419965079830, 0, 0, 1⟩
theorem s4_119_edges : next 4 s4_119 = [s5_289, s5_255] := by decide
theorem s4_119_safe : Safe 9 4 s4_119 := by
  apply safe_succ 8 4 s4_119 [s5_289, s5_255] (by decide) s4_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_289_safe
  · subst z; exact s5_255_safe
def s4_120 : State := ⟨4, 8, 67, 146, 89204682205957097258460429771303567384183062, 0, 0, 1⟩
theorem s4_120_edges : next 4 s4_120 = [s5_290, s5_256] := by decide
theorem s4_120_safe : Safe 9 4 s4_120 := by
  apply safe_succ 8 4 s4_120 [s5_290, s5_256] (by decide) s4_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_290_safe
  · subst z; exact s5_256_safe
def s4_121 : State := ⟨4, 8, 67, 146, 111504066275020036646142257652034054398214422, 0, 0, 1⟩
theorem s4_121_edges : next 4 s4_121 = [s5_291, s5_257] := by decide
theorem s4_121_safe : Safe 9 4 s4_121 := by
  apply safe_succ 8 4 s4_121 [s5_291, s5_257] (by decide) s4_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_291_safe
  · subst z; exact s5_257_safe
def s4_122 : State := ⟨4, 8, 67, 146, 111504066275020036646142294545522201817317654, 0, 0, 1⟩
theorem s4_122_edges : next 4 s4_122 = [s5_292, s5_258] := by decide
theorem s4_122_safe : Safe 9 4 s4_122 := by
  apply safe_succ 8 4 s4_122 [s5_292, s5_258] (by decide) s4_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_292_safe
  · subst z; exact s5_258_safe
def s4_123 : State := ⟨4, 8, 67, 162, 5846006551025023507419431648384919300597671330070, 0, 0, 1⟩
theorem s4_123_edges : next 4 s4_123 = [s5_293, s5_259] := by decide
theorem s4_123_safe : Safe 9 4 s4_123 := by
  apply safe_succ 8 4 s4_123 [s5_293, s5_259] (by decide) s4_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_293_safe
  · subst z; exact s5_259_safe
def s4_124 : State := ⟨4, 8, 67, 162, 5846006551025023507419431648421812788745090433302, 0, 0, 1⟩
theorem s4_124_edges : next 4 s4_124 = [s5_294, s5_260] := by decide
theorem s4_124_safe : Safe 9 4 s4_124 := by
  apply safe_succ 8 4 s4_124 [s5_294, s5_260] (by decide) s4_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_294_safe
  · subst z; exact s5_260_safe
def s4_125 : State := ⟨4, 8, 67, 162, 7307508186994796957939362627247703890526531027222, 0, 0, 1⟩
theorem s4_125_edges : next 4 s4_125 = [s5_295, s5_261] := by decide
theorem s4_125_safe : Safe 9 4 s4_125 := by
  apply safe_succ 8 4 s4_125 [s5_295, s5_261] (by decide) s4_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_295_safe
  · subst z; exact s5_261_safe
def s4_126 : State := ⟨4, 8, 67, 162, 7307508186994796957939362627284597378673950130454, 0, 0, 1⟩
theorem s4_126_edges : next 4 s4_126 = [s5_296, s5_262] := by decide
theorem s4_126_safe : Safe 9 4 s4_126 := by
  apply safe_succ 8 4 s4_126 [s5_296, s5_262] (by decide) s4_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_296_safe
  · subst z; exact s5_262_safe
def s4_127 : State := ⟨4, 8, 67, 176, 95780971326419139128294233276893708537611803510767894, 0, 0, 1⟩
theorem s4_127_edges : next 4 s4_127 = [s5_297, s5_263] := by decide
theorem s4_127_safe : Safe 9 4 s4_127 := by
  apply safe_succ 8 4 s4_127 [s5_297, s5_263] (by decide) s4_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_297_safe
  · subst z; exact s5_263_safe
def s4_128 : State := ⟨4, 8, 67, 176, 95780971326419139128294233276893745431099950929871126, 0, 0, 1⟩
theorem s4_128_edges : next 4 s4_128 = [s5_298, s5_264] := by decide
theorem s4_128_safe : Safe 9 4 s4_128 := by
  apply safe_succ 8 4 s4_128 [s5_298, s5_264] (by decide) s4_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_298_safe
  · subst z; exact s5_264_safe
def s4_129 : State := ⟨4, 8, 67, 176, 95782432805755724832681813820190706547983097937330454, 0, 0, 1⟩
theorem s4_129_edges : next 4 s4_129 = [s5_299, s5_265] := by decide
theorem s4_129_safe : Safe 9 4 s4_129 := by
  apply safe_succ 8 4 s4_129 [s5_299, s5_265] (by decide) s4_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_299_safe
  · subst z; exact s5_265_safe
def s4_130 : State := ⟨4, 8, 67, 176, 95782432805755724832681813820190743441471245356433686, 0, 0, 1⟩
theorem s4_130_edges : next 4 s4_130 = [s5_300, s5_266] := by decide
theorem s4_130_safe : Safe 9 4 s4_130 := by
  apply safe_succ 8 4 s4_130 [s5_300, s5_266] (by decide) s4_130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_300_safe
  · subst z; exact s5_266_safe
def s4_131 : State := ⟨4, 8, 67, 210, 1645504557321206042177270268038248049062735287088508619142005014, 0, 0, 1⟩
theorem s4_131_edges : next 4 s4_131 = [s5_301, s5_323, s5_267, s5_126] := by decide
theorem s4_131_safe : Safe 9 4 s4_131 := by
  apply safe_succ 8 4 s4_131 [s5_301, s5_323, s5_267, s5_126] (by decide) s4_131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_301_safe
  · subst z; exact s5_323_safe
  · subst z; exact s5_267_safe
  · subst z; exact s5_126_safe
def s4_132 : State := ⟨4, 8, 67, 210, 1645529665728147588878024865997410256586863978237638113774076182, 0, 0, 1⟩
theorem s4_132_edges : next 4 s4_132 = [s5_302, s5_324, s5_268, s5_127] := by decide
theorem s4_132_safe : Safe 9 4 s4_132 := by
  apply safe_succ 8 4 s4_132 [s5_302, s5_324, s5_268, s5_127] (by decide) s4_132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_302_safe
  · subst z; exact s5_324_safe
  · subst z; exact s5_268_safe
  · subst z; exact s5_127_safe
def s4_133 : State := ⟨4, 8, 67, 224, 26959946667150639796128516724690815958761767718923144293006411104534, 0, 0, 1⟩
theorem s4_133_edges : next 4 s4_133 = [s5_303, s5_325, s5_269] := by decide
theorem s4_133_safe : Safe 9 4 s4_133 := by
  apply safe_succ 8 4 s4_133 [s5_303, s5_325, s5_269] (by decide) s4_133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_303_safe
  · subst z; exact s5_325_safe
  · subst z; exact s5_269_safe
def s4_134 : State := ⟨4, 8, 67, 224, 26959946667150639796128516724690815958761767718960037781153830207766, 0, 0, 1⟩
theorem s4_134_edges : next 4 s4_134 = [s5_304, s5_326, s5_270] := by decide
theorem s4_134_safe : Safe 9 4 s4_134 := by
  apply safe_succ 8 4 s4_134 [s5_304, s5_326, s5_270] (by decide) s4_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_304_safe
  · subst z; exact s5_326_safe
  · subst z; exact s5_270_safe
def s4_135 : State := ⟨4, 8, 67, 224, 26959946673427741530053695851195702463765749302309216717814513074454, 0, 0, 1⟩
theorem s4_135_edges : next 4 s4_135 = [s5_305, s5_327, s5_271] := by decide
theorem s4_135_safe : Safe 9 4 s4_135 := by
  apply safe_succ 8 4 s4_135 [s5_305, s5_327, s5_271] (by decide) s4_135_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_305_safe
  · subst z; exact s5_327_safe
  · subst z; exact s5_271_safe
def s4_136 : State := ⟨4, 8, 67, 224, 26959946673427741530053695851195702463765749302346110205961932177686, 0, 0, 1⟩
theorem s4_136_edges : next 4 s4_136 = [s5_306, s5_328, s5_272] := by decide
theorem s4_136_safe : Safe 9 4 s4_136 := by
  apply safe_succ 8 4 s4_136 [s5_306, s5_328, s5_272] (by decide) s4_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_306_safe
  · subst z; exact s5_328_safe
  · subst z; exact s5_272_safe
def s4_137 : State := ⟨4, 8, 68, 214, 26328072917139296674568711603123565176982234353695557675800133910, 0, 0, 1⟩
theorem s4_137_edges : next 4 s4_137 = [] := by decide
theorem s4_137_safe : Safe 9 4 s4_137 := by
  apply safe_succ 8 4 s4_137 [] (by decide) s4_137_edges
  simp
def s4_138 : State := ⟨4, 8, 68, 214, 26328072917139296674591010987192628116369916218469776310233268502, 0, 0, 1⟩
theorem s4_138_edges : next 4 s4_138 = [] := by decide
theorem s4_138_safe : Safe 9 4 s4_138 := by
  apply safe_succ 8 4 s4_138 [] (by decide) s4_138_edges
  simp
def s4_139 : State := ⟨4, 8, 80, 129, 1020847100762816599334390181002483929366, 1, 1, 1⟩
theorem s4_139_edges : next 4 s4_139 = [s5_142] := by decide
theorem s4_139_safe : Safe 9 4 s4_139 := by
  apply safe_succ 8 4 s4_139 [s5_142] (by decide) s4_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_142_safe
def s4_140 : State := ⟨4, 8, 80, 129, 1020847100762816599334390181002483929366, 2, 2, 1⟩
theorem s4_140_edges : next 4 s4_140 = [s5_143] := by decide
theorem s4_140_safe : Safe 9 4 s4_140 := by
  apply safe_succ 8 4 s4_140 [s5_143] (by decide) s4_140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_143_safe
def s4_141 : State := ⟨4, 8, 80, 130, 1701411834604693526261139395866020352278, 1, 1, 1⟩
theorem s4_141_edges : next 4 s4_141 = [s5_232, s5_148, s5_130] := by decide
theorem s4_141_safe : Safe 9 4 s4_141 := by
  apply safe_succ 8 4 s4_141 [s5_232, s5_148, s5_130] (by decide) s4_141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_232_safe
  · subst z; exact s5_148_safe
  · subst z; exact s5_130_safe
def s4_142 : State := ⟨4, 8, 80, 130, 1701411834604693526261139395866020352278, 2, 2, 1⟩
theorem s4_142_edges : next 4 s4_142 = [s5_233, s5_149, s5_131] := by decide
theorem s4_142_safe : Safe 9 4 s4_142 := by
  apply safe_succ 8 4 s4_142 [s5_233, s5_149, s5_131] (by decide) s4_142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_233_safe
  · subst z; exact s5_149_safe
  · subst z; exact s5_131_safe
def s4_143 : State := ⟨4, 8, 80, 132, 5784800237655955087821634685047238889750, 1, 1, 1⟩
theorem s4_143_edges : next 4 s4_143 = [s5_154] := by decide
theorem s4_143_safe : Safe 9 4 s4_143 := by
  apply safe_succ 8 4 s4_143 [s5_154] (by decide) s4_143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_154_safe
def s4_144 : State := ⟨4, 8, 80, 132, 5784800237655955087821634685047238889750, 2, 2, 1⟩
theorem s4_144_edges : next 4 s4_144 = [s5_155] := by decide
theorem s4_144_safe : Safe 9 4 s4_144 := by
  apply safe_succ 8 4 s4_144 [s5_155] (by decide) s4_144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_155_safe
def s4_145 : State := ⟨4, 8, 80, 132, 1399581375145819901433804026725569833009430, 2, 2, 1⟩
theorem s4_145_edges : next 4 s4_145 = [s5_159] := by decide
theorem s4_145_safe : Safe 9 4 s4_145 := by
  apply safe_succ 8 4 s4_145 [s5_159] (by decide) s4_145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_159_safe
def s4_146 : State := ⟨4, 8, 80, 136, 87452568298681186319031540468671609639190, 1, 1, 1⟩
theorem s4_146_edges : next 4 s4_146 = [s5_162] := by decide
theorem s4_146_safe : Safe 9 4 s4_146 := by
  apply safe_succ 8 4 s4_146 [s5_162] (by decide) s4_146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_162_safe
def s4_147 : State := ⟨4, 8, 80, 136, 87452568298681186319031540468671609639190, 2, 2, 1⟩
theorem s4_147_edges : next 4 s4_147 = [s5_163] := by decide
theorem s4_147_safe : Safe 9 4 s4_147 := by
  apply safe_succ 8 4 s4_147 [s5_163] (by decide) s4_147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_163_safe
def s4_148 : State := ⟨4, 8, 80, 136, 1481249143206845132665013932509194203758870, 1, 1, 1⟩
theorem s4_148_edges : next 4 s4_148 = [s5_167] := by decide
theorem s4_148_safe : Safe 9 4 s4_148 := by
  apply safe_succ 8 4 s4_148 [s5_167] (by decide) s4_148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_167_safe
def s4_149 : State := ⟨4, 8, 80, 140, 1394136857275084886018390033006661541630230, 1, 1, 1⟩
theorem s4_149_edges : next 4 s4_149 = [s5_170] := by decide
theorem s4_149_safe : Safe 9 4 s4_149 := by
  apply safe_succ 8 4 s4_149 [s5_170] (by decide) s4_149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_170_safe
def s4_150 : State := ⟨4, 8, 80, 140, 1394136857275084886018390033006661541630230, 2, 2, 1⟩
theorem s4_150_edges : next 4 s4_150 = [s5_171] := by decide
theorem s4_150_safe : Safe 9 4 s4_150 := by
  apply safe_succ 8 4 s4_150 [s5_171] (by decide) s4_150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_171_safe
def s4_151 : State := ⟨4, 8, 80, 144, 22301085480897544081208125913614500453486870, 1, 1, 1⟩
theorem s4_151_edges : next 4 s4_151 = [s5_174] := by decide
theorem s4_151_safe : Safe 9 4 s4_151 := by
  apply safe_succ 8 4 s4_151 [s5_174] (by decide) s4_151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_174_safe
def s4_152 : State := ⟨4, 8, 80, 144, 22301085480897544081208125913614500453486870, 2, 2, 1⟩
theorem s4_152_edges : next 4 s4_152 = [s5_175] := by decide
theorem s4_152_safe : Safe 9 4 s4_152 := by
  apply safe_succ 8 4 s4_152 [s5_175] (by decide) s4_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_175_safe
def s4_153 : State := ⟨4, 8, 80, 160, 1461501637671185285124624505123923985794880049430, 1, 1, 1⟩
theorem s4_153_edges : next 4 s4_153 = [s5_180] := by decide
theorem s4_153_safe : Safe 9 4 s4_153 := by
  apply safe_succ 8 4 s4_153 [s5_180] (by decide) s4_153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_180_safe
def s4_154 : State := ⟨4, 8, 80, 160, 1461501637671185285124624505123923985794880049430, 2, 2, 1⟩
theorem s4_154_edges : next 4 s4_154 = [s5_181] := by decide
theorem s4_154_safe : Safe 9 4 s4_154 := by
  apply safe_succ 8 4 s4_154 [s5_181] (by decide) s4_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_181_safe
def s4_155 : State := ⟨4, 8, 80, 192, 6277101735386680764176071790128606088509996410602982019350, 1, 1, 1⟩
theorem s4_155_edges : next 4 s4_155 = [s5_186, s5_138] := by decide
theorem s4_155_safe : Safe 9 4 s4_155 := by
  apply safe_succ 8 4 s4_155 [s5_186, s5_138] (by decide) s4_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_186_safe
  · subst z; exact s5_138_safe
def s4_156 : State := ⟨4, 8, 80, 192, 6277101735386680764176071790128606088509996410602982019350, 2, 2, 1⟩
theorem s4_156_edges : next 4 s4_156 = [s5_187, s5_139] := by decide
theorem s4_156_safe : Safe 9 4 s4_156 := by
  apply safe_succ 8 4 s4_156 [s5_187, s5_139] (by decide) s4_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_187_safe
  · subst z; exact s5_139_safe
def s4_157 : State := ⟨4, 8, 80, 208, 411376139330301510538742635921704547185356374049361104784658710, 1, 1, 1⟩
theorem s4_157_edges : next 4 s4_157 = [s5_193, s5_132] := by decide
theorem s4_157_safe : Safe 9 4 s4_157 := by
  apply safe_succ 8 4 s4_157 [s5_193, s5_132] (by decide) s4_157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_193_safe
  · subst z; exact s5_132_safe
def s4_158 : State := ⟨4, 8, 80, 208, 411376139330301510538742635921704547185356374049361104784658710, 2, 2, 1⟩
theorem s4_158_edges : next 4 s4_158 = [s5_194, s5_133] := by decide
theorem s4_158_safe : Safe 9 4 s4_158 := by
  apply safe_succ 8 4 s4_158 [s5_194, s5_133] (by decide) s4_158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_194_safe
  · subst z; exact s5_133_safe
def s4_159 : State := ⟨4, 8, 80, 214, 27973577474460502716634477804886793189400035976910253542946701590, 0, 0, 1⟩
theorem s4_159_edges : next 4 s4_159 = [] := by decide
theorem s4_159_safe : Safe 9 4 s4_159 := by
  apply safe_succ 8 4 s4_159 [] (by decide) s4_159_edges
  simp
def s4_160 : State := ⟨4, 8, 80, 214, 28384953613790804227173218739396663131891866089820218781711008022, 0, 0, 1⟩
theorem s4_160_edges : next 4 s4_160 = [] := by decide
theorem s4_160_safe : Safe 9 4 s4_160 := by
  apply safe_succ 8 4 s4_160 [] (by decide) s4_160_edges
  simp
def s4_161 : State := ⟨4, 8, 82, 128, 340282366920943299258886786321309831446, 1, 1, 0⟩
theorem s4_161_edges : next 4 s4_161 = [s5_152, s5_160, s5_196, s5_140, s5_146, s5_172, s5_178] := by decide
theorem s4_161_safe : Safe 9 4 s4_161 := by
  apply safe_succ 8 4 s4_161 [s5_152, s5_160, s5_196, s5_140, s5_146, s5_172, s5_178] (by decide) s4_161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_152_safe
  · subst z; exact s5_160_safe
  · subst z; exact s5_196_safe
  · subst z; exact s5_140_safe
  · subst z; exact s5_146_safe
  · subst z; exact s5_172_safe
  · subst z; exact s5_178_safe
def s4_162 : State := ⟨4, 8, 82, 128, 340282366920943299258886786321309831446, 2, 2, 0⟩
theorem s4_162_edges : next 4 s4_162 = [s5_153, s5_161, s5_197, s5_141, s5_147, s5_173, s5_179] := by decide
theorem s4_162_safe : Safe 9 4 s4_162 := by
  apply safe_succ 8 4 s4_162 [s5_153, s5_161, s5_197, s5_141, s5_147, s5_173, s5_179] (by decide) s4_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_153_safe
  · subst z; exact s5_161_safe
  · subst z; exact s5_197_safe
  · subst z; exact s5_141_safe
  · subst z; exact s5_147_safe
  · subst z; exact s5_173_safe
  · subst z; exact s5_179_safe
def s4_163 : State := ⟨4, 8, 82, 128, 340282366920944508110919424655646331158, 1, 1, 0⟩
theorem s4_163_edges : next 4 s4_163 = [s5_154, s5_162, s5_198, s5_142, s5_148, s5_174, s5_180] := by decide
theorem s4_163_safe : Safe 9 4 s4_163 := by
  apply safe_succ 8 4 s4_163 [s5_154, s5_162, s5_198, s5_142, s5_148, s5_174, s5_180] (by decide) s4_163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_154_safe
  · subst z; exact s5_162_safe
  · subst z; exact s5_198_safe
  · subst z; exact s5_142_safe
  · subst z; exact s5_148_safe
  · subst z; exact s5_174_safe
  · subst z; exact s5_180_safe
def s4_164 : State := ⟨4, 8, 82, 128, 340282366920944508110919424655646331158, 2, 2, 0⟩
theorem s4_164_edges : next 4 s4_164 = [s5_155, s5_163, s5_199, s5_143, s5_149, s5_175, s5_181] := by decide
theorem s4_164_safe : Safe 9 4 s4_164 := by
  apply safe_succ 8 4 s4_164 [s5_155, s5_163, s5_199, s5_143, s5_149, s5_175, s5_181] (by decide) s4_164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_155_safe
  · subst z; exact s5_163_safe
  · subst z; exact s5_199_safe
  · subst z; exact s5_143_safe
  · subst z; exact s5_149_safe
  · subst z; exact s5_175_safe
  · subst z; exact s5_181_safe
def s4_165 : State := ⟨4, 8, 82, 128, 340282366921020670511342122588491022614, 1, 1, 0⟩
theorem s4_165_edges : next 4 s4_165 = [s5_156, s5_164, s5_200, s5_144, s5_150, s5_176, s5_182] := by decide
theorem s4_165_safe : Safe 9 4 s4_165 := by
  apply safe_succ 8 4 s4_165 [s5_156, s5_164, s5_200, s5_144, s5_150, s5_176, s5_182] (by decide) s4_165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_156_safe
  · subst z; exact s5_164_safe
  · subst z; exact s5_200_safe
  · subst z; exact s5_144_safe
  · subst z; exact s5_150_safe
  · subst z; exact s5_176_safe
  · subst z; exact s5_182_safe
def s4_166 : State := ⟨4, 8, 82, 128, 340282366921021879363374760922827522326, 1, 1, 0⟩
theorem s4_166_edges : next 4 s4_166 = [s5_157, s5_165, s5_201, s5_145, s5_151, s5_177, s5_183] := by decide
theorem s4_166_safe : Safe 9 4 s4_166 := by
  apply safe_succ 8 4 s4_166 [s5_157, s5_165, s5_201, s5_145, s5_151, s5_177, s5_183] (by decide) s4_166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s5_157_safe
  · subst z; exact s5_165_safe
  · subst z; exact s5_201_safe
  · subst z; exact s5_145_safe
  · subst z; exact s5_151_safe
  · subst z; exact s5_177_safe
  · subst z; exact s5_183_safe
def s4_167 : State := ⟨4, 8, 82, 140, 1399581375145819905060655272545752195334422, 0, 0, 1⟩
theorem s4_167_edges : next 4 s4_167 = [] := by decide
theorem s4_167_safe : Safe 9 4 s4_167 := by
  apply safe_succ 8 4 s4_167 [] (by decide) s4_167_edges
  simp
def s4_168 : State := ⟨4, 8, 82, 140, 1399581375145819906269507305184086531834134, 0, 0, 1⟩
theorem s4_168_edges : next 4 s4_168 = [] := by decide
theorem s4_168_safe : Safe 9 4 s4_168 := by
  apply safe_succ 8 4 s4_168 [] (by decide) s4_168_edges
  simp
def s4_169 : State := ⟨4, 8, 82, 140, 1481249143206845136291865178329376566083862, 0, 0, 1⟩
theorem s4_169_edges : next 4 s4_169 = [] := by decide
theorem s4_169_safe : Safe 9 4 s4_169 := by
  apply safe_succ 8 4 s4_169 [] (by decide) s4_169_edges
  simp
def s4_170 : State := ⟨4, 8, 82, 140, 1481249143206845137500717210967710902583574, 0, 0, 1⟩
theorem s4_170_edges : next 4 s4_170 = [] := by decide
theorem s4_170_safe : Safe 9 4 s4_170 := by
  apply safe_succ 8 4 s4_170 [] (by decide) s4_170_edges
  simp
def s4_171 : State := ⟨4, 8, 82, 214, 26328072917139296674479512705717845735682488523017783043178955030, 0, 0, 1⟩
theorem s4_171_edges : next 4 s4_171 = [] := by decide
theorem s4_171_safe : Safe 9 4 s4_171 := by
  apply safe_succ 8 4 s4_171 [] (by decide) s4_171_edges
  simp
def s4_172 : State := ⟨4, 8, 82, 214, 26328072917139296674479512705717845735683697375050421377515454742, 0, 0, 1⟩
theorem s4_172_edges : next 4 s4_172 = [] := by decide
theorem s4_172_safe : Safe 9 4 s4_172 := by
  apply safe_succ 8 4 s4_172 [] (by decide) s4_172_edges
  simp
def s4_173 : State := ⟨4, 8, 82, 214, 27973577474460502716634476443757325505649808974657643998236180758, 0, 0, 1⟩
theorem s4_173_edges : next 4 s4_173 = [] := by decide
theorem s4_173_safe : Safe 9 4 s4_173 := by
  apply safe_succ 8 4 s4_173 [] (by decide) s4_173_edges
  simp
def s4_174 : State := ⟨4, 8, 82, 214, 27973577474460502716634476443757325505651017826690282332572680470, 0, 0, 1⟩
theorem s4_174_edges : next 4 s4_174 = [] := by decide
theorem s4_174_safe : Safe 9 4 s4_174 := by
  apply safe_succ 8 4 s4_174 [] (by decide) s4_174_edges
  simp
def s4_175 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761772554515742287080852619542, 0, 0, 1⟩
theorem s4_175_edges : next 4 s4_175 = [s5_307, s5_317, s5_273, s5_206] := by decide
theorem s4_175_safe : Safe 9 4 s4_175 := by
  apply safe_succ 8 4 s4_175 [s5_307, s5_317, s5_273, s5_206] (by decide) s4_175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_307_safe
  · subst z; exact s5_317_safe
  · subst z; exact s5_273_safe
  · subst z; exact s5_206_safe
def s4_176 : State := ⟨4, 8, 82, 224, 26959946667150639796128516724690815958761773763367774925415189119254, 0, 0, 1⟩
theorem s4_176_edges : next 4 s4_176 = [s5_308, s5_318, s5_274, s5_207] := by decide
theorem s4_176_safe : Safe 9 4 s4_176 := by
  apply safe_succ 8 4 s4_176 [s5_308, s5_318, s5_274, s5_207] (by decide) s4_176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_308_safe
  · subst z; exact s5_318_safe
  · subst z; exact s5_274_safe
  · subst z; exact s5_207_safe
def s4_177 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765754137901814711888954589462, 0, 0, 1⟩
theorem s4_177_edges : next 4 s4_177 = [s5_309, s5_319, s5_275, s5_208] := by decide
theorem s4_177_safe : Safe 9 4 s4_177 := by
  apply safe_succ 8 4 s4_177 [s5_309, s5_319, s5_275, s5_208] (by decide) s4_177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_309_safe
  · subst z; exact s5_319_safe
  · subst z; exact s5_275_safe
  · subst z; exact s5_208_safe
def s4_178 : State := ⟨4, 8, 82, 224, 26959946673427741530053695851195702463765755346753847350223291089174, 0, 0, 1⟩
theorem s4_178_edges : next 4 s4_178 = [s5_310, s5_320, s5_276, s5_209] := by decide
theorem s4_178_safe : Safe 9 4 s4_178 := by
  apply safe_succ 8 4 s4_178 [s5_310, s5_320, s5_276, s5_209] (by decide) s4_178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_310_safe
  · subst z; exact s5_320_safe
  · subst z; exact s5_276_safe
  · subst z; exact s5_209_safe
def s4_179 : State := ⟨4, 8, 86, 129, 1020847100762897597438091337452027445526, 0, 0, 1⟩
theorem s4_179_edges : next 4 s4_179 = [] := by decide
theorem s4_179_safe : Safe 9 4 s4_179 := by
  apply safe_succ 8 4 s4_179 [] (by decide) s4_179_edges
  simp
def s4_180 : State := ⟨4, 8, 86, 129, 1020847100762898806290123975786363945238, 0, 0, 1⟩
theorem s4_180_edges : next 4 s4_180 = [] := by decide
theorem s4_180_safe : Safe 9 4 s4_180 := by
  apply safe_succ 8 4 s4_180 [] (by decide) s4_180_edges
  simp
def s4_181 : State := ⟨4, 8, 86, 130, 1701411834604774524364840552315563868438, 0, 0, 1⟩
theorem s4_181_edges : next 4 s4_181 = [] := by decide
theorem s4_181_safe : Safe 9 4 s4_181 := by
  apply safe_succ 8 4 s4_181 [] (by decide) s4_181_edges
  simp
def s4_182 : State := ⟨4, 8, 86, 130, 1701411834604775733216873190649900368150, 0, 0, 1⟩
theorem s4_182_edges : next 4 s4_182 = [] := by decide
theorem s4_182_safe : Safe 9 4 s4_182 := by
  apply safe_succ 8 4 s4_182 [] (by decide) s4_182_edges
  simp
def s4_183 : State := ⟨4, 8, 86, 132, 5784800237656036085925335841496782405910, 0, 0, 1⟩
theorem s4_183_edges : next 4 s4_183 = [] := by decide
theorem s4_183_safe : Safe 9 4 s4_183 := by
  apply safe_succ 8 4 s4_183 [] (by decide) s4_183_edges
  simp
def s4_184 : State := ⟨4, 8, 86, 132, 5784800237656037294777368479831118905622, 0, 0, 1⟩
theorem s4_184_edges : next 4 s4_184 = [] := by decide
theorem s4_184_safe : Safe 9 4 s4_184 := by
  apply safe_succ 8 4 s4_184 [] (by decide) s4_184_edges
  simp
def s4_185 : State := ⟨4, 8, 86, 136, 87452568298681267317135241625121153155350, 0, 0, 1⟩
theorem s4_185_edges : next 4 s4_185 = [] := by decide
theorem s4_185_safe : Safe 9 4 s4_185 := by
  apply safe_succ 8 4 s4_185 [] (by decide) s4_185_edges
  simp
def s4_186 : State := ⟨4, 8, 86, 136, 87452568298681268525987274263455489655062, 0, 0, 1⟩
theorem s4_186_edges : next 4 s4_186 = [] := by decide
theorem s4_186_safe : Safe 9 4 s4_186 := by
  apply safe_succ 8 4 s4_186 [] (by decide) s4_186_edges
  simp
def s4_187 : State := ⟨4, 8, 86, 144, 22301085480897544162206229614770949997003030, 0, 0, 1⟩
theorem s4_187_edges : next 4 s4_187 = [] := by decide
theorem s4_187_safe : Safe 9 4 s4_187 := by
  apply safe_succ 8 4 s4_187 [] (by decide) s4_187_edges
  simp
def s4_188 : State := ⟨4, 8, 86, 144, 22301085480897544163415081647409284333502742, 0, 0, 1⟩
theorem s4_188_edges : next 4 s4_188 = [] := by decide
theorem s4_188_safe : Safe 9 4 s4_188 := by
  apply safe_succ 8 4 s4_188 [] (by decide) s4_188_edges
  simp
def s4_189 : State := ⟨4, 8, 86, 160, 1461501637671185285124705503227625142244423565590, 0, 0, 1⟩
theorem s4_189_edges : next 4 s4_189 = [] := by decide
theorem s4_189_safe : Safe 9 4 s4_189 := by
  apply safe_succ 8 4 s4_189 [] (by decide) s4_189_edges
  simp
def s4_190 : State := ⟨4, 8, 86, 160, 1461501637671185285124706712079657780578760065302, 0, 0, 1⟩
theorem s4_190_edges : next 4 s4_190 = [] := by decide
theorem s4_190_safe : Safe 9 4 s4_190 := by
  apply safe_succ 8 4 s4_190 [] (by decide) s4_190_edges
  simp
def s4_191 : State := ⟨4, 8, 86, 192, 6277101735386680764176071790128687086613697567052525535510, 0, 0, 1⟩
theorem s4_191_edges : next 4 s4_191 = [s5_208] := by decide
theorem s4_191_safe : Safe 9 4 s4_191 := by
  apply safe_succ 8 4 s4_191 [s5_208] (by decide) s4_191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_208_safe
def s4_192 : State := ⟨4, 8, 86, 192, 6277101735386680764176071790128688295465730205386862035222, 0, 0, 1⟩
theorem s4_192_edges : next 4 s4_192 = [s5_209] := by decide
theorem s4_192_safe : Safe 9 4 s4_192 := by
  apply safe_succ 8 4 s4_192 [s5_209] (by decide) s4_192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_209_safe
def s4_193 : State := ⟨4, 8, 86, 194, 25108406941546723055683440059751686334920763900444629074198, 0, 0, 1⟩
theorem s4_193_edges : next 4 s4_193 = [] := by decide
theorem s4_193_safe : Safe 9 4 s4_193 := by
  apply safe_succ 8 4 s4_193 [] (by decide) s4_193_edges
  simp
def s4_194 : State := ⟨4, 8, 86, 208, 411376139330301510538742635921704547267563329783155888664674582, 0, 0, 1⟩
theorem s4_194_edges : next 4 s4_194 = [] := by decide
theorem s4_194_safe : Safe 9 4 s4_194 := by
  apply safe_succ 8 4 s4_194 [] (by decide) s4_194_edges
  simp
def s4_195 : State := ⟨4, 8, 86, 210, 1645504557321206042154969522839717426003406376975702451839631638, 0, 0, 1⟩
theorem s4_195_edges : next 4 s4_195 = [] := by decide
theorem s4_195_safe : Safe 9 4 s4_195 := by
  apply safe_succ 8 4 s4_195 [] (by decide) s4_195_edges
  simp
def s4_196 : State := ⟨4, 8, 86, 210, 1645504557321206042154969522839717426004615229008340786176131350, 0, 0, 1⟩
theorem s4_196_edges : next 4 s4_196 = [] := by decide
theorem s4_196_safe : Safe 9 4 s4_196 := by
  apply safe_succ 8 4 s4_196 [] (by decide) s4_196_edges
  simp
def s4_197 : State := ⟨4, 8, 86, 214, 26328072917139296674479507261199975000744444361479400402068766998, 0, 0, 1⟩
theorem s4_197_edges : next 4 s4_197 = [] := by decide
theorem s4_197_safe : Safe 9 4 s4_197 := by
  apply safe_succ 8 4 s4_197 [] (by decide) s4_197_edges
  simp
def s4_198 : State := ⟨4, 8, 86, 214, 26328072917139296674479507261199975000745653213512038736405266710, 0, 0, 1⟩
theorem s4_198_edges : next 4 s4_198 = [] := by decide
theorem s4_198_safe : Safe 9 4 s4_198 := by
  apply safe_succ 8 4 s4_198 [] (by decide) s4_198_edges
  simp
def s4_199 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913040637311048536658170206926996246, 2, 2, 1⟩
theorem s4_199_edges : next 4 s4_199 = [s5_280, s5_218] := by decide
theorem s4_199_safe : Safe 9 4 s4_199 := by
  apply safe_succ 8 4 s4_199 [s5_280, s5_218] (by decide) s4_199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_280_safe
  · subst z; exact s5_218_safe
def s4_200 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913040637311048536658170206926999830, 1, 1, 1⟩
theorem s4_200_edges : next 4 s4_200 = [s5_282, s5_219, s5_214, s5_225] := by decide
theorem s4_200_safe : Safe 9 4 s4_200 := by
  apply safe_succ 8 4 s4_200 [s5_282, s5_219, s5_214, s5_225] (by decide) s4_200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_282_safe
  · subst z; exact s5_219_safe
  · subst z; exact s5_214_safe
  · subst z; exact s5_225_safe
def s4_201 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913040637311048536658170206926999830, 2, 2, 1⟩
theorem s4_201_edges : next 4 s4_201 = [s5_281, s5_220, s5_215, s5_226] := by decide
theorem s4_201_safe : Safe 9 4 s4_201 := by
  apply safe_succ 8 4 s4_201 [s5_281, s5_220, s5_215, s5_226] (by decide) s4_201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_281_safe
  · subst z; exact s5_220_safe
  · subst z; exact s5_215_safe
  · subst z; exact s5_226_safe
def s4_202 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913040637311048831806075386279821590, 1, 1, 1⟩
theorem s4_202_edges : next 4 s4_202 = [s5_283, s5_221] := by decide
theorem s4_202_safe : Safe 9 4 s4_202 := by
  apply safe_succ 8 4 s4_202 [s5_283, s5_221] (by decide) s4_202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_283_safe
  · subst z; exact s5_221_safe
def s4_203 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913041904961648764887571703630201110, 1, 1, 1⟩
theorem s4_203_edges : next 4 s4_203 = [s5_284, s5_222] := by decide
theorem s4_203_safe : Safe 9 4 s4_203 := by
  apply safe_succ 8 4 s4_203 [s5_284, s5_222] (by decide) s4_203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_284_safe
  · subst z; exact s5_222_safe
def s4_204 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913060919720652188328594154178281750, 2, 2, 1⟩
theorem s4_204_edges : next 4 s4_204 = [s5_311, s5_321, s5_329, s5_277, s5_252, s5_217, s5_216, s5_227] := by decide
theorem s4_204_safe : Safe 9 4 s4_204 := by
  apply safe_succ 8 4 s4_204 [s5_311, s5_321, s5_329, s5_277, s5_252, s5_217, s5_216, s5_227] (by decide) s4_204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s5_311_safe
  · subst z; exact s5_321_safe
  · subst z; exact s5_329_safe
  · subst z; exact s5_277_safe
  · subst z; exact s5_252_safe
  · subst z; exact s5_217_safe
  · subst z; exact s5_216_safe
  · subst z; exact s5_227_safe
def s4_205 : State := ⟨4, 8, 96, 224, 458319093341560876509339256479674003818831621809185817867864690983190, 1, 1, 1⟩
theorem s4_205_edges : next 4 s4_205 = [s5_286, s5_224] := by decide
theorem s4_205_safe : Safe 9 4 s4_205 := by
  apply safe_succ 8 4 s4_205 [s5_286, s5_224] (by decide) s4_205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_286_safe
  · subst z; exact s5_224_safe
def s4_206 : State := ⟨4, 8, 108, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 0, 0, 1⟩
theorem s4_206_edges : next 4 s4_206 = [] := by decide
theorem s4_206_safe : Safe 9 4 s4_206 := by
  apply safe_succ 8 4 s4_206 [] (by decide) s4_206_edges
  simp
def s4_207 : State := ⟨4, 8, 120, 224, 26959946667150639794667015087361242288915505568061232401214458626326, 0, 0, 1⟩
theorem s4_207_edges : next 4 s4_207 = [] := by decide
theorem s4_207_safe : Safe 9 4 s4_207 := by
  apply safe_succ 8 4 s4_207 [] (by decide) s4_207_edges
  simp
def s4_208 : State := ⟨4, 8, 162, 224, 26959946667150639801974523274014427631576507049677595907187883966742, 0, 0, 1⟩
theorem s4_208_edges : next 4 s4_208 = [s5_312, s5_278] := by decide
theorem s4_208_safe : Safe 9 4 s4_208 := by
  apply safe_succ 8 4 s4_208 [s5_312, s5_278] (by decide) s4_208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_312_safe
  · subst z; exact s5_278_safe
def s4_209 : State := ⟨4, 8, 162, 224, 26959946673427741535899702400519314136580488633063668331995985936662, 0, 0, 1⟩
theorem s4_209_edges : next 4 s4_209 = [s5_313, s5_279] := by decide
theorem s4_209_safe : Safe 9 4 s4_209 := by
  apply safe_succ 8 4 s4_209 [s5_313, s5_279] (by decide) s4_209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_313_safe
  · subst z; exact s5_279_safe
def s4_210 : State := ⟨4, 8, 193, 129, 12554203470773361528692425947178148222613281455301378248982, 1, 1, 1⟩
theorem s4_210_edges : next 4 s4_210 = [] := by decide
theorem s4_210_safe : Safe 9 4 s4_210 := by
  apply safe_succ 8 4 s4_210 [] (by decide) s4_210_edges
  simp
def s4_211 : State := ⟨4, 8, 193, 129, 12554203470773361528692425947178148222613281455301378248982, 2, 2, 1⟩
theorem s4_211_edges : next 4 s4_211 = [] := by decide
theorem s4_211_safe : Safe 9 4 s4_211 := by
  apply safe_succ 8 4 s4_211 [] (by decide) s4_211_edges
  simp
def s4_212 : State := ⟨4, 8, 194, 130, 25108406941546723057044569527435357981744741559092983697686, 1, 1, 1⟩
theorem s4_212_edges : next 4 s4_212 = [s5_234, s5_228, s5_230] := by decide
theorem s4_212_safe : Safe 9 4 s4_212 := by
  apply safe_succ 8 4 s4_212 [s5_234, s5_228, s5_230] (by decide) s4_212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_234_safe
  · subst z; exact s5_228_safe
  · subst z; exact s5_230_safe
def s4_213 : State := ⟨4, 8, 194, 130, 25108406941546723057044569527435357981744741559092983697686, 2, 2, 1⟩
theorem s4_213_edges : next 4 s4_213 = [s5_235, s5_229, s5_231] := by decide
theorem s4_213_safe : Safe 9 4 s4_213 := by
  apply safe_succ 8 4 s4_213 [s5_235, s5_229, s5_231] (by decide) s4_213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_235_safe
  · subst z; exact s5_229_safe
  · subst z; exact s5_231_safe
def s4_214 : State := ⟨4, 8, 208, 144, 411376139330301510561043381120235170325683166502394837115932950, 1, 1, 1⟩
theorem s4_214_edges : next 4 s4_214 = [s5_240] := by decide
theorem s4_214_safe : Safe 9 4 s4_214 := by
  apply safe_succ 8 4 s4_214 [s5_240] (by decide) s4_214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_240_safe
def s4_215 : State := ⟨4, 8, 208, 144, 411376139330301510561043381120235170325683166502394837115932950, 2, 2, 1⟩
theorem s4_215_edges : next 4 s4_215 = [s5_241] := by decide
theorem s4_215_safe : Safe 9 4 s4_215 := by
  apply safe_succ 8 4 s4_215 [s5_241] (by decide) s4_215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_241_safe
def s4_216 : State := ⟨4, 8, 214, 130, 27973577474460502716634477804886793189400035976910253542946701590, 0, 0, 1⟩
theorem s4_216_edges : next 4 s4_216 = [] := by decide
theorem s4_216_safe : Safe 9 4 s4_216 := by
  apply safe_succ 8 4 s4_216 [] (by decide) s4_216_edges
  simp
def s4_217 : State := ⟨4, 8, 214, 130, 27973602582867444263357533148044486020064491460512416769910046998, 0, 0, 1⟩
theorem s4_217_edges : next 4 s4_217 = [] := by decide
theorem s4_217_safe : Safe 9 4 s4_217 := by
  apply safe_succ 8 4 s4_217 [] (by decide) s4_217_edges
  simp
def s4_218 : State := ⟨4, 8, 214, 132, 26328072917139296674479512705717845735682488523017783043178955030, 0, 0, 1⟩
theorem s4_218_edges : next 4 s4_218 = [] := by decide
theorem s4_218_safe : Safe 9 4 s4_218 := by
  apply safe_succ 8 4 s4_218 [] (by decide) s4_218_edges
  simp
def s4_219 : State := ⟨4, 8, 214, 132, 26328072917139296674479512705717845735683697375050421377515454742, 0, 0, 1⟩
theorem s4_219_edges : next 4 s4_219 = [] := by decide
theorem s4_219_safe : Safe 9 4 s4_219 := by
  apply safe_succ 8 4 s4_219 [] (by decide) s4_219_edges
  simp
def s4_220 : State := ⟨4, 8, 214, 144, 27973577474460502716656777188955856128786508989651833843043336470, 0, 0, 1⟩
theorem s4_220_edges : next 4 s4_220 = [] := by decide
theorem s4_220_safe : Safe 9 4 s4_220 := by
  apply safe_succ 8 4 s4_220 [] (by decide) s4_220_edges
  simp
def s4_221 : State := ⟨4, 8, 214, 144, 28384953613790804227195519484595193755032192882273252514042282262, 0, 0, 1⟩
theorem s4_221_edges : next 4 s4_221 = [] := by decide
theorem s4_221_safe : Safe 9 4 s4_221 := by
  apply safe_succ 8 4 s4_221 [] (by decide) s4_221_edges
  simp
def s4_222 : State := ⟨4, 8, 214, 146, 26328072917139296674568711603123565176982234353695557675800133910, 0, 0, 1⟩
theorem s4_222_edges : next 4 s4_222 = [] := by decide
theorem s4_222_safe : Safe 9 4 s4_222 := by
  apply safe_succ 8 4 s4_222 [] (by decide) s4_222_edges
  simp
def s4_223 : State := ⟨4, 8, 214, 146, 26328072917139296674591010987192628116369916218469776310233268502, 0, 0, 1⟩
theorem s4_223_edges : next 4 s4_223 = [] := by decide
theorem s4_223_safe : Safe 9 4 s4_223 := by
  apply safe_succ 8 4 s4_223 [] (by decide) s4_223_edges
  simp
def s4_224 : State := ⟨4, 8, 214, 146, 27973577474460502716723680785680915681964969924181232359795917078, 0, 0, 1⟩
theorem s4_224_edges : next 4 s4_224 = [] := by decide
theorem s4_224_safe : Safe 9 4 s4_224 := by
  apply safe_succ 8 4 s4_224 [] (by decide) s4_224_edges
  simp
def s4_225 : State := ⟨4, 8, 214, 146, 27973577474460502716745980169749978621352651788955450994229051670, 0, 0, 1⟩
theorem s4_225_edges : next 4 s4_225 = [] := by decide
theorem s4_225_safe : Safe 9 4 s4_225 := by
  apply safe_succ 8 4 s4_225 [] (by decide) s4_225_edges
  simp
def s4_226 : State := ⟨4, 8, 214, 150, 26328072917139296675995959295829525058040520027997147632830054678, 0, 0, 1⟩
theorem s4_226_edges : next 4 s4_226 = [] := by decide
theorem s4_226_safe : Safe 9 4 s4_226 := by
  apply safe_succ 8 4 s4_226 [] (by decide) s4_226_edges
  simp
def s4_227 : State := ⟨4, 8, 214, 150, 26328072917139296676018258679898587997428201892771366267263189270, 0, 0, 1⟩
theorem s4_227_edges : next 4 s4_227 = [] := by decide
theorem s4_227_safe : Safe 9 4 s4_227 := by
  apply safe_succ 8 4 s4_227 [] (by decide) s4_227_edges
  simp
def s4_228 : State := ⟨4, 9, 64, 171, 2999001359804714199988565969051148076115210423829270, 2, 0, 1⟩
theorem s4_228_edges : next 4 s4_228 = [s5_18] := by decide
theorem s4_228_safe : Safe 9 4 s4_228 := by
  apply safe_succ 8 4 s4_228 [s5_18] (by decide) s4_228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_18_safe
def s4_229 : State := ⟨4, 9, 64, 171, 3000462861440683973439085900030010860705139283526422, 2, 0, 1⟩
theorem s4_229_edges : next 4 s4_229 = [s5_19] := by decide
theorem s4_229_safe : Safe 9 4 s4_229 := by
  apply safe_succ 8 4 s4_229 [s5_19] (by decide) s4_229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_19_safe
def s4_230 : State := ⟨4, 9, 96, 128, 340282387282576229647756113050568033046, 2, 2, 0⟩
theorem s4_230_edges : next 4 s4_230 = [s5_252] := by decide
theorem s4_230_safe : Safe 9 4 s4_230 := by
  apply safe_succ 8 4 s4_230 [s5_252] (by decide) s4_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_252_safe
def s4_231 : State := ⟨4, 9, 104, 224, 26959946667150639794667015087359913060919720652188328594154178282262, 2, 0, 1⟩
theorem s4_231_edges : next 4 s4_231 = [s5_218] := by decide
theorem s4_231_safe : Safe 9 4 s4_231 := by
  apply safe_succ 8 4 s4_231 [s5_218] (by decide) s4_231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_218_safe
def s4_232 : State := ⟨4, 12, 64, 163, 11692013102390329381759801759845831583074915258646, 2, 0, 1⟩
theorem s4_232_edges : next 4 s4_232 = [s5_1] := by decide
theorem s4_232_safe : Safe 9 4 s4_232 := by
  apply safe_succ 8 4 s4_232 [s5_1] (by decide) s4_232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_1_safe
def s4_233 : State := ⟨4, 12, 64, 163, 11692013103070894115601678686772580797938451681558, 2, 0, 1⟩
theorem s4_233_edges : next 4 s4_233 = [s5_3] := by decide
theorem s4_233_safe : Safe 9 4 s4_233 := by
  apply safe_succ 8 4 s4_233 [s5_3] (by decide) s4_233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_3_safe
def s4_234 : State := ⟨4, 12, 64, 163, 14615016374329876282799663717571400762932634652950, 2, 0, 1⟩
theorem s4_234_edges : next 4 s4_234 = [s5_5] := by decide
theorem s4_234_safe : Safe 9 4 s4_234 := by
  apply safe_succ 8 4 s4_234 [s5_5] (by decide) s4_234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_5_safe
def s4_235 : State := ⟨4, 12, 64, 163, 16076518010980214467161471623360934567725030773014, 2, 0, 1⟩
theorem s4_235_edges : next 4 s4_235 = [s5_7] := by decide
theorem s4_235_safe : Safe 9 4 s4_235 := by
  apply safe_succ 8 4 s4_235 [s5_7] (by decide) s4_235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_7_safe
def s4_236 : State := ⟨4, 12, 64, 163, 17538019649672246853048910309930716017108036161814, 2, 0, 1⟩
theorem s4_236_edges : next 4 s4_236 = [s5_9] := by decide
theorem s4_236_safe : Safe 9 4 s4_236 := by
  apply safe_succ 8 4 s4_236 [s5_9] (by decide) s4_236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_9_safe
def s4_237 : State := ⟨4, 12, 64, 163, 18999521285642020303568841288793500607036895858966, 2, 0, 1⟩
theorem s4_237_edges : next 4 s4_237 = [s5_11] := by decide
theorem s4_237_safe : Safe 9 4 s4_237 := by
  apply safe_succ 8 4 s4_237 [s5_11] (by decide) s4_237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_11_safe
def s4_238 : State := ⟨4, 12, 64, 210, 1645504557321206042244173864763307602241196074043954546218176790, 2, 0, 1⟩
theorem s4_238_edges : next 4 s4_238 = [s5_21] := by decide
theorem s4_238_safe : Safe 9 4 s4_238 := by
  apply safe_succ 8 4 s4_238 [s5_21] (by decide) s4_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_21_safe
def s4_239 : State := ⟨4, 12, 64, 210, 1645504557321206042266473248832370541628877938818173180651311382, 2, 0, 1⟩
theorem s4_239_edges : next 4 s4_239 = [s5_23] := by decide
theorem s4_239_safe : Safe 9 4 s4_239 := by
  apply safe_succ 8 4 s4_239 [s5_23] (by decide) s4_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_23_safe
def s4_240 : State := ⟨4, 12, 64, 210, 1645529665728147588878026227126877940340717610375138956332306710, 2, 0, 1⟩
theorem s4_240_edges : next 4 s4_240 = [s5_25] := by decide
theorem s4_240_safe : Safe 9 4 s4_240 := by
  apply safe_succ 8 4 s4_240 [s5_25] (by decide) s4_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_25_safe
def s4_241 : State := ⟨4, 12, 64, 210, 1645535942829882975558788701786833464253279859232153693293973782, 2, 0, 1⟩
theorem s4_241_edges : next 4 s4_241 = [s5_27] := by decide
theorem s4_241_safe : Safe 9 4 s4_241 := by
  apply safe_succ 8 4 s4_241 [s5_27] (by decide) s4_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_27_safe
def s4_242 : State := ⟨4, 12, 64, 210, 2056880696651507552716012563677585675308419032135974700464541974, 2, 0, 1⟩
theorem s4_242_edges : next 4 s4_242 = [s5_29] := by decide
theorem s4_242_safe : Safe 9 4 s4_242 := by
  apply safe_succ 8 4 s4_242 [s5_29] (by decide) s4_242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_29_safe
def s4_243 : State := ⟨4, 12, 64, 210, 2056886973753242939374475654268478259833299416218770802993074454, 2, 0, 1⟩
theorem s4_243_edges : next 4 s4_243 = [s5_31] := by decide
theorem s4_243_safe : Safe 9 4 s4_243 := by
  apply safe_succ 8 4 s4_243 [s5_31] (by decide) s4_243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_31_safe
def s4_244 : State := ⟨4, 12, 65, 146, 89204682205957097258460245303862830288670998, 2, 0, 1⟩
theorem s4_244_edges : next 4 s4_244 = [s5_41, s5_255] := by decide
theorem s4_244_safe : Safe 9 4 s4_244 := by
  apply safe_succ 8 4 s4_244 [s5_41, s5_255] (by decide) s4_244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_41_safe
  · subst z; exact s5_255_safe
def s4_245 : State := ⟨4, 12, 65, 146, 111504066275020036646142110078081464721805590, 2, 0, 1⟩
theorem s4_245_edges : next 4 s4_245 = [s5_43, s5_257] := by decide
theorem s4_245_safe : Safe 9 4 s4_245 := by
  apply safe_succ 8 4 s4_245 [s5_43, s5_257] (by decide) s4_245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_43_safe
  · subst z; exact s5_257_safe
def s4_246 : State := ⟨4, 12, 65, 162, 5846006551025023507419431648237345348007994921238, 2, 0, 1⟩
theorem s4_246_edges : next 4 s4_246 = [s5_45, s5_259] := by decide
theorem s4_246_safe : Safe 9 4 s4_246 := by
  apply safe_succ 8 4 s4_246 [s5_45, s5_259] (by decide) s4_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_45_safe
  · subst z; exact s5_259_safe
def s4_247 : State := ⟨4, 12, 65, 162, 7307508186994796957939362627100129937936854618390, 2, 0, 1⟩
theorem s4_247_edges : next 4 s4_247 = [s5_47, s5_261] := by decide
theorem s4_247_safe : Safe 9 4 s4_247 := by
  apply safe_succ 8 4 s4_247 [s5_47, s5_261] (by decide) s4_247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_47_safe
  · subst z; exact s5_261_safe
def s4_248 : State := ⟨4, 12, 65, 176, 95780971326419139128294233276893560963659213834359062, 2, 0, 1⟩
theorem s4_248_edges : next 4 s4_248 = [s5_49, s5_263] := by decide
theorem s4_248_safe : Safe 9 4 s4_248 := by
  apply safe_succ 8 4 s4_248 [s5_49, s5_263] (by decide) s4_248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_49_safe
  · subst z; exact s5_263_safe
def s4_249 : State := ⟨4, 12, 65, 176, 95782432805755724832681813820190558974030508260921622, 2, 0, 1⟩
theorem s4_249_edges : next 4 s4_249 = [s5_51, s5_265] := by decide
theorem s4_249_safe : Safe 9 4 s4_249 := by
  apply safe_succ 8 4 s4_249 [s5_51, s5_265] (by decide) s4_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_51_safe
  · subst z; exact s5_265_safe
def s4_250 : State := ⟨4, 12, 65, 224, 26959946667150639796128516724690815958761767718775570340416734695702, 2, 0, 1⟩
theorem s4_250_edges : next 4 s4_250 = [s5_53, s5_269] := by decide
theorem s4_250_safe : Safe 9 4 s4_250 := by
  apply safe_succ 8 4 s4_250 [s5_53, s5_269] (by decide) s4_250_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_53_safe
  · subst z; exact s5_269_safe
def s4_251 : State := ⟨4, 12, 65, 224, 26959946673427741530053695851195702463765749302161642765224836665622, 2, 0, 1⟩
theorem s4_251_edges : next 4 s4_251 = [s5_55, s5_271] := by decide
theorem s4_251_safe : Safe 9 4 s4_251 := by
  apply safe_succ 8 4 s4_251 [s5_55, s5_271] (by decide) s4_251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_55_safe
  · subst z; exact s5_271_safe
def s4_252 : State := ⟨4, 12, 66, 146, 89204682205957097258460282197350977707774230, 2, 0, 1⟩
theorem s4_252_edges : next 4 s4_252 = [s5_59, s5_256] := by decide
theorem s4_252_safe : Safe 9 4 s4_252 := by
  apply safe_succ 8 4 s4_252 [s5_59, s5_256] (by decide) s4_252_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_59_safe
  · subst z; exact s5_256_safe
def s4_253 : State := ⟨4, 12, 66, 146, 111504066275020036646142146971569612140908822, 2, 0, 1⟩
theorem s4_253_edges : next 4 s4_253 = [s5_61, s5_258] := by decide
theorem s4_253_safe : Safe 9 4 s4_253 := by
  apply safe_succ 8 4 s4_253 [s5_61, s5_258] (by decide) s4_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_61_safe
  · subst z; exact s5_258_safe
def s4_254 : State := ⟨4, 12, 66, 162, 5846006551025023507419431648274238836155414024470, 2, 0, 1⟩
theorem s4_254_edges : next 4 s4_254 = [s5_63, s5_260, s5_253] := by decide
theorem s4_254_safe : Safe 9 4 s4_254 := by
  apply safe_succ 8 4 s4_254 [s5_63, s5_260, s5_253] (by decide) s4_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_63_safe
  · subst z; exact s5_260_safe
  · subst z; exact s5_253_safe
def s4_255 : State := ⟨4, 12, 66, 162, 7307508186994796957939362627137023426084273721622, 2, 0, 1⟩
theorem s4_255_edges : next 4 s4_255 = [s5_65, s5_262, s5_254] := by decide
theorem s4_255_safe : Safe 9 4 s4_255 := by
  apply safe_succ 8 4 s4_255 [s5_65, s5_262, s5_254] (by decide) s4_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_65_safe
  · subst z; exact s5_262_safe
  · subst z; exact s5_254_safe
def s4_256 : State := ⟨4, 12, 66, 176, 95780971326419139128294233276893597857147361253462294, 2, 0, 1⟩
theorem s4_256_edges : next 4 s4_256 = [s5_67, s5_264] := by decide
theorem s4_256_safe : Safe 9 4 s4_256 := by
  apply safe_succ 8 4 s4_256 [s5_67, s5_264] (by decide) s4_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_67_safe
  · subst z; exact s5_264_safe
def s4_257 : State := ⟨4, 12, 66, 176, 95782432805755724832681813820190595867518655680024854, 2, 0, 1⟩
theorem s4_257_edges : next 4 s4_257 = [s5_69, s5_266] := by decide
theorem s4_257_safe : Safe 9 4 s4_257 := by
  apply safe_succ 8 4 s4_257 [s5_69, s5_266] (by decide) s4_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_69_safe
  · subst z; exact s5_266_safe
def s4_258 : State := ⟨4, 12, 66, 210, 1645504557321206042177270268038248049062735139514556029465596182, 2, 0, 1⟩
theorem s4_258_edges : next 4 s4_258 = [s5_71, s5_267] := by decide
theorem s4_258_safe : Safe 9 4 s4_258 := by
  apply safe_succ 8 4 s4_258 [s5_71, s5_267] (by decide) s4_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_71_safe
  · subst z; exact s5_267_safe
def s4_259 : State := ⟨4, 12, 66, 210, 1645529665728147588878024865997410256586863830663685524097667350, 2, 0, 1⟩
theorem s4_259_edges : next 4 s4_259 = [s5_73, s5_268] := by decide
theorem s4_259_safe : Safe 9 4 s4_259 := by
  apply safe_succ 8 4 s4_259 [s5_73, s5_268] (by decide) s4_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_73_safe
  · subst z; exact s5_268_safe
def s4_260 : State := ⟨4, 12, 66, 224, 26959946667150639796128516724690815958761767718812463828564153798934, 2, 0, 1⟩
theorem s4_260_edges : next 4 s4_260 = [s5_77, s5_278, s5_270, s5_273] := by decide
theorem s4_260_safe : Safe 9 4 s4_260 := by
  apply safe_succ 8 4 s4_260 [s5_77, s5_278, s5_270, s5_273] (by decide) s4_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_77_safe
  · subst z; exact s5_278_safe
  · subst z; exact s5_270_safe
  · subst z; exact s5_273_safe
def s4_261 : State := ⟨4, 12, 66, 224, 26959946673427741530053695851195702463765749302198536253372255768854, 2, 0, 1⟩
theorem s4_261_edges : next 4 s4_261 = [s5_79, s5_279, s5_272, s5_275] := by decide
theorem s4_261_safe : Safe 9 4 s4_261 := by
  apply safe_succ 8 4 s4_261 [s5_79, s5_279, s5_272, s5_275] (by decide) s4_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_79_safe
  · subst z; exact s5_279_safe
  · subst z; exact s5_272_safe
  · subst z; exact s5_275_safe
def s4_262 : State := ⟨4, 12, 67, 129, 1020847100762815390593038007110404739350, 2, 0, 1⟩
theorem s4_262_edges : next 4 s4_262 = [s5_83] := by decide
theorem s4_262_safe : Safe 9 4 s4_262 := by
  apply safe_succ 8 4 s4_262 [s5_83] (by decide) s4_262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_83_safe
def s4_263 : State := ⟨4, 12, 67, 129, 1020847100762815390629931495257823842582, 2, 0, 1⟩
theorem s4_263_edges : next 4 s4_263 = [s5_85] := by decide
theorem s4_263_safe : Safe 9 4 s4_263 := by
  apply safe_succ 8 4 s4_263 [s5_85] (by decide) s4_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_85_safe
def s4_264 : State := ⟨4, 12, 67, 130, 1701411834604692317519787221973941162262, 2, 0, 1⟩
theorem s4_264_edges : next 4 s4_264 = [s5_87, s5_255, s5_259] := by decide
theorem s4_264_safe : Safe 9 4 s4_264 := by
  apply safe_succ 8 4 s4_264 [s5_87, s5_255, s5_259] (by decide) s4_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_87_safe
  · subst z; exact s5_255_safe
  · subst z; exact s5_259_safe
def s4_265 : State := ⟨4, 12, 67, 130, 1701411834604692317556680710121360265494, 2, 0, 1⟩
theorem s4_265_edges : next 4 s4_265 = [s5_89, s5_256, s5_260] := by decide
theorem s4_265_safe : Safe 9 4 s4_265 := by
  apply safe_succ 8 4 s4_265 [s5_89, s5_256, s5_260] (by decide) s4_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_89_safe
  · subst z; exact s5_256_safe
  · subst z; exact s5_260_safe
def s4_266 : State := ⟨4, 12, 67, 132, 5784800237655953879080282511155159699734, 2, 0, 1⟩
theorem s4_266_edges : next 4 s4_266 = [s5_91] := by decide
theorem s4_266_safe : Safe 9 4 s4_266 := by
  apply safe_succ 8 4 s4_266 [s5_91] (by decide) s4_266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_91_safe
def s4_267 : State := ⟨4, 12, 67, 132, 5784800237655953879117175999302578802966, 2, 0, 1⟩
theorem s4_267_edges : next 4 s4_267 = [s5_93] := by decide
theorem s4_267_safe : Safe 9 4 s4_267 := by
  apply safe_succ 8 4 s4_267 [s5_93] (by decide) s4_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_93_safe
def s4_268 : State := ⟨4, 12, 67, 136, 87452568298681185110290188294779530449174, 2, 0, 1⟩
theorem s4_268_edges : next 4 s4_268 = [s5_97] := by decide
theorem s4_268_safe : Safe 9 4 s4_268 := by
  apply safe_succ 8 4 s4_268 [s5_97] (by decide) s4_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_97_safe
def s4_269 : State := ⟨4, 12, 67, 136, 87452568298681185110327081782926949552406, 2, 0, 1⟩
theorem s4_269_edges : next 4 s4_269 = [s5_99] := by decide
theorem s4_269_safe : Safe 9 4 s4_269 := by
  apply safe_succ 8 4 s4_269 [s5_99] (by decide) s4_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_99_safe
def s4_270 : State := ⟨4, 12, 67, 140, 1394136857275084884809648680832769462440214, 2, 0, 1⟩
theorem s4_270_edges : next 4 s4_270 = [s5_103] := by decide
theorem s4_270_safe : Safe 9 4 s4_270 := by
  apply safe_succ 8 4 s4_270 [s5_103] (by decide) s4_270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_103_safe
def s4_271 : State := ⟨4, 12, 67, 140, 1394136857275084884809685574320916881543446, 2, 0, 1⟩
theorem s4_271_edges : next 4 s4_271 = [s5_105] := by decide
theorem s4_271_safe : Safe 9 4 s4_271 := by
  apply safe_succ 8 4 s4_271 [s5_105] (by decide) s4_271_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_105_safe
def s4_272 : State := ⟨4, 12, 67, 144, 22301085480897544079999384561440608374296854, 2, 0, 1⟩
theorem s4_272_edges : next 4 s4_272 = [s5_107, s5_257, s5_263] := by decide
theorem s4_272_safe : Safe 9 4 s4_272 := by
  apply safe_succ 8 4 s4_272 [s5_107, s5_257, s5_263] (by decide) s4_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_107_safe
  · subst z; exact s5_257_safe
  · subst z; exact s5_263_safe
def s4_273 : State := ⟨4, 12, 67, 144, 22301085480897544079999421454928755793400086, 2, 0, 1⟩
theorem s4_273_edges : next 4 s4_273 = [s5_109, s5_258, s5_264] := by decide
theorem s4_273_safe : Safe 9 4 s4_273 := by
  apply safe_succ 8 4 s4_273 [s5_109, s5_258, s5_264] (by decide) s4_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_109_safe
  · subst z; exact s5_258_safe
  · subst z; exact s5_264_safe
def s4_274 : State := ⟨4, 12, 67, 160, 1461501637671185285124623296382571811902800859414, 2, 0, 1⟩
theorem s4_274_edges : next 4 s4_274 = [s5_111, s5_261, s5_265] := by decide
theorem s4_274_safe : Safe 9 4 s4_274 := by
  apply safe_succ 8 4 s4_274 [s5_111, s5_261, s5_265] (by decide) s4_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_111_safe
  · subst z; exact s5_261_safe
  · subst z; exact s5_265_safe
def s4_275 : State := ⟨4, 12, 67, 160, 1461501637671185285124623296419465300050219962646, 2, 0, 1⟩
theorem s4_275_edges : next 4 s4_275 = [s5_113, s5_262, s5_266] := by decide
theorem s4_275_safe : Safe 9 4 s4_275 := by
  apply safe_succ 8 4 s4_275 [s5_113, s5_262, s5_266] (by decide) s4_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_113_safe
  · subst z; exact s5_262_safe
  · subst z; exact s5_266_safe
def s4_276 : State := ⟨4, 12, 67, 192, 6277101735386680764176071790128604879768644236710902829334, 2, 0, 1⟩
theorem s4_276_edges : next 4 s4_276 = [s5_115, s5_271] := by decide
theorem s4_276_safe : Safe 9 4 s4_276 := by
  apply safe_succ 8 4 s4_276 [s5_115, s5_271] (by decide) s4_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_115_safe
  · subst z; exact s5_271_safe
def s4_277 : State := ⟨4, 12, 67, 192, 6277101735386680764176071790128604879805537724858321932566, 2, 0, 1⟩
theorem s4_277_edges : next 4 s4_277 = [s5_117, s5_272] := by decide
theorem s4_277_safe : Safe 9 4 s4_277 := by
  apply safe_succ 8 4 s4_277 [s5_117, s5_272] (by decide) s4_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_117_safe
  · subst z; exact s5_272_safe
def s4_278 : State := ⟨4, 12, 67, 193, 12554203470773361528011861213336271295870999681174937342230, 2, 0, 1⟩
theorem s4_278_edges : next 4 s4_278 = [s5_119] := by decide
theorem s4_278_safe : Safe 9 4 s4_278 := by
  apply safe_succ 8 4 s4_278 [s5_119] (by decide) s4_278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_119_safe
def s4_279 : State := ⟨4, 12, 67, 194, 25108406941546723055683440059751604128112604058250425471254, 2, 0, 1⟩
theorem s4_279_edges : next 4 s4_279 = [s5_121, s5_268] := by decide
theorem s4_279_safe : Safe 9 4 s4_279 := by
  apply safe_succ 8 4 s4_279 [s5_121, s5_268] (by decide) s4_279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_121_safe
  · subst z; exact s5_268_safe
def s4_280 : State := ⟨4, 12, 67, 195, 50216813883093446111026597752582269792485132347959144419606, 2, 0, 1⟩
theorem s4_280_edges : next 4 s4_280 = [s5_123] := by decide
theorem s4_280_safe : Safe 9 4 s4_280 := by
  apply safe_succ 8 4 s4_280 [s5_123] (by decide) s4_280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_123_safe
def s4_281 : State := ⟨4, 12, 67, 195, 50216813883093446111026597752582269792522025836106563522838, 2, 0, 1⟩
theorem s4_281_edges : next 4 s4_281 = [s5_125] := by decide
theorem s4_281_safe : Safe 9 4 s4_281 := by
  apply safe_succ 8 4 s4_281 [s5_125] (by decide) s4_281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_125_safe
def s4_282 : State := ⟨4, 12, 80, 210, 1645504557321206042154970883969185109676262126772975729368961302, 2, 0, 1⟩
theorem s4_282_edges : next 4 s4_282 = [s5_131] := by decide
theorem s4_282_safe : Safe 9 4 s4_282 := by
  apply safe_succ 8 4 s4_282 [s5_131] (by decide) s4_282_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_131_safe
def s4_283 : State := ⟨4, 12, 80, 210, 2056880696651507552693711818479055052168092239682940968133267734, 2, 0, 1⟩
theorem s4_283_edges : next 4 s4_283 = [s5_133] := by decide
theorem s4_283_safe : Safe 9 4 s4_283 := by
  apply safe_succ 8 4 s4_283 [s5_133] (by decide) s4_283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_133_safe
def s4_284 : State := ⟨4, 12, 80, 224, 26959946667150639796128516724690815958761768927664496466898490298646, 2, 0, 1⟩
theorem s4_284_edges : next 4 s4_284 = [s5_137, s5_274] := by decide
theorem s4_284_safe : Safe 9 4 s4_284 := by
  apply safe_succ 8 4 s4_284 [s5_137, s5_274] (by decide) s4_284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_137_safe
  · subst z; exact s5_274_safe
def s4_285 : State := ⟨4, 12, 80, 224, 26959946673427741530053695851195702463765750511050568891706592268566, 2, 0, 1⟩
theorem s4_285_edges : next 4 s4_285 = [s5_139, s5_276] := by decide
theorem s4_285_safe : Safe 9 4 s4_285 := by
  apply safe_succ 8 4 s4_285 [s5_139, s5_276] (by decide) s4_285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_139_safe
  · subst z; exact s5_276_safe
def s4_286 : State := ⟨4, 12, 82, 129, 1020847100762820226185636001184846254358, 2, 0, 1⟩
theorem s4_286_edges : next 4 s4_286 = [s5_141] := by decide
theorem s4_286_safe : Safe 9 4 s4_286 := by
  apply safe_succ 8 4 s4_286 [s5_141] (by decide) s4_286_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_141_safe
def s4_287 : State := ⟨4, 12, 82, 129, 1020847100762821435037668639519182754070, 2, 0, 1⟩
theorem s4_287_edges : next 4 s4_287 = [s5_143] := by decide
theorem s4_287_safe : Safe 9 4 s4_287 := by
  apply safe_succ 8 4 s4_287 [s5_143] (by decide) s4_287_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_143_safe
def s4_288 : State := ⟨4, 12, 82, 130, 1701411834604697153112385216048382677270, 2, 0, 1⟩
theorem s4_288_edges : next 4 s4_288 = [s5_147] := by decide
theorem s4_288_safe : Safe 9 4 s4_288 := by
  apply safe_succ 8 4 s4_288 [s5_147] (by decide) s4_288_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_147_safe
def s4_289 : State := ⟨4, 12, 82, 130, 1701411834604698361964417854382719176982, 2, 0, 1⟩
theorem s4_289_edges : next 4 s4_289 = [s5_149] := by decide
theorem s4_289_safe : Safe 9 4 s4_289 := by
  apply safe_succ 8 4 s4_289 [s5_149] (by decide) s4_289_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_149_safe
def s4_290 : State := ⟨4, 12, 82, 132, 5784800237655958714672880505229601214742, 2, 0, 1⟩
theorem s4_290_edges : next 4 s4_290 = [s5_153] := by decide
theorem s4_290_safe : Safe 9 4 s4_290 := by
  apply safe_succ 8 4 s4_290 [s5_153] (by decide) s4_290_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_153_safe
def s4_291 : State := ⟨4, 12, 82, 132, 5784800237655959923524913143563937714454, 2, 0, 1⟩
theorem s4_291_edges : next 4 s4_291 = [s5_155] := by decide
theorem s4_291_safe : Safe 9 4 s4_291 := by
  apply safe_succ 8 4 s4_291 [s5_155] (by decide) s4_291_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_155_safe
def s4_292 : State := ⟨4, 12, 82, 136, 87452568298681189945882786288853971964182, 2, 0, 1⟩
theorem s4_292_edges : next 4 s4_292 = [s5_161] := by decide
theorem s4_292_safe : Safe 9 4 s4_292 := by
  apply safe_succ 8 4 s4_292 [s5_161] (by decide) s4_292_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_161_safe
def s4_293 : State := ⟨4, 12, 82, 136, 87452568298681191154734818927188308463894, 2, 0, 1⟩
theorem s4_293_edges : next 4 s4_293 = [s5_163] := by decide
theorem s4_293_safe : Safe 9 4 s4_293 := by
  apply safe_succ 8 4 s4_293 [s5_163] (by decide) s4_293_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_163_safe
def s4_294 : State := ⟨4, 12, 82, 140, 1394136857275084889645241278826843903955222, 2, 0, 1⟩
theorem s4_294_edges : next 4 s4_294 = [s5_169] := by decide
theorem s4_294_safe : Safe 9 4 s4_294 := by
  apply safe_succ 8 4 s4_294 [s5_169] (by decide) s4_294_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_169_safe
def s4_295 : State := ⟨4, 12, 82, 140, 1394136857275084890854093311465178240454934, 2, 0, 1⟩
theorem s4_295_edges : next 4 s4_295 = [s5_171] := by decide
theorem s4_295_safe : Safe 9 4 s4_295 := by
  apply safe_succ 8 4 s4_295 [s5_171] (by decide) s4_295_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_171_safe
def s4_296 : State := ⟨4, 12, 82, 144, 22301085480897544084834977159434682815811862, 2, 0, 1⟩
theorem s4_296_edges : next 4 s4_296 = [s5_173] := by decide
theorem s4_296_safe : Safe 9 4 s4_296 := by
  apply safe_succ 8 4 s4_296 [s5_173] (by decide) s4_296_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_173_safe
def s4_297 : State := ⟨4, 12, 82, 144, 22301085480897544086043829192073017152311574, 2, 0, 1⟩
theorem s4_297_edges : next 4 s4_297 = [s5_175] := by decide
theorem s4_297_safe : Safe 9 4 s4_297 := by
  apply safe_succ 8 4 s4_297 [s5_175] (by decide) s4_297_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_175_safe
def s4_298 : State := ⟨4, 12, 82, 160, 1461501637671185285124628131975169805977242374422, 2, 0, 1⟩
theorem s4_298_edges : next 4 s4_298 = [s5_179] := by decide
theorem s4_298_safe : Safe 9 4 s4_298 := by
  apply safe_succ 8 4 s4_298 [s5_179] (by decide) s4_298_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_179_safe
def s4_299 : State := ⟨4, 12, 82, 160, 1461501637671185285124629340827202444311578874134, 2, 0, 1⟩
theorem s4_299_edges : next 4 s4_299 = [s5_181] := by decide
theorem s4_299_safe : Safe 9 4 s4_299 := by
  apply safe_succ 8 4 s4_299 [s5_181] (by decide) s4_299_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_181_safe
def s4_300 : State := ⟨4, 12, 82, 192, 6277101735386680764176071790128609715361242230785344344342, 2, 0, 1⟩
theorem s4_300_edges : next 4 s4_300 = [s5_185, s5_275] := by decide
theorem s4_300_safe : Safe 9 4 s4_300 := by
  apply safe_succ 8 4 s4_300 [s5_185, s5_275] (by decide) s4_300_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_185_safe
  · subst z; exact s5_275_safe
def s4_301 : State := ⟨4, 12, 82, 192, 6277101735386680764176071790128610924213274869119680844054, 2, 0, 1⟩
theorem s4_301_edges : next 4 s4_301 = [s5_187, s5_276] := by decide
theorem s4_301_safe : Safe 9 4 s4_301 := by
  apply safe_succ 8 4 s4_301 [s5_187, s5_276] (by decide) s4_301_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_187_safe
  · subst z; exact s5_276_safe
def s4_302 : State := ⟨4, 12, 82, 194, 25108406941546723055683440059751608963668308564177447883030, 2, 0, 1⟩
theorem s4_302_edges : next 4 s4_302 = [s5_191] := by decide
theorem s4_302_safe : Safe 9 4 s4_302 := by
  apply safe_succ 8 4 s4_302 [s5_191] (by decide) s4_302_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_191_safe
def s4_303 : State := ⟨4, 12, 82, 208, 411376139330301510538742635921704547190192077327819621483483414, 2, 0, 1⟩
theorem s4_303_edges : next 4 s4_303 = [s5_194] := by decide
theorem s4_303_safe : Safe 9 4 s4_303 := by
  apply safe_succ 8 4 s4_303 [s5_194] (by decide) s4_303_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_194_safe
def s4_304 : State := ⟨4, 12, 82, 210, 1645504557321206042154969522839717425926035124520366184658440470, 2, 0, 1⟩
theorem s4_304_edges : next 4 s4_304 = [s5_197] := by decide
theorem s4_304_safe : Safe 9 4 s4_304 := by
  apply safe_succ 8 4 s4_304 [s5_197] (by decide) s4_304_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_197_safe
def s4_305 : State := ⟨4, 12, 82, 210, 1645504557321206042154969522839717425927243976553004518994940182, 2, 0, 1⟩
theorem s4_305_edges : next 4 s4_305 = [s5_199] := by decide
theorem s4_305_safe : Safe 9 4 s4_305 := by
  apply safe_succ 8 4 s4_305 [s5_199] (by decide) s4_305_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_199_safe
def s4_306 : State := ⟨4, 12, 96, 128, 340282387282576229647756113050568036630, 2, 2, 0⟩
theorem s4_306_edges : next 4 s4_306 = [s5_277] := by decide
theorem s4_306_safe : Safe 9 4 s4_306 := by
  apply safe_succ 8 4 s4_306 [s5_277] (by decide) s4_306_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_277_safe
def s4_307 : State := ⟨4, 12, 97, 224, 26959946667150639794667015087359913040795767373565186845394014900502, 2, 0, 1⟩
theorem s4_307_edges : next 4 s4_307 = [s5_215] := by decide
theorem s4_307_safe : Safe 9 4 s4_307 := by
  apply safe_succ 8 4 s4_307 [s5_215] (by decide) s4_307_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_215_safe
def s4_308 : State := ⟨4, 12, 104, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 2, 0, 1⟩
theorem s4_308_edges : next 4 s4_308 = [s5_220] := by decide
theorem s4_308_safe : Safe 9 4 s4_308 := by
  apply safe_succ 8 4 s4_308 [s5_220] (by decide) s4_308_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_220_safe
def s4_309 : State := ⟨4, 12, 112, 224, 26959946667150639794667015087359918232934169583364286700703256219926, 2, 0, 1⟩
theorem s4_309_edges : next 4 s4_309 = [s5_226] := by decide
theorem s4_309_safe : Safe 9 4 s4_309 := by
  apply safe_succ 8 4 s4_309 [s5_226] (by decide) s4_309_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_226_safe
def s4_310 : State := ⟨4, 12, 194, 146, 25108406941546812260025363649927924124617832152539007619350, 2, 0, 1⟩
theorem s4_310_edges : next 4 s4_310 = [s5_229] := by decide
theorem s4_310_safe : Safe 9 4 s4_310 := by
  apply safe_succ 8 4 s4_310 [s5_229] (by decide) s4_310_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_229_safe
def s4_311 : State := ⟨4, 12, 194, 162, 25108406947392729606368181200250097312609873637716713869590, 2, 0, 1⟩
theorem s4_311_edges : next 4 s4_311 = [s5_231] := by decide
theorem s4_311_safe : Safe 9 4 s4_311 := by
  apply safe_succ 8 4 s4_311 [s5_231] (by decide) s4_311_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_231_safe
def s4_312 : State := ⟨4, 12, 210, 130, 1645504557321206042154970883969185109676262126772975729368961302, 2, 0, 1⟩
theorem s4_312_edges : next 4 s4_312 = [s5_233] := by decide
theorem s4_312_safe : Safe 9 4 s4_312 := by
  apply safe_succ 8 4 s4_312 [s5_233] (by decide) s4_312_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_233_safe
def s4_313 : State := ⟨4, 12, 210, 130, 1645529665728147588878026227126877940340717610375138956332306710, 2, 0, 1⟩
theorem s4_313_edges : next 4 s4_313 = [s5_235] := by decide
theorem s4_313_safe : Safe 9 4 s4_313 := by
  apply safe_succ 8 4 s4_313 [s5_235] (by decide) s4_313_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_235_safe
def s4_314 : State := ⟨4, 12, 210, 144, 1645504557321206042177270268038248049062735139514556029465596182, 2, 0, 1⟩
theorem s4_314_edges : next 4 s4_314 = [s5_239] := by decide
theorem s4_314_safe : Safe 9 4 s4_314 := by
  apply safe_succ 8 4 s4_314 [s5_239] (by decide) s4_314_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_239_safe
def s4_315 : State := ⟨4, 12, 210, 144, 2056880696651507552716012563677585675308419032135974700464541974, 2, 0, 1⟩
theorem s4_315_edges : next 4 s4_315 = [s5_241] := by decide
theorem s4_315_safe : Safe 9 4 s4_315 := by
  apply safe_succ 8 4 s4_315 [s5_241] (by decide) s4_315_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_241_safe
def s4_316 : State := ⟨4, 12, 210, 146, 1645504557321206042244173864763307602241196074043954546218176790, 2, 0, 1⟩
theorem s4_316_edges : next 4 s4_316 = [s5_245] := by decide
theorem s4_316_safe : Safe 9 4 s4_316 := by
  apply safe_succ 8 4 s4_316 [s5_245] (by decide) s4_316_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_245_safe
def s4_317 : State := ⟨4, 12, 210, 146, 1645504557321206042266473248832370541628877938818173180651311382, 2, 0, 1⟩
theorem s4_317_edges : next 4 s4_317 = [s5_247] := by decide
theorem s4_317_safe : Safe 9 4 s4_317 := by
  apply safe_succ 8 4 s4_317 [s5_247] (by decide) s4_317_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_247_safe
def s4_318 : State := ⟨4, 104, 96, 128, 340282387282576229647756113050568033046, 2, 2, 0⟩
theorem s4_318_edges : next 4 s4_318 = [s5_280] := by decide
theorem s4_318_safe : Safe 9 4 s4_318 := by
  apply safe_succ 8 4 s4_318 [s5_280] (by decide) s4_318_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_280_safe
def s4_319 : State := ⟨4, 104, 96, 128, 340282387282576229647756113050568036630, 2, 2, 0⟩
theorem s4_319_edges : next 4 s4_319 = [s5_281] := by decide
theorem s4_319_safe : Safe 9 4 s4_319 := by
  apply safe_succ 8 4 s4_319 [s5_281] (by decide) s4_319_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_281_safe
def s4_320 : State := ⟨4, 104, 96, 128, 340282387282576229647756113050568036630, 3, 1, 0⟩
theorem s4_320_edges : next 4 s4_320 = [s5_210, s5_282] := by decide
theorem s4_320_safe : Safe 9 4 s4_320 := by
  apply safe_succ 8 4 s4_320 [s5_210, s5_282] (by decide) s4_320_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_210_safe
  · subst z; exact s5_282_safe
def s4_321 : State := ⟨4, 104, 96, 128, 340282387282576229942904018229920858390, 3, 1, 0⟩
theorem s4_321_edges : next 4 s4_321 = [s5_211, s5_283] := by decide
theorem s4_321_safe : Safe 9 4 s4_321 := by
  apply safe_succ 8 4 s4_321 [s5_211, s5_283] (by decide) s4_321_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_211_safe
  · subst z; exact s5_283_safe
def s4_322 : State := ⟨4, 104, 96, 128, 340282388550226829875985514547271237910, 3, 1, 0⟩
theorem s4_322_edges : next 4 s4_322 = [s5_212, s5_284] := by decide
theorem s4_322_safe : Safe 9 4 s4_322 := by
  apply safe_succ 8 4 s4_322 [s5_212, s5_284] (by decide) s4_322_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_212_safe
  · subst z; exact s5_284_safe
def s4_323 : State := ⟨4, 104, 96, 128, 340282711801129888074482896206588608790, 3, 1, 0⟩
theorem s4_323_edges : next 4 s4_323 = [s5_213, s5_285] := by decide
theorem s4_323_safe : Safe 9 4 s4_323 := by
  apply safe_succ 8 4 s4_323 [s5_213, s5_285] (by decide) s4_323_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_213_safe
  · subst z; exact s5_285_safe
def s4_324 : State := ⟨4, 104, 97, 224, 26959946667150639794667015087359913061078176977216857269341266182422, 2, 0, 1⟩
theorem s4_324_edges : next 4 s4_324 = [] := by decide
theorem s4_324_safe : Safe 9 4 s4_324 := by
  apply safe_succ 8 4 s4_324 [] (by decide) s4_324_edges
  simp
def s4_325 : State := ⟨4, 104, 100, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 2, 0, 1⟩
theorem s4_325_edges : next 4 s4_325 = [] := by decide
theorem s4_325_safe : Safe 9 4 s4_325 := by
  apply safe_succ 8 4 s4_325 [] (by decide) s4_325_edges
  simp
def s4_326 : State := ⟨4, 104, 112, 224, 26959946667150639794667015087359918253216579187015957124650507501846, 2, 0, 1⟩
theorem s4_326_edges : next 4 s4_326 = [] := by decide
theorem s4_326_safe : Safe 9 4 s4_326 := by
  apply safe_succ 8 4 s4_326 [] (by decide) s4_326_edges
  simp
def s4_327 : State := ⟨4, 108, 96, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 2, 0, 1⟩
theorem s4_327_edges : next 4 s4_327 = [] := by decide
theorem s4_327_safe : Safe 9 4 s4_327 := by
  apply safe_succ 8 4 s4_327 [] (by decide) s4_327_edges
  simp
def s4_328 : State := ⟨4, 120, 96, 224, 26959946667150639794667015087361242288915505568061232401214458626326, 2, 0, 1⟩
theorem s4_328_edges : next 4 s4_328 = [] := by decide
theorem s4_328_safe : Safe 9 4 s4_328 := by
  apply safe_succ 8 4 s4_328 [] (by decide) s4_328_edges
  simp
def s4_329 : State := ⟨4, 140, 67, 132, 1399581375145819900225062674551677753819414, 2, 0, 1⟩
theorem s4_329_edges : next 4 s4_329 = [s5_94] := by decide
theorem s4_329_safe : Safe 9 4 s4_329 := by
  apply safe_succ 8 4 s4_329 [s5_94] (by decide) s4_329_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_94_safe
def s4_330 : State := ⟨4, 140, 67, 132, 1399581375145819900225099568039825172922646, 2, 0, 1⟩
theorem s4_330_edges : next 4 s4_330 = [s5_95] := by decide
theorem s4_330_safe : Safe 9 4 s4_330 := by
  apply safe_succ 8 4 s4_330 [s5_95] (by decide) s4_330_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_95_safe
def s4_331 : State := ⟨4, 140, 82, 132, 1399581375145819905060655272545752195334422, 2, 0, 1⟩
theorem s4_331_edges : next 4 s4_331 = [s5_158] := by decide
theorem s4_331_safe : Safe 9 4 s4_331 := by
  apply safe_succ 8 4 s4_331 [s5_158] (by decide) s4_331_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_158_safe
def s4_332 : State := ⟨4, 140, 82, 132, 1399581375145819906269507305184086531834134, 2, 0, 1⟩
theorem s4_332_edges : next 4 s4_332 = [s5_159] := by decide
theorem s4_332_safe : Safe 9 4 s4_332 := by
  apply safe_succ 8 4 s4_332 [s5_159] (by decide) s4_332_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_159_safe
def s4_333 : State := ⟨4, 171, 64, 162, 2999001359804714199988565969051148076115210423829270, 2, 0, 1⟩
theorem s4_333_edges : next 4 s4_333 = [] := by decide
theorem s4_333_safe : Safe 9 4 s4_333 := by
  apply safe_succ 8 4 s4_333 [] (by decide) s4_333_edges
  simp
def s4_334 : State := ⟨4, 171, 64, 162, 3000462861440683973439085900030010860705139283526422, 2, 0, 1⟩
theorem s4_334_edges : next 4 s4_334 = [] := by decide
theorem s4_334_safe : Safe 9 4 s4_334 := by
  apply safe_succ 8 4 s4_334 [] (by decide) s4_334_edges
  simp
def s4_335 : State := ⟨4, 171, 64, 162, 4495579036431558788229139237752621888242885347836182, 2, 0, 1⟩
theorem s4_335_edges : next 4 s4_335 = [] := by decide
theorem s4_335_safe : Safe 9 4 s4_335 := by
  apply safe_succ 8 4 s4_335 [] (by decide) s4_335_edges
  simp
def s4_336 : State := ⟨4, 171, 64, 162, 4497040538067528561679659168731484672832814207533334, 2, 0, 1⟩
theorem s4_336_edges : next 4 s4_336 = [] := by decide
theorem s4_336_safe : Safe 9 4 s4_336 := by
  apply safe_succ 8 4 s4_336 [] (by decide) s4_336_edges
  simp
def s4_337 : State := ⟨4, 171, 64, 163, 3004847366356079505862906339162793455838424763269398, 2, 0, 1⟩
theorem s4_337_edges : next 4 s4_337 = [s5_12] := by decide
theorem s4_337_safe : Safe 9 4 s4_337 := by
  apply safe_succ 8 4 s4_337 [s5_12] (by decide) s4_337_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_12_safe
def s4_338 : State := ⟨4, 171, 64, 163, 3004847366356760070596748216089720205053288299692310, 2, 0, 1⟩
theorem s4_338_edges : next 4 s4_338 = [s5_13] := by decide
theorem s4_338_safe : Safe 9 4 s4_338 := by
  apply safe_succ 8 4 s4_338 [s5_13] (by decide) s4_338_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_13_safe
def s4_339 : State := ⟨4, 171, 64, 163, 3007770369628019052763946201120519025018282482663702, 2, 0, 1⟩
theorem s4_339_edges : next 4 s4_339 = [s5_14] := by decide
theorem s4_339_safe : Safe 9 4 s4_339 := by
  apply safe_succ 8 4 s4_339 [s5_14] (by decide) s4_339_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_14_safe
def s4_340 : State := ⟨4, 171, 64, 163, 3009231871264669390948308009026308558823074878783766, 2, 0, 1⟩
theorem s4_340_edges : next 4 s4_340 = [s5_15] := by decide
theorem s4_340_safe : Safe 9 4 s4_340 := by
  apply safe_succ 8 4 s4_340 [s5_15] (by decide) s4_340_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_15_safe
def s4_341 : State := ⟨4, 171, 64, 163, 3010693372903361423334195447712878340272457884172566, 2, 0, 1⟩
theorem s4_341_edges : next 4 s4_341 = [s5_16] := by decide
theorem s4_341_safe : Safe 9 4 s4_341 := by
  apply safe_succ 8 4 s4_341 [s5_16] (by decide) s4_341_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_16_safe
def s4_342 : State := ⟨4, 171, 64, 163, 3012154874539331196784715378691741124862386743869718, 2, 0, 1⟩
theorem s4_342_edges : next 4 s4_342 = [s5_17] := by decide
theorem s4_342_safe : Safe 9 4 s4_342 := by
  apply safe_succ 8 4 s4_342 [s5_17] (by decide) s4_342_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_17_safe
def s4_343 : State := ⟨12, 8, 64, 163, 11692013102390329381759801759845831583074915258646, 1, 0, 1⟩
theorem s4_343_edges : next 4 s4_343 = [s5_0] := by decide
theorem s4_343_safe : Safe 9 4 s4_343 := by
  apply safe_succ 8 4 s4_343 [s5_0] (by decide) s4_343_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_0_safe
def s4_344 : State := ⟨12, 8, 64, 163, 11692013103070894115601678686772580797938451681558, 1, 0, 1⟩
theorem s4_344_edges : next 4 s4_344 = [s5_2] := by decide
theorem s4_344_safe : Safe 9 4 s4_344 := by
  apply safe_succ 8 4 s4_344 [s5_2] (by decide) s4_344_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_2_safe
def s4_345 : State := ⟨12, 8, 64, 163, 14615016374329876282799663717571400762932634652950, 1, 0, 1⟩
theorem s4_345_edges : next 4 s4_345 = [s5_4] := by decide
theorem s4_345_safe : Safe 9 4 s4_345 := by
  apply safe_succ 8 4 s4_345 [s5_4] (by decide) s4_345_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_4_safe
def s4_346 : State := ⟨12, 8, 64, 163, 16076518010980214467161471623360934567725030773014, 1, 0, 1⟩
theorem s4_346_edges : next 4 s4_346 = [s5_6] := by decide
theorem s4_346_safe : Safe 9 4 s4_346 := by
  apply safe_succ 8 4 s4_346 [s5_6] (by decide) s4_346_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_6_safe
def s4_347 : State := ⟨12, 8, 64, 163, 17538019649672246853048910309930716017108036161814, 1, 0, 1⟩
theorem s4_347_edges : next 4 s4_347 = [s5_8] := by decide
theorem s4_347_safe : Safe 9 4 s4_347 := by
  apply safe_succ 8 4 s4_347 [s5_8] (by decide) s4_347_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_8_safe
def s4_348 : State := ⟨12, 8, 64, 163, 18999521285642020303568841288793500607036895858966, 1, 0, 1⟩
theorem s4_348_edges : next 4 s4_348 = [s5_10] := by decide
theorem s4_348_safe : Safe 9 4 s4_348 := by
  apply safe_succ 8 4 s4_348 [s5_10] (by decide) s4_348_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_10_safe
def s4_349 : State := ⟨12, 8, 64, 210, 1645504557321206042244173864763307602241196074043954546218176790, 1, 0, 1⟩
theorem s4_349_edges : next 4 s4_349 = [s5_20] := by decide
theorem s4_349_safe : Safe 9 4 s4_349 := by
  apply safe_succ 8 4 s4_349 [s5_20] (by decide) s4_349_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_20_safe
def s4_350 : State := ⟨12, 8, 64, 210, 1645504557321206042266473248832370541628877938818173180651311382, 1, 0, 1⟩
theorem s4_350_edges : next 4 s4_350 = [s5_22] := by decide
theorem s4_350_safe : Safe 9 4 s4_350 := by
  apply safe_succ 8 4 s4_350 [s5_22] (by decide) s4_350_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_22_safe
def s4_351 : State := ⟨12, 8, 64, 210, 1645529665728147588878026227126877940340717610375138956332306710, 1, 0, 1⟩
theorem s4_351_edges : next 4 s4_351 = [s5_24] := by decide
theorem s4_351_safe : Safe 9 4 s4_351 := by
  apply safe_succ 8 4 s4_351 [s5_24] (by decide) s4_351_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_24_safe
def s4_352 : State := ⟨12, 8, 64, 210, 1645535942829882975558788701786833464253279859232153693293973782, 1, 0, 1⟩
theorem s4_352_edges : next 4 s4_352 = [s5_26] := by decide
theorem s4_352_safe : Safe 9 4 s4_352 := by
  apply safe_succ 8 4 s4_352 [s5_26] (by decide) s4_352_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_26_safe
def s4_353 : State := ⟨12, 8, 64, 210, 2056880696651507552716012563677585675308419032135974700464541974, 1, 0, 1⟩
theorem s4_353_edges : next 4 s4_353 = [s5_28] := by decide
theorem s4_353_safe : Safe 9 4 s4_353 := by
  apply safe_succ 8 4 s4_353 [s5_28] (by decide) s4_353_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_28_safe
def s4_354 : State := ⟨12, 8, 64, 210, 2056886973753242939374475654268478259833299416218770802993074454, 1, 0, 1⟩
theorem s4_354_edges : next 4 s4_354 = [s5_30] := by decide
theorem s4_354_safe : Safe 9 4 s4_354 := by
  apply safe_succ 8 4 s4_354 [s5_30] (by decide) s4_354_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_30_safe
def s4_355 : State := ⟨12, 8, 65, 146, 89204682205957097258460245303862830288670998, 1, 0, 1⟩
theorem s4_355_edges : next 4 s4_355 = [s5_40, s5_289] := by decide
theorem s4_355_safe : Safe 9 4 s4_355 := by
  apply safe_succ 8 4 s4_355 [s5_40, s5_289] (by decide) s4_355_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_40_safe
  · subst z; exact s5_289_safe
def s4_356 : State := ⟨12, 8, 65, 146, 111504066275020036646142110078081464721805590, 1, 0, 1⟩
theorem s4_356_edges : next 4 s4_356 = [s5_42, s5_291] := by decide
theorem s4_356_safe : Safe 9 4 s4_356 := by
  apply safe_succ 8 4 s4_356 [s5_42, s5_291] (by decide) s4_356_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_42_safe
  · subst z; exact s5_291_safe
def s4_357 : State := ⟨12, 8, 65, 162, 5846006551025023507419431648237345348007994921238, 1, 0, 1⟩
theorem s4_357_edges : next 4 s4_357 = [s5_44, s5_293] := by decide
theorem s4_357_safe : Safe 9 4 s4_357 := by
  apply safe_succ 8 4 s4_357 [s5_44, s5_293] (by decide) s4_357_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_44_safe
  · subst z; exact s5_293_safe
def s4_358 : State := ⟨12, 8, 65, 162, 7307508186994796957939362627100129937936854618390, 1, 0, 1⟩
theorem s4_358_edges : next 4 s4_358 = [s5_46, s5_295] := by decide
theorem s4_358_safe : Safe 9 4 s4_358 := by
  apply safe_succ 8 4 s4_358 [s5_46, s5_295] (by decide) s4_358_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_46_safe
  · subst z; exact s5_295_safe
def s4_359 : State := ⟨12, 8, 65, 176, 95780971326419139128294233276893560963659213834359062, 1, 0, 1⟩
theorem s4_359_edges : next 4 s4_359 = [s5_48, s5_297] := by decide
theorem s4_359_safe : Safe 9 4 s4_359 := by
  apply safe_succ 8 4 s4_359 [s5_48, s5_297] (by decide) s4_359_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_48_safe
  · subst z; exact s5_297_safe
def s4_360 : State := ⟨12, 8, 65, 176, 95782432805755724832681813820190558974030508260921622, 1, 0, 1⟩
theorem s4_360_edges : next 4 s4_360 = [s5_50, s5_299] := by decide
theorem s4_360_safe : Safe 9 4 s4_360 := by
  apply safe_succ 8 4 s4_360 [s5_50, s5_299] (by decide) s4_360_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_50_safe
  · subst z; exact s5_299_safe
def s4_361 : State := ⟨12, 8, 65, 224, 26959946667150639796128516724690815958761767718775570340416734695702, 1, 0, 1⟩
theorem s4_361_edges : next 4 s4_361 = [s5_52, s5_303] := by decide
theorem s4_361_safe : Safe 9 4 s4_361 := by
  apply safe_succ 8 4 s4_361 [s5_52, s5_303] (by decide) s4_361_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_52_safe
  · subst z; exact s5_303_safe
def s4_362 : State := ⟨12, 8, 65, 224, 26959946673427741530053695851195702463765749302161642765224836665622, 1, 0, 1⟩
theorem s4_362_edges : next 4 s4_362 = [s5_54, s5_305] := by decide
theorem s4_362_safe : Safe 9 4 s4_362 := by
  apply safe_succ 8 4 s4_362 [s5_54, s5_305] (by decide) s4_362_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_54_safe
  · subst z; exact s5_305_safe
def s4_363 : State := ⟨12, 8, 66, 146, 89204682205957097258460282197350977707774230, 1, 0, 1⟩
theorem s4_363_edges : next 4 s4_363 = [s5_58, s5_290] := by decide
theorem s4_363_safe : Safe 9 4 s4_363 := by
  apply safe_succ 8 4 s4_363 [s5_58, s5_290] (by decide) s4_363_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_58_safe
  · subst z; exact s5_290_safe
def s4_364 : State := ⟨12, 8, 66, 146, 111504066275020036646142146971569612140908822, 1, 0, 1⟩
theorem s4_364_edges : next 4 s4_364 = [s5_60, s5_292] := by decide
theorem s4_364_safe : Safe 9 4 s4_364 := by
  apply safe_succ 8 4 s4_364 [s5_60, s5_292] (by decide) s4_364_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_60_safe
  · subst z; exact s5_292_safe
def s4_365 : State := ⟨12, 8, 66, 162, 5846006551025023507419431648274238836155414024470, 1, 0, 1⟩
theorem s4_365_edges : next 4 s4_365 = [s5_62, s5_294, s5_287] := by decide
theorem s4_365_safe : Safe 9 4 s4_365 := by
  apply safe_succ 8 4 s4_365 [s5_62, s5_294, s5_287] (by decide) s4_365_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_62_safe
  · subst z; exact s5_294_safe
  · subst z; exact s5_287_safe
def s4_366 : State := ⟨12, 8, 66, 162, 7307508186994796957939362627137023426084273721622, 1, 0, 1⟩
theorem s4_366_edges : next 4 s4_366 = [s5_64, s5_296, s5_288] := by decide
theorem s4_366_safe : Safe 9 4 s4_366 := by
  apply safe_succ 8 4 s4_366 [s5_64, s5_296, s5_288] (by decide) s4_366_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_64_safe
  · subst z; exact s5_296_safe
  · subst z; exact s5_288_safe
def s4_367 : State := ⟨12, 8, 66, 176, 95780971326419139128294233276893597857147361253462294, 1, 0, 1⟩
theorem s4_367_edges : next 4 s4_367 = [s5_66, s5_298] := by decide
theorem s4_367_safe : Safe 9 4 s4_367 := by
  apply safe_succ 8 4 s4_367 [s5_66, s5_298] (by decide) s4_367_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_66_safe
  · subst z; exact s5_298_safe
def s4_368 : State := ⟨12, 8, 66, 176, 95782432805755724832681813820190595867518655680024854, 1, 0, 1⟩
theorem s4_368_edges : next 4 s4_368 = [s5_68, s5_300] := by decide
theorem s4_368_safe : Safe 9 4 s4_368 := by
  apply safe_succ 8 4 s4_368 [s5_68, s5_300] (by decide) s4_368_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_68_safe
  · subst z; exact s5_300_safe
def s4_369 : State := ⟨12, 8, 66, 210, 1645504557321206042177270268038248049062735139514556029465596182, 1, 0, 1⟩
theorem s4_369_edges : next 4 s4_369 = [s5_70, s5_301] := by decide
theorem s4_369_safe : Safe 9 4 s4_369 := by
  apply safe_succ 8 4 s4_369 [s5_70, s5_301] (by decide) s4_369_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_70_safe
  · subst z; exact s5_301_safe
def s4_370 : State := ⟨12, 8, 66, 210, 1645529665728147588878024865997410256586863830663685524097667350, 1, 0, 1⟩
theorem s4_370_edges : next 4 s4_370 = [s5_72, s5_302] := by decide
theorem s4_370_safe : Safe 9 4 s4_370 := by
  apply safe_succ 8 4 s4_370 [s5_72, s5_302] (by decide) s4_370_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_72_safe
  · subst z; exact s5_302_safe
def s4_371 : State := ⟨12, 8, 66, 224, 26959946667150639796128516724690815958761767718812463828564153798934, 1, 0, 1⟩
theorem s4_371_edges : next 4 s4_371 = [s5_76, s5_312, s5_304, s5_307] := by decide
theorem s4_371_safe : Safe 9 4 s4_371 := by
  apply safe_succ 8 4 s4_371 [s5_76, s5_312, s5_304, s5_307] (by decide) s4_371_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_76_safe
  · subst z; exact s5_312_safe
  · subst z; exact s5_304_safe
  · subst z; exact s5_307_safe
def s4_372 : State := ⟨12, 8, 66, 224, 26959946673427741530053695851195702463765749302198536253372255768854, 1, 0, 1⟩
theorem s4_372_edges : next 4 s4_372 = [s5_78, s5_313, s5_306, s5_309] := by decide
theorem s4_372_safe : Safe 9 4 s4_372 := by
  apply safe_succ 8 4 s4_372 [s5_78, s5_313, s5_306, s5_309] (by decide) s4_372_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s5_78_safe
  · subst z; exact s5_313_safe
  · subst z; exact s5_306_safe
  · subst z; exact s5_309_safe
def s4_373 : State := ⟨12, 8, 67, 129, 1020847100762815390593038007110404739350, 1, 0, 1⟩
theorem s4_373_edges : next 4 s4_373 = [s5_82] := by decide
theorem s4_373_safe : Safe 9 4 s4_373 := by
  apply safe_succ 8 4 s4_373 [s5_82] (by decide) s4_373_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_82_safe
def s4_374 : State := ⟨12, 8, 67, 129, 1020847100762815390629931495257823842582, 1, 0, 1⟩
theorem s4_374_edges : next 4 s4_374 = [s5_84] := by decide
theorem s4_374_safe : Safe 9 4 s4_374 := by
  apply safe_succ 8 4 s4_374 [s5_84] (by decide) s4_374_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_84_safe
def s4_375 : State := ⟨12, 8, 67, 130, 1701411834604692317519787221973941162262, 1, 0, 1⟩
theorem s4_375_edges : next 4 s4_375 = [s5_86, s5_289, s5_293] := by decide
theorem s4_375_safe : Safe 9 4 s4_375 := by
  apply safe_succ 8 4 s4_375 [s5_86, s5_289, s5_293] (by decide) s4_375_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_86_safe
  · subst z; exact s5_289_safe
  · subst z; exact s5_293_safe
def s4_376 : State := ⟨12, 8, 67, 130, 1701411834604692317556680710121360265494, 1, 0, 1⟩
theorem s4_376_edges : next 4 s4_376 = [s5_88, s5_290, s5_294] := by decide
theorem s4_376_safe : Safe 9 4 s4_376 := by
  apply safe_succ 8 4 s4_376 [s5_88, s5_290, s5_294] (by decide) s4_376_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_88_safe
  · subst z; exact s5_290_safe
  · subst z; exact s5_294_safe
def s4_377 : State := ⟨12, 8, 67, 132, 5784800237655953879080282511155159699734, 1, 0, 1⟩
theorem s4_377_edges : next 4 s4_377 = [s5_90] := by decide
theorem s4_377_safe : Safe 9 4 s4_377 := by
  apply safe_succ 8 4 s4_377 [s5_90] (by decide) s4_377_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_90_safe
def s4_378 : State := ⟨12, 8, 67, 132, 5784800237655953879117175999302578802966, 1, 0, 1⟩
theorem s4_378_edges : next 4 s4_378 = [s5_92] := by decide
theorem s4_378_safe : Safe 9 4 s4_378 := by
  apply safe_succ 8 4 s4_378 [s5_92] (by decide) s4_378_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_92_safe
def s4_379 : State := ⟨12, 8, 67, 136, 87452568298681185110290188294779530449174, 1, 0, 1⟩
theorem s4_379_edges : next 4 s4_379 = [s5_96] := by decide
theorem s4_379_safe : Safe 9 4 s4_379 := by
  apply safe_succ 8 4 s4_379 [s5_96] (by decide) s4_379_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_96_safe
def s4_380 : State := ⟨12, 8, 67, 136, 87452568298681185110327081782926949552406, 1, 0, 1⟩
theorem s4_380_edges : next 4 s4_380 = [s5_98] := by decide
theorem s4_380_safe : Safe 9 4 s4_380 := by
  apply safe_succ 8 4 s4_380 [s5_98] (by decide) s4_380_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_98_safe
def s4_381 : State := ⟨12, 8, 67, 140, 1394136857275084884809648680832769462440214, 1, 0, 1⟩
theorem s4_381_edges : next 4 s4_381 = [s5_102] := by decide
theorem s4_381_safe : Safe 9 4 s4_381 := by
  apply safe_succ 8 4 s4_381 [s5_102] (by decide) s4_381_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_102_safe
def s4_382 : State := ⟨12, 8, 67, 140, 1394136857275084884809685574320916881543446, 1, 0, 1⟩
theorem s4_382_edges : next 4 s4_382 = [s5_104] := by decide
theorem s4_382_safe : Safe 9 4 s4_382 := by
  apply safe_succ 8 4 s4_382 [s5_104] (by decide) s4_382_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_104_safe
def s4_383 : State := ⟨12, 8, 67, 144, 22301085480897544079999384561440608374296854, 1, 0, 1⟩
theorem s4_383_edges : next 4 s4_383 = [s5_106, s5_291, s5_297] := by decide
theorem s4_383_safe : Safe 9 4 s4_383 := by
  apply safe_succ 8 4 s4_383 [s5_106, s5_291, s5_297] (by decide) s4_383_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_106_safe
  · subst z; exact s5_291_safe
  · subst z; exact s5_297_safe
def s4_384 : State := ⟨12, 8, 67, 144, 22301085480897544079999421454928755793400086, 1, 0, 1⟩
theorem s4_384_edges : next 4 s4_384 = [s5_108, s5_292, s5_298] := by decide
theorem s4_384_safe : Safe 9 4 s4_384 := by
  apply safe_succ 8 4 s4_384 [s5_108, s5_292, s5_298] (by decide) s4_384_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_108_safe
  · subst z; exact s5_292_safe
  · subst z; exact s5_298_safe
def s4_385 : State := ⟨12, 8, 67, 160, 1461501637671185285124623296382571811902800859414, 1, 0, 1⟩
theorem s4_385_edges : next 4 s4_385 = [s5_110, s5_295, s5_299] := by decide
theorem s4_385_safe : Safe 9 4 s4_385 := by
  apply safe_succ 8 4 s4_385 [s5_110, s5_295, s5_299] (by decide) s4_385_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_110_safe
  · subst z; exact s5_295_safe
  · subst z; exact s5_299_safe
def s4_386 : State := ⟨12, 8, 67, 160, 1461501637671185285124623296419465300050219962646, 1, 0, 1⟩
theorem s4_386_edges : next 4 s4_386 = [s5_112, s5_296, s5_300] := by decide
theorem s4_386_safe : Safe 9 4 s4_386 := by
  apply safe_succ 8 4 s4_386 [s5_112, s5_296, s5_300] (by decide) s4_386_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_112_safe
  · subst z; exact s5_296_safe
  · subst z; exact s5_300_safe
def s4_387 : State := ⟨12, 8, 67, 192, 6277101735386680764176071790128604879768644236710902829334, 1, 0, 1⟩
theorem s4_387_edges : next 4 s4_387 = [s5_114, s5_305] := by decide
theorem s4_387_safe : Safe 9 4 s4_387 := by
  apply safe_succ 8 4 s4_387 [s5_114, s5_305] (by decide) s4_387_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_114_safe
  · subst z; exact s5_305_safe
def s4_388 : State := ⟨12, 8, 67, 192, 6277101735386680764176071790128604879805537724858321932566, 1, 0, 1⟩
theorem s4_388_edges : next 4 s4_388 = [s5_116, s5_306] := by decide
theorem s4_388_safe : Safe 9 4 s4_388 := by
  apply safe_succ 8 4 s4_388 [s5_116, s5_306] (by decide) s4_388_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_116_safe
  · subst z; exact s5_306_safe
def s4_389 : State := ⟨12, 8, 67, 193, 12554203470773361528011861213336271295870999681174937342230, 1, 0, 1⟩
theorem s4_389_edges : next 4 s4_389 = [s5_118] := by decide
theorem s4_389_safe : Safe 9 4 s4_389 := by
  apply safe_succ 8 4 s4_389 [s5_118] (by decide) s4_389_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_118_safe
def s4_390 : State := ⟨12, 8, 67, 194, 25108406941546723055683440059751604128112604058250425471254, 1, 0, 1⟩
theorem s4_390_edges : next 4 s4_390 = [s5_120, s5_302] := by decide
theorem s4_390_safe : Safe 9 4 s4_390 := by
  apply safe_succ 8 4 s4_390 [s5_120, s5_302] (by decide) s4_390_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_120_safe
  · subst z; exact s5_302_safe
def s4_391 : State := ⟨12, 8, 67, 195, 50216813883093446111026597752582269792485132347959144419606, 1, 0, 1⟩
theorem s4_391_edges : next 4 s4_391 = [s5_122] := by decide
theorem s4_391_safe : Safe 9 4 s4_391 := by
  apply safe_succ 8 4 s4_391 [s5_122] (by decide) s4_391_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_122_safe
def s4_392 : State := ⟨12, 8, 67, 195, 50216813883093446111026597752582269792522025836106563522838, 1, 0, 1⟩
theorem s4_392_edges : next 4 s4_392 = [s5_124] := by decide
theorem s4_392_safe : Safe 9 4 s4_392 := by
  apply safe_succ 8 4 s4_392 [s5_124] (by decide) s4_392_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_124_safe
def s4_393 : State := ⟨12, 8, 80, 210, 1645504557321206042154970883969185109676262126772975729368961302, 1, 0, 1⟩
theorem s4_393_edges : next 4 s4_393 = [s5_130] := by decide
theorem s4_393_safe : Safe 9 4 s4_393 := by
  apply safe_succ 8 4 s4_393 [s5_130] (by decide) s4_393_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_130_safe
def s4_394 : State := ⟨12, 8, 80, 210, 2056880696651507552693711818479055052168092239682940968133267734, 1, 0, 1⟩
theorem s4_394_edges : next 4 s4_394 = [s5_132] := by decide
theorem s4_394_safe : Safe 9 4 s4_394 := by
  apply safe_succ 8 4 s4_394 [s5_132] (by decide) s4_394_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_132_safe
def s4_395 : State := ⟨12, 8, 80, 224, 26959946667150639796128516724690815958761768927664496466898490298646, 1, 0, 1⟩
theorem s4_395_edges : next 4 s4_395 = [s5_136, s5_308] := by decide
theorem s4_395_safe : Safe 9 4 s4_395 := by
  apply safe_succ 8 4 s4_395 [s5_136, s5_308] (by decide) s4_395_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_136_safe
  · subst z; exact s5_308_safe
def s4_396 : State := ⟨12, 8, 80, 224, 26959946673427741530053695851195702463765750511050568891706592268566, 1, 0, 1⟩
theorem s4_396_edges : next 4 s4_396 = [s5_138, s5_310] := by decide
theorem s4_396_safe : Safe 9 4 s4_396 := by
  apply safe_succ 8 4 s4_396 [s5_138, s5_310] (by decide) s4_396_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_138_safe
  · subst z; exact s5_310_safe
def s4_397 : State := ⟨12, 8, 82, 129, 1020847100762820226185636001184846254358, 1, 0, 1⟩
theorem s4_397_edges : next 4 s4_397 = [s5_140] := by decide
theorem s4_397_safe : Safe 9 4 s4_397 := by
  apply safe_succ 8 4 s4_397 [s5_140] (by decide) s4_397_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_140_safe
def s4_398 : State := ⟨12, 8, 82, 129, 1020847100762821435037668639519182754070, 1, 0, 1⟩
theorem s4_398_edges : next 4 s4_398 = [s5_142] := by decide
theorem s4_398_safe : Safe 9 4 s4_398 := by
  apply safe_succ 8 4 s4_398 [s5_142] (by decide) s4_398_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_142_safe
def s4_399 : State := ⟨12, 8, 82, 130, 1701411834604697153112385216048382677270, 1, 0, 1⟩
theorem s4_399_edges : next 4 s4_399 = [s5_146] := by decide
theorem s4_399_safe : Safe 9 4 s4_399 := by
  apply safe_succ 8 4 s4_399 [s5_146] (by decide) s4_399_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_146_safe
def s4_400 : State := ⟨12, 8, 82, 130, 1701411834604698361964417854382719176982, 1, 0, 1⟩
theorem s4_400_edges : next 4 s4_400 = [s5_148] := by decide
theorem s4_400_safe : Safe 9 4 s4_400 := by
  apply safe_succ 8 4 s4_400 [s5_148] (by decide) s4_400_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_148_safe
def s4_401 : State := ⟨12, 8, 82, 132, 5784800237655958714672880505229601214742, 1, 0, 1⟩
theorem s4_401_edges : next 4 s4_401 = [s5_152] := by decide
theorem s4_401_safe : Safe 9 4 s4_401 := by
  apply safe_succ 8 4 s4_401 [s5_152] (by decide) s4_401_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_152_safe
def s4_402 : State := ⟨12, 8, 82, 132, 5784800237655959923524913143563937714454, 1, 0, 1⟩
theorem s4_402_edges : next 4 s4_402 = [s5_154] := by decide
theorem s4_402_safe : Safe 9 4 s4_402 := by
  apply safe_succ 8 4 s4_402 [s5_154] (by decide) s4_402_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_154_safe
def s4_403 : State := ⟨12, 8, 82, 136, 87452568298681189945882786288853971964182, 1, 0, 1⟩
theorem s4_403_edges : next 4 s4_403 = [s5_160] := by decide
theorem s4_403_safe : Safe 9 4 s4_403 := by
  apply safe_succ 8 4 s4_403 [s5_160] (by decide) s4_403_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_160_safe
def s4_404 : State := ⟨12, 8, 82, 136, 87452568298681191154734818927188308463894, 1, 0, 1⟩
theorem s4_404_edges : next 4 s4_404 = [s5_162] := by decide
theorem s4_404_safe : Safe 9 4 s4_404 := by
  apply safe_succ 8 4 s4_404 [s5_162] (by decide) s4_404_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_162_safe
def s4_405 : State := ⟨12, 8, 82, 140, 1394136857275084889645241278826843903955222, 1, 0, 1⟩
theorem s4_405_edges : next 4 s4_405 = [s5_168] := by decide
theorem s4_405_safe : Safe 9 4 s4_405 := by
  apply safe_succ 8 4 s4_405 [s5_168] (by decide) s4_405_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_168_safe
def s4_406 : State := ⟨12, 8, 82, 140, 1394136857275084890854093311465178240454934, 1, 0, 1⟩
theorem s4_406_edges : next 4 s4_406 = [s5_170] := by decide
theorem s4_406_safe : Safe 9 4 s4_406 := by
  apply safe_succ 8 4 s4_406 [s5_170] (by decide) s4_406_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_170_safe
def s4_407 : State := ⟨12, 8, 82, 144, 22301085480897544084834977159434682815811862, 1, 0, 1⟩
theorem s4_407_edges : next 4 s4_407 = [s5_172] := by decide
theorem s4_407_safe : Safe 9 4 s4_407 := by
  apply safe_succ 8 4 s4_407 [s5_172] (by decide) s4_407_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_172_safe
def s4_408 : State := ⟨12, 8, 82, 144, 22301085480897544086043829192073017152311574, 1, 0, 1⟩
theorem s4_408_edges : next 4 s4_408 = [s5_174] := by decide
theorem s4_408_safe : Safe 9 4 s4_408 := by
  apply safe_succ 8 4 s4_408 [s5_174] (by decide) s4_408_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_174_safe
def s4_409 : State := ⟨12, 8, 82, 160, 1461501637671185285124628131975169805977242374422, 1, 0, 1⟩
theorem s4_409_edges : next 4 s4_409 = [s5_178] := by decide
theorem s4_409_safe : Safe 9 4 s4_409 := by
  apply safe_succ 8 4 s4_409 [s5_178] (by decide) s4_409_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_178_safe
def s4_410 : State := ⟨12, 8, 82, 160, 1461501637671185285124629340827202444311578874134, 1, 0, 1⟩
theorem s4_410_edges : next 4 s4_410 = [s5_180] := by decide
theorem s4_410_safe : Safe 9 4 s4_410 := by
  apply safe_succ 8 4 s4_410 [s5_180] (by decide) s4_410_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_180_safe
def s4_411 : State := ⟨12, 8, 82, 192, 6277101735386680764176071790128609715361242230785344344342, 1, 0, 1⟩
theorem s4_411_edges : next 4 s4_411 = [s5_184, s5_309] := by decide
theorem s4_411_safe : Safe 9 4 s4_411 := by
  apply safe_succ 8 4 s4_411 [s5_184, s5_309] (by decide) s4_411_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_184_safe
  · subst z; exact s5_309_safe
def s4_412 : State := ⟨12, 8, 82, 192, 6277101735386680764176071790128610924213274869119680844054, 1, 0, 1⟩
theorem s4_412_edges : next 4 s4_412 = [s5_186, s5_310] := by decide
theorem s4_412_safe : Safe 9 4 s4_412 := by
  apply safe_succ 8 4 s4_412 [s5_186, s5_310] (by decide) s4_412_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_186_safe
  · subst z; exact s5_310_safe
def s4_413 : State := ⟨12, 8, 82, 194, 25108406941546723055683440059751608963668308564177447883030, 1, 0, 1⟩
theorem s4_413_edges : next 4 s4_413 = [s5_190] := by decide
theorem s4_413_safe : Safe 9 4 s4_413 := by
  apply safe_succ 8 4 s4_413 [s5_190] (by decide) s4_413_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_190_safe
def s4_414 : State := ⟨12, 8, 82, 208, 411376139330301510538742635921704547190192077327819621483483414, 1, 0, 1⟩
theorem s4_414_edges : next 4 s4_414 = [s5_193] := by decide
theorem s4_414_safe : Safe 9 4 s4_414 := by
  apply safe_succ 8 4 s4_414 [s5_193] (by decide) s4_414_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_193_safe
def s4_415 : State := ⟨12, 8, 82, 210, 1645504557321206042154969522839717425926035124520366184658440470, 1, 0, 1⟩
theorem s4_415_edges : next 4 s4_415 = [s5_196] := by decide
theorem s4_415_safe : Safe 9 4 s4_415 := by
  apply safe_succ 8 4 s4_415 [s5_196] (by decide) s4_415_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_196_safe
def s4_416 : State := ⟨12, 8, 82, 210, 1645504557321206042154969522839717425927243976553004518994940182, 1, 0, 1⟩
theorem s4_416_edges : next 4 s4_416 = [s5_198] := by decide
theorem s4_416_safe : Safe 9 4 s4_416 := by
  apply safe_succ 8 4 s4_416 [s5_198] (by decide) s4_416_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_198_safe
def s4_417 : State := ⟨12, 8, 96, 128, 340282387282576229647756113050568036630, 3, 2, 0⟩
theorem s4_417_edges : next 4 s4_417 = [s5_210, s5_311] := by decide
theorem s4_417_safe : Safe 9 4 s4_417 := by
  apply safe_succ 8 4 s4_417 [s5_210, s5_311] (by decide) s4_417_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_210_safe
  · subst z; exact s5_311_safe
def s4_418 : State := ⟨12, 8, 97, 224, 26959946667150639794667015087359913040795767373565186845394014900502, 1, 0, 1⟩
theorem s4_418_edges : next 4 s4_418 = [s5_214] := by decide
theorem s4_418_safe : Safe 9 4 s4_418 := by
  apply safe_succ 8 4 s4_418 [s5_214] (by decide) s4_418_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_214_safe
def s4_419 : State := ⟨12, 8, 104, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 1, 0, 1⟩
theorem s4_419_edges : next 4 s4_419 = [s5_219] := by decide
theorem s4_419_safe : Safe 9 4 s4_419 := by
  apply safe_succ 8 4 s4_419 [s5_219] (by decide) s4_419_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_219_safe
def s4_420 : State := ⟨12, 8, 112, 224, 26959946667150639794667015087359918232934169583364286700703256219926, 1, 0, 1⟩
theorem s4_420_edges : next 4 s4_420 = [s5_225] := by decide
theorem s4_420_safe : Safe 9 4 s4_420 := by
  apply safe_succ 8 4 s4_420 [s5_225] (by decide) s4_420_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_225_safe
def s4_421 : State := ⟨12, 8, 194, 146, 25108406941546812260025363649927924124617832152539007619350, 1, 0, 1⟩
theorem s4_421_edges : next 4 s4_421 = [s5_228] := by decide
theorem s4_421_safe : Safe 9 4 s4_421 := by
  apply safe_succ 8 4 s4_421 [s5_228] (by decide) s4_421_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_228_safe
def s4_422 : State := ⟨12, 8, 194, 162, 25108406947392729606368181200250097312609873637716713869590, 1, 0, 1⟩
theorem s4_422_edges : next 4 s4_422 = [s5_230] := by decide
theorem s4_422_safe : Safe 9 4 s4_422 := by
  apply safe_succ 8 4 s4_422 [s5_230] (by decide) s4_422_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_230_safe
def s4_423 : State := ⟨12, 8, 210, 130, 1645504557321206042154970883969185109676262126772975729368961302, 1, 0, 1⟩
theorem s4_423_edges : next 4 s4_423 = [s5_232] := by decide
theorem s4_423_safe : Safe 9 4 s4_423 := by
  apply safe_succ 8 4 s4_423 [s5_232] (by decide) s4_423_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_232_safe
def s4_424 : State := ⟨12, 8, 210, 130, 1645529665728147588878026227126877940340717610375138956332306710, 1, 0, 1⟩
theorem s4_424_edges : next 4 s4_424 = [s5_234] := by decide
theorem s4_424_safe : Safe 9 4 s4_424 := by
  apply safe_succ 8 4 s4_424 [s5_234] (by decide) s4_424_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_234_safe
def s4_425 : State := ⟨12, 8, 210, 144, 1645504557321206042177270268038248049062735139514556029465596182, 1, 0, 1⟩
theorem s4_425_edges : next 4 s4_425 = [s5_238] := by decide
theorem s4_425_safe : Safe 9 4 s4_425 := by
  apply safe_succ 8 4 s4_425 [s5_238] (by decide) s4_425_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_238_safe
def s4_426 : State := ⟨12, 8, 210, 144, 2056880696651507552716012563677585675308419032135974700464541974, 1, 0, 1⟩
theorem s4_426_edges : next 4 s4_426 = [s5_240] := by decide
theorem s4_426_safe : Safe 9 4 s4_426 := by
  apply safe_succ 8 4 s4_426 [s5_240] (by decide) s4_426_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_240_safe
def s4_427 : State := ⟨12, 8, 210, 146, 1645504557321206042244173864763307602241196074043954546218176790, 1, 0, 1⟩
theorem s4_427_edges : next 4 s4_427 = [s5_244] := by decide
theorem s4_427_safe : Safe 9 4 s4_427 := by
  apply safe_succ 8 4 s4_427 [s5_244] (by decide) s4_427_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_244_safe
def s4_428 : State := ⟨12, 8, 210, 146, 1645504557321206042266473248832370541628877938818173180651311382, 1, 0, 1⟩
theorem s4_428_edges : next 4 s4_428 = [s5_246] := by decide
theorem s4_428_safe : Safe 9 4 s4_428 := by
  apply safe_succ 8 4 s4_428 [s5_246] (by decide) s4_428_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_246_safe
def s4_429 : State := ⟨12, 104, 96, 224, 26959946667150639794667015087359913060919720652188328594154178285846, 3, 0, 1⟩
theorem s4_429_edges : next 4 s4_429 = [s5_311, s5_314, s5_315] := by decide
theorem s4_429_safe : Safe 9 4 s4_429 := by
  apply safe_succ 8 4 s4_429 [s5_311, s5_314, s5_315] (by decide) s4_429_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s5_311_safe
  · subst z; exact s5_314_safe
  · subst z; exact s5_315_safe
def s4_430 : State := ⟨68, 8, 64, 214, 26328072917139296674568711603123565176982234353695557675800133910, 1, 0, 1⟩
theorem s4_430_edges : next 4 s4_430 = [s5_38] := by decide
theorem s4_430_safe : Safe 9 4 s4_430 := by
  apply safe_succ 8 4 s4_430 [s5_38] (by decide) s4_430_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_38_safe
def s4_431 : State := ⟨68, 8, 64, 214, 26328072917139296674591010987192628116369916218469776310233268502, 1, 0, 1⟩
theorem s4_431_edges : next 4 s4_431 = [s5_39] := by decide
theorem s4_431_safe : Safe 9 4 s4_431 := by
  apply safe_succ 8 4 s4_431 [s5_39] (by decide) s4_431_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_39_safe
def s4_432 : State := ⟨68, 8, 96, 128, 340282387282576229942904018229920858390, 3, 2, 0⟩
theorem s4_432_edges : next 4 s4_432 = [s5_316] := by decide
theorem s4_432_safe : Safe 9 4 s4_432 := by
  apply safe_succ 8 4 s4_432 [s5_316] (by decide) s4_432_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_316_safe
def s4_433 : State := ⟨68, 8, 104, 224, 26959946667150639794667015087359913060919720652483476499333531107606, 1, 0, 1⟩
theorem s4_433_edges : next 4 s4_433 = [] := by decide
theorem s4_433_safe : Safe 9 4 s4_433 := by
  apply safe_succ 8 4 s4_433 [] (by decide) s4_433_edges
  simp
def s4_434 : State := ⟨68, 104, 96, 224, 26959946667150639794667015087359913060919720652483476499333531107606, 3, 0, 1⟩
theorem s4_434_edges : next 4 s4_434 = [s5_316] := by decide
theorem s4_434_safe : Safe 9 4 s4_434 := by
  apply safe_succ 8 4 s4_434 [s5_316] (by decide) s4_434_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_316_safe
def s4_435 : State := ⟨86, 8, 82, 129, 1020847100762897597438091337452027445526, 1, 0, 1⟩
theorem s4_435_edges : next 4 s4_435 = [s5_144] := by decide
theorem s4_435_safe : Safe 9 4 s4_435 := by
  apply safe_succ 8 4 s4_435 [s5_144] (by decide) s4_435_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_144_safe
def s4_436 : State := ⟨86, 8, 82, 129, 1020847100762898806290123975786363945238, 1, 0, 1⟩
theorem s4_436_edges : next 4 s4_436 = [s5_145] := by decide
theorem s4_436_safe : Safe 9 4 s4_436 := by
  apply safe_succ 8 4 s4_436 [s5_145] (by decide) s4_436_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_145_safe
def s4_437 : State := ⟨86, 8, 82, 130, 1701411834604774524364840552315563868438, 1, 0, 1⟩
theorem s4_437_edges : next 4 s4_437 = [s5_150] := by decide
theorem s4_437_safe : Safe 9 4 s4_437 := by
  apply safe_succ 8 4 s4_437 [s5_150] (by decide) s4_437_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_150_safe
def s4_438 : State := ⟨86, 8, 82, 130, 1701411834604775733216873190649900368150, 1, 0, 1⟩
theorem s4_438_edges : next 4 s4_438 = [s5_151] := by decide
theorem s4_438_safe : Safe 9 4 s4_438 := by
  apply safe_succ 8 4 s4_438 [s5_151] (by decide) s4_438_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_151_safe
def s4_439 : State := ⟨86, 8, 82, 132, 5784800237656036085925335841496782405910, 1, 0, 1⟩
theorem s4_439_edges : next 4 s4_439 = [s5_156] := by decide
theorem s4_439_safe : Safe 9 4 s4_439 := by
  apply safe_succ 8 4 s4_439 [s5_156] (by decide) s4_439_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_156_safe
def s4_440 : State := ⟨86, 8, 82, 132, 5784800237656037294777368479831118905622, 1, 0, 1⟩
theorem s4_440_edges : next 4 s4_440 = [s5_157] := by decide
theorem s4_440_safe : Safe 9 4 s4_440 := by
  apply safe_succ 8 4 s4_440 [s5_157] (by decide) s4_440_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_157_safe
def s4_441 : State := ⟨86, 8, 82, 136, 87452568298681267317135241625121153155350, 1, 0, 1⟩
theorem s4_441_edges : next 4 s4_441 = [s5_164] := by decide
theorem s4_441_safe : Safe 9 4 s4_441 := by
  apply safe_succ 8 4 s4_441 [s5_164] (by decide) s4_441_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_164_safe
def s4_442 : State := ⟨86, 8, 82, 136, 87452568298681268525987274263455489655062, 1, 0, 1⟩
theorem s4_442_edges : next 4 s4_442 = [s5_165] := by decide
theorem s4_442_safe : Safe 9 4 s4_442 := by
  apply safe_succ 8 4 s4_442 [s5_165] (by decide) s4_442_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_165_safe
def s4_443 : State := ⟨86, 8, 82, 144, 22301085480897544162206229614770949997003030, 1, 0, 1⟩
theorem s4_443_edges : next 4 s4_443 = [s5_176] := by decide
theorem s4_443_safe : Safe 9 4 s4_443 := by
  apply safe_succ 8 4 s4_443 [s5_176] (by decide) s4_443_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_176_safe
def s4_444 : State := ⟨86, 8, 82, 144, 22301085480897544163415081647409284333502742, 1, 0, 1⟩
theorem s4_444_edges : next 4 s4_444 = [s5_177] := by decide
theorem s4_444_safe : Safe 9 4 s4_444 := by
  apply safe_succ 8 4 s4_444 [s5_177] (by decide) s4_444_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_177_safe
def s4_445 : State := ⟨86, 8, 82, 160, 1461501637671185285124705503227625142244423565590, 1, 0, 1⟩
theorem s4_445_edges : next 4 s4_445 = [s5_182] := by decide
theorem s4_445_safe : Safe 9 4 s4_445 := by
  apply safe_succ 8 4 s4_445 [s5_182] (by decide) s4_445_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_182_safe
def s4_446 : State := ⟨86, 8, 82, 160, 1461501637671185285124706712079657780578760065302, 1, 0, 1⟩
theorem s4_446_edges : next 4 s4_446 = [s5_183] := by decide
theorem s4_446_safe : Safe 9 4 s4_446 := by
  apply safe_succ 8 4 s4_446 [s5_183] (by decide) s4_446_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_183_safe
def s4_447 : State := ⟨86, 8, 82, 192, 6277101735386680764176071790128687086613697567052525535510, 1, 0, 1⟩
theorem s4_447_edges : next 4 s4_447 = [s5_188, s5_319] := by decide
theorem s4_447_safe : Safe 9 4 s4_447 := by
  apply safe_succ 8 4 s4_447 [s5_188, s5_319] (by decide) s4_447_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_188_safe
  · subst z; exact s5_319_safe
def s4_448 : State := ⟨86, 8, 82, 192, 6277101735386680764176071790128688295465730205386862035222, 1, 0, 1⟩
theorem s4_448_edges : next 4 s4_448 = [s5_189, s5_320] := by decide
theorem s4_448_safe : Safe 9 4 s4_448 := by
  apply safe_succ 8 4 s4_448 [s5_189, s5_320] (by decide) s4_448_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_189_safe
  · subst z; exact s5_320_safe
def s4_449 : State := ⟨86, 8, 82, 194, 25108406941546723055683440059751686334920763900444629074198, 1, 0, 1⟩
theorem s4_449_edges : next 4 s4_449 = [s5_192] := by decide
theorem s4_449_safe : Safe 9 4 s4_449 := by
  apply safe_succ 8 4 s4_449 [s5_192] (by decide) s4_449_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_192_safe
def s4_450 : State := ⟨86, 8, 82, 208, 411376139330301510538742635921704547267563329783155888664674582, 1, 0, 1⟩
theorem s4_450_edges : next 4 s4_450 = [s5_195] := by decide
theorem s4_450_safe : Safe 9 4 s4_450 := by
  apply safe_succ 8 4 s4_450 [s5_195] (by decide) s4_450_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_195_safe
def s4_451 : State := ⟨86, 8, 82, 210, 1645504557321206042154969522839717426003406376975702451839631638, 1, 0, 1⟩
theorem s4_451_edges : next 4 s4_451 = [s5_200] := by decide
theorem s4_451_safe : Safe 9 4 s4_451 := by
  apply safe_succ 8 4 s4_451 [s5_200] (by decide) s4_451_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_200_safe
def s4_452 : State := ⟨86, 8, 82, 210, 1645504557321206042154969522839717426004615229008340786176131350, 1, 0, 1⟩
theorem s4_452_edges : next 4 s4_452 = [s5_201] := by decide
theorem s4_452_safe : Safe 9 4 s4_452 := by
  apply safe_succ 8 4 s4_452 [s5_201] (by decide) s4_452_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_201_safe
def s4_453 : State := ⟨86, 8, 82, 214, 26328072917139296674479507261199975000744444361479400402068766998, 1, 0, 1⟩
theorem s4_453_edges : next 4 s4_453 = [s5_204] := by decide
theorem s4_453_safe : Safe 9 4 s4_453 := by
  apply safe_succ 8 4 s4_453 [s5_204] (by decide) s4_453_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_204_safe
def s4_454 : State := ⟨86, 8, 82, 214, 26328072917139296674479507261199975000745653213512038736405266710, 1, 0, 1⟩
theorem s4_454_edges : next 4 s4_454 = [s5_205] := by decide
theorem s4_454_safe : Safe 9 4 s4_454 := by
  apply safe_succ 8 4 s4_454 [s5_205] (by decide) s4_454_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_205_safe
def s4_455 : State := ⟨100, 8, 96, 128, 340282388550226829875985514547271237910, 3, 2, 0⟩
theorem s4_455_edges : next 4 s4_455 = [s5_212, s5_321] := by decide
theorem s4_455_safe : Safe 9 4 s4_455 := by
  apply safe_succ 8 4 s4_455 [s5_212, s5_321] (by decide) s4_455_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_212_safe
  · subst z; exact s5_321_safe
def s4_456 : State := ⟨100, 8, 104, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 1, 0, 1⟩
theorem s4_456_edges : next 4 s4_456 = [] := by decide
theorem s4_456_safe : Safe 9 4 s4_456 := by
  apply safe_succ 8 4 s4_456 [] (by decide) s4_456_edges
  simp
def s4_457 : State := ⟨100, 104, 96, 224, 26959946667150639794667015087359913062187371252416557995650881487126, 3, 0, 1⟩
theorem s4_457_edges : next 4 s4_457 = [s5_284, s5_321] := by decide
theorem s4_457_safe : Safe 9 4 s4_457 := by
  apply safe_succ 8 4 s4_457 [s5_284, s5_321] (by decide) s4_457_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_284_safe
  · subst z; exact s5_321_safe
def s4_458 : State := ⟨108, 8, 96, 128, 340282711801129888074482896206588608790, 3, 2, 0⟩
theorem s4_458_edges : next 4 s4_458 = [s5_322] := by decide
theorem s4_458_safe : Safe 9 4 s4_458 := by
  apply safe_succ 8 4 s4_458 [s5_322] (by decide) s4_458_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_322_safe
def s4_459 : State := ⟨108, 8, 104, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 1, 0, 1⟩
theorem s4_459_edges : next 4 s4_459 = [s5_223] := by decide
theorem s4_459_safe : Safe 9 4 s4_459 := by
  apply safe_succ 8 4 s4_459 [s5_223] (by decide) s4_459_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_223_safe
def s4_460 : State := ⟨108, 104, 96, 224, 26959946667150639794667015087359913385438274310615055377310198858006, 3, 0, 1⟩
theorem s4_460_edges : next 4 s4_460 = [s5_285, s5_322] := by decide
theorem s4_460_safe : Safe 9 4 s4_460 := by
  apply safe_succ 8 4 s4_460 [s5_285, s5_322] (by decide) s4_460_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_285_safe
  · subst z; exact s5_322_safe
def s4_461 : State := ⟨140, 8, 67, 136, 1481249143206845131456272580335302124568854, 1, 0, 1⟩
theorem s4_461_edges : next 4 s4_461 = [s5_100] := by decide
theorem s4_461_safe : Safe 9 4 s4_461 := by
  apply safe_succ 8 4 s4_461 [s5_100] (by decide) s4_461_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_100_safe
def s4_462 : State := ⟨140, 8, 67, 136, 1481249143206845131456309473823449543672086, 1, 0, 1⟩
theorem s4_462_edges : next 4 s4_462 = [s5_101] := by decide
theorem s4_462_safe : Safe 9 4 s4_462 := by
  apply safe_succ 8 4 s4_462 [s5_101] (by decide) s4_462_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_101_safe
def s4_463 : State := ⟨140, 8, 82, 136, 1481249143206845136291865178329376566083862, 1, 0, 1⟩
theorem s4_463_edges : next 4 s4_463 = [s5_166] := by decide
theorem s4_463_safe : Safe 9 4 s4_463 := by
  apply safe_succ 8 4 s4_463 [s5_166] (by decide) s4_463_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_166_safe
def s4_464 : State := ⟨140, 8, 82, 136, 1481249143206845137500717210967710902583574, 1, 0, 1⟩
theorem s4_464_edges : next 4 s4_464 = [s5_167] := by decide
theorem s4_464_safe : Safe 9 4 s4_464 := by
  apply safe_succ 8 4 s4_464 [s5_167] (by decide) s4_464_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_167_safe
def s4_465 : State := ⟨150, 8, 214, 146, 26328072917139296675995959295829525058040520027997147632830054678, 1, 0, 1⟩
theorem s4_465_edges : next 4 s4_465 = [s5_250] := by decide
theorem s4_465_safe : Safe 9 4 s4_465 := by
  apply safe_succ 8 4 s4_465 [s5_250] (by decide) s4_465_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_250_safe
def s4_466 : State := ⟨150, 8, 214, 146, 26328072917139296676018258679898587997428201892771366267263189270, 1, 0, 1⟩
theorem s4_466_edges : next 4 s4_466 = [s5_251] := by decide
theorem s4_466_safe : Safe 9 4 s4_466 := by
  apply safe_succ 8 4 s4_466 [s5_251] (by decide) s4_466_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_251_safe
def s4_467 : State := ⟨214, 8, 64, 146, 26328072917139296674568711603123565176982234353695557675800133910, 1, 0, 1⟩
theorem s4_467_edges : next 4 s4_467 = [] := by decide
theorem s4_467_safe : Safe 9 4 s4_467 := by
  apply safe_succ 8 4 s4_467 [] (by decide) s4_467_edges
  simp
def s4_468 : State := ⟨214, 8, 64, 146, 26328072917139296674591010987192628116369916218469776310233268502, 1, 0, 1⟩
theorem s4_468_edges : next 4 s4_468 = [] := by decide
theorem s4_468_safe : Safe 9 4 s4_468 := by
  apply safe_succ 8 4 s4_468 [] (by decide) s4_468_edges
  simp
def s4_469 : State := ⟨214, 8, 64, 146, 26328072917139296675995959295829525058040520027997147632830054678, 1, 0, 1⟩
theorem s4_469_edges : next 4 s4_469 = [] := by decide
theorem s4_469_safe : Safe 9 4 s4_469 := by
  apply safe_succ 8 4 s4_469 [] (by decide) s4_469_edges
  simp
def s4_470 : State := ⟨214, 8, 64, 146, 26328072917139296676018258679898587997428201892771366267263189270, 1, 0, 1⟩
theorem s4_470_edges : next 4 s4_470 = [] := by decide
theorem s4_470_safe : Safe 9 4 s4_470 := by
  apply safe_succ 8 4 s4_470 [] (by decide) s4_470_edges
  simp
def s4_471 : State := ⟨214, 8, 64, 210, 27973577474460502716723680785680915681964969924181232359795917078, 1, 0, 1⟩
theorem s4_471_edges : next 4 s4_471 = [s5_32] := by decide
theorem s4_471_safe : Safe 9 4 s4_471 := by
  apply safe_succ 8 4 s4_471 [s5_32] (by decide) s4_471_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_32_safe
def s4_472 : State := ⟨214, 8, 64, 210, 27973577474460502716745980169749978621352651788955450994229051670, 1, 0, 1⟩
theorem s4_472_edges : next 4 s4_472 = [s5_33] := by decide
theorem s4_472_safe : Safe 9 4 s4_472 := by
  apply safe_succ 8 4 s4_472 [s5_33] (by decide) s4_472_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_33_safe
def s4_473 : State := ⟨214, 8, 64, 210, 27973602582867444263357533148044486020064491460512416769910046998, 1, 0, 1⟩
theorem s4_473_edges : next 4 s4_473 = [s5_34] := by decide
theorem s4_473_safe : Safe 9 4 s4_473 := by
  apply safe_succ 8 4 s4_473 [s5_34] (by decide) s4_473_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_34_safe
def s4_474 : State := ⟨214, 8, 64, 210, 27973608859969179650038295622704441543977053709369431506871714070, 1, 0, 1⟩
theorem s4_474_edges : next 4 s4_474 = [s5_35] := by decide
theorem s4_474_safe : Safe 9 4 s4_474 := by
  apply safe_succ 8 4 s4_474 [s5_35] (by decide) s4_474_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_35_safe
def s4_475 : State := ⟨214, 8, 64, 210, 28384953613790804227195519484595193755032192882273252514042282262, 1, 0, 1⟩
theorem s4_475_edges : next 4 s4_475 = [s5_36] := by decide
theorem s4_475_safe : Safe 9 4 s4_475 := by
  apply safe_succ 8 4 s4_475 [s5_36] (by decide) s4_475_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_36_safe
def s4_476 : State := ⟨214, 8, 64, 210, 28384959890892539613853982575186086339557073266356048616570814742, 1, 0, 1⟩
theorem s4_476_edges : next 4 s4_476 = [s5_37] := by decide
theorem s4_476_safe : Safe 9 4 s4_476 := by
  apply safe_succ 8 4 s4_476 [s5_37] (by decide) s4_476_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_37_safe
def s4_477 : State := ⟨214, 8, 66, 210, 27973577474460502716656777188955856128786508989651833843043336470, 1, 0, 1⟩
theorem s4_477_edges : next 4 s4_477 = [s5_74, s5_323] := by decide
theorem s4_477_safe : Safe 9 4 s4_477 := by
  apply safe_succ 8 4 s4_477 [s5_74, s5_323] (by decide) s4_477_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_74_safe
  · subst z; exact s5_323_safe
def s4_478 : State := ⟨214, 8, 66, 210, 27973602582867444263357531786915018336310637680800963337675407638, 1, 0, 1⟩
theorem s4_478_edges : next 4 s4_478 = [s5_75, s5_324] := by decide
theorem s4_478_safe : Safe 9 4 s4_478 := by
  apply safe_succ 8 4 s4_478 [s5_75, s5_324] (by decide) s4_478_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_75_safe
  · subst z; exact s5_324_safe
def s4_479 : State := ⟨214, 8, 80, 210, 27973577474460502716634477804886793189400035976910253542946701590, 1, 0, 1⟩
theorem s4_479_edges : next 4 s4_479 = [s5_134] := by decide
theorem s4_479_safe : Safe 9 4 s4_479 := by
  apply safe_succ 8 4 s4_479 [s5_134] (by decide) s4_479_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_134_safe
def s4_480 : State := ⟨214, 8, 80, 210, 28384953613790804227173218739396663131891866089820218781711008022, 1, 0, 1⟩
theorem s4_480_edges : next 4 s4_480 = [s5_135] := by decide
theorem s4_480_safe : Safe 9 4 s4_480 := by
  apply safe_succ 8 4 s4_480 [s5_135] (by decide) s4_480_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_135_safe
def s4_481 : State := ⟨214, 8, 82, 210, 27973577474460502716634476443757325505649808974657643998236180758, 1, 0, 1⟩
theorem s4_481_edges : next 4 s4_481 = [s5_202] := by decide
theorem s4_481_safe : Safe 9 4 s4_481 := by
  apply safe_succ 8 4 s4_481 [s5_202] (by decide) s4_481_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_202_safe
def s4_482 : State := ⟨214, 8, 82, 210, 27973577474460502716634476443757325505651017826690282332572680470, 1, 0, 1⟩
theorem s4_482_edges : next 4 s4_482 = [s5_203] := by decide
theorem s4_482_safe : Safe 9 4 s4_482 := by
  apply safe_succ 8 4 s4_482 [s5_203] (by decide) s4_482_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_203_safe
def s4_483 : State := ⟨214, 8, 210, 130, 27973577474460502716634477804886793189400035976910253542946701590, 1, 0, 1⟩
theorem s4_483_edges : next 4 s4_483 = [s5_236] := by decide
theorem s4_483_safe : Safe 9 4 s4_483 := by
  apply safe_succ 8 4 s4_483 [s5_236] (by decide) s4_483_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_236_safe
def s4_484 : State := ⟨214, 8, 210, 130, 27973602582867444263357533148044486020064491460512416769910046998, 1, 0, 1⟩
theorem s4_484_edges : next 4 s4_484 = [s5_237] := by decide
theorem s4_484_safe : Safe 9 4 s4_484 := by
  apply safe_succ 8 4 s4_484 [s5_237] (by decide) s4_484_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_237_safe
def s4_485 : State := ⟨214, 8, 210, 144, 27973577474460502716656777188955856128786508989651833843043336470, 1, 0, 1⟩
theorem s4_485_edges : next 4 s4_485 = [s5_242] := by decide
theorem s4_485_safe : Safe 9 4 s4_485 := by
  apply safe_succ 8 4 s4_485 [s5_242] (by decide) s4_485_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_242_safe
def s4_486 : State := ⟨214, 8, 210, 144, 28384953613790804227195519484595193755032192882273252514042282262, 1, 0, 1⟩
theorem s4_486_edges : next 4 s4_486 = [s5_243] := by decide
theorem s4_486_safe : Safe 9 4 s4_486 := by
  apply safe_succ 8 4 s4_486 [s5_243] (by decide) s4_486_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_243_safe
def s4_487 : State := ⟨214, 8, 210, 146, 27973577474460502716723680785680915681964969924181232359795917078, 1, 0, 1⟩
theorem s4_487_edges : next 4 s4_487 = [s5_248] := by decide
theorem s4_487_safe : Safe 9 4 s4_487 := by
  apply safe_succ 8 4 s4_487 [s5_248] (by decide) s4_487_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_248_safe
def s4_488 : State := ⟨214, 8, 210, 146, 27973577474460502716745980169749978621352651788955450994229051670, 1, 0, 1⟩
theorem s4_488_edges : next 4 s4_488 = [s5_249] := by decide
theorem s4_488_safe : Safe 9 4 s4_488 := by
  apply safe_succ 8 4 s4_488 [s5_249] (by decide) s4_488_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_249_safe
def s4_489 : State := ⟨228, 8, 65, 224, 458319093341560876510800758117004906736956078479424730038074498679062, 1, 0, 1⟩
theorem s4_489_edges : next 4 s4_489 = [s5_56, s5_325] := by decide
theorem s4_489_safe : Safe 9 4 s4_489 := by
  apply safe_succ 8 4 s4_489 [s5_56, s5_325] (by decide) s4_489_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_56_safe
  · subst z; exact s5_325_safe
def s4_490 : State := ⟨228, 8, 65, 224, 458319093347837978244725937243509793241960060062810802462882600648982, 1, 0, 1⟩
theorem s4_490_edges : next 4 s4_490 = [s5_57, s5_327] := by decide
theorem s4_490_safe : Safe 9 4 s4_490 := by
  apply safe_succ 8 4 s4_490 [s5_57, s5_327] (by decide) s4_490_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_57_safe
  · subst z; exact s5_327_safe
def s4_491 : State := ⟨228, 8, 66, 224, 458319093341560876510800758117004906736956078479461623526221917782294, 1, 0, 1⟩
theorem s4_491_edges : next 4 s4_491 = [s5_80, s5_326] := by decide
theorem s4_491_safe : Safe 9 4 s4_491 := by
  apply safe_succ 8 4 s4_491 [s5_80, s5_326] (by decide) s4_491_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_80_safe
  · subst z; exact s5_326_safe
def s4_492 : State := ⟨228, 8, 66, 224, 458319093347837978244725937243509793241960060062847695951030019752214, 1, 0, 1⟩
theorem s4_492_edges : next 4 s4_492 = [s5_81, s5_328] := by decide
theorem s4_492_safe : Safe 9 4 s4_492 := by
  apply safe_succ 8 4 s4_492 [s5_81, s5_328] (by decide) s4_492_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_81_safe
  · subst z; exact s5_328_safe
def s4_493 : State := ⟨228, 8, 104, 224, 458319093341560876509339256479674003839114031412837488291811942269206, 1, 0, 1⟩
theorem s4_493_edges : next 4 s4_493 = [s5_224] := by decide
theorem s4_493_safe : Safe 9 4 s4_493 := by
  apply safe_succ 8 4 s4_493 [s5_224] (by decide) s4_493_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s5_224_safe
def s4_494 : State := ⟨228, 104, 96, 224, 458319093341560876509339256479674003839114031412837488291811942269206, 3, 0, 1⟩
theorem s4_494_edges : next 4 s4_494 = [s5_286, s5_329] := by decide
theorem s4_494_safe : Safe 9 4 s4_494 := by
  apply safe_succ 8 4 s4_494 [s5_286, s5_329] (by decide) s4_494_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s5_286_safe
  · subst z; exact s5_329_safe
def s3_0 : State := ⟨4, 8, 64, 129, 1020847100762815390408570566373309219606, 2, 2, 1⟩
theorem s3_0_edges : next 3 s3_0 = [] := by decide
theorem s3_0_safe : Safe 10 3 s3_0 := by
  apply safe_succ 9 3 s3_0 [] (by decide) s3_0_edges
  simp
def s3_1 : State := ⟨4, 8, 64, 129, 1020847100762815390408570566373309223190, 1, 1, 1⟩
theorem s3_1_edges : next 3 s3_1 = [s4_210, s4_67, s4_87, s4_139, s4_36, s4_0, s4_12] := by decide
theorem s3_1_safe : Safe 10 3 s3_1 := by
  apply safe_succ 9 3 s3_1 [s4_210, s4_67, s4_87, s4_139, s4_36, s4_0, s4_12] (by decide) s3_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_210_safe
  · subst z; exact s4_67_safe
  · subst z; exact s4_87_safe
  · subst z; exact s4_139_safe
  · subst z; exact s4_36_safe
  · subst z; exact s4_0_safe
  · subst z; exact s4_12_safe
def s3_2 : State := ⟨4, 8, 64, 129, 1020847100762815390408570566373309223190, 2, 2, 1⟩
theorem s3_2_edges : next 3 s3_2 = [s4_211, s4_68, s4_88, s4_140, s4_37, s4_1, s4_13] := by decide
theorem s3_2_safe : Safe 10 3 s3_2 := by
  apply safe_succ 9 3 s3_2 [s4_211, s4_68, s4_88, s4_140, s4_37, s4_1, s4_13] (by decide) s3_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_211_safe
  · subst z; exact s4_68_safe
  · subst z; exact s4_88_safe
  · subst z; exact s4_140_safe
  · subst z; exact s4_37_safe
  · subst z; exact s4_1_safe
  · subst z; exact s4_13_safe
def s3_3 : State := ⟨4, 8, 64, 129, 1020847100762815390703718471552662044950, 1, 1, 1⟩
theorem s3_3_edges : next 3 s3_3 = [] := by decide
theorem s3_3_safe : Safe 10 3 s3_3 := by
  apply safe_succ 9 3 s3_3 [] (by decide) s3_3_edges
  simp
def s3_4 : State := ⟨4, 8, 64, 129, 175245418964283308683656369571438633484566, 2, 2, 1⟩
theorem s3_4_edges : next 3 s3_4 = [] := by decide
theorem s3_4_safe : Safe 10 3 s3_4 := by
  apply safe_succ 9 3 s3_4 [] (by decide) s3_4_edges
  simp
def s3_5 : State := ⟨4, 8, 64, 130, 1701411834604692317335319781236845642518, 2, 2, 1⟩
theorem s3_5_edges : next 3 s3_5 = [s4_16] := by decide
theorem s3_5_safe : Safe 10 3 s3_5 := by
  apply safe_succ 9 3 s3_5 [s4_16] (by decide) s3_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_16_safe
def s3_6 : State := ⟨4, 8, 64, 130, 1701411834604692317335319781236845646102, 1, 1, 1⟩
theorem s3_6_edges : next 3 s3_6 = [s4_212, s4_69, s4_89, s4_141, s4_40, s4_2, s4_4, s4_17] := by decide
theorem s3_6_safe : Safe 10 3 s3_6 := by
  apply safe_succ 9 3 s3_6 [s4_212, s4_69, s4_89, s4_141, s4_40, s4_2, s4_4, s4_17] (by decide) s3_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_212_safe
  · subst z; exact s4_69_safe
  · subst z; exact s4_89_safe
  · subst z; exact s4_141_safe
  · subst z; exact s4_40_safe
  · subst z; exact s4_2_safe
  · subst z; exact s4_4_safe
  · subst z; exact s4_17_safe
def s3_7 : State := ⟨4, 8, 64, 130, 1701411834604692317335319781236845646102, 2, 2, 1⟩
theorem s3_7_edges : next 3 s3_7 = [s4_213, s4_70, s4_90, s4_142, s4_41, s4_3, s4_5, s4_18] := by decide
theorem s3_7_safe : Safe 10 3 s3_7 := by
  apply safe_succ 9 3 s3_7 [s4_213, s4_70, s4_90, s4_142, s4_41, s4_3, s4_5, s4_18] (by decide) s3_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_213_safe
  · subst z; exact s4_70_safe
  · subst z; exact s4_90_safe
  · subst z; exact s4_142_safe
  · subst z; exact s4_41_safe
  · subst z; exact s4_3_safe
  · subst z; exact s4_5_safe
  · subst z; exact s4_18_safe
def s3_8 : State := ⟨4, 8, 64, 130, 1701411834604692317630467686416198467862, 1, 1, 1⟩
theorem s3_8_edges : next 3 s3_8 = [s4_6] := by decide
theorem s3_8_safe : Safe 10 3 s3_8 := by
  apply safe_succ 9 3 s3_8 [s4_6] (by decide) s3_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_6_safe
def s3_9 : State := ⟨4, 8, 64, 132, 5784800237655953878895815070418064179990, 2, 2, 1⟩
theorem s3_9_edges : next 3 s3_9 = [] := by decide
theorem s3_9_safe : Safe 10 3 s3_9 := by
  apply safe_succ 9 3 s3_9 [] (by decide) s3_9_edges
  simp
def s3_10 : State := ⟨4, 8, 64, 132, 5784800237655953878895815070418064183574, 1, 1, 1⟩
theorem s3_10_edges : next 3 s3_10 = [s4_71, s4_91, s4_143] := by decide
theorem s3_10_safe : Safe 10 3 s3_10 := by
  apply safe_succ 9 3 s3_10 [s4_71, s4_91, s4_143] (by decide) s3_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_71_safe
  · subst z; exact s4_91_safe
  · subst z; exact s4_143_safe
def s3_11 : State := ⟨4, 8, 64, 132, 5784800237655953878895815070418064183574, 2, 2, 1⟩
theorem s3_11_edges : next 3 s3_11 = [s4_72, s4_92, s4_144] := by decide
theorem s3_11_safe : Safe 10 3 s3_11 := by
  apply safe_succ 9 3 s3_11 [s4_72, s4_92, s4_144] (by decide) s3_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_72_safe
  · subst z; exact s4_92_safe
  · subst z; exact s4_144_safe
def s3_12 : State := ⟨4, 8, 64, 132, 5784800237655953879190962975597417005334, 1, 1, 1⟩
theorem s3_12_edges : next 3 s3_12 = [] := by decide
theorem s3_12_safe : Safe 10 3 s3_12 := by
  apply safe_succ 9 3 s3_12 [] (by decide) s3_12_edges
  simp
def s3_13 : State := ⟨4, 8, 64, 132, 1399581375145819900224878207110940658303254, 2, 2, 1⟩
theorem s3_13_edges : next 3 s3_13 = [s4_73, s4_93, s4_145] := by decide
theorem s3_13_safe : Safe 10 3 s3_13 := by
  apply safe_succ 9 3 s3_13 [s4_73, s4_93, s4_145] (by decide) s3_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_73_safe
  · subst z; exact s4_93_safe
  · subst z; exact s4_145_safe
def s3_14 : State := ⟨4, 8, 64, 136, 87452568298681185110105720854042434929430, 2, 2, 1⟩
theorem s3_14_edges : next 3 s3_14 = [] := by decide
theorem s3_14_safe : Safe 10 3 s3_14 := by
  apply safe_succ 9 3 s3_14 [] (by decide) s3_14_edges
  simp
def s3_15 : State := ⟨4, 8, 64, 136, 87452568298681185110105720854042434933014, 1, 1, 1⟩
theorem s3_15_edges : next 3 s3_15 = [s4_74, s4_94, s4_146] := by decide
theorem s3_15_safe : Safe 10 3 s3_15 := by
  apply safe_succ 9 3 s3_15 [s4_74, s4_94, s4_146] (by decide) s3_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_74_safe
  · subst z; exact s4_94_safe
  · subst z; exact s4_146_safe
def s3_16 : State := ⟨4, 8, 64, 136, 87452568298681185110105720854042434933014, 2, 2, 1⟩
theorem s3_16_edges : next 3 s3_16 = [s4_75, s4_95, s4_147] := by decide
theorem s3_16_safe : Safe 10 3 s3_16 := by
  apply safe_succ 9 3 s3_16 [s4_75, s4_95, s4_147] (by decide) s3_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_75_safe
  · subst z; exact s4_95_safe
  · subst z; exact s4_147_safe
def s3_17 : State := ⟨4, 8, 64, 136, 87452568298681185110400868759221787754774, 1, 1, 1⟩
theorem s3_17_edges : next 3 s3_17 = [] := by decide
theorem s3_17_safe : Safe 10 3 s3_17 := by
  apply safe_succ 9 3 s3_17 [] (by decide) s3_17_edges
  simp
def s3_18 : State := ⟨4, 8, 64, 136, 1481249143206845131456088112894565029052694, 1, 1, 1⟩
theorem s3_18_edges : next 3 s3_18 = [s4_76, s4_96, s4_148] := by decide
theorem s3_18_safe : Safe 10 3 s3_18 := by
  apply safe_succ 9 3 s3_18 [s4_76, s4_96, s4_148] (by decide) s3_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_76_safe
  · subst z; exact s4_96_safe
  · subst z; exact s4_148_safe
def s3_19 : State := ⟨4, 8, 64, 137, 174564854230441431756729620356575097062166, 2, 2, 1⟩
theorem s3_19_edges : next 3 s3_19 = [] := by decide
theorem s3_19_safe : Safe 10 3 s3_19 := by
  apply safe_succ 9 3 s3_19 [] (by decide) s3_19_edges
  simp
def s3_20 : State := ⟨4, 8, 64, 140, 1394136857275084884809464213392032366924054, 1, 1, 1⟩
theorem s3_20_edges : next 3 s3_20 = [s4_77, s4_97, s4_149] := by decide
theorem s3_20_safe : Safe 10 3 s3_20 := by
  apply safe_succ 9 3 s3_20 [s4_77, s4_97, s4_149] (by decide) s3_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_77_safe
  · subst z; exact s4_97_safe
  · subst z; exact s4_149_safe
def s3_21 : State := ⟨4, 8, 64, 140, 1394136857275084884809464213392032366924054, 2, 2, 1⟩
theorem s3_21_edges : next 3 s3_21 = [s4_78, s4_98, s4_150] := by decide
theorem s3_21_safe : Safe 10 3 s3_21 := by
  apply safe_succ 9 3 s3_21 [s4_78, s4_98, s4_150] (by decide) s3_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_78_safe
  · subst z; exact s4_98_safe
  · subst z; exact s4_150_safe
def s3_22 : State := ⟨4, 8, 64, 144, 22301085480897544079999200093999871278777110, 2, 2, 1⟩
theorem s3_22_edges : next 3 s3_22 = [] := by decide
theorem s3_22_safe : Safe 10 3 s3_22 := by
  apply safe_succ 9 3 s3_22 [] (by decide) s3_22_edges
  simp
def s3_23 : State := ⟨4, 8, 64, 144, 22301085480897544079999200093999871278780694, 1, 1, 1⟩
theorem s3_23_edges : next 3 s3_23 = [s4_214, s4_79, s4_99, s4_151, s4_44, s4_7, s4_32] := by decide
theorem s3_23_safe : Safe 10 3 s3_23 := by
  apply safe_succ 9 3 s3_23 [s4_214, s4_79, s4_99, s4_151, s4_44, s4_7, s4_32] (by decide) s3_23_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_214_safe
  · subst z; exact s4_79_safe
  · subst z; exact s4_99_safe
  · subst z; exact s4_151_safe
  · subst z; exact s4_44_safe
  · subst z; exact s4_7_safe
  · subst z; exact s4_32_safe
def s3_24 : State := ⟨4, 8, 64, 144, 22301085480897544079999200093999871278780694, 2, 2, 1⟩
theorem s3_24_edges : next 3 s3_24 = [s4_215, s4_80, s4_100, s4_152, s4_45, s4_8, s4_33] := by decide
theorem s3_24_safe : Safe 10 3 s3_24 := by
  apply safe_succ 9 3 s3_24 [s4_215, s4_80, s4_100, s4_152, s4_45, s4_8, s4_33] (by decide) s3_24_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_215_safe
  · subst z; exact s4_80_safe
  · subst z; exact s4_100_safe
  · subst z; exact s4_152_safe
  · subst z; exact s4_45_safe
  · subst z; exact s4_8_safe
  · subst z; exact s4_33_safe
def s3_25 : State := ⟨4, 8, 64, 144, 22301085480897544079999495241905050631602454, 1, 1, 1⟩
theorem s3_25_edges : next 3 s3_25 = [s4_9] := by decide
theorem s3_25_safe : Safe 10 3 s3_25 := by
  apply safe_succ 9 3 s3_25 [s4_9] (by decide) s3_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_9_safe
def s3_26 : State := ⟨4, 8, 64, 150, 1516452374911916978316746177859869819252310294, 0, 0, 1⟩
theorem s3_26_edges : next 3 s3_26 = [s4_226, s4_48] := by decide
theorem s3_26_safe : Safe 10 3 s3_26 := by
  apply safe_succ 9 3 s3_26 [s4_226, s4_48] (by decide) s3_26_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_226_safe
  · subst z; exact s4_48_safe
def s3_27 : State := ⟨4, 8, 64, 150, 1538751758980979917704428042634088453685444886, 0, 0, 1⟩
theorem s3_27_edges : next 3 s3_27 = [s4_227, s4_49] := by decide
theorem s3_27_safe : Safe 10 3 s3_27 := by
  apply safe_succ 9 3 s3_27 [s4_227, s4_49] (by decide) s3_27_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_227_safe
  · subst z; exact s4_49_safe
def s3_28 : State := ⟨4, 8, 64, 160, 1461501637671185285124623296198104371165705339670, 2, 2, 1⟩
theorem s3_28_edges : next 3 s3_28 = [s4_56, s4_19] := by decide
theorem s3_28_safe : Safe 10 3 s3_28 := by
  apply safe_succ 9 3 s3_28 [s4_56, s4_19] (by decide) s3_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_56_safe
  · subst z; exact s4_19_safe
def s3_29 : State := ⟨4, 8, 64, 160, 1461501637671185285124623296198104371165705343254, 1, 1, 1⟩
theorem s3_29_edges : next 3 s3_29 = [s4_81, s4_101, s4_153, s4_57, s4_14, s4_20, s4_34] := by decide
theorem s3_29_safe : Safe 10 3 s3_29 := by
  apply safe_succ 9 3 s3_29 [s4_81, s4_101, s4_153, s4_57, s4_14, s4_20, s4_34] (by decide) s3_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_81_safe
  · subst z; exact s4_101_safe
  · subst z; exact s4_153_safe
  · subst z; exact s4_57_safe
  · subst z; exact s4_14_safe
  · subst z; exact s4_20_safe
  · subst z; exact s4_34_safe
def s3_30 : State := ⟨4, 8, 64, 160, 1461501637671185285124623296198104371165705343254, 2, 2, 1⟩
theorem s3_30_edges : next 3 s3_30 = [s4_82, s4_102, s4_154, s4_58, s4_15, s4_21, s4_35] := by decide
theorem s3_30_safe : Safe 10 3 s3_30 := by
  apply safe_succ 9 3 s3_30 [s4_82, s4_102, s4_154, s4_58, s4_15, s4_21, s4_35] (by decide) s3_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_82_safe
  · subst z; exact s4_102_safe
  · subst z; exact s4_154_safe
  · subst z; exact s4_58_safe
  · subst z; exact s4_15_safe
  · subst z; exact s4_21_safe
  · subst z; exact s4_35_safe
def s3_31 : State := ⟨4, 8, 64, 160, 1461501637671185285124623296493252276345058165014, 1, 1, 1⟩
theorem s3_31_edges : next 3 s3_31 = [s4_59] := by decide
theorem s3_31_safe : Safe 10 3 s3_31 := by
  apply safe_succ 9 3 s3_31 [s4_59] (by decide) s3_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_59_safe
def s3_32 : State := ⟨4, 8, 64, 163, 11692013102390329381759801759845831583074915254550, 0, 0, 1⟩
theorem s3_32_edges : next 3 s3_32 = [s4_343, s4_232, s4_337, s4_24] := by decide
theorem s3_32_safe : Safe 10 3 s3_32 := by
  apply safe_succ 9 3 s3_32 [s4_343, s4_232, s4_337, s4_24] (by decide) s3_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_343_safe
  · subst z; exact s4_232_safe
  · subst z; exact s4_337_safe
  · subst z; exact s4_24_safe
def s3_33 : State := ⟨4, 8, 64, 163, 11692013103070894115601678686772580797938451677462, 0, 0, 1⟩
theorem s3_33_edges : next 3 s3_33 = [s4_344, s4_233, s4_338, s4_25] := by decide
theorem s3_33_safe : Safe 10 3 s3_33 := by
  apply safe_succ 9 3 s3_33 [s4_344, s4_233, s4_338, s4_25] (by decide) s3_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_344_safe
  · subst z; exact s4_233_safe
  · subst z; exact s4_338_safe
  · subst z; exact s4_25_safe
def s3_34 : State := ⟨4, 8, 64, 163, 14615016374329876282799663717571400762932634648854, 0, 0, 1⟩
theorem s3_34_edges : next 3 s3_34 = [s4_345, s4_234, s4_339, s4_26] := by decide
theorem s3_34_safe : Safe 10 3 s3_34 := by
  apply safe_succ 9 3 s3_34 [s4_345, s4_234, s4_339, s4_26] (by decide) s3_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_345_safe
  · subst z; exact s4_234_safe
  · subst z; exact s4_339_safe
  · subst z; exact s4_26_safe
def s3_35 : State := ⟨4, 8, 64, 163, 16076518010980214467161471623360934567725030768918, 0, 0, 1⟩
theorem s3_35_edges : next 3 s3_35 = [s4_346, s4_235, s4_340, s4_27] := by decide
theorem s3_35_safe : Safe 10 3 s3_35 := by
  apply safe_succ 9 3 s3_35 [s4_346, s4_235, s4_340, s4_27] (by decide) s3_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_346_safe
  · subst z; exact s4_235_safe
  · subst z; exact s4_340_safe
  · subst z; exact s4_27_safe
def s3_36 : State := ⟨4, 8, 64, 163, 17538019649672246853048910309930716017108036157718, 0, 0, 1⟩
theorem s3_36_edges : next 3 s3_36 = [s4_347, s4_236, s4_341, s4_28] := by decide
theorem s3_36_safe : Safe 10 3 s3_36 := by
  apply safe_succ 9 3 s3_36 [s4_347, s4_236, s4_341, s4_28] (by decide) s3_36_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_347_safe
  · subst z; exact s4_236_safe
  · subst z; exact s4_341_safe
  · subst z; exact s4_28_safe
def s3_37 : State := ⟨4, 8, 64, 163, 18999521285642020303568841288793500607036895854870, 0, 0, 1⟩
theorem s3_37_edges : next 3 s3_37 = [s4_348, s4_237, s4_342, s4_29] := by decide
theorem s3_37_safe : Safe 10 3 s3_37 := by
  apply safe_succ 9 3 s3_37 [s4_348, s4_237, s4_342, s4_29] (by decide) s3_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_348_safe
  · subst z; exact s4_237_safe
  · subst z; exact s4_342_safe
  · subst z; exact s4_29_safe
def s3_38 : State := ⟨4, 8, 64, 170, 1502423683177869611747992700349674263987535499821334, 0, 0, 1⟩
theorem s3_38_edges : next 3 s3_38 = [s4_30] := by decide
theorem s3_38_safe : Safe 10 3 s3_38 := by
  apply safe_succ 9 3 s3_38 [s4_30] (by decide) s3_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_30_safe
def s3_39 : State := ⟨4, 8, 64, 170, 1503885184813839385198512631328537048577464359518486, 0, 0, 1⟩
theorem s3_39_edges : next 3 s3_39 = [s4_31] := by decide
theorem s3_39_safe : Safe 10 3 s3_39 := by
  apply safe_succ 9 3 s3_39 [s4_31] (by decide) s3_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_31_safe
def s3_40 : State := ⟨4, 8, 64, 192, 6277101735386680764176071790128604879584176795973807309590, 2, 2, 1⟩
theorem s3_40_edges : next 3 s3_40 = [s4_60] := by decide
theorem s3_40_safe : Safe 10 3 s3_40 := by
  apply safe_succ 9 3 s3_40 [s4_60] (by decide) s3_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_60_safe
def s3_41 : State := ⟨4, 8, 64, 192, 6277101735386680764176071790128604879584176795973807313174, 1, 1, 1⟩
theorem s3_41_edges : next 3 s3_41 = [s4_83, s4_103, s4_155, s4_38, s4_42, s4_46, s4_61] := by decide
theorem s3_41_safe : Safe 10 3 s3_41 := by
  apply safe_succ 9 3 s3_41 [s4_83, s4_103, s4_155, s4_38, s4_42, s4_46, s4_61] (by decide) s3_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_83_safe
  · subst z; exact s4_103_safe
  · subst z; exact s4_155_safe
  · subst z; exact s4_38_safe
  · subst z; exact s4_42_safe
  · subst z; exact s4_46_safe
  · subst z; exact s4_61_safe
def s3_42 : State := ⟨4, 8, 64, 192, 6277101735386680764176071790128604879584176795973807313174, 2, 2, 1⟩
theorem s3_42_edges : next 3 s3_42 = [s4_84, s4_104, s4_156, s4_39, s4_43, s4_47, s4_62] := by decide
theorem s3_42_safe : Safe 10 3 s3_42 := by
  apply safe_succ 9 3 s3_42 [s4_84, s4_104, s4_156, s4_39, s4_43, s4_47, s4_62] (by decide) s3_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_84_safe
  · subst z; exact s4_104_safe
  · subst z; exact s4_156_safe
  · subst z; exact s4_39_safe
  · subst z; exact s4_43_safe
  · subst z; exact s4_47_safe
  · subst z; exact s4_62_safe
def s3_43 : State := ⟨4, 8, 64, 192, 6277101735386680764176071790128604879879324701153160134934, 1, 1, 1⟩
theorem s3_43_edges : next 3 s3_43 = [s4_63] := by decide
theorem s3_43_safe : Safe 10 3 s3_43 := by
  apply safe_succ 9 3 s3_43 [s4_63] (by decide) s3_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_63_safe
def s3_44 : State := ⟨4, 8, 64, 192, 106710729501573572985548702561451267537221863907398359515414, 1, 1, 1⟩
theorem s3_44_edges : next 3 s3_44 = [s4_64] := by decide
theorem s3_44_safe : Safe 10 3 s3_44 := by
  apply safe_succ 9 3 s3_44 [s4_64] (by decide) s3_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_64_safe
def s3_45 : State := ⟨4, 8, 64, 196, 100433627766186892221712913138243601121414656368113677828374, 1, 1, 1⟩
theorem s3_45_edges : next 3 s3_45 = [] := by decide
theorem s3_45_safe : Safe 10 3 s3_45 := by
  apply safe_succ 9 3 s3_45 [] (by decide) s3_45_edges
  simp
def s3_46 : State := ⟨4, 8, 64, 210, 1645504557321206042244173864763307602241196074043954546218172694, 0, 0, 1⟩
theorem s3_46_edges : next 3 s3_46 = [s4_349, s4_471, s4_238, s4_50] := by decide
theorem s3_46_safe : Safe 10 3 s3_46 := by
  apply safe_succ 9 3 s3_46 [s4_349, s4_471, s4_238, s4_50] (by decide) s3_46_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_349_safe
  · subst z; exact s4_471_safe
  · subst z; exact s4_238_safe
  · subst z; exact s4_50_safe
def s3_47 : State := ⟨4, 8, 64, 210, 1645504557321206042266473248832370541628877938818173180651307286, 0, 0, 1⟩
theorem s3_47_edges : next 3 s3_47 = [s4_350, s4_472, s4_239, s4_51] := by decide
theorem s3_47_safe : Safe 10 3 s3_47 := by
  apply safe_succ 9 3 s3_47 [s4_350, s4_472, s4_239, s4_51] (by decide) s3_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_350_safe
  · subst z; exact s4_472_safe
  · subst z; exact s4_239_safe
  · subst z; exact s4_51_safe
def s3_48 : State := ⟨4, 8, 64, 210, 1645529665728147588878026227126877940340717610375138956332302614, 0, 0, 1⟩
theorem s3_48_edges : next 3 s3_48 = [s4_351, s4_473, s4_240, s4_52] := by decide
theorem s3_48_safe : Safe 10 3 s3_48 := by
  apply safe_succ 9 3 s3_48 [s4_351, s4_473, s4_240, s4_52] (by decide) s3_48_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_351_safe
  · subst z; exact s4_473_safe
  · subst z; exact s4_240_safe
  · subst z; exact s4_52_safe
def s3_49 : State := ⟨4, 8, 64, 210, 1645535942829882975558788701786833464253279859232153693293969686, 0, 0, 1⟩
theorem s3_49_edges : next 3 s3_49 = [s4_352, s4_474, s4_241, s4_53] := by decide
theorem s3_49_safe : Safe 10 3 s3_49 := by
  apply safe_succ 9 3 s3_49 [s4_352, s4_474, s4_241, s4_53] (by decide) s3_49_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_352_safe
  · subst z; exact s4_474_safe
  · subst z; exact s4_241_safe
  · subst z; exact s4_53_safe
def s3_50 : State := ⟨4, 8, 64, 210, 2056880696651507552716012563677585675308419032135974700464537878, 0, 0, 1⟩
theorem s3_50_edges : next 3 s3_50 = [s4_353, s4_475, s4_242, s4_54] := by decide
theorem s3_50_safe : Safe 10 3 s3_50 := by
  apply safe_succ 9 3 s3_50 [s4_353, s4_475, s4_242, s4_54] (by decide) s3_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_353_safe
  · subst z; exact s4_475_safe
  · subst z; exact s4_242_safe
  · subst z; exact s4_54_safe
def s3_51 : State := ⟨4, 8, 64, 210, 2056886973753242939374475654268478259833299416218770802993070358, 0, 0, 1⟩
theorem s3_51_edges : next 3 s3_51 = [s4_354, s4_476, s4_243, s4_55] := by decide
theorem s3_51_safe : Safe 10 3 s3_51 := by
  apply safe_succ 9 3 s3_51 [s4_354, s4_476, s4_243, s4_55] (by decide) s3_51_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_354_safe
  · subst z; exact s4_476_safe
  · subst z; exact s4_243_safe
  · subst z; exact s4_55_safe
def s3_52 : State := ⟨4, 8, 65, 128, 340282366920938463518714839657191903510, 1, 1, 0⟩
theorem s3_52_edges : next 3 s3_52 = [s4_111, s4_71, s4_74, s4_85, s4_67, s4_69, s4_79, s4_81] := by decide
theorem s3_52_safe : Safe 10 3 s3_52 := by
  apply safe_succ 9 3 s3_52 [s4_111, s4_71, s4_74, s4_85, s4_67, s4_69, s4_79, s4_81] (by decide) s3_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_111_safe
  · subst z; exact s4_71_safe
  · subst z; exact s4_74_safe
  · subst z; exact s4_85_safe
  · subst z; exact s4_67_safe
  · subst z; exact s4_69_safe
  · subst z; exact s4_79_safe
  · subst z; exact s4_81_safe
def s3_53 : State := ⟨4, 8, 65, 128, 340282366920938463518714839657191903510, 2, 2, 0⟩
theorem s3_53_edges : next 3 s3_53 = [s4_112, s4_72, s4_75, s4_86, s4_68, s4_70, s4_80, s4_82] := by decide
theorem s3_53_safe : Safe 10 3 s3_53 := by
  apply safe_succ 9 3 s3_53 [s4_112, s4_72, s4_75, s4_86, s4_68, s4_70, s4_80, s4_82] (by decide) s3_53_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_112_safe
  · subst z; exact s4_72_safe
  · subst z; exact s4_75_safe
  · subst z; exact s4_86_safe
  · subst z; exact s4_68_safe
  · subst z; exact s4_70_safe
  · subst z; exact s4_80_safe
  · subst z; exact s4_82_safe
def s3_54 : State := ⟨4, 8, 65, 140, 1399581375145819900224915100599088077406486, 0, 0, 1⟩
theorem s3_54_edges : next 3 s3_54 = [s4_115] := by decide
theorem s3_54_safe : Safe 10 3 s3_54 := by
  apply safe_succ 9 3 s3_54 [s4_115] (by decide) s3_54_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_115_safe
def s3_55 : State := ⟨4, 8, 65, 140, 1481249143206845131456125006382712448155926, 0, 0, 1⟩
theorem s3_55_edges : next 3 s3_55 = [s4_117] := by decide
theorem s3_55_safe : Safe 10 3 s3_55 := by
  apply safe_succ 9 3 s3_55 [s4_117] (by decide) s3_55_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_117_safe
def s3_56 : State := ⟨4, 8, 65, 146, 89204682205957097258460245303862830288666902, 0, 0, 1⟩
theorem s3_56_edges : next 3 s3_56 = [s4_355, s4_244, s4_119] := by decide
theorem s3_56_safe : Safe 10 3 s3_56 := by
  apply safe_succ 9 3 s3_56 [s4_355, s4_244, s4_119] (by decide) s3_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_355_safe
  · subst z; exact s4_244_safe
  · subst z; exact s4_119_safe
def s3_57 : State := ⟨4, 8, 65, 146, 111504066275020036646142110078081464721801494, 0, 0, 1⟩
theorem s3_57_edges : next 3 s3_57 = [s4_356, s4_245, s4_121] := by decide
theorem s3_57_safe : Safe 10 3 s3_57 := by
  apply safe_succ 9 3 s3_57 [s4_356, s4_245, s4_121] (by decide) s3_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_356_safe
  · subst z; exact s4_245_safe
  · subst z; exact s4_121_safe
def s3_58 : State := ⟨4, 8, 65, 162, 5846006551025023507419431648237345348007994917142, 0, 0, 1⟩
theorem s3_58_edges : next 3 s3_58 = [s4_357, s4_246, s4_123] := by decide
theorem s3_58_safe : Safe 10 3 s3_58 := by
  apply safe_succ 9 3 s3_58 [s4_357, s4_246, s4_123] (by decide) s3_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_357_safe
  · subst z; exact s4_246_safe
  · subst z; exact s4_123_safe
def s3_59 : State := ⟨4, 8, 65, 162, 7307508186994796957939362627100129937936854614294, 0, 0, 1⟩
theorem s3_59_edges : next 3 s3_59 = [s4_358, s4_247, s4_125] := by decide
theorem s3_59_safe : Safe 10 3 s3_59 := by
  apply safe_succ 9 3 s3_59 [s4_358, s4_247, s4_125] (by decide) s3_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_358_safe
  · subst z; exact s4_247_safe
  · subst z; exact s4_125_safe
def s3_60 : State := ⟨4, 8, 65, 176, 95780971326419139128294233276893560963659213834354966, 0, 0, 1⟩
theorem s3_60_edges : next 3 s3_60 = [s4_359, s4_248, s4_127] := by decide
theorem s3_60_safe : Safe 10 3 s3_60 := by
  apply safe_succ 9 3 s3_60 [s4_359, s4_248, s4_127] (by decide) s3_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_359_safe
  · subst z; exact s4_248_safe
  · subst z; exact s4_127_safe
def s3_61 : State := ⟨4, 8, 65, 176, 95782432805755724832681813820190558974030508260917526, 0, 0, 1⟩
theorem s3_61_edges : next 3 s3_61 = [s4_360, s4_249, s4_129] := by decide
theorem s3_61_safe : Safe 10 3 s3_61 := by
  apply safe_succ 9 3 s3_61 [s4_360, s4_249, s4_129] (by decide) s3_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_360_safe
  · subst z; exact s4_249_safe
  · subst z; exact s4_129_safe
def s3_62 : State := ⟨4, 8, 65, 224, 26959946667150639796128516724690815958761767718775570340416734691606, 0, 0, 1⟩
theorem s3_62_edges : next 3 s3_62 = [s4_361, s4_489, s4_250, s4_133] := by decide
theorem s3_62_safe : Safe 10 3 s3_62 := by
  apply safe_succ 9 3 s3_62 [s4_361, s4_489, s4_250, s4_133] (by decide) s3_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_361_safe
  · subst z; exact s4_489_safe
  · subst z; exact s4_250_safe
  · subst z; exact s4_133_safe
def s3_63 : State := ⟨4, 8, 65, 224, 26959946673427741530053695851195702463765749302161642765224836661526, 0, 0, 1⟩
theorem s3_63_edges : next 3 s3_63 = [s4_362, s4_490, s4_251, s4_135] := by decide
theorem s3_63_safe : Safe 10 3 s3_63 := by
  apply safe_succ 9 3 s3_63 [s4_362, s4_490, s4_251, s4_135] (by decide) s3_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_362_safe
  · subst z; exact s4_490_safe
  · subst z; exact s4_251_safe
  · subst z; exact s4_135_safe
def s3_64 : State := ⟨4, 8, 66, 128, 340282366920938463555608327804611006742, 1, 1, 0⟩
theorem s3_64_edges : next 3 s3_64 = [s4_113, s4_161, s4_91, s4_94, s4_105, s4_87, s4_89, s4_99, s4_101] := by decide
theorem s3_64_safe : Safe 10 3 s3_64 := by
  apply safe_succ 9 3 s3_64 [s4_113, s4_161, s4_91, s4_94, s4_105, s4_87, s4_89, s4_99, s4_101] (by decide) s3_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_113_safe
  · subst z; exact s4_161_safe
  · subst z; exact s4_91_safe
  · subst z; exact s4_94_safe
  · subst z; exact s4_105_safe
  · subst z; exact s4_87_safe
  · subst z; exact s4_89_safe
  · subst z; exact s4_99_safe
  · subst z; exact s4_101_safe
def s3_65 : State := ⟨4, 8, 66, 128, 340282366920938463555608327804611006742, 2, 2, 0⟩
theorem s3_65_edges : next 3 s3_65 = [s4_114, s4_162, s4_92, s4_95, s4_106, s4_88, s4_90, s4_100, s4_102] := by decide
theorem s3_65_safe : Safe 10 3 s3_65 := by
  apply safe_succ 9 3 s3_65 [s4_114, s4_162, s4_92, s4_95, s4_106, s4_88, s4_90, s4_100, s4_102] (by decide) s3_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_114_safe
  · subst z; exact s4_162_safe
  · subst z; exact s4_92_safe
  · subst z; exact s4_95_safe
  · subst z; exact s4_106_safe
  · subst z; exact s4_88_safe
  · subst z; exact s4_90_safe
  · subst z; exact s4_100_safe
  · subst z; exact s4_102_safe
def s3_66 : State := ⟨4, 8, 66, 140, 1399581375145819900224951994087235496509718, 0, 0, 1⟩
theorem s3_66_edges : next 3 s3_66 = [s4_116, s4_167] := by decide
theorem s3_66_safe : Safe 10 3 s3_66 := by
  apply safe_succ 9 3 s3_66 [s4_116, s4_167] (by decide) s3_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_116_safe
  · subst z; exact s4_167_safe
def s3_67 : State := ⟨4, 8, 66, 140, 1481249143206845131456161899870859867259158, 0, 0, 1⟩
theorem s3_67_edges : next 3 s3_67 = [s4_118, s4_169] := by decide
theorem s3_67_safe : Safe 10 3 s3_67 := by
  apply safe_succ 9 3 s3_67 [s4_118, s4_169] (by decide) s3_67_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_118_safe
  · subst z; exact s4_169_safe
def s3_68 : State := ⟨4, 8, 66, 146, 89204682205957097258460282197350977707770134, 0, 0, 1⟩
theorem s3_68_edges : next 3 s3_68 = [s4_363, s4_252, s4_120] := by decide
theorem s3_68_safe : Safe 10 3 s3_68 := by
  apply safe_succ 9 3 s3_68 [s4_363, s4_252, s4_120] (by decide) s3_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_363_safe
  · subst z; exact s4_252_safe
  · subst z; exact s4_120_safe
def s3_69 : State := ⟨4, 8, 66, 146, 111504066275020036646142146971569612140904726, 0, 0, 1⟩
theorem s3_69_edges : next 3 s3_69 = [s4_364, s4_253, s4_122] := by decide
theorem s3_69_safe : Safe 10 3 s3_69 := by
  apply safe_succ 9 3 s3_69 [s4_364, s4_253, s4_122] (by decide) s3_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_364_safe
  · subst z; exact s4_253_safe
  · subst z; exact s4_122_safe
def s3_70 : State := ⟨4, 8, 66, 162, 5846006551025023507419431648274238836155414020374, 0, 0, 1⟩
theorem s3_70_edges : next 3 s3_70 = [s4_365, s4_254, s4_124, s4_109] := by decide
theorem s3_70_safe : Safe 10 3 s3_70 := by
  apply safe_succ 9 3 s3_70 [s4_365, s4_254, s4_124, s4_109] (by decide) s3_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_365_safe
  · subst z; exact s4_254_safe
  · subst z; exact s4_124_safe
  · subst z; exact s4_109_safe
def s3_71 : State := ⟨4, 8, 66, 162, 7307508186994796957939362627137023426084273717526, 0, 0, 1⟩
theorem s3_71_edges : next 3 s3_71 = [s4_366, s4_255, s4_126, s4_110] := by decide
theorem s3_71_safe : Safe 10 3 s3_71 := by
  apply safe_succ 9 3 s3_71 [s4_366, s4_255, s4_126, s4_110] (by decide) s3_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_366_safe
  · subst z; exact s4_255_safe
  · subst z; exact s4_126_safe
  · subst z; exact s4_110_safe
def s3_72 : State := ⟨4, 8, 66, 176, 95780971326419139128294233276893597857147361253458198, 0, 0, 1⟩
theorem s3_72_edges : next 3 s3_72 = [s4_367, s4_256, s4_128] := by decide
theorem s3_72_safe : Safe 10 3 s3_72 := by
  apply safe_succ 9 3 s3_72 [s4_367, s4_256, s4_128] (by decide) s3_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_367_safe
  · subst z; exact s4_256_safe
  · subst z; exact s4_128_safe
def s3_73 : State := ⟨4, 8, 66, 176, 95782432805755724832681813820190595867518655680020758, 0, 0, 1⟩
theorem s3_73_edges : next 3 s3_73 = [s4_368, s4_257, s4_130] := by decide
theorem s3_73_safe : Safe 10 3 s3_73 := by
  apply safe_succ 9 3 s3_73 [s4_368, s4_257, s4_130] (by decide) s3_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_368_safe
  · subst z; exact s4_257_safe
  · subst z; exact s4_130_safe
def s3_74 : State := ⟨4, 8, 66, 210, 1645504557321206042177270268038248049062735139514556029465592086, 0, 0, 1⟩
theorem s3_74_edges : next 3 s3_74 = [s4_369, s4_477, s4_258, s4_131, s4_107] := by decide
theorem s3_74_safe : Safe 10 3 s3_74 := by
  apply safe_succ 9 3 s3_74 [s4_369, s4_477, s4_258, s4_131, s4_107] (by decide) s3_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_369_safe
  · subst z; exact s4_477_safe
  · subst z; exact s4_258_safe
  · subst z; exact s4_131_safe
  · subst z; exact s4_107_safe
def s3_75 : State := ⟨4, 8, 66, 210, 1645529665728147588878024865997410256586863830663685524097663254, 0, 0, 1⟩
theorem s3_75_edges : next 3 s3_75 = [s4_370, s4_478, s4_259, s4_132, s4_108] := by decide
theorem s3_75_safe : Safe 10 3 s3_75 := by
  apply safe_succ 9 3 s3_75 [s4_370, s4_478, s4_259, s4_132, s4_108] (by decide) s3_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_370_safe
  · subst z; exact s4_478_safe
  · subst z; exact s4_259_safe
  · subst z; exact s4_132_safe
  · subst z; exact s4_108_safe
def s3_76 : State := ⟨4, 8, 66, 224, 26959946667150639796128516724690815958761767718812463828564153794838, 0, 0, 1⟩
theorem s3_76_edges : next 3 s3_76 = [s4_371, s4_491, s4_260, s4_208, s4_134, s4_175] := by decide
theorem s3_76_safe : Safe 10 3 s3_76 := by
  apply safe_succ 9 3 s3_76 [s4_371, s4_491, s4_260, s4_208, s4_134, s4_175] (by decide) s3_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_371_safe
  · subst z; exact s4_491_safe
  · subst z; exact s4_260_safe
  · subst z; exact s4_208_safe
  · subst z; exact s4_134_safe
  · subst z; exact s4_175_safe
def s3_77 : State := ⟨4, 8, 66, 224, 26959946673427741530053695851195702463765749302198536253372255764758, 0, 0, 1⟩
theorem s3_77_edges : next 3 s3_77 = [s4_372, s4_492, s4_261, s4_209, s4_136, s4_177] := by decide
theorem s3_77_safe : Safe 10 3 s3_77 := by
  apply safe_succ 9 3 s3_77 [s4_372, s4_492, s4_261, s4_209, s4_136, s4_177] (by decide) s3_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_372_safe
  · subst z; exact s4_492_safe
  · subst z; exact s4_261_safe
  · subst z; exact s4_209_safe
  · subst z; exact s4_136_safe
  · subst z; exact s4_177_safe
def s3_78 : State := ⟨4, 8, 67, 129, 1020847100762815390593038007110404735254, 0, 0, 1⟩
theorem s3_78_edges : next 3 s3_78 = [s4_373, s4_262] := by decide
theorem s3_78_safe : Safe 10 3 s3_78 := by
  apply safe_succ 9 3 s3_78 [s4_373, s4_262] (by decide) s3_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_373_safe
  · subst z; exact s4_262_safe
def s3_79 : State := ⟨4, 8, 67, 129, 1020847100762815390629931495257823838486, 0, 0, 1⟩
theorem s3_79_edges : next 3 s3_79 = [s4_374, s4_263] := by decide
theorem s3_79_safe : Safe 10 3 s3_79 := by
  apply safe_succ 9 3 s3_79 [s4_374, s4_263] (by decide) s3_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_374_safe
  · subst z; exact s4_263_safe
def s3_80 : State := ⟨4, 8, 67, 130, 1701411834604692317519787221973941158166, 0, 0, 1⟩
theorem s3_80_edges : next 3 s3_80 = [s4_375, s4_264, s4_119, s4_123] := by decide
theorem s3_80_safe : Safe 10 3 s3_80 := by
  apply safe_succ 9 3 s3_80 [s4_375, s4_264, s4_119, s4_123] (by decide) s3_80_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_375_safe
  · subst z; exact s4_264_safe
  · subst z; exact s4_119_safe
  · subst z; exact s4_123_safe
def s3_81 : State := ⟨4, 8, 67, 130, 1701411834604692317556680710121360261398, 0, 0, 1⟩
theorem s3_81_edges : next 3 s3_81 = [s4_376, s4_265, s4_120, s4_124] := by decide
theorem s3_81_safe : Safe 10 3 s3_81 := by
  apply safe_succ 9 3 s3_81 [s4_376, s4_265, s4_120, s4_124] (by decide) s3_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_376_safe
  · subst z; exact s4_265_safe
  · subst z; exact s4_120_safe
  · subst z; exact s4_124_safe
def s3_82 : State := ⟨4, 8, 67, 132, 5784800237655953879080282511155159695638, 0, 0, 1⟩
theorem s3_82_edges : next 3 s3_82 = [s4_377, s4_266, s4_329, s4_115] := by decide
theorem s3_82_safe : Safe 10 3 s3_82 := by
  apply safe_succ 9 3 s3_82 [s4_377, s4_266, s4_329, s4_115] (by decide) s3_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_377_safe
  · subst z; exact s4_266_safe
  · subst z; exact s4_329_safe
  · subst z; exact s4_115_safe
def s3_83 : State := ⟨4, 8, 67, 132, 5784800237655953879117175999302578798870, 0, 0, 1⟩
theorem s3_83_edges : next 3 s3_83 = [s4_378, s4_267, s4_330, s4_116] := by decide
theorem s3_83_safe : Safe 10 3 s3_83 := by
  apply safe_succ 9 3 s3_83 [s4_378, s4_267, s4_330, s4_116] (by decide) s3_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_378_safe
  · subst z; exact s4_267_safe
  · subst z; exact s4_330_safe
  · subst z; exact s4_116_safe
def s3_84 : State := ⟨4, 8, 67, 136, 87452568298681185110290188294779530445078, 0, 0, 1⟩
theorem s3_84_edges : next 3 s3_84 = [s4_379, s4_461, s4_268, s4_117] := by decide
theorem s3_84_safe : Safe 10 3 s3_84 := by
  apply safe_succ 9 3 s3_84 [s4_379, s4_461, s4_268, s4_117] (by decide) s3_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_379_safe
  · subst z; exact s4_461_safe
  · subst z; exact s4_268_safe
  · subst z; exact s4_117_safe
def s3_85 : State := ⟨4, 8, 67, 136, 87452568298681185110327081782926949548310, 0, 0, 1⟩
theorem s3_85_edges : next 3 s3_85 = [s4_380, s4_462, s4_269, s4_118] := by decide
theorem s3_85_safe : Safe 10 3 s3_85 := by
  apply safe_succ 9 3 s3_85 [s4_380, s4_462, s4_269, s4_118] (by decide) s3_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_380_safe
  · subst z; exact s4_462_safe
  · subst z; exact s4_269_safe
  · subst z; exact s4_118_safe
def s3_86 : State := ⟨4, 8, 67, 144, 22301085480897544079999384561440608374292758, 0, 0, 1⟩
theorem s3_86_edges : next 3 s3_86 = [s4_383, s4_272, s4_121, s4_127] := by decide
theorem s3_86_safe : Safe 10 3 s3_86 := by
  apply safe_succ 9 3 s3_86 [s4_383, s4_272, s4_121, s4_127] (by decide) s3_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_383_safe
  · subst z; exact s4_272_safe
  · subst z; exact s4_121_safe
  · subst z; exact s4_127_safe
def s3_87 : State := ⟨4, 8, 67, 144, 22301085480897544079999421454928755793395990, 0, 0, 1⟩
theorem s3_87_edges : next 3 s3_87 = [s4_384, s4_273, s4_122, s4_128] := by decide
theorem s3_87_safe : Safe 10 3 s3_87 := by
  apply safe_succ 9 3 s3_87 [s4_384, s4_273, s4_122, s4_128] (by decide) s3_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_384_safe
  · subst z; exact s4_273_safe
  · subst z; exact s4_122_safe
  · subst z; exact s4_128_safe
def s3_88 : State := ⟨4, 8, 67, 160, 1461501637671185285124623296382571811902800855318, 0, 0, 1⟩
theorem s3_88_edges : next 3 s3_88 = [s4_385, s4_274, s4_125, s4_129] := by decide
theorem s3_88_safe : Safe 10 3 s3_88 := by
  apply safe_succ 9 3 s3_88 [s4_385, s4_274, s4_125, s4_129] (by decide) s3_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_385_safe
  · subst z; exact s4_274_safe
  · subst z; exact s4_125_safe
  · subst z; exact s4_129_safe
def s3_89 : State := ⟨4, 8, 67, 160, 1461501637671185285124623296419465300050219958550, 0, 0, 1⟩
theorem s3_89_edges : next 3 s3_89 = [s4_386, s4_275, s4_126, s4_130] := by decide
theorem s3_89_safe : Safe 10 3 s3_89 := by
  apply safe_succ 9 3 s3_89 [s4_386, s4_275, s4_126, s4_130] (by decide) s3_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_386_safe
  · subst z; exact s4_275_safe
  · subst z; exact s4_126_safe
  · subst z; exact s4_130_safe
def s3_90 : State := ⟨4, 8, 67, 192, 6277101735386680764176071790128604879768644236710902825238, 0, 0, 1⟩
theorem s3_90_edges : next 3 s3_90 = [s4_387, s4_276, s4_135] := by decide
theorem s3_90_safe : Safe 10 3 s3_90 := by
  apply safe_succ 9 3 s3_90 [s4_387, s4_276, s4_135] (by decide) s3_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_387_safe
  · subst z; exact s4_276_safe
  · subst z; exact s4_135_safe
def s3_91 : State := ⟨4, 8, 67, 192, 6277101735386680764176071790128604879805537724858321928470, 0, 0, 1⟩
theorem s3_91_edges : next 3 s3_91 = [s4_388, s4_277, s4_136] := by decide
theorem s3_91_safe : Safe 10 3 s3_91 := by
  apply safe_succ 9 3 s3_91 [s4_388, s4_277, s4_136] (by decide) s3_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_388_safe
  · subst z; exact s4_277_safe
  · subst z; exact s4_136_safe
def s3_92 : State := ⟨4, 8, 67, 193, 12554203470773361528011861213336271295870999681174937338134, 0, 0, 1⟩
theorem s3_92_edges : next 3 s3_92 = [s4_389, s4_278] := by decide
theorem s3_92_safe : Safe 10 3 s3_92 := by
  apply safe_succ 9 3 s3_92 [s4_389, s4_278] (by decide) s3_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_389_safe
  · subst z; exact s4_278_safe
def s3_93 : State := ⟨4, 8, 67, 194, 25108406941546723055683440059751604128112604058250425467158, 0, 0, 1⟩
theorem s3_93_edges : next 3 s3_93 = [s4_390, s4_279, s4_132] := by decide
theorem s3_93_safe : Safe 10 3 s3_93 := by
  apply safe_succ 9 3 s3_93 [s4_390, s4_279, s4_132] (by decide) s3_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_390_safe
  · subst z; exact s4_279_safe
  · subst z; exact s4_132_safe
def s3_94 : State := ⟨4, 8, 67, 195, 50216813883093446111026597752582269792485132347959144415510, 0, 0, 1⟩
theorem s3_94_edges : next 3 s3_94 = [s4_391, s4_280] := by decide
theorem s3_94_safe : Safe 10 3 s3_94 := by
  apply safe_succ 9 3 s3_94 [s4_391, s4_280] (by decide) s3_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_391_safe
  · subst z; exact s4_280_safe
def s3_95 : State := ⟨4, 8, 67, 195, 50216813883093446111026597752582269792522025836106563518742, 0, 0, 1⟩
theorem s3_95_edges : next 3 s3_95 = [s4_392, s4_281] := by decide
theorem s3_95_safe : Safe 10 3 s3_95 := by
  apply safe_succ 9 3 s3_95 [s4_392, s4_281] (by decide) s3_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_392_safe
  · subst z; exact s4_281_safe
def s3_96 : State := ⟨4, 8, 68, 146, 89204682205957097258460503558279862222389526, 0, 0, 1⟩
theorem s3_96_edges : next 3 s3_96 = [s4_222, s4_137] := by decide
theorem s3_96_safe : Safe 10 3 s3_96 := by
  apply safe_succ 9 3 s3_96 [s4_222, s4_137] (by decide) s3_96_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_222_safe
  · subst z; exact s4_137_safe
def s3_97 : State := ⟨4, 8, 68, 146, 111504066275020036646142368332498496655524118, 0, 0, 1⟩
theorem s3_97_edges : next 3 s3_97 = [s4_223, s4_138] := by decide
theorem s3_97_safe : Safe 10 3 s3_97 := by
  apply safe_succ 9 3 s3_97 [s4_223, s4_138] (by decide) s3_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_223_safe
  · subst z; exact s4_138_safe
def s3_98 : State := ⟨4, 8, 68, 224, 26959946667150639796128516724690815958761767719033824757448668414230, 0, 0, 1⟩
theorem s3_98_edges : next 3 s3_98 = [] := by decide
theorem s3_98_safe : Safe 10 3 s3_98 := by
  apply safe_succ 9 3 s3_98 [] (by decide) s3_98_edges
  simp
def s3_99 : State := ⟨4, 8, 68, 224, 26959946673427741530053695851195702463765749302419897182256770384150, 0, 0, 1⟩
theorem s3_99_edges : next 3 s3_99 = [] := by decide
theorem s3_99_safe : Safe 10 3 s3_99 := by
  apply safe_succ 9 3 s3_99 [] (by decide) s3_99_edges
  simp
def s3_100 : State := ⟨4, 8, 80, 128, 340282366920939672407640966138947506454, 1, 1, 0⟩
theorem s3_100_edges : next 3 s3_100 = [s4_163, s4_143, s4_146, s4_157, s4_139, s4_141, s4_151, s4_153] := by decide
theorem s3_100_safe : Safe 10 3 s3_100 := by
  apply safe_succ 9 3 s3_100 [s4_163, s4_143, s4_146, s4_157, s4_139, s4_141, s4_151, s4_153] (by decide) s3_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_163_safe
  · subst z; exact s4_143_safe
  · subst z; exact s4_146_safe
  · subst z; exact s4_157_safe
  · subst z; exact s4_139_safe
  · subst z; exact s4_141_safe
  · subst z; exact s4_151_safe
  · subst z; exact s4_153_safe
def s3_101 : State := ⟨4, 8, 80, 128, 340282366920939672407640966138947506454, 2, 2, 0⟩
theorem s3_101_edges : next 3 s3_101 = [s4_164, s4_144, s4_147, s4_158, s4_140, s4_142, s4_152, s4_154] := by decide
theorem s3_101_safe : Safe 10 3 s3_101 := by
  apply safe_succ 9 3 s3_101 [s4_164, s4_144, s4_147, s4_158, s4_140, s4_142, s4_152, s4_154] (by decide) s3_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_164_safe
  · subst z; exact s4_144_safe
  · subst z; exact s4_147_safe
  · subst z; exact s4_158_safe
  · subst z; exact s4_140_safe
  · subst z; exact s4_142_safe
  · subst z; exact s4_152_safe
  · subst z; exact s4_154_safe
def s3_102 : State := ⟨4, 8, 80, 140, 1399581375145819901433804026725569833009430, 0, 0, 1⟩
theorem s3_102_edges : next 3 s3_102 = [s4_168] := by decide
theorem s3_102_safe : Safe 10 3 s3_102 := by
  apply safe_succ 9 3 s3_102 [s4_168] (by decide) s3_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_168_safe
def s3_103 : State := ⟨4, 8, 80, 140, 1481249143206845132665013932509194203758870, 0, 0, 1⟩
theorem s3_103_edges : next 3 s3_103 = [s4_170] := by decide
theorem s3_103_safe : Safe 10 3 s3_103 := by
  apply safe_succ 9 3 s3_103 [s4_170] (by decide) s3_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_170_safe
def s3_104 : State := ⟨4, 8, 80, 210, 1645504557321206042154970883969185109676262126772975729368957206, 0, 0, 1⟩
theorem s3_104_edges : next 3 s3_104 = [s4_393, s4_479, s4_282, s4_159] := by decide
theorem s3_104_safe : Safe 10 3 s3_104 := by
  apply safe_succ 9 3 s3_104 [s4_393, s4_479, s4_282, s4_159] (by decide) s3_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_393_safe
  · subst z; exact s4_479_safe
  · subst z; exact s4_282_safe
  · subst z; exact s4_159_safe
def s3_105 : State := ⟨4, 8, 80, 210, 2056880696651507552693711818479055052168092239682940968133263638, 0, 0, 1⟩
theorem s3_105_edges : next 3 s3_105 = [s4_394, s4_480, s4_283, s4_160] := by decide
theorem s3_105_safe : Safe 10 3 s3_105 := by
  apply safe_succ 9 3 s3_105 [s4_394, s4_480, s4_283, s4_160] (by decide) s3_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_394_safe
  · subst z; exact s4_480_safe
  · subst z; exact s4_283_safe
  · subst z; exact s4_160_safe
def s3_106 : State := ⟨4, 8, 80, 224, 26959946667150639796128516724690815958761768927664496466898490294550, 0, 0, 1⟩
theorem s3_106_edges : next 3 s3_106 = [s4_395, s4_284, s4_176] := by decide
theorem s3_106_safe : Safe 10 3 s3_106 := by
  apply safe_succ 9 3 s3_106 [s4_395, s4_284, s4_176] (by decide) s3_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_395_safe
  · subst z; exact s4_284_safe
  · subst z; exact s4_176_safe
def s3_107 : State := ⟨4, 8, 80, 224, 26959946673427741530053695851195702463765750511050568891706592264470, 0, 0, 1⟩
theorem s3_107_edges : next 3 s3_107 = [s4_396, s4_285, s4_178] := by decide
theorem s3_107_safe : Safe 10 3 s3_107 := by
  apply safe_succ 9 3 s3_107 [s4_396, s4_285, s4_178] (by decide) s3_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_396_safe
  · subst z; exact s4_285_safe
  · subst z; exact s4_178_safe
def s3_108 : State := ⟨4, 8, 82, 129, 1020847100762820226185636001184846250262, 0, 0, 1⟩
theorem s3_108_edges : next 3 s3_108 = [s4_397, s4_435, s4_286, s4_179] := by decide
theorem s3_108_safe : Safe 10 3 s3_108 := by
  apply safe_succ 9 3 s3_108 [s4_397, s4_435, s4_286, s4_179] (by decide) s3_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_397_safe
  · subst z; exact s4_435_safe
  · subst z; exact s4_286_safe
  · subst z; exact s4_179_safe
def s3_109 : State := ⟨4, 8, 82, 129, 1020847100762821435037668639519182749974, 0, 0, 1⟩
theorem s3_109_edges : next 3 s3_109 = [s4_398, s4_436, s4_287, s4_180] := by decide
theorem s3_109_safe : Safe 10 3 s3_109 := by
  apply safe_succ 9 3 s3_109 [s4_398, s4_436, s4_287, s4_180] (by decide) s3_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_398_safe
  · subst z; exact s4_436_safe
  · subst z; exact s4_287_safe
  · subst z; exact s4_180_safe
def s3_110 : State := ⟨4, 8, 82, 130, 1701411834604697153112385216048382673174, 0, 0, 1⟩
theorem s3_110_edges : next 3 s3_110 = [s4_399, s4_437, s4_288, s4_181] := by decide
theorem s3_110_safe : Safe 10 3 s3_110 := by
  apply safe_succ 9 3 s3_110 [s4_399, s4_437, s4_288, s4_181] (by decide) s3_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_399_safe
  · subst z; exact s4_437_safe
  · subst z; exact s4_288_safe
  · subst z; exact s4_181_safe
def s3_111 : State := ⟨4, 8, 82, 130, 1701411834604698361964417854382719172886, 0, 0, 1⟩
theorem s3_111_edges : next 3 s3_111 = [s4_400, s4_438, s4_289, s4_182] := by decide
theorem s3_111_safe : Safe 10 3 s3_111 := by
  apply safe_succ 9 3 s3_111 [s4_400, s4_438, s4_289, s4_182] (by decide) s3_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_400_safe
  · subst z; exact s4_438_safe
  · subst z; exact s4_289_safe
  · subst z; exact s4_182_safe
def s3_112 : State := ⟨4, 8, 82, 132, 5784800237655958714672880505229601210646, 0, 0, 1⟩
theorem s3_112_edges : next 3 s3_112 = [s4_401, s4_439, s4_290, s4_331, s4_183, s4_218, s4_167, s4_171] := by decide
theorem s3_112_safe : Safe 10 3 s3_112 := by
  apply safe_succ 9 3 s3_112 [s4_401, s4_439, s4_290, s4_331, s4_183, s4_218, s4_167, s4_171] (by decide) s3_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_401_safe
  · subst z; exact s4_439_safe
  · subst z; exact s4_290_safe
  · subst z; exact s4_331_safe
  · subst z; exact s4_183_safe
  · subst z; exact s4_218_safe
  · subst z; exact s4_167_safe
  · subst z; exact s4_171_safe
def s3_113 : State := ⟨4, 8, 82, 132, 5784800237655959923524913143563937710358, 0, 0, 1⟩
theorem s3_113_edges : next 3 s3_113 = [s4_402, s4_440, s4_291, s4_332, s4_184, s4_219, s4_168, s4_172] := by decide
theorem s3_113_safe : Safe 10 3 s3_113 := by
  apply safe_succ 9 3 s3_113 [s4_402, s4_440, s4_291, s4_332, s4_184, s4_219, s4_168, s4_172] (by decide) s3_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_402_safe
  · subst z; exact s4_440_safe
  · subst z; exact s4_291_safe
  · subst z; exact s4_332_safe
  · subst z; exact s4_184_safe
  · subst z; exact s4_219_safe
  · subst z; exact s4_168_safe
  · subst z; exact s4_172_safe
def s3_114 : State := ⟨4, 8, 82, 136, 87452568298681189945882786288853971960086, 0, 0, 1⟩
theorem s3_114_edges : next 3 s3_114 = [s4_403, s4_441, s4_463, s4_292, s4_185, s4_169] := by decide
theorem s3_114_safe : Safe 10 3 s3_114 := by
  apply safe_succ 9 3 s3_114 [s4_403, s4_441, s4_463, s4_292, s4_185, s4_169] (by decide) s3_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_403_safe
  · subst z; exact s4_441_safe
  · subst z; exact s4_463_safe
  · subst z; exact s4_292_safe
  · subst z; exact s4_185_safe
  · subst z; exact s4_169_safe
def s3_115 : State := ⟨4, 8, 82, 136, 87452568298681191154734818927188308459798, 0, 0, 1⟩
theorem s3_115_edges : next 3 s3_115 = [s4_404, s4_442, s4_464, s4_293, s4_186, s4_170] := by decide
theorem s3_115_safe : Safe 10 3 s3_115 := by
  apply safe_succ 9 3 s3_115 [s4_404, s4_442, s4_464, s4_293, s4_186, s4_170] (by decide) s3_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_404_safe
  · subst z; exact s4_442_safe
  · subst z; exact s4_464_safe
  · subst z; exact s4_293_safe
  · subst z; exact s4_186_safe
  · subst z; exact s4_170_safe
def s3_116 : State := ⟨4, 8, 82, 144, 22301085480897544084834977159434682815807766, 0, 0, 1⟩
theorem s3_116_edges : next 3 s3_116 = [s4_407, s4_443, s4_296, s4_187] := by decide
theorem s3_116_safe : Safe 10 3 s3_116 := by
  apply safe_succ 9 3 s3_116 [s4_407, s4_443, s4_296, s4_187] (by decide) s3_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_407_safe
  · subst z; exact s4_443_safe
  · subst z; exact s4_296_safe
  · subst z; exact s4_187_safe
def s3_117 : State := ⟨4, 8, 82, 144, 22301085480897544086043829192073017152307478, 0, 0, 1⟩
theorem s3_117_edges : next 3 s3_117 = [s4_408, s4_444, s4_297, s4_188] := by decide
theorem s3_117_safe : Safe 10 3 s3_117 := by
  apply safe_succ 9 3 s3_117 [s4_408, s4_444, s4_297, s4_188] (by decide) s3_117_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_408_safe
  · subst z; exact s4_444_safe
  · subst z; exact s4_297_safe
  · subst z; exact s4_188_safe
def s3_118 : State := ⟨4, 8, 82, 160, 1461501637671185285124628131975169805977242370326, 0, 0, 1⟩
theorem s3_118_edges : next 3 s3_118 = [s4_409, s4_445, s4_298, s4_189] := by decide
theorem s3_118_safe : Safe 10 3 s3_118 := by
  apply safe_succ 9 3 s3_118 [s4_409, s4_445, s4_298, s4_189] (by decide) s3_118_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_409_safe
  · subst z; exact s4_445_safe
  · subst z; exact s4_298_safe
  · subst z; exact s4_189_safe
def s3_119 : State := ⟨4, 8, 82, 160, 1461501637671185285124629340827202444311578870038, 0, 0, 1⟩
theorem s3_119_edges : next 3 s3_119 = [s4_410, s4_446, s4_299, s4_190] := by decide
theorem s3_119_safe : Safe 10 3 s3_119 := by
  apply safe_succ 9 3 s3_119 [s4_410, s4_446, s4_299, s4_190] (by decide) s3_119_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_410_safe
  · subst z; exact s4_446_safe
  · subst z; exact s4_299_safe
  · subst z; exact s4_190_safe
def s3_120 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128609715361242230785344340246, 0, 0, 1⟩
theorem s3_120_edges : next 3 s3_120 = [s4_411, s4_447, s4_300, s4_191, s4_177] := by decide
theorem s3_120_safe : Safe 10 3 s3_120 := by
  apply safe_succ 9 3 s3_120 [s4_411, s4_447, s4_300, s4_191, s4_177] (by decide) s3_120_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_411_safe
  · subst z; exact s4_447_safe
  · subst z; exact s4_300_safe
  · subst z; exact s4_191_safe
  · subst z; exact s4_177_safe
def s3_121 : State := ⟨4, 8, 82, 192, 6277101735386680764176071790128610924213274869119680839958, 0, 0, 1⟩
theorem s3_121_edges : next 3 s3_121 = [s4_412, s4_448, s4_301, s4_192, s4_178] := by decide
theorem s3_121_safe : Safe 10 3 s3_121 := by
  apply safe_succ 9 3 s3_121 [s4_412, s4_448, s4_301, s4_192, s4_178] (by decide) s3_121_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_412_safe
  · subst z; exact s4_448_safe
  · subst z; exact s4_301_safe
  · subst z; exact s4_192_safe
  · subst z; exact s4_178_safe
def s3_122 : State := ⟨4, 8, 82, 194, 25108406941546723055683440059751608963668308564177447878934, 0, 0, 1⟩
theorem s3_122_edges : next 3 s3_122 = [s4_413, s4_449, s4_302, s4_193] := by decide
theorem s3_122_safe : Safe 10 3 s3_122 := by
  apply safe_succ 9 3 s3_122 [s4_413, s4_449, s4_302, s4_193] (by decide) s3_122_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_413_safe
  · subst z; exact s4_449_safe
  · subst z; exact s4_302_safe
  · subst z; exact s4_193_safe
def s3_123 : State := ⟨4, 8, 82, 208, 411376139330301510538742635921704547190192077327819621483479318, 0, 0, 1⟩
theorem s3_123_edges : next 3 s3_123 = [s4_414, s4_450, s4_303, s4_194] := by decide
theorem s3_123_safe : Safe 10 3 s3_123 := by
  apply safe_succ 9 3 s3_123 [s4_414, s4_450, s4_303, s4_194] (by decide) s3_123_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_414_safe
  · subst z; exact s4_450_safe
  · subst z; exact s4_303_safe
  · subst z; exact s4_194_safe
def s3_124 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717425926035124520366184658436374, 0, 0, 1⟩
theorem s3_124_edges : next 3 s3_124 = [s4_415, s4_451, s4_481, s4_304, s4_195, s4_173] := by decide
theorem s3_124_safe : Safe 10 3 s3_124 := by
  apply safe_succ 9 3 s3_124 [s4_415, s4_451, s4_481, s4_304, s4_195, s4_173] (by decide) s3_124_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_415_safe
  · subst z; exact s4_451_safe
  · subst z; exact s4_481_safe
  · subst z; exact s4_304_safe
  · subst z; exact s4_195_safe
  · subst z; exact s4_173_safe
def s3_125 : State := ⟨4, 8, 82, 210, 1645504557321206042154969522839717425927243976553004518994936086, 0, 0, 1⟩
theorem s3_125_edges : next 3 s3_125 = [s4_416, s4_452, s4_482, s4_305, s4_196, s4_174] := by decide
theorem s3_125_safe : Safe 10 3 s3_125 := by
  apply safe_succ 9 3 s3_125 [s4_416, s4_452, s4_482, s4_305, s4_196, s4_174] (by decide) s3_125_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s4_416_safe
  · subst z; exact s4_452_safe
  · subst z; exact s4_482_safe
  · subst z; exact s4_305_safe
  · subst z; exact s4_196_safe
  · subst z; exact s4_174_safe
def s3_126 : State := ⟨4, 8, 86, 128, 340282366921020670511342122588491022614, 0, 0, 0⟩
theorem s3_126_edges : next 3 s3_126 = [s4_183, s4_185, s4_197, s4_179, s4_181, s4_187, s4_189] := by decide
theorem s3_126_safe : Safe 10 3 s3_126 := by
  apply safe_succ 9 3 s3_126 [s4_183, s4_185, s4_197, s4_179, s4_181, s4_187, s4_189] (by decide) s3_126_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_183_safe
  · subst z; exact s4_185_safe
  · subst z; exact s4_197_safe
  · subst z; exact s4_179_safe
  · subst z; exact s4_181_safe
  · subst z; exact s4_187_safe
  · subst z; exact s4_189_safe
def s3_127 : State := ⟨4, 8, 86, 128, 340282366921021879363374760922827522326, 0, 0, 0⟩
theorem s3_127_edges : next 3 s3_127 = [s4_184, s4_186, s4_198, s4_180, s4_182, s4_188, s4_190] := by decide
theorem s3_127_safe : Safe 10 3 s3_127 := by
  apply safe_succ 9 3 s3_127 [s4_184, s4_186, s4_198, s4_180, s4_182, s4_188, s4_190] (by decide) s3_127_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_184_safe
  · subst z; exact s4_186_safe
  · subst z; exact s4_198_safe
  · subst z; exact s4_180_safe
  · subst z; exact s4_182_safe
  · subst z; exact s4_188_safe
  · subst z; exact s4_190_safe
def s3_128 : State := ⟨4, 8, 96, 128, 340282367000166625996085689103316747030, 2, 2, 0⟩
theorem s3_128_edges : next 3 s3_128 = [s4_318, s4_199] := by decide
theorem s3_128_safe : Safe 10 3 s3_128 := by
  apply safe_succ 9 3 s3_128 [s4_318, s4_199] (by decide) s3_128_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_318_safe
  · subst z; exact s4_199_safe
def s3_129 : State := ⟨4, 8, 96, 128, 340282367000166625996085689103316750614, 1, 1, 0⟩
theorem s3_129_edges : next 3 s3_129 = [s4_320, s4_200] := by decide
theorem s3_129_safe : Safe 10 3 s3_129 := by
  apply safe_succ 9 3 s3_129 [s4_320, s4_200] (by decide) s3_129_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_320_safe
  · subst z; exact s4_200_safe
def s3_130 : State := ⟨4, 8, 96, 128, 340282367000166625996085689103316750614, 2, 2, 0⟩
theorem s3_130_edges : next 3 s3_130 = [s4_319, s4_201] := by decide
theorem s3_130_safe : Safe 10 3 s3_130 := by
  apply safe_succ 9 3 s3_130 [s4_319, s4_201] (by decide) s3_130_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_319_safe
  · subst z; exact s4_201_safe
def s3_131 : State := ⟨4, 8, 96, 128, 340282367000166626291233594282669572374, 1, 1, 0⟩
theorem s3_131_edges : next 3 s3_131 = [s4_321, s4_202] := by decide
theorem s3_131_safe : Safe 10 3 s3_131 := by
  apply safe_succ 9 3 s3_131 [s4_321, s4_202] (by decide) s3_131_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_321_safe
  · subst z; exact s4_202_safe
def s3_132 : State := ⟨4, 8, 96, 128, 340282368267817226224315090600019951894, 1, 1, 0⟩
theorem s3_132_edges : next 3 s3_132 = [s4_322, s4_203] := by decide
theorem s3_132_safe : Safe 10 3 s3_132 := by
  apply safe_succ 9 3 s3_132 [s4_322, s4_203] (by decide) s3_132_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_322_safe
  · subst z; exact s4_203_safe
def s3_133 : State := ⟨4, 8, 96, 128, 340282387282576229647756113050568032534, 2, 2, 0⟩
theorem s3_133_edges : next 3 s3_133 = [s4_417, s4_455, s4_306, s4_230, s4_204] := by decide
theorem s3_133_safe : Safe 10 3 s3_133 := by
  apply safe_succ 9 3 s3_133 [s4_417, s4_455, s4_306, s4_230, s4_204] (by decide) s3_133_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_417_safe
  · subst z; exact s4_455_safe
  · subst z; exact s4_306_safe
  · subst z; exact s4_230_safe
  · subst z; exact s4_204_safe
def s3_134 : State := ⟨4, 8, 97, 224, 26959946667150639794667015087359913040795767373565186845394014896406, 0, 0, 1⟩
theorem s3_134_edges : next 3 s3_134 = [s4_418, s4_307] := by decide
theorem s3_134_safe : Safe 10 3 s3_134 := by
  apply safe_succ 9 3 s3_134 [s4_418, s4_307] (by decide) s3_134_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_418_safe
  · subst z; exact s4_307_safe
def s3_135 : State := ⟨4, 8, 100, 224, 26959946667150639794667015087359913041904961648764887571703630201110, 0, 0, 1⟩
theorem s3_135_edges : next 3 s3_135 = [] := by decide
theorem s3_135_safe : Safe 10 3 s3_135 := by
  apply safe_succ 9 3 s3_135 [] (by decide) s3_135_edges
  simp
def s3_136 : State := ⟨4, 8, 104, 224, 26959946667150639794667015087359913060919720652188328594154178281750, 0, 0, 1⟩
theorem s3_136_edges : next 3 s3_136 = [s4_419, s4_459, s4_493, s4_308, s4_231, s4_206, s4_207] := by decide
theorem s3_136_safe : Safe 10 3 s3_136 := by
  apply safe_succ 9 3 s3_136 [s4_419, s4_459, s4_493, s4_308, s4_231, s4_206, s4_207] (by decide) s3_136_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_419_safe
  · subst z; exact s4_459_safe
  · subst z; exact s4_493_safe
  · subst z; exact s4_308_safe
  · subst z; exact s4_231_safe
  · subst z; exact s4_206_safe
  · subst z; exact s4_207_safe
def s3_137 : State := ⟨4, 8, 112, 224, 26959946667150639794667015087359918232934169583364286700703256215830, 0, 0, 1⟩
theorem s3_137_edges : next 3 s3_137 = [s4_420, s4_309] := by decide
theorem s3_137_safe : Safe 10 3 s3_137 := by
  apply safe_succ 9 3 s3_137 [s4_420, s4_309] (by decide) s3_137_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_420_safe
  · subst z; exact s4_309_safe
def s3_138 : State := ⟨4, 8, 194, 146, 25108406941546812260025363649927924124617832152539007615254, 0, 0, 1⟩
theorem s3_138_edges : next 3 s3_138 = [s4_421, s4_310] := by decide
theorem s3_138_safe : Safe 10 3 s3_138 := by
  apply safe_succ 9 3 s3_138 [s4_421, s4_310] (by decide) s3_138_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_421_safe
  · subst z; exact s4_310_safe
def s3_139 : State := ⟨4, 8, 194, 162, 25108406947392729606368181200250097312609873637716713865494, 0, 0, 1⟩
theorem s3_139_edges : next 3 s3_139 = [s4_422, s4_311] := by decide
theorem s3_139_safe : Safe 10 3 s3_139 := by
  apply safe_succ 9 3 s3_139 [s4_422, s4_311] (by decide) s3_139_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_422_safe
  · subst z; exact s4_311_safe
def s3_140 : State := ⟨4, 8, 210, 130, 1645504557321206042154970883969185109676262126772975729368957206, 0, 0, 1⟩
theorem s3_140_edges : next 3 s3_140 = [s4_423, s4_483, s4_312, s4_216] := by decide
theorem s3_140_safe : Safe 10 3 s3_140 := by
  apply safe_succ 9 3 s3_140 [s4_423, s4_483, s4_312, s4_216] (by decide) s3_140_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_423_safe
  · subst z; exact s4_483_safe
  · subst z; exact s4_312_safe
  · subst z; exact s4_216_safe
def s3_141 : State := ⟨4, 8, 210, 130, 1645529665728147588878026227126877940340717610375138956332302614, 0, 0, 1⟩
theorem s3_141_edges : next 3 s3_141 = [s4_424, s4_484, s4_313, s4_217] := by decide
theorem s3_141_safe : Safe 10 3 s3_141 := by
  apply safe_succ 9 3 s3_141 [s4_424, s4_484, s4_313, s4_217] (by decide) s3_141_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_424_safe
  · subst z; exact s4_484_safe
  · subst z; exact s4_313_safe
  · subst z; exact s4_217_safe
def s3_142 : State := ⟨4, 8, 210, 144, 1645504557321206042177270268038248049062735139514556029465592086, 0, 0, 1⟩
theorem s3_142_edges : next 3 s3_142 = [s4_425, s4_485, s4_314, s4_220] := by decide
theorem s3_142_safe : Safe 10 3 s3_142 := by
  apply safe_succ 9 3 s3_142 [s4_425, s4_485, s4_314, s4_220] (by decide) s3_142_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_425_safe
  · subst z; exact s4_485_safe
  · subst z; exact s4_314_safe
  · subst z; exact s4_220_safe
def s3_143 : State := ⟨4, 8, 210, 144, 2056880696651507552716012563677585675308419032135974700464537878, 0, 0, 1⟩
theorem s3_143_edges : next 3 s3_143 = [s4_426, s4_486, s4_315, s4_221] := by decide
theorem s3_143_safe : Safe 10 3 s3_143 := by
  apply safe_succ 9 3 s3_143 [s4_426, s4_486, s4_315, s4_221] (by decide) s3_143_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_426_safe
  · subst z; exact s4_486_safe
  · subst z; exact s4_315_safe
  · subst z; exact s4_221_safe
def s3_144 : State := ⟨4, 8, 210, 146, 1645504557321206042244173864763307602241196074043954546218172694, 0, 0, 1⟩
theorem s3_144_edges : next 3 s3_144 = [s4_427, s4_487, s4_316, s4_224] := by decide
theorem s3_144_safe : Safe 10 3 s3_144 := by
  apply safe_succ 9 3 s3_144 [s4_427, s4_487, s4_316, s4_224] (by decide) s3_144_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_427_safe
  · subst z; exact s4_487_safe
  · subst z; exact s4_316_safe
  · subst z; exact s4_224_safe
def s3_145 : State := ⟨4, 8, 210, 146, 1645504557321206042266473248832370541628877938818173180651307286, 0, 0, 1⟩
theorem s3_145_edges : next 3 s3_145 = [s4_428, s4_488, s4_317, s4_225] := by decide
theorem s3_145_safe : Safe 10 3 s3_145 := by
  apply safe_succ 9 3 s3_145 [s4_428, s4_488, s4_317, s4_225] (by decide) s3_145_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_428_safe
  · subst z; exact s4_488_safe
  · subst z; exact s4_317_safe
  · subst z; exact s4_225_safe
def s3_146 : State := ⟨4, 9, 64, 162, 5846006551025023507419431648200451859860575814422, 2, 0, 1⟩
theorem s3_146_edges : next 3 s3_146 = [s4_333, s4_16, s4_228] := by decide
theorem s3_146_safe : Safe 10 3 s3_146 := by
  apply safe_succ 9 3 s3_146 [s4_333, s4_16, s4_228] (by decide) s3_146_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_333_safe
  · subst z; exact s4_16_safe
  · subst z; exact s4_228_safe
def s3_147 : State := ⟨4, 9, 64, 162, 7307508186994796957939362627063236449789435511574, 2, 0, 1⟩
theorem s3_147_edges : next 3 s3_147 = [s4_334, s4_19, s4_229] := by decide
theorem s3_147_safe : Safe 10 3 s3_147 := by
  apply safe_succ 9 3 s3_147 [s4_334, s4_19, s4_229] (by decide) s3_147_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_334_safe
  · subst z; exact s4_19_safe
  · subst z; exact s4_229_safe
def s3_148 : State := ⟨4, 9, 64, 224, 26959946667150639796128516724690815958761767718738676852269315588886, 2, 0, 1⟩
theorem s3_148_edges : next 3 s3_148 = [s4_56] := by decide
theorem s3_148_safe : Safe 10 3 s3_148 := by
  apply safe_succ 9 3 s3_148 [s4_56] (by decide) s3_148_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_56_safe
def s3_149 : State := ⟨4, 9, 64, 224, 26959946673427741530053695851195702463765749302124749277077417558806, 2, 0, 1⟩
theorem s3_149_edges : next 3 s3_149 = [s4_60] := by decide
theorem s3_149_safe : Safe 10 3 s3_149 := by
  apply safe_succ 9 3 s3_149 [s4_60] (by decide) s3_149_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_60_safe
def s3_150 : State := ⟨4, 9, 96, 224, 26959946667150639794667015087359913040637311048536658170206926996246, 2, 0, 1⟩
theorem s3_150_edges : next 3 s3_150 = [s4_199] := by decide
theorem s3_150_safe : Safe 10 3 s3_150 := by
  apply safe_succ 9 3 s3_150 [s4_199] (by decide) s3_150_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_199_safe
def s3_151 : State := ⟨4, 12, 64, 131, 3743106036130323098115567425827454914838, 2, 0, 1⟩
theorem s3_151_edges : next 3 s3_151 = [s4_1, s4_232] := by decide
theorem s3_151_safe : Safe 10 3 s3_151 := by
  apply safe_succ 9 3 s3_151 [s4_1, s4_232] (by decide) s3_151_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_1_safe
  · subst z; exact s4_232_safe
def s3_152 : State := ⟨4, 12, 64, 131, 4423670769972200025042316640690991337750, 2, 0, 1⟩
theorem s3_152_edges : next 3 s3_152 = [s4_3, s4_233] := by decide
theorem s3_152_safe : Safe 10 3 s3_152 := by
  apply safe_succ 9 3 s3_152 [s4_3, s4_233] (by decide) s3_152_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_3_safe
  · subst z; exact s4_233_safe
def s3_153 : State := ⟨4, 12, 64, 146, 89204682205957097258460208410374682869567766, 2, 0, 1⟩
theorem s3_153_edges : next 3 s3_153 = [s4_5, s4_316, s4_244, s4_252, s4_238] := by decide
theorem s3_153_safe : Safe 10 3 s3_153 := by
  apply safe_succ 9 3 s3_153 [s4_5, s4_316, s4_244, s4_252, s4_238] (by decide) s3_153_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_5_safe
  · subst z; exact s4_316_safe
  · subst z; exact s4_244_safe
  · subst z; exact s4_252_safe
  · subst z; exact s4_238_safe
def s3_154 : State := ⟨4, 12, 64, 146, 111504066275020036646142073184593317302702358, 2, 0, 1⟩
theorem s3_154_edges : next 3 s3_154 = [s4_8, s4_317, s4_245, s4_253, s4_239] := by decide
theorem s3_154_safe : Safe 10 3 s3_154 := by
  apply safe_succ 9 3 s3_154 [s4_8, s4_317, s4_245, s4_253, s4_239] (by decide) s3_154_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_8_safe
  · subst z; exact s4_317_safe
  · subst z; exact s4_245_safe
  · subst z; exact s4_253_safe
  · subst z; exact s4_239_safe
def s3_155 : State := ⟨4, 12, 64, 161, 2923003275682652937170185055841136605685174309142, 2, 0, 1⟩
theorem s3_155_edges : next 3 s3_155 = [s4_13, s4_234] := by decide
theorem s3_155_safe : Safe 10 3 s3_155 := by
  apply safe_succ 9 3 s3_155 [s4_13, s4_234] (by decide) s3_155_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_13_safe
  · subst z; exact s4_234_safe
def s3_156 : State := ⟨4, 12, 64, 161, 4384504912332991121531992961630670410477570429206, 2, 0, 1⟩
theorem s3_156_edges : next 3 s3_156 = [s4_15, s4_235] := by decide
theorem s3_156_safe : Safe 10 3 s3_156 := by
  apply safe_succ 9 3 s3_156 [s4_15, s4_235] (by decide) s3_156_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_15_safe
  · subst z; exact s4_235_safe
def s3_157 : State := ⟨4, 12, 64, 162, 5846006551025023507419431648200451859860575818006, 2, 0, 1⟩
theorem s3_157_edges : next 3 s3_157 = [s4_18, s4_246, s4_254, s4_236] := by decide
theorem s3_157_safe : Safe 10 3 s3_157 := by
  apply safe_succ 9 3 s3_157 [s4_18, s4_246, s4_254, s4_236] (by decide) s3_157_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_18_safe
  · subst z; exact s4_246_safe
  · subst z; exact s4_254_safe
  · subst z; exact s4_236_safe
def s3_158 : State := ⟨4, 12, 64, 162, 7307508186994796957939362627063236449789435515158, 2, 0, 1⟩
theorem s3_158_edges : next 3 s3_158 = [s4_21, s4_247, s4_255, s4_237] := by decide
theorem s3_158_safe : Safe 10 3 s3_158 := by
  apply safe_succ 9 3 s3_158 [s4_21, s4_247, s4_255, s4_237] (by decide) s3_158_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_21_safe
  · subst z; exact s4_247_safe
  · subst z; exact s4_255_safe
  · subst z; exact s4_237_safe
def s3_159 : State := ⟨4, 12, 64, 176, 95780971326419139128294233276893524070171066415255830, 2, 0, 1⟩
theorem s3_159_edges : next 3 s3_159 = [s4_33, s4_248, s4_256] := by decide
theorem s3_159_safe : Safe 10 3 s3_159 := by
  apply safe_succ 9 3 s3_159 [s4_33, s4_248, s4_256] (by decide) s3_159_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_33_safe
  · subst z; exact s4_248_safe
  · subst z; exact s4_256_safe
def s3_160 : State := ⟨4, 12, 64, 176, 95782432805755724832681813820190522080542360841818390, 2, 0, 1⟩
theorem s3_160_edges : next 3 s3_160 = [s4_35, s4_249, s4_257] := by decide
theorem s3_160_safe : Safe 10 3 s3_160 := by
  apply safe_succ 9 3 s3_160 [s4_35, s4_249, s4_257] (by decide) s3_160_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_35_safe
  · subst z; exact s4_249_safe
  · subst z; exact s4_257_safe
def s3_161 : State := ⟨4, 12, 64, 193, 12554203470773361528692425947178148222613281455301378248982, 2, 0, 1⟩
theorem s3_161_edges : next 3 s3_161 = [s4_37] := by decide
theorem s3_161_safe : Safe 10 3 s3_161 := by
  apply safe_succ 9 3 s3_161 [s4_37] (by decide) s3_161_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_37_safe
def s3_162 : State := ⟨4, 12, 64, 193, 18831305206160042291847650636543937711788887684901876338966, 2, 0, 1⟩
theorem s3_162_edges : next 3 s3_162 = [s4_39] := by decide
theorem s3_162_safe : Safe 10 3 s3_162 := by
  apply safe_succ 9 3 s3_162 [s4_39] (by decide) s3_162_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_39_safe
def s3_163 : State := ⟨4, 12, 64, 194, 25108406941546723057044569527435357981744741559092983697686, 2, 0, 1⟩
theorem s3_163_edges : next 3 s3_163 = [s4_41, s4_240] := by decide
theorem s3_163_safe : Safe 10 3 s3_163 := by
  apply safe_succ 9 3 s3_163 [s4_41, s4_240] (by decide) s3_163_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_41_safe
  · subst z; exact s4_240_safe
def s3_164 : State := ⟨4, 12, 64, 194, 31385508676933403819519229482959270543993598573829945364758, 2, 0, 1⟩
theorem s3_164_edges : next 3 s3_164 = [s4_43, s4_241] := by decide
theorem s3_164_safe : Safe 10 3 s3_164 := by
  apply safe_succ 9 3 s3_164 [s4_43, s4_241] (by decide) s3_164_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_43_safe
  · subst z; exact s4_241_safe
def s3_165 : State := ⟨4, 12, 64, 208, 411376139330301510561043381120235170325683166502394837115932950, 2, 0, 1⟩
theorem s3_165_edges : next 3 s3_165 = [s4_45, s4_242] := by decide
theorem s3_165_safe : Safe 10 3 s3_165 := by
  apply safe_succ 9 3 s3_165 [s4_45, s4_242] (by decide) s3_165_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_45_safe
  · subst z; exact s4_242_safe
def s3_166 : State := ⟨4, 12, 64, 208, 411382416432036897219506471711127754850563550585190939644465430, 2, 0, 1⟩
theorem s3_166_edges : next 3 s3_166 = [s4_47, s4_243] := by decide
theorem s3_166_safe : Safe 10 3 s3_166 := by
  apply safe_succ 9 3 s3_166 [s4_47, s4_243] (by decide) s3_166_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_47_safe
  · subst z; exact s4_243_safe
def s3_167 : State := ⟨4, 12, 64, 224, 26959946667150639796128516724690815958761767718738676852269315592470, 2, 0, 1⟩
theorem s3_167_edges : next 3 s3_167 = [s4_58, s4_250, s4_260, s4_284] := by decide
theorem s3_167_safe : Safe 10 3 s3_167 := by
  apply safe_succ 9 3 s3_167 [s4_58, s4_250, s4_260, s4_284] (by decide) s3_167_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_58_safe
  · subst z; exact s4_250_safe
  · subst z; exact s4_260_safe
  · subst z; exact s4_284_safe
def s3_168 : State := ⟨4, 12, 64, 224, 26959946673427741530053695851195702463765749302124749277077417562390, 2, 0, 1⟩
theorem s3_168_edges : next 3 s3_168 = [s4_62, s4_251, s4_261, s4_285] := by decide
theorem s3_168_safe : Safe 10 3 s3_168 := by
  apply safe_succ 9 3 s3_168 [s4_62, s4_251, s4_261, s4_285] (by decide) s3_168_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_62_safe
  · subst z; exact s4_251_safe
  · subst z; exact s4_261_safe
  · subst z; exact s4_285_safe
def s3_169 : State := ⟨4, 12, 65, 129, 1020847100762815390445464054520728326422, 2, 0, 1⟩
theorem s3_169_edges : next 3 s3_169 = [s4_68, s4_262] := by decide
theorem s3_169_safe : Safe 10 3 s3_169 := by
  apply safe_succ 9 3 s3_169 [s4_68, s4_262] (by decide) s3_169_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_68_safe
  · subst z; exact s4_262_safe
def s3_170 : State := ⟨4, 12, 65, 130, 1701411834604692317372213269384264749334, 2, 0, 1⟩
theorem s3_170_edges : next 3 s3_170 = [s4_70, s4_264, s4_244, s4_246] := by decide
theorem s3_170_safe : Safe 10 3 s3_170 := by
  apply safe_succ 9 3 s3_170 [s4_70, s4_264, s4_244, s4_246] (by decide) s3_170_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_70_safe
  · subst z; exact s4_264_safe
  · subst z; exact s4_244_safe
  · subst z; exact s4_246_safe
def s3_171 : State := ⟨4, 12, 65, 132, 5784800237655953878932708558565483286806, 2, 0, 1⟩
theorem s3_171_edges : next 3 s3_171 = [s4_72, s4_266] := by decide
theorem s3_171_safe : Safe 10 3 s3_171 := by
  apply safe_succ 9 3 s3_171 [s4_72, s4_266] (by decide) s3_171_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_72_safe
  · subst z; exact s4_266_safe
def s3_172 : State := ⟨4, 12, 65, 136, 87452568298681185110142614342189854036246, 2, 0, 1⟩
theorem s3_172_edges : next 3 s3_172 = [s4_75, s4_268] := by decide
theorem s3_172_safe : Safe 10 3 s3_172 := by
  apply safe_succ 9 3 s3_172 [s4_75, s4_268] (by decide) s3_172_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_75_safe
  · subst z; exact s4_268_safe
def s3_173 : State := ⟨4, 12, 65, 140, 1394136857275084884809501106880179786027286, 2, 0, 1⟩
theorem s3_173_edges : next 3 s3_173 = [s4_78, s4_270] := by decide
theorem s3_173_safe : Safe 10 3 s3_173 := by
  apply safe_succ 9 3 s3_173 [s4_78, s4_270] (by decide) s3_173_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_78_safe
  · subst z; exact s4_270_safe
def s3_174 : State := ⟨4, 12, 65, 144, 22301085480897544079999236987488018697883926, 2, 0, 1⟩
theorem s3_174_edges : next 3 s3_174 = [s4_80, s4_272, s4_245, s4_248] := by decide
theorem s3_174_safe : Safe 10 3 s3_174 := by
  apply safe_succ 9 3 s3_174 [s4_80, s4_272, s4_245, s4_248] (by decide) s3_174_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_80_safe
  · subst z; exact s4_272_safe
  · subst z; exact s4_245_safe
  · subst z; exact s4_248_safe
def s3_175 : State := ⟨4, 12, 65, 160, 1461501637671185285124623296234997859313124446486, 2, 0, 1⟩
theorem s3_175_edges : next 3 s3_175 = [s4_82, s4_274, s4_247, s4_249] := by decide
theorem s3_175_safe : Safe 10 3 s3_175 := by
  apply safe_succ 9 3 s3_175 [s4_82, s4_274, s4_247, s4_249] (by decide) s3_175_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_82_safe
  · subst z; exact s4_274_safe
  · subst z; exact s4_247_safe
  · subst z; exact s4_249_safe
def s3_176 : State := ⟨4, 12, 65, 192, 6277101735386680764176071790128604879621070284121226416406, 2, 0, 1⟩
theorem s3_176_edges : next 3 s3_176 = [s4_84, s4_276, s4_251] := by decide
theorem s3_176_safe : Safe 10 3 s3_176 := by
  apply safe_succ 9 3 s3_176 [s4_84, s4_276, s4_251] (by decide) s3_176_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_84_safe
  · subst z; exact s4_276_safe
  · subst z; exact s4_251_safe
def s3_177 : State := ⟨4, 12, 65, 193, 12554203470773361528011861213336271295723425728585260929302, 2, 0, 1⟩
theorem s3_177_edges : next 3 s3_177 = [s4_86, s4_278] := by decide
theorem s3_177_safe : Safe 10 3 s3_177 := by
  apply safe_succ 9 3 s3_177 [s4_86, s4_278] (by decide) s3_177_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_86_safe
  · subst z; exact s4_278_safe
def s3_178 : State := ⟨4, 12, 66, 129, 1020847100762815390482357542668147429654, 2, 0, 1⟩
theorem s3_178_edges : next 3 s3_178 = [s4_88, s4_263, s4_286] := by decide
theorem s3_178_safe : Safe 10 3 s3_178 := by
  apply safe_succ 9 3 s3_178 [s4_88, s4_263, s4_286] (by decide) s3_178_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_88_safe
  · subst z; exact s4_263_safe
  · subst z; exact s4_286_safe
def s3_179 : State := ⟨4, 12, 66, 130, 1701411834604692317409106757531683852566, 2, 0, 1⟩
theorem s3_179_edges : next 3 s3_179 = [s4_90, s4_265, s4_288, s4_252, s4_254] := by decide
theorem s3_179_safe : Safe 10 3 s3_179 := by
  apply safe_succ 9 3 s3_179 [s4_90, s4_265, s4_288, s4_252, s4_254] (by decide) s3_179_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_90_safe
  · subst z; exact s4_265_safe
  · subst z; exact s4_288_safe
  · subst z; exact s4_252_safe
  · subst z; exact s4_254_safe
def s3_180 : State := ⟨4, 12, 66, 132, 5784800237655953878969602046712902390038, 2, 0, 1⟩
theorem s3_180_edges : next 3 s3_180 = [s4_92, s4_267, s4_290] := by decide
theorem s3_180_safe : Safe 10 3 s3_180 := by
  apply safe_succ 9 3 s3_180 [s4_92, s4_267, s4_290] (by decide) s3_180_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_92_safe
  · subst z; exact s4_267_safe
  · subst z; exact s4_290_safe
def s3_181 : State := ⟨4, 12, 66, 136, 87452568298681185110179507830337273139478, 2, 0, 1⟩
theorem s3_181_edges : next 3 s3_181 = [s4_95, s4_269, s4_292] := by decide
theorem s3_181_safe : Safe 10 3 s3_181 := by
  apply safe_succ 9 3 s3_181 [s4_95, s4_269, s4_292] (by decide) s3_181_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_95_safe
  · subst z; exact s4_269_safe
  · subst z; exact s4_292_safe
def s3_182 : State := ⟨4, 12, 66, 140, 1394136857275084884809538000368327205130518, 2, 0, 1⟩
theorem s3_182_edges : next 3 s3_182 = [s4_98, s4_271, s4_294] := by decide
theorem s3_182_safe : Safe 10 3 s3_182 := by
  apply safe_succ 9 3 s3_182 [s4_98, s4_271, s4_294] (by decide) s3_182_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_98_safe
  · subst z; exact s4_271_safe
  · subst z; exact s4_294_safe
def s3_183 : State := ⟨4, 12, 66, 144, 22301085480897544079999273880976166116987158, 2, 0, 1⟩
theorem s3_183_edges : next 3 s3_183 = [s4_100, s4_314, s4_273, s4_296, s4_258, s4_253, s4_256] := by decide
theorem s3_183_safe : Safe 10 3 s3_183 := by
  apply safe_succ 9 3 s3_183 [s4_100, s4_314, s4_273, s4_296, s4_258, s4_253, s4_256] (by decide) s3_183_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_100_safe
  · subst z; exact s4_314_safe
  · subst z; exact s4_273_safe
  · subst z; exact s4_296_safe
  · subst z; exact s4_258_safe
  · subst z; exact s4_253_safe
  · subst z; exact s4_256_safe
def s3_184 : State := ⟨4, 12, 66, 160, 1461501637671185285124623296271891347460543549718, 2, 0, 1⟩
theorem s3_184_edges : next 3 s3_184 = [s4_102, s4_275, s4_298, s4_255, s4_257] := by decide
theorem s3_184_safe : Safe 10 3 s3_184 := by
  apply safe_succ 9 3 s3_184 [s4_102, s4_275, s4_298, s4_255, s4_257] (by decide) s3_184_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_102_safe
  · subst z; exact s4_275_safe
  · subst z; exact s4_298_safe
  · subst z; exact s4_255_safe
  · subst z; exact s4_257_safe
def s3_185 : State := ⟨4, 12, 66, 192, 6277101735386680764176071790128604879657963772268645519638, 2, 0, 1⟩
theorem s3_185_edges : next 3 s3_185 = [s4_104, s4_277, s4_300, s4_261] := by decide
theorem s3_185_safe : Safe 10 3 s3_185 := by
  apply safe_succ 9 3 s3_185 [s4_104, s4_277, s4_300, s4_261] (by decide) s3_185_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_104_safe
  · subst z; exact s4_277_safe
  · subst z; exact s4_300_safe
  · subst z; exact s4_261_safe
def s3_186 : State := ⟨4, 12, 66, 194, 25108406941546723055683440059751604127965030105660749058326, 2, 0, 1⟩
theorem s3_186_edges : next 3 s3_186 = [s4_106, s4_279, s4_302, s4_259] := by decide
theorem s3_186_safe : Safe 10 3 s3_186 := by
  apply safe_succ 9 3 s3_186 [s4_106, s4_279, s4_302, s4_259] (by decide) s3_186_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_106_safe
  · subst z; exact s4_279_safe
  · subst z; exact s4_302_safe
  · subst z; exact s4_259_safe
def s3_187 : State := ⟨4, 12, 67, 128, 340282366920938463666288792246868316438, 2, 0, 0⟩
theorem s3_187_edges : next 3 s3_187 = [s4_112, s4_266, s4_270, s4_280, s4_262, s4_264, s4_272, s4_274] := by decide
theorem s3_187_safe : Safe 10 3 s3_187 := by
  apply safe_succ 9 3 s3_187 [s4_112, s4_266, s4_270, s4_280, s4_262, s4_264, s4_272, s4_274] (by decide) s3_187_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_112_safe
  · subst z; exact s4_266_safe
  · subst z; exact s4_270_safe
  · subst z; exact s4_280_safe
  · subst z; exact s4_262_safe
  · subst z; exact s4_264_safe
  · subst z; exact s4_272_safe
  · subst z; exact s4_274_safe
def s3_188 : State := ⟨4, 12, 67, 128, 340282366920938463703182280394287419670, 2, 0, 0⟩
theorem s3_188_edges : next 3 s3_188 = [s4_114, s4_267, s4_271, s4_281, s4_263, s4_265, s4_273, s4_275] := by decide
theorem s3_188_safe : Safe 10 3 s3_188 := by
  apply safe_succ 9 3 s3_188 [s4_114, s4_267, s4_271, s4_281, s4_263, s4_265, s4_273, s4_275] (by decide) s3_188_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_114_safe
  · subst z; exact s4_267_safe
  · subst z; exact s4_271_safe
  · subst z; exact s4_281_safe
  · subst z; exact s4_263_safe
  · subst z; exact s4_265_safe
  · subst z; exact s4_273_safe
  · subst z; exact s4_275_safe
def s3_189 : State := ⟨4, 12, 80, 129, 1020847100762816599334390181002483929366, 2, 0, 1⟩
theorem s3_189_edges : next 3 s3_189 = [s4_140, s4_287] := by decide
theorem s3_189_safe : Safe 10 3 s3_189 := by
  apply safe_succ 9 3 s3_189 [s4_140, s4_287] (by decide) s3_189_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_140_safe
  · subst z; exact s4_287_safe
def s3_190 : State := ⟨4, 12, 80, 130, 1701411834604693526261139395866020352278, 2, 0, 1⟩
theorem s3_190_edges : next 3 s3_190 = [s4_142, s4_312, s4_289, s4_282] := by decide
theorem s3_190_safe : Safe 10 3 s3_190 := by
  apply safe_succ 9 3 s3_190 [s4_142, s4_312, s4_289, s4_282] (by decide) s3_190_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_142_safe
  · subst z; exact s4_312_safe
  · subst z; exact s4_289_safe
  · subst z; exact s4_282_safe
def s3_191 : State := ⟨4, 12, 80, 132, 5784800237655955087821634685047238889750, 2, 0, 1⟩
theorem s3_191_edges : next 3 s3_191 = [s4_144, s4_291] := by decide
theorem s3_191_safe : Safe 10 3 s3_191 := by
  apply safe_succ 9 3 s3_191 [s4_144, s4_291] (by decide) s3_191_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_144_safe
  · subst z; exact s4_291_safe
def s3_192 : State := ⟨4, 12, 80, 136, 87452568298681186319031540468671609639190, 2, 0, 1⟩
theorem s3_192_edges : next 3 s3_192 = [s4_147, s4_293] := by decide
theorem s3_192_safe : Safe 10 3 s3_192 := by
  apply safe_succ 9 3 s3_192 [s4_147, s4_293] (by decide) s3_192_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_147_safe
  · subst z; exact s4_293_safe
def s3_193 : State := ⟨4, 12, 80, 140, 1394136857275084886018390033006661541630230, 2, 0, 1⟩
theorem s3_193_edges : next 3 s3_193 = [s4_150, s4_295] := by decide
theorem s3_193_safe : Safe 10 3 s3_193 := by
  apply safe_succ 9 3 s3_193 [s4_150, s4_295] (by decide) s3_193_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_150_safe
  · subst z; exact s4_295_safe
def s3_194 : State := ⟨4, 12, 80, 144, 22301085480897544081208125913614500453486870, 2, 0, 1⟩
theorem s3_194_edges : next 3 s3_194 = [s4_152, s4_297] := by decide
theorem s3_194_safe : Safe 10 3 s3_194 := by
  apply safe_succ 9 3 s3_194 [s4_152, s4_297] (by decide) s3_194_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_152_safe
  · subst z; exact s4_297_safe
def s3_195 : State := ⟨4, 12, 80, 160, 1461501637671185285124624505123923985794880049430, 2, 0, 1⟩
theorem s3_195_edges : next 3 s3_195 = [s4_154, s4_299] := by decide
theorem s3_195_safe : Safe 10 3 s3_195 := by
  apply safe_succ 9 3 s3_195 [s4_154, s4_299] (by decide) s3_195_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_154_safe
  · subst z; exact s4_299_safe
def s3_196 : State := ⟨4, 12, 80, 192, 6277101735386680764176071790128606088509996410602982019350, 2, 0, 1⟩
theorem s3_196_edges : next 3 s3_196 = [s4_156, s4_301, s4_285] := by decide
theorem s3_196_safe : Safe 10 3 s3_196 := by
  apply safe_succ 9 3 s3_196 [s4_156, s4_301, s4_285] (by decide) s3_196_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_156_safe
  · subst z; exact s4_301_safe
  · subst z; exact s4_285_safe
def s3_197 : State := ⟨4, 12, 80, 208, 411376139330301510538742635921704547185356374049361104784658710, 2, 0, 1⟩
theorem s3_197_edges : next 3 s3_197 = [s4_158, s4_303, s4_283] := by decide
theorem s3_197_safe : Safe 10 3 s3_197 := by
  apply safe_succ 9 3 s3_197 [s4_158, s4_303, s4_283] (by decide) s3_197_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_158_safe
  · subst z; exact s4_303_safe
  · subst z; exact s4_283_safe
def s3_198 : State := ⟨4, 12, 82, 128, 340282366920943299258886786321309831446, 2, 0, 0⟩
theorem s3_198_edges : next 3 s3_198 = [s4_162, s4_290, s4_294, s4_304, s4_286, s4_288, s4_296, s4_298] := by decide
theorem s3_198_safe : Safe 10 3 s3_198 := by
  apply safe_succ 9 3 s3_198 [s4_162, s4_290, s4_294, s4_304, s4_286, s4_288, s4_296, s4_298] (by decide) s3_198_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_162_safe
  · subst z; exact s4_290_safe
  · subst z; exact s4_294_safe
  · subst z; exact s4_304_safe
  · subst z; exact s4_286_safe
  · subst z; exact s4_288_safe
  · subst z; exact s4_296_safe
  · subst z; exact s4_298_safe
def s3_199 : State := ⟨4, 12, 82, 128, 340282366920944508110919424655646331158, 2, 0, 0⟩
theorem s3_199_edges : next 3 s3_199 = [s4_164, s4_291, s4_295, s4_305, s4_287, s4_289, s4_297, s4_299] := by decide
theorem s3_199_safe : Safe 10 3 s3_199 := by
  apply safe_succ 9 3 s3_199 [s4_164, s4_291, s4_295, s4_305, s4_287, s4_289, s4_297, s4_299] (by decide) s3_199_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_164_safe
  · subst z; exact s4_291_safe
  · subst z; exact s4_295_safe
  · subst z; exact s4_305_safe
  · subst z; exact s4_287_safe
  · subst z; exact s4_289_safe
  · subst z; exact s4_297_safe
  · subst z; exact s4_299_safe
def s3_200 : State := ⟨4, 12, 96, 224, 26959946667150639794667015087359913040637311048536658170206926999830, 2, 0, 1⟩
theorem s3_200_edges : next 3 s3_200 = [s4_201, s4_307, s4_309] := by decide
theorem s3_200_safe : Safe 10 3 s3_200 := by
  apply safe_succ 9 3 s3_200 [s4_201, s4_307, s4_309] (by decide) s3_200_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_201_safe
  · subst z; exact s4_307_safe
  · subst z; exact s4_309_safe
def s3_201 : State := ⟨4, 12, 193, 129, 12554203470773361528692425947178148222613281455301378248982, 2, 0, 1⟩
theorem s3_201_edges : next 3 s3_201 = [s4_211] := by decide
theorem s3_201_safe : Safe 10 3 s3_201 := by
  apply safe_succ 9 3 s3_201 [s4_211] (by decide) s3_201_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_211_safe
def s3_202 : State := ⟨4, 12, 194, 130, 25108406941546723057044569527435357981744741559092983697686, 2, 0, 1⟩
theorem s3_202_edges : next 3 s3_202 = [s4_213, s4_313, s4_310, s4_311] := by decide
theorem s3_202_safe : Safe 10 3 s3_202 := by
  apply safe_succ 9 3 s3_202 [s4_213, s4_313, s4_310, s4_311] (by decide) s3_202_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_213_safe
  · subst z; exact s4_313_safe
  · subst z; exact s4_310_safe
  · subst z; exact s4_311_safe
def s3_203 : State := ⟨4, 12, 208, 144, 411376139330301510561043381120235170325683166502394837115932950, 2, 0, 1⟩
theorem s3_203_edges : next 3 s3_203 = [s4_215, s4_315] := by decide
theorem s3_203_safe : Safe 10 3 s3_203 := by
  apply safe_succ 9 3 s3_203 [s4_215, s4_315] (by decide) s3_203_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_215_safe
  · subst z; exact s4_315_safe
def s3_204 : State := ⟨4, 104, 96, 224, 26959946667150639794667015087359913060919720652188328594154178281750, 2, 0, 1⟩
theorem s3_204_edges : next 3 s3_204 = [s4_460, s4_457, s4_494, s4_327, s4_204, s4_328, s4_325, s4_324, s4_326] := by decide
theorem s3_204_safe : Safe 10 3 s3_204 := by
  apply safe_succ 9 3 s3_204 [s4_460, s4_457, s4_494, s4_327, s4_204, s4_328, s4_325, s4_324, s4_326] (by decide) s3_204_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s4_460_safe
  · subst z; exact s4_457_safe
  · subst z; exact s4_494_safe
  · subst z; exact s4_327_safe
  · subst z; exact s4_204_safe
  · subst z; exact s4_328_safe
  · subst z; exact s4_325_safe
  · subst z; exact s4_324_safe
  · subst z; exact s4_326_safe
def s3_205 : State := ⟨4, 108, 96, 128, 340282711801129888074482896206588608790, 2, 0, 0⟩
theorem s3_205_edges : next 3 s3_205 = [s4_327] := by decide
theorem s3_205_safe : Safe 10 3 s3_205 := by
  apply safe_succ 9 3 s3_205 [s4_327] (by decide) s3_205_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_327_safe
def s3_206 : State := ⟨4, 120, 96, 128, 341611615278361145520659920110848377110, 2, 0, 0⟩
theorem s3_206_edges : next 3 s3_206 = [s4_328] := by decide
theorem s3_206_safe : Safe 10 3 s3_206 := by
  apply safe_succ 9 3 s3_206 [s4_328] (by decide) s3_206_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_328_safe
def s3_207 : State := ⟨4, 140, 65, 132, 1399581375145819900224915100599088077406486, 2, 0, 1⟩
theorem s3_207_edges : next 3 s3_207 = [s4_73, s4_329] := by decide
theorem s3_207_safe : Safe 10 3 s3_207 := by
  apply safe_succ 9 3 s3_207 [s4_73, s4_329] (by decide) s3_207_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_73_safe
  · subst z; exact s4_329_safe
def s3_208 : State := ⟨4, 140, 66, 132, 1399581375145819900224951994087235496509718, 2, 0, 1⟩
theorem s3_208_edges : next 3 s3_208 = [s4_93, s4_330, s4_331] := by decide
theorem s3_208_safe : Safe 10 3 s3_208 := by
  apply safe_succ 9 3 s3_208 [s4_93, s4_330, s4_331] (by decide) s3_208_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_93_safe
  · subst z; exact s4_330_safe
  · subst z; exact s4_331_safe
def s3_209 : State := ⟨4, 140, 80, 132, 1399581375145819901433804026725569833009430, 2, 0, 1⟩
theorem s3_209_edges : next 3 s3_209 = [s4_145, s4_332] := by decide
theorem s3_209_safe : Safe 10 3 s3_209 := by
  apply safe_succ 9 3 s3_209 [s4_145, s4_332] (by decide) s3_209_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_145_safe
  · subst z; exact s4_332_safe
def s3_210 : State := ⟨4, 170, 64, 162, 1502423683177869611747992700349674263987535499821334, 2, 0, 1⟩
theorem s3_210_edges : next 3 s3_210 = [s4_22, s4_335] := by decide
theorem s3_210_safe : Safe 10 3 s3_210 := by
  apply safe_succ 9 3 s3_210 [s4_22, s4_335] (by decide) s3_210_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_22_safe
  · subst z; exact s4_335_safe
def s3_211 : State := ⟨4, 170, 64, 162, 1503885184813839385198512631328537048577464359518486, 2, 0, 1⟩
theorem s3_211_edges : next 3 s3_211 = [s4_23, s4_336] := by decide
theorem s3_211_safe : Safe 10 3 s3_211 := by
  apply safe_succ 9 3 s3_211 [s4_23, s4_336] (by decide) s3_211_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_23_safe
  · subst z; exact s4_336_safe
def s3_212 : State := ⟨12, 8, 64, 131, 3743106036130323098115567425827454914838, 1, 0, 1⟩
theorem s3_212_edges : next 3 s3_212 = [s4_0, s4_343] := by decide
theorem s3_212_safe : Safe 10 3 s3_212 := by
  apply safe_succ 9 3 s3_212 [s4_0, s4_343] (by decide) s3_212_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_0_safe
  · subst z; exact s4_343_safe
def s3_213 : State := ⟨12, 8, 64, 131, 4423670769972200025042316640690991337750, 1, 0, 1⟩
theorem s3_213_edges : next 3 s3_213 = [s4_2, s4_344] := by decide
theorem s3_213_safe : Safe 10 3 s3_213 := by
  apply safe_succ 9 3 s3_213 [s4_2, s4_344] (by decide) s3_213_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_2_safe
  · subst z; exact s4_344_safe
def s3_214 : State := ⟨12, 8, 64, 146, 89204682205957097258460208410374682869567766, 1, 0, 1⟩
theorem s3_214_edges : next 3 s3_214 = [s4_4, s4_427, s4_355, s4_363, s4_349] := by decide
theorem s3_214_safe : Safe 10 3 s3_214 := by
  apply safe_succ 9 3 s3_214 [s4_4, s4_427, s4_355, s4_363, s4_349] (by decide) s3_214_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_4_safe
  · subst z; exact s4_427_safe
  · subst z; exact s4_355_safe
  · subst z; exact s4_363_safe
  · subst z; exact s4_349_safe
def s3_215 : State := ⟨12, 8, 64, 146, 111504066275020036646142073184593317302702358, 1, 0, 1⟩
theorem s3_215_edges : next 3 s3_215 = [s4_7, s4_428, s4_356, s4_364, s4_350] := by decide
theorem s3_215_safe : Safe 10 3 s3_215 := by
  apply safe_succ 9 3 s3_215 [s4_7, s4_428, s4_356, s4_364, s4_350] (by decide) s3_215_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_7_safe
  · subst z; exact s4_428_safe
  · subst z; exact s4_356_safe
  · subst z; exact s4_364_safe
  · subst z; exact s4_350_safe
def s3_216 : State := ⟨12, 8, 64, 161, 2923003275682652937170185055841136605685174309142, 1, 0, 1⟩
theorem s3_216_edges : next 3 s3_216 = [s4_12, s4_345] := by decide
theorem s3_216_safe : Safe 10 3 s3_216 := by
  apply safe_succ 9 3 s3_216 [s4_12, s4_345] (by decide) s3_216_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_12_safe
  · subst z; exact s4_345_safe
def s3_217 : State := ⟨12, 8, 64, 161, 4384504912332991121531992961630670410477570429206, 1, 0, 1⟩
theorem s3_217_edges : next 3 s3_217 = [s4_14, s4_346] := by decide
theorem s3_217_safe : Safe 10 3 s3_217 := by
  apply safe_succ 9 3 s3_217 [s4_14, s4_346] (by decide) s3_217_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_14_safe
  · subst z; exact s4_346_safe
def s3_218 : State := ⟨12, 8, 64, 162, 5846006551025023507419431648200451859860575818006, 1, 0, 1⟩
theorem s3_218_edges : next 3 s3_218 = [s4_17, s4_357, s4_365, s4_347] := by decide
theorem s3_218_safe : Safe 10 3 s3_218 := by
  apply safe_succ 9 3 s3_218 [s4_17, s4_357, s4_365, s4_347] (by decide) s3_218_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_17_safe
  · subst z; exact s4_357_safe
  · subst z; exact s4_365_safe
  · subst z; exact s4_347_safe
def s3_219 : State := ⟨12, 8, 64, 162, 7307508186994796957939362627063236449789435515158, 1, 0, 1⟩
theorem s3_219_edges : next 3 s3_219 = [s4_20, s4_358, s4_366, s4_348] := by decide
theorem s3_219_safe : Safe 10 3 s3_219 := by
  apply safe_succ 9 3 s3_219 [s4_20, s4_358, s4_366, s4_348] (by decide) s3_219_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_20_safe
  · subst z; exact s4_358_safe
  · subst z; exact s4_366_safe
  · subst z; exact s4_348_safe
def s3_220 : State := ⟨12, 8, 64, 176, 95780971326419139128294233276893524070171066415255830, 1, 0, 1⟩
theorem s3_220_edges : next 3 s3_220 = [s4_32, s4_359, s4_367] := by decide
theorem s3_220_safe : Safe 10 3 s3_220 := by
  apply safe_succ 9 3 s3_220 [s4_32, s4_359, s4_367] (by decide) s3_220_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_32_safe
  · subst z; exact s4_359_safe
  · subst z; exact s4_367_safe
def s3_221 : State := ⟨12, 8, 64, 176, 95782432805755724832681813820190522080542360841818390, 1, 0, 1⟩
theorem s3_221_edges : next 3 s3_221 = [s4_34, s4_360, s4_368] := by decide
theorem s3_221_safe : Safe 10 3 s3_221 := by
  apply safe_succ 9 3 s3_221 [s4_34, s4_360, s4_368] (by decide) s3_221_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_34_safe
  · subst z; exact s4_360_safe
  · subst z; exact s4_368_safe
def s3_222 : State := ⟨12, 8, 64, 193, 12554203470773361528692425947178148222613281455301378248982, 1, 0, 1⟩
theorem s3_222_edges : next 3 s3_222 = [s4_36] := by decide
theorem s3_222_safe : Safe 10 3 s3_222 := by
  apply safe_succ 9 3 s3_222 [s4_36] (by decide) s3_222_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_36_safe
def s3_223 : State := ⟨12, 8, 64, 193, 18831305206160042291847650636543937711788887684901876338966, 1, 0, 1⟩
theorem s3_223_edges : next 3 s3_223 = [s4_38] := by decide
theorem s3_223_safe : Safe 10 3 s3_223 := by
  apply safe_succ 9 3 s3_223 [s4_38] (by decide) s3_223_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_38_safe
def s3_224 : State := ⟨12, 8, 64, 194, 25108406941546723057044569527435357981744741559092983697686, 1, 0, 1⟩
theorem s3_224_edges : next 3 s3_224 = [s4_40, s4_351] := by decide
theorem s3_224_safe : Safe 10 3 s3_224 := by
  apply safe_succ 9 3 s3_224 [s4_40, s4_351] (by decide) s3_224_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_40_safe
  · subst z; exact s4_351_safe
def s3_225 : State := ⟨12, 8, 64, 194, 31385508676933403819519229482959270543993598573829945364758, 1, 0, 1⟩
theorem s3_225_edges : next 3 s3_225 = [s4_42, s4_352] := by decide
theorem s3_225_safe : Safe 10 3 s3_225 := by
  apply safe_succ 9 3 s3_225 [s4_42, s4_352] (by decide) s3_225_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_42_safe
  · subst z; exact s4_352_safe
def s3_226 : State := ⟨12, 8, 64, 208, 411376139330301510561043381120235170325683166502394837115932950, 1, 0, 1⟩
theorem s3_226_edges : next 3 s3_226 = [s4_44, s4_353] := by decide
theorem s3_226_safe : Safe 10 3 s3_226 := by
  apply safe_succ 9 3 s3_226 [s4_44, s4_353] (by decide) s3_226_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_44_safe
  · subst z; exact s4_353_safe
def s3_227 : State := ⟨12, 8, 64, 208, 411382416432036897219506471711127754850563550585190939644465430, 1, 0, 1⟩
theorem s3_227_edges : next 3 s3_227 = [s4_46, s4_354] := by decide
theorem s3_227_safe : Safe 10 3 s3_227 := by
  apply safe_succ 9 3 s3_227 [s4_46, s4_354] (by decide) s3_227_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_46_safe
  · subst z; exact s4_354_safe
def s3_228 : State := ⟨12, 8, 64, 224, 26959946667150639796128516724690815958761767718738676852269315592470, 1, 0, 1⟩
theorem s3_228_edges : next 3 s3_228 = [s4_57, s4_361, s4_371, s4_395] := by decide
theorem s3_228_safe : Safe 10 3 s3_228 := by
  apply safe_succ 9 3 s3_228 [s4_57, s4_361, s4_371, s4_395] (by decide) s3_228_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_57_safe
  · subst z; exact s4_361_safe
  · subst z; exact s4_371_safe
  · subst z; exact s4_395_safe
def s3_229 : State := ⟨12, 8, 64, 224, 26959946673427741530053695851195702463765749302124749277077417562390, 1, 0, 1⟩
theorem s3_229_edges : next 3 s3_229 = [s4_61, s4_362, s4_372, s4_396] := by decide
theorem s3_229_safe : Safe 10 3 s3_229 := by
  apply safe_succ 9 3 s3_229 [s4_61, s4_362, s4_372, s4_396] (by decide) s3_229_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_61_safe
  · subst z; exact s4_362_safe
  · subst z; exact s4_372_safe
  · subst z; exact s4_396_safe
def s3_230 : State := ⟨12, 8, 65, 129, 1020847100762815390445464054520728326422, 1, 0, 1⟩
theorem s3_230_edges : next 3 s3_230 = [s4_67, s4_373] := by decide
theorem s3_230_safe : Safe 10 3 s3_230 := by
  apply safe_succ 9 3 s3_230 [s4_67, s4_373] (by decide) s3_230_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_67_safe
  · subst z; exact s4_373_safe
def s3_231 : State := ⟨12, 8, 65, 130, 1701411834604692317372213269384264749334, 1, 0, 1⟩
theorem s3_231_edges : next 3 s3_231 = [s4_69, s4_375, s4_355, s4_357] := by decide
theorem s3_231_safe : Safe 10 3 s3_231 := by
  apply safe_succ 9 3 s3_231 [s4_69, s4_375, s4_355, s4_357] (by decide) s3_231_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_69_safe
  · subst z; exact s4_375_safe
  · subst z; exact s4_355_safe
  · subst z; exact s4_357_safe
def s3_232 : State := ⟨12, 8, 65, 132, 5784800237655953878932708558565483286806, 1, 0, 1⟩
theorem s3_232_edges : next 3 s3_232 = [s4_71, s4_377] := by decide
theorem s3_232_safe : Safe 10 3 s3_232 := by
  apply safe_succ 9 3 s3_232 [s4_71, s4_377] (by decide) s3_232_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_71_safe
  · subst z; exact s4_377_safe
def s3_233 : State := ⟨12, 8, 65, 136, 87452568298681185110142614342189854036246, 1, 0, 1⟩
theorem s3_233_edges : next 3 s3_233 = [s4_74, s4_379] := by decide
theorem s3_233_safe : Safe 10 3 s3_233 := by
  apply safe_succ 9 3 s3_233 [s4_74, s4_379] (by decide) s3_233_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_74_safe
  · subst z; exact s4_379_safe
def s3_234 : State := ⟨12, 8, 65, 140, 1394136857275084884809501106880179786027286, 1, 0, 1⟩
theorem s3_234_edges : next 3 s3_234 = [s4_77, s4_381] := by decide
theorem s3_234_safe : Safe 10 3 s3_234 := by
  apply safe_succ 9 3 s3_234 [s4_77, s4_381] (by decide) s3_234_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_77_safe
  · subst z; exact s4_381_safe
def s3_235 : State := ⟨12, 8, 65, 144, 22301085480897544079999236987488018697883926, 1, 0, 1⟩
theorem s3_235_edges : next 3 s3_235 = [s4_79, s4_383, s4_356, s4_359] := by decide
theorem s3_235_safe : Safe 10 3 s3_235 := by
  apply safe_succ 9 3 s3_235 [s4_79, s4_383, s4_356, s4_359] (by decide) s3_235_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_79_safe
  · subst z; exact s4_383_safe
  · subst z; exact s4_356_safe
  · subst z; exact s4_359_safe
def s3_236 : State := ⟨12, 8, 65, 160, 1461501637671185285124623296234997859313124446486, 1, 0, 1⟩
theorem s3_236_edges : next 3 s3_236 = [s4_81, s4_385, s4_358, s4_360] := by decide
theorem s3_236_safe : Safe 10 3 s3_236 := by
  apply safe_succ 9 3 s3_236 [s4_81, s4_385, s4_358, s4_360] (by decide) s3_236_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_81_safe
  · subst z; exact s4_385_safe
  · subst z; exact s4_358_safe
  · subst z; exact s4_360_safe
def s3_237 : State := ⟨12, 8, 65, 192, 6277101735386680764176071790128604879621070284121226416406, 1, 0, 1⟩
theorem s3_237_edges : next 3 s3_237 = [s4_83, s4_387, s4_362] := by decide
theorem s3_237_safe : Safe 10 3 s3_237 := by
  apply safe_succ 9 3 s3_237 [s4_83, s4_387, s4_362] (by decide) s3_237_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_83_safe
  · subst z; exact s4_387_safe
  · subst z; exact s4_362_safe
def s3_238 : State := ⟨12, 8, 65, 193, 12554203470773361528011861213336271295723425728585260929302, 1, 0, 1⟩
theorem s3_238_edges : next 3 s3_238 = [s4_85, s4_389] := by decide
theorem s3_238_safe : Safe 10 3 s3_238 := by
  apply safe_succ 9 3 s3_238 [s4_85, s4_389] (by decide) s3_238_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_85_safe
  · subst z; exact s4_389_safe
def s3_239 : State := ⟨12, 8, 66, 129, 1020847100762815390482357542668147429654, 1, 0, 1⟩
theorem s3_239_edges : next 3 s3_239 = [s4_87, s4_374, s4_397] := by decide
theorem s3_239_safe : Safe 10 3 s3_239 := by
  apply safe_succ 9 3 s3_239 [s4_87, s4_374, s4_397] (by decide) s3_239_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_87_safe
  · subst z; exact s4_374_safe
  · subst z; exact s4_397_safe
def s3_240 : State := ⟨12, 8, 66, 130, 1701411834604692317409106757531683852566, 1, 0, 1⟩
theorem s3_240_edges : next 3 s3_240 = [s4_89, s4_376, s4_399, s4_363, s4_365] := by decide
theorem s3_240_safe : Safe 10 3 s3_240 := by
  apply safe_succ 9 3 s3_240 [s4_89, s4_376, s4_399, s4_363, s4_365] (by decide) s3_240_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_89_safe
  · subst z; exact s4_376_safe
  · subst z; exact s4_399_safe
  · subst z; exact s4_363_safe
  · subst z; exact s4_365_safe
def s3_241 : State := ⟨12, 8, 66, 132, 5784800237655953878969602046712902390038, 1, 0, 1⟩
theorem s3_241_edges : next 3 s3_241 = [s4_91, s4_378, s4_401] := by decide
theorem s3_241_safe : Safe 10 3 s3_241 := by
  apply safe_succ 9 3 s3_241 [s4_91, s4_378, s4_401] (by decide) s3_241_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_91_safe
  · subst z; exact s4_378_safe
  · subst z; exact s4_401_safe
def s3_242 : State := ⟨12, 8, 66, 136, 87452568298681185110179507830337273139478, 1, 0, 1⟩
theorem s3_242_edges : next 3 s3_242 = [s4_94, s4_380, s4_403] := by decide
theorem s3_242_safe : Safe 10 3 s3_242 := by
  apply safe_succ 9 3 s3_242 [s4_94, s4_380, s4_403] (by decide) s3_242_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_94_safe
  · subst z; exact s4_380_safe
  · subst z; exact s4_403_safe
def s3_243 : State := ⟨12, 8, 66, 140, 1394136857275084884809538000368327205130518, 1, 0, 1⟩
theorem s3_243_edges : next 3 s3_243 = [s4_97, s4_382, s4_405] := by decide
theorem s3_243_safe : Safe 10 3 s3_243 := by
  apply safe_succ 9 3 s3_243 [s4_97, s4_382, s4_405] (by decide) s3_243_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_97_safe
  · subst z; exact s4_382_safe
  · subst z; exact s4_405_safe
def s3_244 : State := ⟨12, 8, 66, 144, 22301085480897544079999273880976166116987158, 1, 0, 1⟩
theorem s3_244_edges : next 3 s3_244 = [s4_99, s4_425, s4_384, s4_407, s4_369, s4_364, s4_367] := by decide
theorem s3_244_safe : Safe 10 3 s3_244 := by
  apply safe_succ 9 3 s3_244 [s4_99, s4_425, s4_384, s4_407, s4_369, s4_364, s4_367] (by decide) s3_244_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s4_99_safe
  · subst z; exact s4_425_safe
  · subst z; exact s4_384_safe
  · subst z; exact s4_407_safe
  · subst z; exact s4_369_safe
  · subst z; exact s4_364_safe
  · subst z; exact s4_367_safe
def s3_245 : State := ⟨12, 8, 66, 160, 1461501637671185285124623296271891347460543549718, 1, 0, 1⟩
theorem s3_245_edges : next 3 s3_245 = [s4_101, s4_386, s4_409, s4_366, s4_368] := by decide
theorem s3_245_safe : Safe 10 3 s3_245 := by
  apply safe_succ 9 3 s3_245 [s4_101, s4_386, s4_409, s4_366, s4_368] (by decide) s3_245_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_101_safe
  · subst z; exact s4_386_safe
  · subst z; exact s4_409_safe
  · subst z; exact s4_366_safe
  · subst z; exact s4_368_safe
def s3_246 : State := ⟨12, 8, 66, 192, 6277101735386680764176071790128604879657963772268645519638, 1, 0, 1⟩
theorem s3_246_edges : next 3 s3_246 = [s4_103, s4_388, s4_411, s4_372] := by decide
theorem s3_246_safe : Safe 10 3 s3_246 := by
  apply safe_succ 9 3 s3_246 [s4_103, s4_388, s4_411, s4_372] (by decide) s3_246_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_103_safe
  · subst z; exact s4_388_safe
  · subst z; exact s4_411_safe
  · subst z; exact s4_372_safe
def s3_247 : State := ⟨12, 8, 66, 194, 25108406941546723055683440059751604127965030105660749058326, 1, 0, 1⟩
theorem s3_247_edges : next 3 s3_247 = [s4_105, s4_390, s4_413, s4_370] := by decide
theorem s3_247_safe : Safe 10 3 s3_247 := by
  apply safe_succ 9 3 s3_247 [s4_105, s4_390, s4_413, s4_370] (by decide) s3_247_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_105_safe
  · subst z; exact s4_390_safe
  · subst z; exact s4_413_safe
  · subst z; exact s4_370_safe
def s3_248 : State := ⟨12, 8, 67, 128, 340282366920938463666288792246868316438, 1, 0, 0⟩
theorem s3_248_edges : next 3 s3_248 = [s4_111, s4_381, s4_379, s4_391, s4_373, s4_375, s4_383, s4_385] := by decide
theorem s3_248_safe : Safe 10 3 s3_248 := by
  apply safe_succ 9 3 s3_248 [s4_111, s4_381, s4_379, s4_391, s4_373, s4_375, s4_383, s4_385] (by decide) s3_248_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_111_safe
  · subst z; exact s4_381_safe
  · subst z; exact s4_379_safe
  · subst z; exact s4_391_safe
  · subst z; exact s4_373_safe
  · subst z; exact s4_375_safe
  · subst z; exact s4_383_safe
  · subst z; exact s4_385_safe
def s3_249 : State := ⟨12, 8, 67, 128, 340282366920938463703182280394287419670, 1, 0, 0⟩
theorem s3_249_edges : next 3 s3_249 = [s4_113, s4_382, s4_380, s4_392, s4_374, s4_376, s4_384, s4_386] := by decide
theorem s3_249_safe : Safe 10 3 s3_249 := by
  apply safe_succ 9 3 s3_249 [s4_113, s4_382, s4_380, s4_392, s4_374, s4_376, s4_384, s4_386] (by decide) s3_249_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_113_safe
  · subst z; exact s4_382_safe
  · subst z; exact s4_380_safe
  · subst z; exact s4_392_safe
  · subst z; exact s4_374_safe
  · subst z; exact s4_376_safe
  · subst z; exact s4_384_safe
  · subst z; exact s4_386_safe
def s3_250 : State := ⟨12, 8, 80, 129, 1020847100762816599334390181002483929366, 1, 0, 1⟩
theorem s3_250_edges : next 3 s3_250 = [s4_139, s4_398] := by decide
theorem s3_250_safe : Safe 10 3 s3_250 := by
  apply safe_succ 9 3 s3_250 [s4_139, s4_398] (by decide) s3_250_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_139_safe
  · subst z; exact s4_398_safe
def s3_251 : State := ⟨12, 8, 80, 130, 1701411834604693526261139395866020352278, 1, 0, 1⟩
theorem s3_251_edges : next 3 s3_251 = [s4_141, s4_423, s4_400, s4_393] := by decide
theorem s3_251_safe : Safe 10 3 s3_251 := by
  apply safe_succ 9 3 s3_251 [s4_141, s4_423, s4_400, s4_393] (by decide) s3_251_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_141_safe
  · subst z; exact s4_423_safe
  · subst z; exact s4_400_safe
  · subst z; exact s4_393_safe
def s3_252 : State := ⟨12, 8, 80, 132, 5784800237655955087821634685047238889750, 1, 0, 1⟩
theorem s3_252_edges : next 3 s3_252 = [s4_143, s4_402] := by decide
theorem s3_252_safe : Safe 10 3 s3_252 := by
  apply safe_succ 9 3 s3_252 [s4_143, s4_402] (by decide) s3_252_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_143_safe
  · subst z; exact s4_402_safe
def s3_253 : State := ⟨12, 8, 80, 136, 87452568298681186319031540468671609639190, 1, 0, 1⟩
theorem s3_253_edges : next 3 s3_253 = [s4_146, s4_404] := by decide
theorem s3_253_safe : Safe 10 3 s3_253 := by
  apply safe_succ 9 3 s3_253 [s4_146, s4_404] (by decide) s3_253_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_146_safe
  · subst z; exact s4_404_safe
def s3_254 : State := ⟨12, 8, 80, 140, 1394136857275084886018390033006661541630230, 1, 0, 1⟩
theorem s3_254_edges : next 3 s3_254 = [s4_149, s4_406] := by decide
theorem s3_254_safe : Safe 10 3 s3_254 := by
  apply safe_succ 9 3 s3_254 [s4_149, s4_406] (by decide) s3_254_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_149_safe
  · subst z; exact s4_406_safe
def s3_255 : State := ⟨12, 8, 80, 144, 22301085480897544081208125913614500453486870, 1, 0, 1⟩
theorem s3_255_edges : next 3 s3_255 = [s4_151, s4_408] := by decide
theorem s3_255_safe : Safe 10 3 s3_255 := by
  apply safe_succ 9 3 s3_255 [s4_151, s4_408] (by decide) s3_255_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_151_safe
  · subst z; exact s4_408_safe
def s3_256 : State := ⟨12, 8, 80, 160, 1461501637671185285124624505123923985794880049430, 1, 0, 1⟩
theorem s3_256_edges : next 3 s3_256 = [s4_153, s4_410] := by decide
theorem s3_256_safe : Safe 10 3 s3_256 := by
  apply safe_succ 9 3 s3_256 [s4_153, s4_410] (by decide) s3_256_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_153_safe
  · subst z; exact s4_410_safe
def s3_257 : State := ⟨12, 8, 80, 192, 6277101735386680764176071790128606088509996410602982019350, 1, 0, 1⟩
theorem s3_257_edges : next 3 s3_257 = [s4_155, s4_412, s4_396] := by decide
theorem s3_257_safe : Safe 10 3 s3_257 := by
  apply safe_succ 9 3 s3_257 [s4_155, s4_412, s4_396] (by decide) s3_257_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_155_safe
  · subst z; exact s4_412_safe
  · subst z; exact s4_396_safe
def s3_258 : State := ⟨12, 8, 80, 208, 411376139330301510538742635921704547185356374049361104784658710, 1, 0, 1⟩
theorem s3_258_edges : next 3 s3_258 = [s4_157, s4_414, s4_394] := by decide
theorem s3_258_safe : Safe 10 3 s3_258 := by
  apply safe_succ 9 3 s3_258 [s4_157, s4_414, s4_394] (by decide) s3_258_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_157_safe
  · subst z; exact s4_414_safe
  · subst z; exact s4_394_safe
def s3_259 : State := ⟨12, 8, 82, 128, 340282366920943299258886786321309831446, 1, 0, 0⟩
theorem s3_259_edges : next 3 s3_259 = [s4_161, s4_405, s4_403, s4_415, s4_397, s4_399, s4_407, s4_409] := by decide
theorem s3_259_safe : Safe 10 3 s3_259 := by
  apply safe_succ 9 3 s3_259 [s4_161, s4_405, s4_403, s4_415, s4_397, s4_399, s4_407, s4_409] (by decide) s3_259_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_161_safe
  · subst z; exact s4_405_safe
  · subst z; exact s4_403_safe
  · subst z; exact s4_415_safe
  · subst z; exact s4_397_safe
  · subst z; exact s4_399_safe
  · subst z; exact s4_407_safe
  · subst z; exact s4_409_safe
def s3_260 : State := ⟨12, 8, 82, 128, 340282366920944508110919424655646331158, 1, 0, 0⟩
theorem s3_260_edges : next 3 s3_260 = [s4_163, s4_406, s4_404, s4_416, s4_398, s4_400, s4_408, s4_410] := by decide
theorem s3_260_safe : Safe 10 3 s3_260 := by
  apply safe_succ 9 3 s3_260 [s4_163, s4_406, s4_404, s4_416, s4_398, s4_400, s4_408, s4_410] (by decide) s3_260_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_163_safe
  · subst z; exact s4_406_safe
  · subst z; exact s4_404_safe
  · subst z; exact s4_416_safe
  · subst z; exact s4_398_safe
  · subst z; exact s4_400_safe
  · subst z; exact s4_408_safe
  · subst z; exact s4_410_safe
def s3_261 : State := ⟨12, 8, 96, 224, 26959946667150639794667015087359913040637311048536658170206926999830, 1, 0, 1⟩
theorem s3_261_edges : next 3 s3_261 = [s4_200, s4_429, s4_419, s4_418, s4_420] := by decide
theorem s3_261_safe : Safe 10 3 s3_261 := by
  apply safe_succ 9 3 s3_261 [s4_200, s4_429, s4_419, s4_418, s4_420] (by decide) s3_261_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s4_200_safe
  · subst z; exact s4_429_safe
  · subst z; exact s4_419_safe
  · subst z; exact s4_418_safe
  · subst z; exact s4_420_safe
def s3_262 : State := ⟨12, 8, 193, 129, 12554203470773361528692425947178148222613281455301378248982, 1, 0, 1⟩
theorem s3_262_edges : next 3 s3_262 = [s4_210] := by decide
theorem s3_262_safe : Safe 10 3 s3_262 := by
  apply safe_succ 9 3 s3_262 [s4_210] (by decide) s3_262_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_210_safe
def s3_263 : State := ⟨12, 8, 194, 130, 25108406941546723057044569527435357981744741559092983697686, 1, 0, 1⟩
theorem s3_263_edges : next 3 s3_263 = [s4_212, s4_424, s4_421, s4_422] := by decide
theorem s3_263_safe : Safe 10 3 s3_263 := by
  apply safe_succ 9 3 s3_263 [s4_212, s4_424, s4_421, s4_422] (by decide) s3_263_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s4_212_safe
  · subst z; exact s4_424_safe
  · subst z; exact s4_421_safe
  · subst z; exact s4_422_safe
def s3_264 : State := ⟨12, 8, 208, 144, 411376139330301510561043381120235170325683166502394837115932950, 1, 0, 1⟩
theorem s3_264_edges : next 3 s3_264 = [s4_214, s4_426] := by decide
theorem s3_264_safe : Safe 10 3 s3_264 := by
  apply safe_succ 9 3 s3_264 [s4_214, s4_426] (by decide) s3_264_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_214_safe
  · subst z; exact s4_426_safe
def s3_265 : State := ⟨12, 104, 96, 128, 340282387282576229647756113050568036630, 3, 0, 0⟩
theorem s3_265_edges : next 3 s3_265 = [s4_417, s4_429] := by decide
theorem s3_265_safe : Safe 10 3 s3_265 := by
  apply safe_succ 9 3 s3_265 [s4_417, s4_429] (by decide) s3_265_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_417_safe
  · subst z; exact s4_429_safe
def s3_266 : State := ⟨68, 8, 64, 146, 89204682205957097258460503558279862222389526, 1, 0, 1⟩
theorem s3_266_edges : next 3 s3_266 = [s4_6, s4_467, s4_430] := by decide
theorem s3_266_safe : Safe 10 3 s3_266 := by
  apply safe_succ 9 3 s3_266 [s4_6, s4_467, s4_430] (by decide) s3_266_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_6_safe
  · subst z; exact s4_467_safe
  · subst z; exact s4_430_safe
def s3_267 : State := ⟨68, 8, 64, 146, 111504066275020036646142368332498496655524118, 1, 0, 1⟩
theorem s3_267_edges : next 3 s3_267 = [s4_9, s4_468, s4_431] := by decide
theorem s3_267_safe : Safe 10 3 s3_267 := by
  apply safe_succ 9 3 s3_267 [s4_9, s4_468, s4_431] (by decide) s3_267_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_9_safe
  · subst z; exact s4_468_safe
  · subst z; exact s4_431_safe
def s3_268 : State := ⟨68, 8, 64, 224, 26959946667150639796128516724690815958761767719033824757448668414230, 1, 0, 1⟩
theorem s3_268_edges : next 3 s3_268 = [s4_59] := by decide
theorem s3_268_safe : Safe 10 3 s3_268 := by
  apply safe_succ 9 3 s3_268 [s4_59] (by decide) s3_268_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_59_safe
def s3_269 : State := ⟨68, 8, 64, 224, 26959946673427741530053695851195702463765749302419897182256770384150, 1, 0, 1⟩
theorem s3_269_edges : next 3 s3_269 = [s4_63] := by decide
theorem s3_269_safe : Safe 10 3 s3_269 := by
  apply safe_succ 9 3 s3_269 [s4_63] (by decide) s3_269_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s4_63_safe
def s3_270 : State := ⟨68, 8, 96, 224, 26959946667150639794667015087359913040637311048831806075386279821590, 1, 0, 1⟩
theorem s3_270_edges : next 3 s3_270 = [s4_434, s4_433] := by decide
theorem s3_270_safe : Safe 10 3 s3_270 := by
  apply safe_succ 9 3 s3_270 [s4_434, s4_433] (by decide) s3_270_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_434_safe
  · subst z; exact s4_433_safe
def s3_271 : State := ⟨68, 104, 96, 128, 340282387282576229942904018229920858390, 3, 0, 0⟩
theorem s3_271_edges : next 3 s3_271 = [s4_432, s4_434] := by decide
theorem s3_271_safe : Safe 10 3 s3_271 := by
  apply safe_succ 9 3 s3_271 [s4_432, s4_434] (by decide) s3_271_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_432_safe
  · subst z; exact s4_434_safe
def s3_272 : State := ⟨86, 8, 82, 128, 340282366921020670511342122588491022614, 1, 0, 0⟩
theorem s3_272_edges : next 3 s3_272 = [s4_165, s4_453, s4_441, s4_451, s4_435, s4_437, s4_443, s4_445] := by decide
theorem s3_272_safe : Safe 10 3 s3_272 := by
  apply safe_succ 9 3 s3_272 [s4_165, s4_453, s4_441, s4_451, s4_435, s4_437, s4_443, s4_445] (by decide) s3_272_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_165_safe
  · subst z; exact s4_453_safe
  · subst z; exact s4_441_safe
  · subst z; exact s4_451_safe
  · subst z; exact s4_435_safe
  · subst z; exact s4_437_safe
  · subst z; exact s4_443_safe
  · subst z; exact s4_445_safe
def s3_273 : State := ⟨86, 8, 82, 128, 340282366921021879363374760922827522326, 1, 0, 0⟩
theorem s3_273_edges : next 3 s3_273 = [s4_166, s4_454, s4_442, s4_452, s4_436, s4_438, s4_444, s4_446] := by decide
theorem s3_273_safe : Safe 10 3 s3_273 := by
  apply safe_succ 9 3 s3_273 [s4_166, s4_454, s4_442, s4_452, s4_436, s4_438, s4_444, s4_446] (by decide) s3_273_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s4_166_safe
  · subst z; exact s4_454_safe
  · subst z; exact s4_442_safe
  · subst z; exact s4_452_safe
  · subst z; exact s4_436_safe
  · subst z; exact s4_438_safe
  · subst z; exact s4_444_safe
  · subst z; exact s4_446_safe
def s3_274 : State := ⟨100, 8, 96, 224, 26959946667150639794667015087359913041904961648764887571703630201110, 1, 0, 1⟩
theorem s3_274_edges : next 3 s3_274 = [s4_203, s4_457, s4_456] := by decide
theorem s3_274_safe : Safe 10 3 s3_274 := by
  apply safe_succ 9 3 s3_274 [s4_203, s4_457, s4_456] (by decide) s3_274_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_203_safe
  · subst z; exact s4_457_safe
  · subst z; exact s4_456_safe
def s3_275 : State := ⟨100, 104, 96, 128, 340282388550226829875985514547271237910, 3, 0, 0⟩
theorem s3_275_edges : next 3 s3_275 = [s4_322, s4_455, s4_457] := by decide
theorem s3_275_safe : Safe 10 3 s3_275 := by
  apply safe_succ 9 3 s3_275 [s4_322, s4_455, s4_457] (by decide) s3_275_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_322_safe
  · subst z; exact s4_455_safe
  · subst z; exact s4_457_safe
def s3_276 : State := ⟨108, 104, 96, 128, 340282711801129888074482896206588608790, 3, 0, 0⟩
theorem s3_276_edges : next 3 s3_276 = [s4_323, s4_458, s4_460] := by decide
theorem s3_276_safe : Safe 10 3 s3_276 := by
  apply safe_succ 9 3 s3_276 [s4_323, s4_458, s4_460] (by decide) s3_276_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_323_safe
  · subst z; exact s4_458_safe
  · subst z; exact s4_460_safe
def s3_277 : State := ⟨140, 8, 65, 136, 1481249143206845131456125006382712448155926, 1, 0, 1⟩
theorem s3_277_edges : next 3 s3_277 = [s4_76, s4_461] := by decide
theorem s3_277_safe : Safe 10 3 s3_277 := by
  apply safe_succ 9 3 s3_277 [s4_76, s4_461] (by decide) s3_277_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_76_safe
  · subst z; exact s4_461_safe
def s3_278 : State := ⟨140, 8, 66, 136, 1481249143206845131456161899870859867259158, 1, 0, 1⟩
theorem s3_278_edges : next 3 s3_278 = [s4_96, s4_462, s4_463] := by decide
theorem s3_278_safe : Safe 10 3 s3_278 := by
  apply safe_succ 9 3 s3_278 [s4_96, s4_462, s4_463] (by decide) s3_278_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_96_safe
  · subst z; exact s4_462_safe
  · subst z; exact s4_463_safe
def s3_279 : State := ⟨140, 8, 80, 136, 1481249143206845132665013932509194203758870, 1, 0, 1⟩
theorem s3_279_edges : next 3 s3_279 = [s4_148, s4_464] := by decide
theorem s3_279_safe : Safe 10 3 s3_279 := by
  apply safe_succ 9 3 s3_279 [s4_148, s4_464] (by decide) s3_279_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s4_148_safe
  · subst z; exact s4_464_safe
def s3_280 : State := ⟨150, 8, 64, 146, 1516452374911916978316746177859869819252310294, 1, 0, 1⟩
theorem s3_280_edges : next 3 s3_280 = [s4_469, s4_10, s4_465] := by decide
theorem s3_280_safe : Safe 10 3 s3_280 := by
  apply safe_succ 9 3 s3_280 [s4_469, s4_10, s4_465] (by decide) s3_280_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_469_safe
  · subst z; exact s4_10_safe
  · subst z; exact s4_465_safe
def s3_281 : State := ⟨150, 8, 64, 146, 1538751758980979917704428042634088453685444886, 1, 0, 1⟩
theorem s3_281_edges : next 3 s3_281 = [s4_470, s4_11, s4_466] := by decide
theorem s3_281_safe : Safe 10 3 s3_281 := by
  apply safe_succ 9 3 s3_281 [s4_470, s4_11, s4_466] (by decide) s3_281_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_470_safe
  · subst z; exact s4_11_safe
  · subst z; exact s4_466_safe
def s3_282 : State := ⟨196, 8, 64, 224, 26959946773861369296240588072568333235088411959762436388501969764630, 1, 0, 1⟩
theorem s3_282_edges : next 3 s3_282 = [] := by decide
theorem s3_282_safe : Safe 10 3 s3_282 := by
  apply safe_succ 9 3 s3_282 [] (by decide) s3_282_edges
  simp
def s3_283 : State := ⟨228, 8, 64, 224, 458319093341560876510800758117004906736956078479387836549927079575830, 1, 0, 1⟩
theorem s3_283_edges : next 3 s3_283 = [s4_65, s4_489, s4_491] := by decide
theorem s3_283_safe : Safe 10 3 s3_283 := by
  apply safe_succ 9 3 s3_283 [s4_65, s4_489, s4_491] (by decide) s3_283_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_65_safe
  · subst z; exact s4_489_safe
  · subst z; exact s4_491_safe
def s3_284 : State := ⟨228, 8, 64, 224, 458319093347837978244725937243509793241960060062773908974735181545750, 1, 0, 1⟩
theorem s3_284_edges : next 3 s3_284 = [s4_66, s4_490, s4_492] := by decide
theorem s3_284_safe : Safe 10 3 s3_284 := by
  apply safe_succ 9 3 s3_284 [s4_66, s4_490, s4_492] (by decide) s3_284_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_66_safe
  · subst z; exact s4_490_safe
  · subst z; exact s4_492_safe
def s3_285 : State := ⟨228, 8, 96, 224, 458319093341560876509339256479674003818831621809185817867864690983190, 1, 0, 1⟩
theorem s3_285_edges : next 3 s3_285 = [s4_205, s4_494, s4_493] := by decide
theorem s3_285_safe : Safe 10 3 s3_285 := by
  apply safe_succ 9 3 s3_285 [s4_205, s4_494, s4_493] (by decide) s3_285_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s4_205_safe
  · subst z; exact s4_494_safe
  · subst z; exact s4_493_safe
def s2_0 : State := ⟨4, 8, 64, 128, 340282366920938463481821351509772796694, 2, 2, 0⟩
theorem s2_0_edges : next 2 s2_0 = [s3_128, s3_9, s3_14, s3_40, s3_0, s3_5, s3_22, s3_28] := by decide
theorem s2_0_safe : Safe 11 2 s2_0 := by
  apply safe_succ 10 2 s2_0 [s3_128, s3_9, s3_14, s3_40, s3_0, s3_5, s3_22, s3_28] (by decide) s2_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_128_safe
  · subst z; exact s3_9_safe
  · subst z; exact s3_14_safe
  · subst z; exact s3_40_safe
  · subst z; exact s3_0_safe
  · subst z; exact s3_5_safe
  · subst z; exact s3_22_safe
  · subst z; exact s3_28_safe
def s2_1 : State := ⟨4, 8, 64, 128, 340282366920938463481821351509772800278, 1, 1, 0⟩
theorem s2_1_edges : next 2 s2_1 = [s3_52, s3_64, s3_100, s3_129, s3_10, s3_15, s3_41, s3_1, s3_6, s3_23, s3_29] := by decide
theorem s2_1_safe : Safe 11 2 s2_1 := by
  apply safe_succ 10 2 s2_1 [s3_52, s3_64, s3_100, s3_129, s3_10, s3_15, s3_41, s3_1, s3_6, s3_23, s3_29] (by decide) s2_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_52_safe
  · subst z; exact s3_64_safe
  · subst z; exact s3_100_safe
  · subst z; exact s3_129_safe
  · subst z; exact s3_10_safe
  · subst z; exact s3_15_safe
  · subst z; exact s3_41_safe
  · subst z; exact s3_1_safe
  · subst z; exact s3_6_safe
  · subst z; exact s3_23_safe
  · subst z; exact s3_29_safe
def s2_2 : State := ⟨4, 8, 64, 128, 340282366920938463481821351509772800278, 2, 2, 0⟩
theorem s2_2_edges : next 2 s2_2 = [s3_53, s3_65, s3_101, s3_130, s3_11, s3_16, s3_42, s3_2, s3_7, s3_24, s3_30] := by decide
theorem s2_2_safe : Safe 11 2 s2_2 := by
  apply safe_succ 10 2 s2_2 [s3_53, s3_65, s3_101, s3_130, s3_11, s3_16, s3_42, s3_2, s3_7, s3_24, s3_30] (by decide) s2_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_53_safe
  · subst z; exact s3_65_safe
  · subst z; exact s3_101_safe
  · subst z; exact s3_130_safe
  · subst z; exact s3_11_safe
  · subst z; exact s3_16_safe
  · subst z; exact s3_42_safe
  · subst z; exact s3_2_safe
  · subst z; exact s3_7_safe
  · subst z; exact s3_24_safe
  · subst z; exact s3_30_safe
def s2_3 : State := ⟨4, 8, 64, 128, 340282366920938463776969256689125622038, 1, 1, 0⟩
theorem s2_3_edges : next 2 s2_3 = [s3_131, s3_12, s3_17, s3_43, s3_3, s3_8, s3_25, s3_31] := by decide
theorem s2_3_safe : Safe 11 2 s2_3 := by
  apply safe_succ 10 2 s2_3 [s3_131, s3_12, s3_17, s3_43, s3_3, s3_8, s3_25, s3_31] (by decide) s2_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_131_safe
  · subst z; exact s3_12_safe
  · subst z; exact s3_17_safe
  · subst z; exact s3_43_safe
  · subst z; exact s3_3_safe
  · subst z; exact s3_8_safe
  · subst z; exact s3_25_safe
  · subst z; exact s3_31_safe
def s2_4 : State := ⟨4, 8, 64, 131, 3743106036130323098115567425827454910742, 0, 0, 1⟩
theorem s2_4_edges : next 2 s2_4 = [s3_212, s3_151, s3_32] := by decide
theorem s2_4_safe : Safe 11 2 s2_4 := by
  apply safe_succ 10 2 s2_4 [s3_212, s3_151, s3_32] (by decide) s2_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_212_safe
  · subst z; exact s3_151_safe
  · subst z; exact s3_32_safe
def s2_5 : State := ⟨4, 8, 64, 131, 4423670769972200025042316640690991333654, 0, 0, 1⟩
theorem s2_5_edges : next 2 s2_5 = [s3_213, s3_152, s3_33] := by decide
theorem s2_5_safe : Safe 11 2 s2_5 := by
  apply safe_succ 10 2 s2_5 [s3_213, s3_152, s3_33] (by decide) s2_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_213_safe
  · subst z; exact s3_152_safe
  · subst z; exact s3_33_safe
def s2_6 : State := ⟨4, 8, 64, 137, 175245418964283308683656369571438633484566, 0, 0, 1⟩
theorem s2_6_edges : next 2 s2_6 = [] := by decide
theorem s2_6_safe : Safe 11 2 s2_6 := by
  apply safe_succ 10 2 s2_6 [] (by decide) s2_6_edges
  simp
def s2_7 : State := ⟨4, 8, 64, 137, 261677140162201678403353519859107759194390, 0, 0, 1⟩
theorem s2_7_edges : next 2 s2_7 = [] := by decide
theorem s2_7_safe : Safe 11 2 s2_7 := by
  apply safe_succ 10 2 s2_7 [] (by decide) s2_7_edges
  simp
def s2_8 : State := ⟨4, 8, 64, 140, 1399581375145819900224878207110940658303254, 0, 0, 1⟩
theorem s2_8_edges : next 2 s2_8 = [s3_54, s3_66, s3_102] := by decide
theorem s2_8_safe : Safe 11 2 s2_8 := by
  apply safe_succ 10 2 s2_8 [s3_54, s3_66, s3_102] (by decide) s2_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_54_safe
  · subst z; exact s3_66_safe
  · subst z; exact s3_102_safe
def s2_9 : State := ⟨4, 8, 64, 140, 1481249143206845131456088112894565029052694, 0, 0, 1⟩
theorem s2_9_edges : next 2 s2_9 = [s3_55, s3_67, s3_103] := by decide
theorem s2_9_safe : Safe 11 2 s2_9 := by
  apply safe_succ 10 2 s2_9 [s3_55, s3_67, s3_103] (by decide) s2_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_55_safe
  · subst z; exact s3_67_safe
  · subst z; exact s3_103_safe
def s2_10 : State := ⟨4, 8, 64, 146, 89204682205957097258460208410374682869563670, 0, 0, 1⟩
theorem s2_10_edges : next 2 s2_10 = [s3_214, s3_266, s3_280, s3_153, s3_96, s3_144, s3_56, s3_68, s3_26, s3_46] := by decide
theorem s2_10_safe : Safe 11 2 s2_10 := by
  apply safe_succ 10 2 s2_10 [s3_214, s3_266, s3_280, s3_153, s3_96, s3_144, s3_56, s3_68, s3_26, s3_46] (by decide) s2_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_214_safe
  · subst z; exact s3_266_safe
  · subst z; exact s3_280_safe
  · subst z; exact s3_153_safe
  · subst z; exact s3_96_safe
  · subst z; exact s3_144_safe
  · subst z; exact s3_56_safe
  · subst z; exact s3_68_safe
  · subst z; exact s3_26_safe
  · subst z; exact s3_46_safe
def s2_11 : State := ⟨4, 8, 64, 146, 111504066275020036646142073184593317302698262, 0, 0, 1⟩
theorem s2_11_edges : next 2 s2_11 = [s3_215, s3_267, s3_281, s3_154, s3_97, s3_145, s3_57, s3_69, s3_27, s3_47] := by decide
theorem s2_11_safe : Safe 11 2 s2_11 := by
  apply safe_succ 10 2 s2_11 [s3_215, s3_267, s3_281, s3_154, s3_97, s3_145, s3_57, s3_69, s3_27, s3_47] (by decide) s2_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_215_safe
  · subst z; exact s3_267_safe
  · subst z; exact s3_281_safe
  · subst z; exact s3_154_safe
  · subst z; exact s3_97_safe
  · subst z; exact s3_145_safe
  · subst z; exact s3_57_safe
  · subst z; exact s3_69_safe
  · subst z; exact s3_27_safe
  · subst z; exact s3_47_safe
def s2_12 : State := ⟨4, 8, 64, 161, 2923003275682652937170185055841136605685174305046, 0, 0, 1⟩
theorem s2_12_edges : next 2 s2_12 = [s3_216, s3_155, s3_34] := by decide
theorem s2_12_safe : Safe 11 2 s2_12 := by
  apply safe_succ 10 2 s2_12 [s3_216, s3_155, s3_34] (by decide) s2_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_216_safe
  · subst z; exact s3_155_safe
  · subst z; exact s3_34_safe
def s2_13 : State := ⟨4, 8, 64, 161, 4384504912332991121531992961630670410477570425110, 0, 0, 1⟩
theorem s2_13_edges : next 2 s2_13 = [s3_217, s3_156, s3_35] := by decide
theorem s2_13_safe : Safe 11 2 s2_13 := by
  apply safe_succ 10 2 s2_13 [s3_217, s3_156, s3_35] (by decide) s2_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_217_safe
  · subst z; exact s3_156_safe
  · subst z; exact s3_35_safe
def s2_14 : State := ⟨4, 8, 64, 162, 5846006551025023507419431648200451859860575813910, 0, 0, 1⟩
theorem s2_14_edges : next 2 s2_14 = [s3_218, s3_157, s3_210, s3_146, s3_58, s3_70, s3_38, s3_36] := by decide
theorem s2_14_safe : Safe 11 2 s2_14 := by
  apply safe_succ 10 2 s2_14 [s3_218, s3_157, s3_210, s3_146, s3_58, s3_70, s3_38, s3_36] (by decide) s2_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_218_safe
  · subst z; exact s3_157_safe
  · subst z; exact s3_210_safe
  · subst z; exact s3_146_safe
  · subst z; exact s3_58_safe
  · subst z; exact s3_70_safe
  · subst z; exact s3_38_safe
  · subst z; exact s3_36_safe
def s2_15 : State := ⟨4, 8, 64, 162, 7307508186994796957939362627063236449789435511062, 0, 0, 1⟩
theorem s2_15_edges : next 2 s2_15 = [s3_219, s3_158, s3_211, s3_147, s3_59, s3_71, s3_39, s3_37] := by decide
theorem s2_15_safe : Safe 11 2 s2_15 := by
  apply safe_succ 10 2 s2_15 [s3_219, s3_158, s3_211, s3_147, s3_59, s3_71, s3_39, s3_37] (by decide) s2_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_219_safe
  · subst z; exact s3_158_safe
  · subst z; exact s3_211_safe
  · subst z; exact s3_147_safe
  · subst z; exact s3_59_safe
  · subst z; exact s3_71_safe
  · subst z; exact s3_39_safe
  · subst z; exact s3_37_safe
def s2_16 : State := ⟨4, 8, 64, 176, 95780971326419139128294233276893524070171066415251734, 0, 0, 1⟩
theorem s2_16_edges : next 2 s2_16 = [s3_220, s3_159, s3_60, s3_72] := by decide
theorem s2_16_safe : Safe 11 2 s2_16 := by
  apply safe_succ 10 2 s2_16 [s3_220, s3_159, s3_60, s3_72] (by decide) s2_16_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_220_safe
  · subst z; exact s3_159_safe
  · subst z; exact s3_60_safe
  · subst z; exact s3_72_safe
def s2_17 : State := ⟨4, 8, 64, 176, 95782432805755724832681813820190522080542360841814294, 0, 0, 1⟩
theorem s2_17_edges : next 2 s2_17 = [s3_221, s3_160, s3_61, s3_73] := by decide
theorem s2_17_safe : Safe 11 2 s2_17 := by
  apply safe_succ 10 2 s2_17 [s3_221, s3_160, s3_61, s3_73] (by decide) s2_17_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_221_safe
  · subst z; exact s3_160_safe
  · subst z; exact s3_61_safe
  · subst z; exact s3_73_safe
def s2_18 : State := ⟨4, 8, 64, 193, 12554203470773361528692425947178148222613281455301378244886, 0, 0, 1⟩
theorem s2_18_edges : next 2 s2_18 = [s3_222, s3_161] := by decide
theorem s2_18_safe : Safe 11 2 s2_18 := by
  apply safe_succ 10 2 s2_18 [s3_222, s3_161] (by decide) s2_18_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_222_safe
  · subst z; exact s3_161_safe
def s2_19 : State := ⟨4, 8, 64, 193, 18831305206160042291847650636543937711788887684901876334870, 0, 0, 1⟩
theorem s2_19_edges : next 2 s2_19 = [s3_223, s3_162] := by decide
theorem s2_19_safe : Safe 11 2 s2_19 := by
  apply safe_succ 10 2 s2_19 [s3_223, s3_162] (by decide) s2_19_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_223_safe
  · subst z; exact s3_162_safe
def s2_20 : State := ⟨4, 8, 64, 194, 25108406941546723057044569527435357981744741559092983693590, 0, 0, 1⟩
theorem s2_20_edges : next 2 s2_20 = [s3_224, s3_163, s3_48] := by decide
theorem s2_20_safe : Safe 11 2 s2_20 := by
  apply safe_succ 10 2 s2_20 [s3_224, s3_163, s3_48] (by decide) s2_20_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_224_safe
  · subst z; exact s3_163_safe
  · subst z; exact s3_48_safe
def s2_21 : State := ⟨4, 8, 64, 194, 31385508676933403819519229482959270543993598573829945360662, 0, 0, 1⟩
theorem s2_21_edges : next 2 s2_21 = [s3_225, s3_164, s3_49] := by decide
theorem s2_21_safe : Safe 11 2 s2_21 := by
  apply safe_succ 10 2 s2_21 [s3_225, s3_164, s3_49] (by decide) s2_21_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_225_safe
  · subst z; exact s3_164_safe
  · subst z; exact s3_49_safe
def s2_22 : State := ⟨4, 8, 64, 196, 100433627766186892227157431008978616536533502181842616385814, 0, 0, 1⟩
theorem s2_22_edges : next 2 s2_22 = [] := by decide
theorem s2_22_safe : Safe 11 2 s2_22 := by
  apply safe_succ 10 2 s2_22 [] (by decide) s2_22_edges
  simp
def s2_23 : State := ⟨4, 8, 64, 196, 106710729501573572985548702561451267537221863907398359515414, 0, 0, 1⟩
theorem s2_23_edges : next 2 s2_23 = [] := by decide
theorem s2_23_safe : Safe 11 2 s2_23 := by
  apply safe_succ 10 2 s2_23 [] (by decide) s2_23_edges
  simp
def s2_24 : State := ⟨4, 8, 64, 208, 411376139330301510561043381120235170325683166502394837115928854, 0, 0, 1⟩
theorem s2_24_edges : next 2 s2_24 = [s3_226, s3_165, s3_50] := by decide
theorem s2_24_safe : Safe 11 2 s2_24 := by
  apply safe_succ 10 2 s2_24 [s3_226, s3_165, s3_50] (by decide) s2_24_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_226_safe
  · subst z; exact s3_165_safe
  · subst z; exact s3_50_safe
def s2_25 : State := ⟨4, 8, 64, 208, 411382416432036897219506471711127754850563550585190939644461334, 0, 0, 1⟩
theorem s2_25_edges : next 2 s2_25 = [s3_227, s3_166, s3_51] := by decide
theorem s2_25_safe : Safe 11 2 s2_25 := by
  apply safe_succ 10 2 s2_25 [s3_227, s3_166, s3_51] (by decide) s2_25_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_227_safe
  · subst z; exact s3_166_safe
  · subst z; exact s3_51_safe
def s2_26 : State := ⟨4, 8, 64, 224, 26959946667150639796128516724690815958761767718738676852269315588374, 0, 0, 1⟩
theorem s2_26_edges : next 2 s2_26 = [s3_228, s3_268, s3_283, s3_167, s3_148, s3_98, s3_62, s3_76, s3_106] := by decide
theorem s2_26_safe : Safe 11 2 s2_26 := by
  apply safe_succ 10 2 s2_26 [s3_228, s3_268, s3_283, s3_167, s3_148, s3_98, s3_62, s3_76, s3_106] (by decide) s2_26_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_228_safe
  · subst z; exact s3_268_safe
  · subst z; exact s3_283_safe
  · subst z; exact s3_167_safe
  · subst z; exact s3_148_safe
  · subst z; exact s3_98_safe
  · subst z; exact s3_62_safe
  · subst z; exact s3_76_safe
  · subst z; exact s3_106_safe
def s2_27 : State := ⟨4, 8, 64, 224, 26959946673427741530053695851195702463765749302124749277077417558294, 0, 0, 1⟩
theorem s2_27_edges : next 2 s2_27 = [s3_229, s3_269, s3_284, s3_168, s3_149, s3_99, s3_63, s3_77, s3_107] := by decide
theorem s2_27_safe : Safe 11 2 s2_27 := by
  apply safe_succ 10 2 s2_27 [s3_229, s3_269, s3_284, s3_168, s3_149, s3_99, s3_63, s3_77, s3_107] (by decide) s2_27_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_229_safe
  · subst z; exact s3_269_safe
  · subst z; exact s3_284_safe
  · subst z; exact s3_168_safe
  · subst z; exact s3_149_safe
  · subst z; exact s3_99_safe
  · subst z; exact s3_63_safe
  · subst z; exact s3_77_safe
  · subst z; exact s3_107_safe
def s2_28 : State := ⟨4, 8, 65, 129, 1020847100762815390445464054520728322326, 0, 0, 1⟩
theorem s2_28_edges : next 2 s2_28 = [s3_230, s3_169, s3_78] := by decide
theorem s2_28_safe : Safe 11 2 s2_28 := by
  apply safe_succ 10 2 s2_28 [s3_230, s3_169, s3_78] (by decide) s2_28_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_230_safe
  · subst z; exact s3_169_safe
  · subst z; exact s3_78_safe
def s2_29 : State := ⟨4, 8, 65, 130, 1701411834604692317372213269384264745238, 0, 0, 1⟩
theorem s2_29_edges : next 2 s2_29 = [s3_231, s3_170, s3_80, s3_56, s3_58] := by decide
theorem s2_29_safe : Safe 11 2 s2_29 := by
  apply safe_succ 10 2 s2_29 [s3_231, s3_170, s3_80, s3_56, s3_58] (by decide) s2_29_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_231_safe
  · subst z; exact s3_170_safe
  · subst z; exact s3_80_safe
  · subst z; exact s3_56_safe
  · subst z; exact s3_58_safe
def s2_30 : State := ⟨4, 8, 65, 132, 5784800237655953878932708558565483282710, 0, 0, 1⟩
theorem s2_30_edges : next 2 s2_30 = [s3_232, s3_171, s3_207, s3_82, s3_54] := by decide
theorem s2_30_safe : Safe 11 2 s2_30 := by
  apply safe_succ 10 2 s2_30 [s3_232, s3_171, s3_207, s3_82, s3_54] (by decide) s2_30_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_232_safe
  · subst z; exact s3_171_safe
  · subst z; exact s3_207_safe
  · subst z; exact s3_82_safe
  · subst z; exact s3_54_safe
def s2_31 : State := ⟨4, 8, 65, 136, 87452568298681185110142614342189854032150, 0, 0, 1⟩
theorem s2_31_edges : next 2 s2_31 = [s3_233, s3_277, s3_172, s3_84, s3_55] := by decide
theorem s2_31_safe : Safe 11 2 s2_31 := by
  apply safe_succ 10 2 s2_31 [s3_233, s3_277, s3_172, s3_84, s3_55] (by decide) s2_31_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_233_safe
  · subst z; exact s3_277_safe
  · subst z; exact s3_172_safe
  · subst z; exact s3_84_safe
  · subst z; exact s3_55_safe
def s2_32 : State := ⟨4, 8, 65, 144, 22301085480897544079999236987488018697879830, 0, 0, 1⟩
theorem s2_32_edges : next 2 s2_32 = [s3_235, s3_174, s3_86, s3_57, s3_60] := by decide
theorem s2_32_safe : Safe 11 2 s2_32 := by
  apply safe_succ 10 2 s2_32 [s3_235, s3_174, s3_86, s3_57, s3_60] (by decide) s2_32_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_235_safe
  · subst z; exact s3_174_safe
  · subst z; exact s3_86_safe
  · subst z; exact s3_57_safe
  · subst z; exact s3_60_safe
def s2_33 : State := ⟨4, 8, 65, 160, 1461501637671185285124623296234997859313124442390, 0, 0, 1⟩
theorem s2_33_edges : next 2 s2_33 = [s3_236, s3_175, s3_88, s3_59, s3_61] := by decide
theorem s2_33_safe : Safe 11 2 s2_33 := by
  apply safe_succ 10 2 s2_33 [s3_236, s3_175, s3_88, s3_59, s3_61] (by decide) s2_33_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_236_safe
  · subst z; exact s3_175_safe
  · subst z; exact s3_88_safe
  · subst z; exact s3_59_safe
  · subst z; exact s3_61_safe
def s2_34 : State := ⟨4, 8, 65, 192, 6277101735386680764176071790128604879621070284121226412310, 0, 0, 1⟩
theorem s2_34_edges : next 2 s2_34 = [s3_237, s3_176, s3_90, s3_63] := by decide
theorem s2_34_safe : Safe 11 2 s2_34 := by
  apply safe_succ 10 2 s2_34 [s3_237, s3_176, s3_90, s3_63] (by decide) s2_34_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_237_safe
  · subst z; exact s3_176_safe
  · subst z; exact s3_90_safe
  · subst z; exact s3_63_safe
def s2_35 : State := ⟨4, 8, 65, 193, 12554203470773361528011861213336271295723425728585260925206, 0, 0, 1⟩
theorem s2_35_edges : next 2 s2_35 = [s3_238, s3_177, s3_92] := by decide
theorem s2_35_safe : Safe 11 2 s2_35 := by
  apply safe_succ 10 2 s2_35 [s3_238, s3_177, s3_92] (by decide) s2_35_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_238_safe
  · subst z; exact s3_177_safe
  · subst z; exact s3_92_safe
def s2_36 : State := ⟨4, 8, 66, 129, 1020847100762815390482357542668147425558, 0, 0, 1⟩
theorem s2_36_edges : next 2 s2_36 = [s3_239, s3_178, s3_79, s3_108] := by decide
theorem s2_36_safe : Safe 11 2 s2_36 := by
  apply safe_succ 10 2 s2_36 [s3_239, s3_178, s3_79, s3_108] (by decide) s2_36_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_239_safe
  · subst z; exact s3_178_safe
  · subst z; exact s3_79_safe
  · subst z; exact s3_108_safe
def s2_37 : State := ⟨4, 8, 66, 130, 1701411834604692317409106757531683848470, 0, 0, 1⟩
theorem s2_37_edges : next 2 s2_37 = [s3_240, s3_179, s3_81, s3_110, s3_68, s3_70] := by decide
theorem s2_37_safe : Safe 11 2 s2_37 := by
  apply safe_succ 10 2 s2_37 [s3_240, s3_179, s3_81, s3_110, s3_68, s3_70] (by decide) s2_37_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_240_safe
  · subst z; exact s3_179_safe
  · subst z; exact s3_81_safe
  · subst z; exact s3_110_safe
  · subst z; exact s3_68_safe
  · subst z; exact s3_70_safe
def s2_38 : State := ⟨4, 8, 66, 132, 5784800237655953878969602046712902385942, 0, 0, 1⟩
theorem s2_38_edges : next 2 s2_38 = [s3_241, s3_180, s3_208, s3_83, s3_112, s3_66] := by decide
theorem s2_38_safe : Safe 11 2 s2_38 := by
  apply safe_succ 10 2 s2_38 [s3_241, s3_180, s3_208, s3_83, s3_112, s3_66] (by decide) s2_38_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_241_safe
  · subst z; exact s3_180_safe
  · subst z; exact s3_208_safe
  · subst z; exact s3_83_safe
  · subst z; exact s3_112_safe
  · subst z; exact s3_66_safe
def s2_39 : State := ⟨4, 8, 66, 136, 87452568298681185110179507830337273135382, 0, 0, 1⟩
theorem s2_39_edges : next 2 s2_39 = [s3_242, s3_278, s3_181, s3_85, s3_114, s3_67] := by decide
theorem s2_39_safe : Safe 11 2 s2_39 := by
  apply safe_succ 10 2 s2_39 [s3_242, s3_278, s3_181, s3_85, s3_114, s3_67] (by decide) s2_39_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_242_safe
  · subst z; exact s3_278_safe
  · subst z; exact s3_181_safe
  · subst z; exact s3_85_safe
  · subst z; exact s3_114_safe
  · subst z; exact s3_67_safe
def s2_40 : State := ⟨4, 8, 66, 144, 22301085480897544079999273880976166116983062, 0, 0, 1⟩
theorem s2_40_edges : next 2 s2_40 = [s3_244, s3_183, s3_142, s3_87, s3_116, s3_74, s3_69, s3_72] := by decide
theorem s2_40_safe : Safe 11 2 s2_40 := by
  apply safe_succ 10 2 s2_40 [s3_244, s3_183, s3_142, s3_87, s3_116, s3_74, s3_69, s3_72] (by decide) s2_40_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_244_safe
  · subst z; exact s3_183_safe
  · subst z; exact s3_142_safe
  · subst z; exact s3_87_safe
  · subst z; exact s3_116_safe
  · subst z; exact s3_74_safe
  · subst z; exact s3_69_safe
  · subst z; exact s3_72_safe
def s2_41 : State := ⟨4, 8, 66, 160, 1461501637671185285124623296271891347460543545622, 0, 0, 1⟩
theorem s2_41_edges : next 2 s2_41 = [s3_245, s3_184, s3_89, s3_118, s3_71, s3_73] := by decide
theorem s2_41_safe : Safe 11 2 s2_41 := by
  apply safe_succ 10 2 s2_41 [s3_245, s3_184, s3_89, s3_118, s3_71, s3_73] (by decide) s2_41_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_245_safe
  · subst z; exact s3_184_safe
  · subst z; exact s3_89_safe
  · subst z; exact s3_118_safe
  · subst z; exact s3_71_safe
  · subst z; exact s3_73_safe
def s2_42 : State := ⟨4, 8, 66, 192, 6277101735386680764176071790128604879657963772268645515542, 0, 0, 1⟩
theorem s2_42_edges : next 2 s2_42 = [s3_246, s3_185, s3_91, s3_120, s3_77] := by decide
theorem s2_42_safe : Safe 11 2 s2_42 := by
  apply safe_succ 10 2 s2_42 [s3_246, s3_185, s3_91, s3_120, s3_77] (by decide) s2_42_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_246_safe
  · subst z; exact s3_185_safe
  · subst z; exact s3_91_safe
  · subst z; exact s3_120_safe
  · subst z; exact s3_77_safe
def s2_43 : State := ⟨4, 8, 66, 194, 25108406941546723055683440059751604127965030105660749054230, 0, 0, 1⟩
theorem s2_43_edges : next 2 s2_43 = [s3_247, s3_186, s3_93, s3_122, s3_75] := by decide
theorem s2_43_safe : Safe 11 2 s2_43 := by
  apply safe_succ 10 2 s2_43 [s3_247, s3_186, s3_93, s3_122, s3_75] (by decide) s2_43_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_247_safe
  · subst z; exact s3_186_safe
  · subst z; exact s3_93_safe
  · subst z; exact s3_122_safe
  · subst z; exact s3_75_safe
def s2_44 : State := ⟨4, 8, 67, 128, 340282366920938463666288792246868312342, 0, 0, 0⟩
theorem s2_44_edges : next 2 s2_44 = [s3_248, s3_187, s3_82, s3_84, s3_94, s3_78, s3_80, s3_86, s3_88] := by decide
theorem s2_44_safe : Safe 11 2 s2_44 := by
  apply safe_succ 10 2 s2_44 [s3_248, s3_187, s3_82, s3_84, s3_94, s3_78, s3_80, s3_86, s3_88] (by decide) s2_44_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_248_safe
  · subst z; exact s3_187_safe
  · subst z; exact s3_82_safe
  · subst z; exact s3_84_safe
  · subst z; exact s3_94_safe
  · subst z; exact s3_78_safe
  · subst z; exact s3_80_safe
  · subst z; exact s3_86_safe
  · subst z; exact s3_88_safe
def s2_45 : State := ⟨4, 8, 67, 128, 340282366920938463703182280394287415574, 0, 0, 0⟩
theorem s2_45_edges : next 2 s2_45 = [s3_249, s3_188, s3_83, s3_85, s3_95, s3_79, s3_81, s3_87, s3_89] := by decide
theorem s2_45_safe : Safe 11 2 s2_45 := by
  apply safe_succ 10 2 s2_45 [s3_249, s3_188, s3_83, s3_85, s3_95, s3_79, s3_81, s3_87, s3_89] (by decide) s2_45_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_249_safe
  · subst z; exact s3_188_safe
  · subst z; exact s3_83_safe
  · subst z; exact s3_85_safe
  · subst z; exact s3_95_safe
  · subst z; exact s3_79_safe
  · subst z; exact s3_81_safe
  · subst z; exact s3_87_safe
  · subst z; exact s3_89_safe
def s2_46 : State := ⟨4, 8, 68, 129, 1020847100762815390703718471552662044950, 0, 0, 1⟩
theorem s2_46_edges : next 2 s2_46 = [] := by decide
theorem s2_46_safe : Safe 11 2 s2_46 := by
  apply safe_succ 10 2 s2_46 [] (by decide) s2_46_edges
  simp
def s2_47 : State := ⟨4, 8, 68, 130, 1701411834604692317630467686416198467862, 0, 0, 1⟩
theorem s2_47_edges : next 2 s2_47 = [s3_96] := by decide
theorem s2_47_safe : Safe 11 2 s2_47 := by
  apply safe_succ 10 2 s2_47 [s3_96] (by decide) s2_47_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_96_safe
def s2_48 : State := ⟨4, 8, 68, 132, 5784800237655953879190962975597417005334, 0, 0, 1⟩
theorem s2_48_edges : next 2 s2_48 = [] := by decide
theorem s2_48_safe : Safe 11 2 s2_48 := by
  apply safe_succ 10 2 s2_48 [] (by decide) s2_48_edges
  simp
def s2_49 : State := ⟨4, 8, 68, 136, 87452568298681185110400868759221787754774, 0, 0, 1⟩
theorem s2_49_edges : next 2 s2_49 = [] := by decide
theorem s2_49_safe : Safe 11 2 s2_49 := by
  apply safe_succ 10 2 s2_49 [] (by decide) s2_49_edges
  simp
def s2_50 : State := ⟨4, 8, 68, 144, 22301085480897544079999495241905050631602454, 0, 0, 1⟩
theorem s2_50_edges : next 2 s2_50 = [s3_97] := by decide
theorem s2_50_safe : Safe 11 2 s2_50 := by
  apply safe_succ 10 2 s2_50 [s3_97] (by decide) s2_50_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_97_safe
def s2_51 : State := ⟨4, 8, 68, 160, 1461501637671185285124623296493252276345058165014, 0, 0, 1⟩
theorem s2_51_edges : next 2 s2_51 = [] := by decide
theorem s2_51_safe : Safe 11 2 s2_51 := by
  apply safe_succ 10 2 s2_51 [] (by decide) s2_51_edges
  simp
def s2_52 : State := ⟨4, 8, 68, 192, 6277101735386680764176071790128604879879324701153160134934, 0, 0, 1⟩
theorem s2_52_edges : next 2 s2_52 = [s3_99] := by decide
theorem s2_52_safe : Safe 11 2 s2_52 := by
  apply safe_succ 10 2 s2_52 [s3_99] (by decide) s2_52_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_99_safe
def s2_53 : State := ⟨4, 8, 68, 196, 100433627766186892221712913138243601121414656368113677828374, 0, 0, 1⟩
theorem s2_53_edges : next 2 s2_53 = [] := by decide
theorem s2_53_safe : Safe 11 2 s2_53 := by
  apply safe_succ 10 2 s2_53 [] (by decide) s2_53_edges
  simp
def s2_54 : State := ⟨4, 8, 80, 129, 1020847100762816599334390181002483925270, 0, 0, 1⟩
theorem s2_54_edges : next 2 s2_54 = [s3_250, s3_189, s3_109] := by decide
theorem s2_54_safe : Safe 11 2 s2_54 := by
  apply safe_succ 10 2 s2_54 [s3_250, s3_189, s3_109] (by decide) s2_54_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_250_safe
  · subst z; exact s3_189_safe
  · subst z; exact s3_109_safe
def s2_55 : State := ⟨4, 8, 80, 130, 1701411834604693526261139395866020348182, 0, 0, 1⟩
theorem s2_55_edges : next 2 s2_55 = [s3_251, s3_190, s3_140, s3_111, s3_104] := by decide
theorem s2_55_safe : Safe 11 2 s2_55 := by
  apply safe_succ 10 2 s2_55 [s3_251, s3_190, s3_140, s3_111, s3_104] (by decide) s2_55_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_251_safe
  · subst z; exact s3_190_safe
  · subst z; exact s3_140_safe
  · subst z; exact s3_111_safe
  · subst z; exact s3_104_safe
def s2_56 : State := ⟨4, 8, 80, 132, 5784800237655955087821634685047238885654, 0, 0, 1⟩
theorem s2_56_edges : next 2 s2_56 = [s3_252, s3_191, s3_209, s3_113, s3_102] := by decide
theorem s2_56_safe : Safe 11 2 s2_56 := by
  apply safe_succ 10 2 s2_56 [s3_252, s3_191, s3_209, s3_113, s3_102] (by decide) s2_56_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_252_safe
  · subst z; exact s3_191_safe
  · subst z; exact s3_209_safe
  · subst z; exact s3_113_safe
  · subst z; exact s3_102_safe
def s2_57 : State := ⟨4, 8, 80, 136, 87452568298681186319031540468671609635094, 0, 0, 1⟩
theorem s2_57_edges : next 2 s2_57 = [s3_253, s3_279, s3_192, s3_115, s3_103] := by decide
theorem s2_57_safe : Safe 11 2 s2_57 := by
  apply safe_succ 10 2 s2_57 [s3_253, s3_279, s3_192, s3_115, s3_103] (by decide) s2_57_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_253_safe
  · subst z; exact s3_279_safe
  · subst z; exact s3_192_safe
  · subst z; exact s3_115_safe
  · subst z; exact s3_103_safe
def s2_58 : State := ⟨4, 8, 80, 144, 22301085480897544081208125913614500453482774, 0, 0, 1⟩
theorem s2_58_edges : next 2 s2_58 = [s3_255, s3_194, s3_117] := by decide
theorem s2_58_safe : Safe 11 2 s2_58 := by
  apply safe_succ 10 2 s2_58 [s3_255, s3_194, s3_117] (by decide) s2_58_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_255_safe
  · subst z; exact s3_194_safe
  · subst z; exact s3_117_safe
def s2_59 : State := ⟨4, 8, 80, 160, 1461501637671185285124624505123923985794880045334, 0, 0, 1⟩
theorem s2_59_edges : next 2 s2_59 = [s3_256, s3_195, s3_119] := by decide
theorem s2_59_safe : Safe 11 2 s2_59 := by
  apply safe_succ 10 2 s2_59 [s3_256, s3_195, s3_119] (by decide) s2_59_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_256_safe
  · subst z; exact s3_195_safe
  · subst z; exact s3_119_safe
def s2_60 : State := ⟨4, 8, 80, 192, 6277101735386680764176071790128606088509996410602982015254, 0, 0, 1⟩
theorem s2_60_edges : next 2 s2_60 = [s3_257, s3_196, s3_121, s3_107] := by decide
theorem s2_60_safe : Safe 11 2 s2_60 := by
  apply safe_succ 10 2 s2_60 [s3_257, s3_196, s3_121, s3_107] (by decide) s2_60_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_257_safe
  · subst z; exact s3_196_safe
  · subst z; exact s3_121_safe
  · subst z; exact s3_107_safe
def s2_61 : State := ⟨4, 8, 80, 208, 411376139330301510538742635921704547185356374049361104784654614, 0, 0, 1⟩
theorem s2_61_edges : next 2 s2_61 = [s3_258, s3_197, s3_123, s3_105] := by decide
theorem s2_61_safe : Safe 11 2 s2_61 := by
  apply safe_succ 10 2 s2_61 [s3_258, s3_197, s3_123, s3_105] (by decide) s2_61_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_258_safe
  · subst z; exact s3_197_safe
  · subst z; exact s3_123_safe
  · subst z; exact s3_105_safe
def s2_62 : State := ⟨4, 8, 82, 128, 340282366920943299258886786321309827350, 0, 0, 0⟩
theorem s2_62_edges : next 2 s2_62 = [s3_259, s3_272, s3_198, s3_126, s3_112, s3_114, s3_124, s3_108, s3_110, s3_116, s3_118] := by decide
theorem s2_62_safe : Safe 11 2 s2_62 := by
  apply safe_succ 10 2 s2_62 [s3_259, s3_272, s3_198, s3_126, s3_112, s3_114, s3_124, s3_108, s3_110, s3_116, s3_118] (by decide) s2_62_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_259_safe
  · subst z; exact s3_272_safe
  · subst z; exact s3_198_safe
  · subst z; exact s3_126_safe
  · subst z; exact s3_112_safe
  · subst z; exact s3_114_safe
  · subst z; exact s3_124_safe
  · subst z; exact s3_108_safe
  · subst z; exact s3_110_safe
  · subst z; exact s3_116_safe
  · subst z; exact s3_118_safe
def s2_63 : State := ⟨4, 8, 82, 128, 340282366920944508110919424655646327062, 0, 0, 0⟩
theorem s2_63_edges : next 2 s2_63 = [s3_260, s3_273, s3_199, s3_127, s3_113, s3_115, s3_125, s3_109, s3_111, s3_117, s3_119] := by decide
theorem s2_63_safe : Safe 11 2 s2_63 := by
  apply safe_succ 10 2 s2_63 [s3_260, s3_273, s3_199, s3_127, s3_113, s3_115, s3_125, s3_109, s3_111, s3_117, s3_119] (by decide) s2_63_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_260_safe
  · subst z; exact s3_273_safe
  · subst z; exact s3_199_safe
  · subst z; exact s3_127_safe
  · subst z; exact s3_113_safe
  · subst z; exact s3_115_safe
  · subst z; exact s3_125_safe
  · subst z; exact s3_109_safe
  · subst z; exact s3_111_safe
  · subst z; exact s3_117_safe
  · subst z; exact s3_119_safe
def s2_64 : State := ⟨4, 8, 96, 224, 26959946667150639794667015087359913040637311048536658170206926995734, 0, 0, 1⟩
theorem s2_64_edges : next 2 s2_64 = [s3_261, s3_274, s3_285, s3_200, s3_204, s3_150, s3_135, s3_136, s3_134, s3_137] := by decide
theorem s2_64_safe : Safe 11 2 s2_64 := by
  apply safe_succ 10 2 s2_64 [s3_261, s3_274, s3_285, s3_200, s3_204, s3_150, s3_135, s3_136, s3_134, s3_137] (by decide) s2_64_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_261_safe
  · subst z; exact s3_274_safe
  · subst z; exact s3_285_safe
  · subst z; exact s3_200_safe
  · subst z; exact s3_204_safe
  · subst z; exact s3_150_safe
  · subst z; exact s3_135_safe
  · subst z; exact s3_136_safe
  · subst z; exact s3_134_safe
  · subst z; exact s3_137_safe
def s2_65 : State := ⟨4, 8, 193, 129, 12554203470773361528692425947178148222613281455301378244886, 0, 0, 1⟩
theorem s2_65_edges : next 2 s2_65 = [s3_262, s3_201] := by decide
theorem s2_65_safe : Safe 11 2 s2_65 := by
  apply safe_succ 10 2 s2_65 [s3_262, s3_201] (by decide) s2_65_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_262_safe
  · subst z; exact s3_201_safe
def s2_66 : State := ⟨4, 8, 194, 130, 25108406941546723057044569527435357981744741559092983693590, 0, 0, 1⟩
theorem s2_66_edges : next 2 s2_66 = [s3_263, s3_202, s3_141, s3_138, s3_139] := by decide
theorem s2_66_safe : Safe 11 2 s2_66 := by
  apply safe_succ 10 2 s2_66 [s3_263, s3_202, s3_141, s3_138, s3_139] (by decide) s2_66_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h
  · subst z; exact s3_263_safe
  · subst z; exact s3_202_safe
  · subst z; exact s3_141_safe
  · subst z; exact s3_138_safe
  · subst z; exact s3_139_safe
def s2_67 : State := ⟨4, 8, 196, 132, 100433627766186892227157431008978616536533502181842616385814, 0, 0, 1⟩
theorem s2_67_edges : next 2 s2_67 = [] := by decide
theorem s2_67_safe : Safe 11 2 s2_67 := by
  apply safe_succ 10 2 s2_67 [] (by decide) s2_67_edges
  simp
def s2_68 : State := ⟨4, 8, 208, 144, 411376139330301510561043381120235170325683166502394837115928854, 0, 0, 1⟩
theorem s2_68_edges : next 2 s2_68 = [s3_264, s3_203, s3_143] := by decide
theorem s2_68_safe : Safe 11 2 s2_68 := by
  apply safe_succ 10 2 s2_68 [s3_264, s3_203, s3_143] (by decide) s2_68_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_264_safe
  · subst z; exact s3_203_safe
  · subst z; exact s3_143_safe
def s2_69 : State := ⟨4, 9, 64, 129, 1020847100762815390408570566373309219606, 2, 0, 1⟩
theorem s2_69_edges : next 2 s2_69 = [s3_0] := by decide
theorem s2_69_safe : Safe 11 2 s2_69 := by
  apply safe_succ 10 2 s2_69 [s3_0] (by decide) s2_69_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_0_safe
def s2_70 : State := ⟨4, 9, 64, 130, 1701411834604692317335319781236845642518, 2, 0, 1⟩
theorem s2_70_edges : next 2 s2_70 = [s3_5, s3_146] := by decide
theorem s2_70_safe : Safe 11 2 s2_70 := by
  apply safe_succ 10 2 s2_70 [s3_5, s3_146] (by decide) s2_70_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_5_safe
  · subst z; exact s3_146_safe
def s2_71 : State := ⟨4, 9, 64, 132, 5784800237655953878895815070418064179990, 2, 0, 1⟩
theorem s2_71_edges : next 2 s2_71 = [s3_9] := by decide
theorem s2_71_safe : Safe 11 2 s2_71 := by
  apply safe_succ 10 2 s2_71 [s3_9] (by decide) s2_71_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_9_safe
def s2_72 : State := ⟨4, 9, 64, 136, 87452568298681185110105720854042434929430, 2, 0, 1⟩
theorem s2_72_edges : next 2 s2_72 = [s3_14] := by decide
theorem s2_72_safe : Safe 11 2 s2_72 := by
  apply safe_succ 10 2 s2_72 [s3_14] (by decide) s2_72_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_14_safe
def s2_73 : State := ⟨4, 9, 64, 137, 174564854230441431756729620356575097062166, 2, 0, 1⟩
theorem s2_73_edges : next 2 s2_73 = [s3_19] := by decide
theorem s2_73_safe : Safe 11 2 s2_73 := by
  apply safe_succ 10 2 s2_73 [s3_19] (by decide) s2_73_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_19_safe
def s2_74 : State := ⟨4, 9, 64, 144, 22301085480897544079999200093999871278777110, 2, 0, 1⟩
theorem s2_74_edges : next 2 s2_74 = [s3_22] := by decide
theorem s2_74_safe : Safe 11 2 s2_74 := by
  apply safe_succ 10 2 s2_74 [s3_22] (by decide) s2_74_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_22_safe
def s2_75 : State := ⟨4, 9, 64, 160, 1461501637671185285124623296198104371165705339670, 2, 0, 1⟩
theorem s2_75_edges : next 2 s2_75 = [s3_28, s3_148, s3_147] := by decide
theorem s2_75_safe : Safe 11 2 s2_75 := by
  apply safe_succ 10 2 s2_75 [s3_28, s3_148, s3_147] (by decide) s2_75_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_28_safe
  · subst z; exact s3_148_safe
  · subst z; exact s3_147_safe
def s2_76 : State := ⟨4, 9, 64, 192, 6277101735386680764176071790128604879584176795973807309590, 2, 0, 1⟩
theorem s2_76_edges : next 2 s2_76 = [s3_40, s3_149] := by decide
theorem s2_76_safe : Safe 11 2 s2_76 := by
  apply safe_succ 10 2 s2_76 [s3_40, s3_149] (by decide) s2_76_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_40_safe
  · subst z; exact s3_149_safe
def s2_77 : State := ⟨4, 9, 96, 128, 340282367000166625996085689103316747030, 2, 0, 0⟩
theorem s2_77_edges : next 2 s2_77 = [s3_128, s3_150] := by decide
theorem s2_77_safe : Safe 11 2 s2_77 := by
  apply safe_succ 10 2 s2_77 [s3_128, s3_150] (by decide) s2_77_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_128_safe
  · subst z; exact s3_150_safe
def s2_78 : State := ⟨4, 12, 64, 129, 1020847100762815390408570566373309223190, 2, 0, 1⟩
theorem s2_78_edges : next 2 s2_78 = [s3_2, s3_201, s3_169, s3_178, s3_189, s3_161, s3_151, s3_155] := by decide
theorem s2_78_safe : Safe 11 2 s2_78 := by
  apply safe_succ 10 2 s2_78 [s3_2, s3_201, s3_169, s3_178, s3_189, s3_161, s3_151, s3_155] (by decide) s2_78_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_2_safe
  · subst z; exact s3_201_safe
  · subst z; exact s3_169_safe
  · subst z; exact s3_178_safe
  · subst z; exact s3_189_safe
  · subst z; exact s3_161_safe
  · subst z; exact s3_151_safe
  · subst z; exact s3_155_safe
def s2_79 : State := ⟨4, 12, 64, 130, 1701411834604692317335319781236845646102, 2, 0, 1⟩
theorem s2_79_edges : next 2 s2_79 = [s3_7, s3_202, s3_170, s3_179, s3_190, s3_163, s3_152, s3_153, s3_157] := by decide
theorem s2_79_safe : Safe 11 2 s2_79 := by
  apply safe_succ 10 2 s2_79 [s3_7, s3_202, s3_170, s3_179, s3_190, s3_163, s3_152, s3_153, s3_157] (by decide) s2_79_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_7_safe
  · subst z; exact s3_202_safe
  · subst z; exact s3_170_safe
  · subst z; exact s3_179_safe
  · subst z; exact s3_190_safe
  · subst z; exact s3_163_safe
  · subst z; exact s3_152_safe
  · subst z; exact s3_153_safe
  · subst z; exact s3_157_safe
def s2_80 : State := ⟨4, 12, 64, 132, 5784800237655953878895815070418064183574, 2, 0, 1⟩
theorem s2_80_edges : next 2 s2_80 = [s3_11, s3_171, s3_180, s3_191] := by decide
theorem s2_80_safe : Safe 11 2 s2_80 := by
  apply safe_succ 10 2 s2_80 [s3_11, s3_171, s3_180, s3_191] (by decide) s2_80_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_11_safe
  · subst z; exact s3_171_safe
  · subst z; exact s3_180_safe
  · subst z; exact s3_191_safe
def s2_81 : State := ⟨4, 12, 64, 136, 87452568298681185110105720854042434933014, 2, 0, 1⟩
theorem s2_81_edges : next 2 s2_81 = [s3_16, s3_172, s3_181, s3_192] := by decide
theorem s2_81_safe : Safe 11 2 s2_81 := by
  apply safe_succ 10 2 s2_81 [s3_16, s3_172, s3_181, s3_192] (by decide) s2_81_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_16_safe
  · subst z; exact s3_172_safe
  · subst z; exact s3_181_safe
  · subst z; exact s3_192_safe
def s2_82 : State := ⟨4, 12, 64, 140, 1394136857275084884809464213392032366924054, 2, 0, 1⟩
theorem s2_82_edges : next 2 s2_82 = [s3_21, s3_173, s3_182, s3_193] := by decide
theorem s2_82_safe : Safe 11 2 s2_82 := by
  apply safe_succ 10 2 s2_82 [s3_21, s3_173, s3_182, s3_193] (by decide) s2_82_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_21_safe
  · subst z; exact s3_173_safe
  · subst z; exact s3_182_safe
  · subst z; exact s3_193_safe
def s2_83 : State := ⟨4, 12, 64, 144, 22301085480897544079999200093999871278780694, 2, 0, 1⟩
theorem s2_83_edges : next 2 s2_83 = [s3_24, s3_203, s3_174, s3_183, s3_194, s3_165, s3_154, s3_159] := by decide
theorem s2_83_safe : Safe 11 2 s2_83 := by
  apply safe_succ 10 2 s2_83 [s3_24, s3_203, s3_174, s3_183, s3_194, s3_165, s3_154, s3_159] (by decide) s2_83_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_24_safe
  · subst z; exact s3_203_safe
  · subst z; exact s3_174_safe
  · subst z; exact s3_183_safe
  · subst z; exact s3_194_safe
  · subst z; exact s3_165_safe
  · subst z; exact s3_154_safe
  · subst z; exact s3_159_safe
def s2_84 : State := ⟨4, 12, 64, 160, 1461501637671185285124623296198104371165705343254, 2, 0, 1⟩
theorem s2_84_edges : next 2 s2_84 = [s3_30, s3_175, s3_184, s3_195, s3_167, s3_156, s3_158, s3_160] := by decide
theorem s2_84_safe : Safe 11 2 s2_84 := by
  apply safe_succ 10 2 s2_84 [s3_30, s3_175, s3_184, s3_195, s3_167, s3_156, s3_158, s3_160] (by decide) s2_84_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_30_safe
  · subst z; exact s3_175_safe
  · subst z; exact s3_184_safe
  · subst z; exact s3_195_safe
  · subst z; exact s3_167_safe
  · subst z; exact s3_156_safe
  · subst z; exact s3_158_safe
  · subst z; exact s3_160_safe
def s2_85 : State := ⟨4, 12, 64, 192, 6277101735386680764176071790128604879584176795973807313174, 2, 0, 1⟩
theorem s2_85_edges : next 2 s2_85 = [s3_42, s3_176, s3_185, s3_196, s3_162, s3_164, s3_166, s3_168] := by decide
theorem s2_85_safe : Safe 11 2 s2_85 := by
  apply safe_succ 10 2 s2_85 [s3_42, s3_176, s3_185, s3_196, s3_162, s3_164, s3_166, s3_168] (by decide) s2_85_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_42_safe
  · subst z; exact s3_176_safe
  · subst z; exact s3_185_safe
  · subst z; exact s3_196_safe
  · subst z; exact s3_162_safe
  · subst z; exact s3_164_safe
  · subst z; exact s3_166_safe
  · subst z; exact s3_168_safe
def s2_86 : State := ⟨4, 12, 65, 128, 340282366920938463518714839657191903510, 2, 0, 0⟩
theorem s2_86_edges : next 2 s2_86 = [s3_53, s3_187, s3_171, s3_173, s3_177, s3_169, s3_170, s3_174, s3_175] := by decide
theorem s2_86_safe : Safe 11 2 s2_86 := by
  apply safe_succ 10 2 s2_86 [s3_53, s3_187, s3_171, s3_173, s3_177, s3_169, s3_170, s3_174, s3_175] (by decide) s2_86_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_53_safe
  · subst z; exact s3_187_safe
  · subst z; exact s3_171_safe
  · subst z; exact s3_173_safe
  · subst z; exact s3_177_safe
  · subst z; exact s3_169_safe
  · subst z; exact s3_170_safe
  · subst z; exact s3_174_safe
  · subst z; exact s3_175_safe
def s2_87 : State := ⟨4, 12, 66, 128, 340282366920938463555608327804611006742, 2, 0, 0⟩
theorem s2_87_edges : next 2 s2_87 = [s3_65, s3_188, s3_198, s3_180, s3_182, s3_186, s3_178, s3_179, s3_183, s3_184] := by decide
theorem s2_87_safe : Safe 11 2 s2_87 := by
  apply safe_succ 10 2 s2_87 [s3_65, s3_188, s3_198, s3_180, s3_182, s3_186, s3_178, s3_179, s3_183, s3_184] (by decide) s2_87_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_65_safe
  · subst z; exact s3_188_safe
  · subst z; exact s3_198_safe
  · subst z; exact s3_180_safe
  · subst z; exact s3_182_safe
  · subst z; exact s3_186_safe
  · subst z; exact s3_178_safe
  · subst z; exact s3_179_safe
  · subst z; exact s3_183_safe
  · subst z; exact s3_184_safe
def s2_88 : State := ⟨4, 12, 80, 128, 340282366920939672407640966138947506454, 2, 0, 0⟩
theorem s2_88_edges : next 2 s2_88 = [s3_101, s3_199, s3_191, s3_193, s3_197, s3_189, s3_190, s3_194, s3_195] := by decide
theorem s2_88_safe : Safe 11 2 s2_88 := by
  apply safe_succ 10 2 s2_88 [s3_101, s3_199, s3_191, s3_193, s3_197, s3_189, s3_190, s3_194, s3_195] (by decide) s2_88_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_101_safe
  · subst z; exact s3_199_safe
  · subst z; exact s3_191_safe
  · subst z; exact s3_193_safe
  · subst z; exact s3_197_safe
  · subst z; exact s3_189_safe
  · subst z; exact s3_190_safe
  · subst z; exact s3_194_safe
  · subst z; exact s3_195_safe
def s2_89 : State := ⟨4, 12, 96, 128, 340282367000166625996085689103316750614, 2, 0, 0⟩
theorem s2_89_edges : next 2 s2_89 = [s3_130, s3_200] := by decide
theorem s2_89_safe : Safe 11 2 s2_89 := by
  apply safe_succ 10 2 s2_89 [s3_130, s3_200] (by decide) s2_89_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_130_safe
  · subst z; exact s3_200_safe
def s2_90 : State := ⟨4, 104, 96, 128, 340282387282576229647756113050568032534, 2, 0, 0⟩
theorem s2_90_edges : next 2 s2_90 = [s3_276, s3_275, s3_205, s3_133, s3_206, s3_204] := by decide
theorem s2_90_safe : Safe 11 2 s2_90 := by
  apply safe_succ 10 2 s2_90 [s3_276, s3_275, s3_205, s3_133, s3_206, s3_204] (by decide) s2_90_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s3_276_safe
  · subst z; exact s3_275_safe
  · subst z; exact s3_205_safe
  · subst z; exact s3_133_safe
  · subst z; exact s3_206_safe
  · subst z; exact s3_204_safe
def s2_91 : State := ⟨4, 137, 64, 129, 175245418964283308683656369571438633484566, 2, 0, 1⟩
theorem s2_91_edges : next 2 s2_91 = [s3_4] := by decide
theorem s2_91_safe : Safe 11 2 s2_91 := by
  apply safe_succ 10 2 s2_91 [s3_4] (by decide) s2_91_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_4_safe
def s2_92 : State := ⟨4, 140, 64, 132, 1399581375145819900224878207110940658303254, 2, 0, 1⟩
theorem s2_92_edges : next 2 s2_92 = [s3_13, s3_207, s3_208, s3_209] := by decide
theorem s2_92_safe : Safe 11 2 s2_92 := by
  apply safe_succ 10 2 s2_92 [s3_13, s3_207, s3_208, s3_209] (by decide) s2_92_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_13_safe
  · subst z; exact s3_207_safe
  · subst z; exact s3_208_safe
  · subst z; exact s3_209_safe
def s2_93 : State := ⟨12, 8, 64, 129, 1020847100762815390408570566373309223190, 1, 0, 1⟩
theorem s2_93_edges : next 2 s2_93 = [s3_1, s3_262, s3_230, s3_239, s3_250, s3_222, s3_212, s3_216] := by decide
theorem s2_93_safe : Safe 11 2 s2_93 := by
  apply safe_succ 10 2 s2_93 [s3_1, s3_262, s3_230, s3_239, s3_250, s3_222, s3_212, s3_216] (by decide) s2_93_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_1_safe
  · subst z; exact s3_262_safe
  · subst z; exact s3_230_safe
  · subst z; exact s3_239_safe
  · subst z; exact s3_250_safe
  · subst z; exact s3_222_safe
  · subst z; exact s3_212_safe
  · subst z; exact s3_216_safe
def s2_94 : State := ⟨12, 8, 64, 130, 1701411834604692317335319781236845646102, 1, 0, 1⟩
theorem s2_94_edges : next 2 s2_94 = [s3_6, s3_263, s3_231, s3_240, s3_251, s3_224, s3_213, s3_214, s3_218] := by decide
theorem s2_94_safe : Safe 11 2 s2_94 := by
  apply safe_succ 10 2 s2_94 [s3_6, s3_263, s3_231, s3_240, s3_251, s3_224, s3_213, s3_214, s3_218] (by decide) s2_94_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_6_safe
  · subst z; exact s3_263_safe
  · subst z; exact s3_231_safe
  · subst z; exact s3_240_safe
  · subst z; exact s3_251_safe
  · subst z; exact s3_224_safe
  · subst z; exact s3_213_safe
  · subst z; exact s3_214_safe
  · subst z; exact s3_218_safe
def s2_95 : State := ⟨12, 8, 64, 132, 5784800237655953878895815070418064183574, 1, 0, 1⟩
theorem s2_95_edges : next 2 s2_95 = [s3_10, s3_232, s3_241, s3_252] := by decide
theorem s2_95_safe : Safe 11 2 s2_95 := by
  apply safe_succ 10 2 s2_95 [s3_10, s3_232, s3_241, s3_252] (by decide) s2_95_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_10_safe
  · subst z; exact s3_232_safe
  · subst z; exact s3_241_safe
  · subst z; exact s3_252_safe
def s2_96 : State := ⟨12, 8, 64, 136, 87452568298681185110105720854042434933014, 1, 0, 1⟩
theorem s2_96_edges : next 2 s2_96 = [s3_15, s3_233, s3_242, s3_253] := by decide
theorem s2_96_safe : Safe 11 2 s2_96 := by
  apply safe_succ 10 2 s2_96 [s3_15, s3_233, s3_242, s3_253] (by decide) s2_96_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_15_safe
  · subst z; exact s3_233_safe
  · subst z; exact s3_242_safe
  · subst z; exact s3_253_safe
def s2_97 : State := ⟨12, 8, 64, 140, 1394136857275084884809464213392032366924054, 1, 0, 1⟩
theorem s2_97_edges : next 2 s2_97 = [s3_20, s3_234, s3_243, s3_254] := by decide
theorem s2_97_safe : Safe 11 2 s2_97 := by
  apply safe_succ 10 2 s2_97 [s3_20, s3_234, s3_243, s3_254] (by decide) s2_97_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_20_safe
  · subst z; exact s3_234_safe
  · subst z; exact s3_243_safe
  · subst z; exact s3_254_safe
def s2_98 : State := ⟨12, 8, 64, 144, 22301085480897544079999200093999871278780694, 1, 0, 1⟩
theorem s2_98_edges : next 2 s2_98 = [s3_23, s3_264, s3_235, s3_244, s3_255, s3_226, s3_215, s3_220] := by decide
theorem s2_98_safe : Safe 11 2 s2_98 := by
  apply safe_succ 10 2 s2_98 [s3_23, s3_264, s3_235, s3_244, s3_255, s3_226, s3_215, s3_220] (by decide) s2_98_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_23_safe
  · subst z; exact s3_264_safe
  · subst z; exact s3_235_safe
  · subst z; exact s3_244_safe
  · subst z; exact s3_255_safe
  · subst z; exact s3_226_safe
  · subst z; exact s3_215_safe
  · subst z; exact s3_220_safe
def s2_99 : State := ⟨12, 8, 64, 160, 1461501637671185285124623296198104371165705343254, 1, 0, 1⟩
theorem s2_99_edges : next 2 s2_99 = [s3_29, s3_236, s3_245, s3_256, s3_228, s3_217, s3_219, s3_221] := by decide
theorem s2_99_safe : Safe 11 2 s2_99 := by
  apply safe_succ 10 2 s2_99 [s3_29, s3_236, s3_245, s3_256, s3_228, s3_217, s3_219, s3_221] (by decide) s2_99_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_29_safe
  · subst z; exact s3_236_safe
  · subst z; exact s3_245_safe
  · subst z; exact s3_256_safe
  · subst z; exact s3_228_safe
  · subst z; exact s3_217_safe
  · subst z; exact s3_219_safe
  · subst z; exact s3_221_safe
def s2_100 : State := ⟨12, 8, 64, 192, 6277101735386680764176071790128604879584176795973807313174, 1, 0, 1⟩
theorem s2_100_edges : next 2 s2_100 = [s3_41, s3_237, s3_246, s3_257, s3_223, s3_225, s3_227, s3_229] := by decide
theorem s2_100_safe : Safe 11 2 s2_100 := by
  apply safe_succ 10 2 s2_100 [s3_41, s3_237, s3_246, s3_257, s3_223, s3_225, s3_227, s3_229] (by decide) s2_100_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h
  · subst z; exact s3_41_safe
  · subst z; exact s3_237_safe
  · subst z; exact s3_246_safe
  · subst z; exact s3_257_safe
  · subst z; exact s3_223_safe
  · subst z; exact s3_225_safe
  · subst z; exact s3_227_safe
  · subst z; exact s3_229_safe
def s2_101 : State := ⟨12, 8, 65, 128, 340282366920938463518714839657191903510, 1, 0, 0⟩
theorem s2_101_edges : next 2 s2_101 = [s3_52, s3_248, s3_234, s3_233, s3_238, s3_230, s3_231, s3_235, s3_236] := by decide
theorem s2_101_safe : Safe 11 2 s2_101 := by
  apply safe_succ 10 2 s2_101 [s3_52, s3_248, s3_234, s3_233, s3_238, s3_230, s3_231, s3_235, s3_236] (by decide) s2_101_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_52_safe
  · subst z; exact s3_248_safe
  · subst z; exact s3_234_safe
  · subst z; exact s3_233_safe
  · subst z; exact s3_238_safe
  · subst z; exact s3_230_safe
  · subst z; exact s3_231_safe
  · subst z; exact s3_235_safe
  · subst z; exact s3_236_safe
def s2_102 : State := ⟨12, 8, 66, 128, 340282366920938463555608327804611006742, 1, 0, 0⟩
theorem s2_102_edges : next 2 s2_102 = [s3_64, s3_249, s3_259, s3_243, s3_242, s3_247, s3_239, s3_240, s3_244, s3_245] := by decide
theorem s2_102_safe : Safe 11 2 s2_102 := by
  apply safe_succ 10 2 s2_102 [s3_64, s3_249, s3_259, s3_243, s3_242, s3_247, s3_239, s3_240, s3_244, s3_245] (by decide) s2_102_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s3_64_safe
  · subst z; exact s3_249_safe
  · subst z; exact s3_259_safe
  · subst z; exact s3_243_safe
  · subst z; exact s3_242_safe
  · subst z; exact s3_247_safe
  · subst z; exact s3_239_safe
  · subst z; exact s3_240_safe
  · subst z; exact s3_244_safe
  · subst z; exact s3_245_safe
def s2_103 : State := ⟨12, 8, 80, 128, 340282366920939672407640966138947506454, 1, 0, 0⟩
theorem s2_103_edges : next 2 s2_103 = [s3_100, s3_260, s3_254, s3_253, s3_258, s3_250, s3_251, s3_255, s3_256] := by decide
theorem s2_103_safe : Safe 11 2 s2_103 := by
  apply safe_succ 10 2 s2_103 [s3_100, s3_260, s3_254, s3_253, s3_258, s3_250, s3_251, s3_255, s3_256] (by decide) s2_103_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s3_100_safe
  · subst z; exact s3_260_safe
  · subst z; exact s3_254_safe
  · subst z; exact s3_253_safe
  · subst z; exact s3_258_safe
  · subst z; exact s3_250_safe
  · subst z; exact s3_251_safe
  · subst z; exact s3_255_safe
  · subst z; exact s3_256_safe
def s2_104 : State := ⟨12, 8, 96, 128, 340282367000166625996085689103316750614, 1, 0, 0⟩
theorem s2_104_edges : next 2 s2_104 = [s3_129, s3_265, s3_261] := by decide
theorem s2_104_safe : Safe 11 2 s2_104 := by
  apply safe_succ 10 2 s2_104 [s3_129, s3_265, s3_261] (by decide) s2_104_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_129_safe
  · subst z; exact s3_265_safe
  · subst z; exact s3_261_safe
def s2_105 : State := ⟨68, 8, 64, 129, 1020847100762815390703718471552662044950, 1, 0, 1⟩
theorem s2_105_edges : next 2 s2_105 = [s3_3] := by decide
theorem s2_105_safe : Safe 11 2 s2_105 := by
  apply safe_succ 10 2 s2_105 [s3_3] (by decide) s2_105_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_3_safe
def s2_106 : State := ⟨68, 8, 64, 130, 1701411834604692317630467686416198467862, 1, 0, 1⟩
theorem s2_106_edges : next 2 s2_106 = [s3_8, s3_266] := by decide
theorem s2_106_safe : Safe 11 2 s2_106 := by
  apply safe_succ 10 2 s2_106 [s3_8, s3_266] (by decide) s2_106_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_8_safe
  · subst z; exact s3_266_safe
def s2_107 : State := ⟨68, 8, 64, 132, 5784800237655953879190962975597417005334, 1, 0, 1⟩
theorem s2_107_edges : next 2 s2_107 = [s3_12] := by decide
theorem s2_107_safe : Safe 11 2 s2_107 := by
  apply safe_succ 10 2 s2_107 [s3_12] (by decide) s2_107_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_12_safe
def s2_108 : State := ⟨68, 8, 64, 136, 87452568298681185110400868759221787754774, 1, 0, 1⟩
theorem s2_108_edges : next 2 s2_108 = [s3_17] := by decide
theorem s2_108_safe : Safe 11 2 s2_108 := by
  apply safe_succ 10 2 s2_108 [s3_17] (by decide) s2_108_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_17_safe
def s2_109 : State := ⟨68, 8, 64, 144, 22301085480897544079999495241905050631602454, 1, 0, 1⟩
theorem s2_109_edges : next 2 s2_109 = [s3_25, s3_267] := by decide
theorem s2_109_safe : Safe 11 2 s2_109 := by
  apply safe_succ 10 2 s2_109 [s3_25, s3_267] (by decide) s2_109_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_25_safe
  · subst z; exact s3_267_safe
def s2_110 : State := ⟨68, 8, 64, 160, 1461501637671185285124623296493252276345058165014, 1, 0, 1⟩
theorem s2_110_edges : next 2 s2_110 = [s3_31, s3_268] := by decide
theorem s2_110_safe : Safe 11 2 s2_110 := by
  apply safe_succ 10 2 s2_110 [s3_31, s3_268] (by decide) s2_110_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_31_safe
  · subst z; exact s3_268_safe
def s2_111 : State := ⟨68, 8, 64, 192, 6277101735386680764176071790128604879879324701153160134934, 1, 0, 1⟩
theorem s2_111_edges : next 2 s2_111 = [s3_43, s3_269] := by decide
theorem s2_111_safe : Safe 11 2 s2_111 := by
  apply safe_succ 10 2 s2_111 [s3_43, s3_269] (by decide) s2_111_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_43_safe
  · subst z; exact s3_269_safe
def s2_112 : State := ⟨68, 8, 64, 196, 100433627766186892221712913138243601121414656368113677828374, 1, 0, 1⟩
theorem s2_112_edges : next 2 s2_112 = [s3_45] := by decide
theorem s2_112_safe : Safe 11 2 s2_112 := by
  apply safe_succ 10 2 s2_112 [s3_45] (by decide) s2_112_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h
  · subst z; exact s3_45_safe
def s2_113 : State := ⟨68, 8, 96, 128, 340282367000166626291233594282669572374, 1, 0, 0⟩
theorem s2_113_edges : next 2 s2_113 = [s3_271, s3_270] := by decide
theorem s2_113_safe : Safe 11 2 s2_113 := by
  apply safe_succ 10 2 s2_113 [s3_271, s3_270] (by decide) s2_113_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_271_safe
  · subst z; exact s3_270_safe
def s2_114 : State := ⟨100, 8, 96, 128, 340282368267817226224315090600019951894, 1, 0, 0⟩
theorem s2_114_edges : next 2 s2_114 = [s3_132, s3_275, s3_274] := by decide
theorem s2_114_safe : Safe 11 2 s2_114 := by
  apply safe_succ 10 2 s2_114 [s3_132, s3_275, s3_274] (by decide) s2_114_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h
  · subst z; exact s3_132_safe
  · subst z; exact s3_275_safe
  · subst z; exact s3_274_safe
def s2_115 : State := ⟨140, 8, 64, 136, 1481249143206845131456088112894565029052694, 1, 0, 1⟩
theorem s2_115_edges : next 2 s2_115 = [s3_18, s3_277, s3_278, s3_279] := by decide
theorem s2_115_safe : Safe 11 2 s2_115 := by
  apply safe_succ 10 2 s2_115 [s3_18, s3_277, s3_278, s3_279] (by decide) s2_115_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h
  · subst z; exact s3_18_safe
  · subst z; exact s3_277_safe
  · subst z; exact s3_278_safe
  · subst z; exact s3_279_safe
def s2_116 : State := ⟨196, 8, 64, 192, 106710729501573572985548702561451267537221863907398359515414, 1, 0, 1⟩
theorem s2_116_edges : next 2 s2_116 = [s3_44, s3_282] := by decide
theorem s2_116_safe : Safe 11 2 s2_116 := by
  apply safe_succ 10 2 s2_116 [s3_44, s3_282] (by decide) s2_116_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h
  · subst z; exact s3_44_safe
  · subst z; exact s3_282_safe
def s1_0 : State := ⟨4, 8, 64, 129, 1020847100762815390408570566373309219094, 0, 0, 1⟩
theorem s1_0_edges : next 1 s1_0 = [s2_93, s2_105, s2_78, s2_91, s2_69, s2_46, s2_65, s2_28, s2_36, s2_54, s2_6, s2_18, s2_4, s2_12] := by decide
theorem s1_0_safe : Safe 12 1 s1_0 := by
  apply safe_succ 11 1 s1_0 [s2_93, s2_105, s2_78, s2_91, s2_69, s2_46, s2_65, s2_28, s2_36, s2_54, s2_6, s2_18, s2_4, s2_12] (by decide) s1_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_93_safe
  · subst z; exact s2_105_safe
  · subst z; exact s2_78_safe
  · subst z; exact s2_91_safe
  · subst z; exact s2_69_safe
  · subst z; exact s2_46_safe
  · subst z; exact s2_65_safe
  · subst z; exact s2_28_safe
  · subst z; exact s2_36_safe
  · subst z; exact s2_54_safe
  · subst z; exact s2_6_safe
  · subst z; exact s2_18_safe
  · subst z; exact s2_4_safe
  · subst z; exact s2_12_safe
def s1_1 : State := ⟨4, 8, 64, 130, 1701411834604692317335319781236845642006, 0, 0, 1⟩
theorem s1_1_edges : next 1 s1_1 = [s2_94, s2_106, s2_79, s2_70, s2_47, s2_66, s2_29, s2_37, s2_55, s2_20, s2_5, s2_10, s2_14] := by decide
theorem s1_1_safe : Safe 12 1 s1_1 := by
  apply safe_succ 11 1 s1_1 [s2_94, s2_106, s2_79, s2_70, s2_47, s2_66, s2_29, s2_37, s2_55, s2_20, s2_5, s2_10, s2_14] (by decide) s1_1_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_94_safe
  · subst z; exact s2_106_safe
  · subst z; exact s2_79_safe
  · subst z; exact s2_70_safe
  · subst z; exact s2_47_safe
  · subst z; exact s2_66_safe
  · subst z; exact s2_29_safe
  · subst z; exact s2_37_safe
  · subst z; exact s2_55_safe
  · subst z; exact s2_20_safe
  · subst z; exact s2_5_safe
  · subst z; exact s2_10_safe
  · subst z; exact s2_14_safe
def s1_2 : State := ⟨4, 8, 64, 132, 5784800237655953878895815070418064179478, 0, 0, 1⟩
theorem s1_2_edges : next 1 s1_2 = [s2_95, s2_107, s2_80, s2_92, s2_71, s2_48, s2_67, s2_30, s2_38, s2_56, s2_8, s2_22] := by decide
theorem s1_2_safe : Safe 12 1 s1_2 := by
  apply safe_succ 11 1 s1_2 [s2_95, s2_107, s2_80, s2_92, s2_71, s2_48, s2_67, s2_30, s2_38, s2_56, s2_8, s2_22] (by decide) s1_2_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_95_safe
  · subst z; exact s2_107_safe
  · subst z; exact s2_80_safe
  · subst z; exact s2_92_safe
  · subst z; exact s2_71_safe
  · subst z; exact s2_48_safe
  · subst z; exact s2_67_safe
  · subst z; exact s2_30_safe
  · subst z; exact s2_38_safe
  · subst z; exact s2_56_safe
  · subst z; exact s2_8_safe
  · subst z; exact s2_22_safe
def s1_3 : State := ⟨4, 8, 64, 136, 87452568298681185110105720854042434928918, 0, 0, 1⟩
theorem s1_3_edges : next 1 s1_3 = [s2_96, s2_108, s2_115, s2_81, s2_72, s2_49, s2_31, s2_39, s2_57, s2_9, s2_7] := by decide
theorem s1_3_safe : Safe 12 1 s1_3 := by
  apply safe_succ 11 1 s1_3 [s2_96, s2_108, s2_115, s2_81, s2_72, s2_49, s2_31, s2_39, s2_57, s2_9, s2_7] (by decide) s1_3_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_96_safe
  · subst z; exact s2_108_safe
  · subst z; exact s2_115_safe
  · subst z; exact s2_81_safe
  · subst z; exact s2_72_safe
  · subst z; exact s2_49_safe
  · subst z; exact s2_31_safe
  · subst z; exact s2_39_safe
  · subst z; exact s2_57_safe
  · subst z; exact s2_9_safe
  · subst z; exact s2_7_safe
def s1_4 : State := ⟨4, 8, 64, 144, 22301085480897544079999200093999871278776598, 0, 0, 1⟩
theorem s1_4_edges : next 1 s1_4 = [s2_98, s2_109, s2_83, s2_74, s2_50, s2_68, s2_32, s2_40, s2_58, s2_24, s2_11, s2_16] := by decide
theorem s1_4_safe : Safe 12 1 s1_4 := by
  apply safe_succ 11 1 s1_4 [s2_98, s2_109, s2_83, s2_74, s2_50, s2_68, s2_32, s2_40, s2_58, s2_24, s2_11, s2_16] (by decide) s1_4_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_98_safe
  · subst z; exact s2_109_safe
  · subst z; exact s2_83_safe
  · subst z; exact s2_74_safe
  · subst z; exact s2_50_safe
  · subst z; exact s2_68_safe
  · subst z; exact s2_32_safe
  · subst z; exact s2_40_safe
  · subst z; exact s2_58_safe
  · subst z; exact s2_24_safe
  · subst z; exact s2_11_safe
  · subst z; exact s2_16_safe
def s1_5 : State := ⟨4, 8, 64, 160, 1461501637671185285124623296198104371165705339158, 0, 0, 1⟩
theorem s1_5_edges : next 1 s1_5 = [s2_99, s2_110, s2_84, s2_75, s2_51, s2_33, s2_41, s2_59, s2_26, s2_13, s2_15, s2_17] := by decide
theorem s1_5_safe : Safe 12 1 s1_5 := by
  apply safe_succ 11 1 s1_5 [s2_99, s2_110, s2_84, s2_75, s2_51, s2_33, s2_41, s2_59, s2_26, s2_13, s2_15, s2_17] (by decide) s1_5_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_99_safe
  · subst z; exact s2_110_safe
  · subst z; exact s2_84_safe
  · subst z; exact s2_75_safe
  · subst z; exact s2_51_safe
  · subst z; exact s2_33_safe
  · subst z; exact s2_41_safe
  · subst z; exact s2_59_safe
  · subst z; exact s2_26_safe
  · subst z; exact s2_13_safe
  · subst z; exact s2_15_safe
  · subst z; exact s2_17_safe
def s1_6 : State := ⟨4, 8, 64, 192, 6277101735386680764176071790128604879584176795973807309078, 0, 0, 1⟩
theorem s1_6_edges : next 1 s1_6 = [s2_100, s2_111, s2_116, s2_85, s2_76, s2_52, s2_34, s2_42, s2_60, s2_23, s2_19, s2_21, s2_25, s2_27] := by decide
theorem s1_6_safe : Safe 12 1 s1_6 := by
  apply safe_succ 11 1 s1_6 [s2_100, s2_111, s2_116, s2_85, s2_76, s2_52, s2_34, s2_42, s2_60, s2_23, s2_19, s2_21, s2_25, s2_27] (by decide) s1_6_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_100_safe
  · subst z; exact s2_111_safe
  · subst z; exact s2_116_safe
  · subst z; exact s2_85_safe
  · subst z; exact s2_76_safe
  · subst z; exact s2_52_safe
  · subst z; exact s2_34_safe
  · subst z; exact s2_42_safe
  · subst z; exact s2_60_safe
  · subst z; exact s2_23_safe
  · subst z; exact s2_19_safe
  · subst z; exact s2_21_safe
  · subst z; exact s2_25_safe
  · subst z; exact s2_27_safe
def s1_7 : State := ⟨4, 8, 65, 128, 340282366920938463518714839657191899414, 0, 0, 0⟩
theorem s1_7_edges : next 1 s1_7 = [s2_101, s2_86, s2_44, s2_30, s2_31, s2_35, s2_28, s2_29, s2_32, s2_33] := by decide
theorem s1_7_safe : Safe 12 1 s1_7 := by
  apply safe_succ 11 1 s1_7 [s2_101, s2_86, s2_44, s2_30, s2_31, s2_35, s2_28, s2_29, s2_32, s2_33] (by decide) s1_7_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_101_safe
  · subst z; exact s2_86_safe
  · subst z; exact s2_44_safe
  · subst z; exact s2_30_safe
  · subst z; exact s2_31_safe
  · subst z; exact s2_35_safe
  · subst z; exact s2_28_safe
  · subst z; exact s2_29_safe
  · subst z; exact s2_32_safe
  · subst z; exact s2_33_safe
def s1_8 : State := ⟨4, 8, 66, 128, 340282366920938463555608327804611002646, 0, 0, 0⟩
theorem s1_8_edges : next 1 s1_8 = [s2_102, s2_87, s2_45, s2_62, s2_38, s2_39, s2_43, s2_36, s2_37, s2_40, s2_41] := by decide
theorem s1_8_safe : Safe 12 1 s1_8 := by
  apply safe_succ 11 1 s1_8 [s2_102, s2_87, s2_45, s2_62, s2_38, s2_39, s2_43, s2_36, s2_37, s2_40, s2_41] (by decide) s1_8_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_102_safe
  · subst z; exact s2_87_safe
  · subst z; exact s2_45_safe
  · subst z; exact s2_62_safe
  · subst z; exact s2_38_safe
  · subst z; exact s2_39_safe
  · subst z; exact s2_43_safe
  · subst z; exact s2_36_safe
  · subst z; exact s2_37_safe
  · subst z; exact s2_40_safe
  · subst z; exact s2_41_safe
def s1_9 : State := ⟨4, 8, 68, 128, 340282366920938463776969256689125622038, 0, 0, 0⟩
theorem s1_9_edges : next 1 s1_9 = [s2_48, s2_49, s2_53, s2_46, s2_47, s2_50, s2_51] := by decide
theorem s1_9_safe : Safe 12 1 s1_9 := by
  apply safe_succ 11 1 s1_9 [s2_48, s2_49, s2_53, s2_46, s2_47, s2_50, s2_51] (by decide) s1_9_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h
  · subst z; exact s2_48_safe
  · subst z; exact s2_49_safe
  · subst z; exact s2_53_safe
  · subst z; exact s2_46_safe
  · subst z; exact s2_47_safe
  · subst z; exact s2_50_safe
  · subst z; exact s2_51_safe
def s1_10 : State := ⟨4, 8, 80, 128, 340282366920939672407640966138947502358, 0, 0, 0⟩
theorem s1_10_edges : next 1 s1_10 = [s2_103, s2_88, s2_63, s2_56, s2_57, s2_61, s2_54, s2_55, s2_58, s2_59] := by decide
theorem s1_10_safe : Safe 12 1 s1_10 := by
  apply safe_succ 11 1 s1_10 [s2_103, s2_88, s2_63, s2_56, s2_57, s2_61, s2_54, s2_55, s2_58, s2_59] (by decide) s1_10_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_103_safe
  · subst z; exact s2_88_safe
  · subst z; exact s2_63_safe
  · subst z; exact s2_56_safe
  · subst z; exact s2_57_safe
  · subst z; exact s2_61_safe
  · subst z; exact s2_54_safe
  · subst z; exact s2_55_safe
  · subst z; exact s2_58_safe
  · subst z; exact s2_59_safe
def s1_11 : State := ⟨4, 8, 96, 128, 340282367000166625996085689103316746518, 0, 0, 0⟩
theorem s1_11_edges : next 1 s1_11 = [s2_104, s2_114, s2_89, s2_90, s2_77, s2_64] := by decide
theorem s1_11_safe : Safe 12 1 s1_11 := by
  apply safe_succ 11 1 s1_11 [s2_104, s2_114, s2_89, s2_90, s2_77, s2_64] (by decide) s1_11_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h
  · subst z; exact s2_104_safe
  · subst z; exact s2_114_safe
  · subst z; exact s2_89_safe
  · subst z; exact s2_90_safe
  · subst z; exact s2_77_safe
  · subst z; exact s2_64_safe
def s1_12 : State := ⟨4, 9, 64, 128, 340282366920938463481821351509772796694, 2, 0, 0⟩
theorem s1_12_edges : next 1 s1_12 = [s2_0, s2_77, s2_71, s2_73, s2_76, s2_69, s2_70, s2_74, s2_75] := by decide
theorem s1_12_safe : Safe 12 1 s1_12 := by
  apply safe_succ 11 1 s1_12 [s2_0, s2_77, s2_71, s2_73, s2_76, s2_69, s2_70, s2_74, s2_75] (by decide) s1_12_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s2_0_safe
  · subst z; exact s2_77_safe
  · subst z; exact s2_71_safe
  · subst z; exact s2_73_safe
  · subst z; exact s2_76_safe
  · subst z; exact s2_69_safe
  · subst z; exact s2_70_safe
  · subst z; exact s2_74_safe
  · subst z; exact s2_75_safe
def s1_13 : State := ⟨4, 12, 64, 128, 340282366920938463481821351509772800278, 2, 0, 0⟩
theorem s1_13_edges : next 1 s1_13 = [s2_2, s2_86, s2_87, s2_88, s2_89, s2_80, s2_82, s2_85, s2_78, s2_79, s2_83, s2_84] := by decide
theorem s1_13_safe : Safe 12 1 s1_13 := by
  apply safe_succ 11 1 s1_13 [s2_2, s2_86, s2_87, s2_88, s2_89, s2_80, s2_82, s2_85, s2_78, s2_79, s2_83, s2_84] (by decide) s1_13_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_2_safe
  · subst z; exact s2_86_safe
  · subst z; exact s2_87_safe
  · subst z; exact s2_88_safe
  · subst z; exact s2_89_safe
  · subst z; exact s2_80_safe
  · subst z; exact s2_82_safe
  · subst z; exact s2_85_safe
  · subst z; exact s2_78_safe
  · subst z; exact s2_79_safe
  · subst z; exact s2_83_safe
  · subst z; exact s2_84_safe
def s1_14 : State := ⟨12, 8, 64, 128, 340282366920938463481821351509772800278, 1, 0, 0⟩
theorem s1_14_edges : next 1 s1_14 = [s2_1, s2_101, s2_102, s2_103, s2_104, s2_97, s2_96, s2_100, s2_93, s2_94, s2_98, s2_99] := by decide
theorem s1_14_safe : Safe 12 1 s1_14 := by
  apply safe_succ 11 1 s1_14 [s2_1, s2_101, s2_102, s2_103, s2_104, s2_97, s2_96, s2_100, s2_93, s2_94, s2_98, s2_99] (by decide) s1_14_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s2_1_safe
  · subst z; exact s2_101_safe
  · subst z; exact s2_102_safe
  · subst z; exact s2_103_safe
  · subst z; exact s2_104_safe
  · subst z; exact s2_97_safe
  · subst z; exact s2_96_safe
  · subst z; exact s2_100_safe
  · subst z; exact s2_93_safe
  · subst z; exact s2_94_safe
  · subst z; exact s2_98_safe
  · subst z; exact s2_99_safe
def s1_15 : State := ⟨68, 8, 64, 128, 340282366920938463776969256689125622038, 1, 0, 0⟩
theorem s1_15_edges : next 1 s1_15 = [s2_3, s2_113, s2_112, s2_108, s2_111, s2_105, s2_106, s2_109, s2_110] := by decide
theorem s1_15_safe : Safe 12 1 s1_15 := by
  apply safe_succ 11 1 s1_15 [s2_3, s2_113, s2_112, s2_108, s2_111, s2_105, s2_106, s2_109, s2_110] (by decide) s1_15_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h
  · subst z; exact s2_3_safe
  · subst z; exact s2_113_safe
  · subst z; exact s2_112_safe
  · subst z; exact s2_108_safe
  · subst z; exact s2_111_safe
  · subst z; exact s2_105_safe
  · subst z; exact s2_106_safe
  · subst z; exact s2_109_safe
  · subst z; exact s2_110_safe
def s0_0 : State := ⟨4, 8, 64, 128, 340282366920938463481821351509772796182, 0, 0, 0⟩
theorem s0_0_edges : next 0 s0_0 = [s1_14, s1_15, s1_13, s1_12, s1_9, s1_7, s1_8, s1_10, s1_11, s1_2, s1_3, s1_6, s1_0, s1_1, s1_4, s1_5] := by decide
theorem s0_0_safe : Safe 13 0 s0_0 := by
  apply safe_succ 12 0 s0_0 [s1_14, s1_15, s1_13, s1_12, s1_9, s1_7, s1_8, s1_10, s1_11, s1_2, s1_3, s1_6, s1_0, s1_1, s1_4, s1_5] (by decide) s0_0_edges
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst z; exact s1_14_safe
  · subst z; exact s1_15_safe
  · subst z; exact s1_13_safe
  · subst z; exact s1_12_safe
  · subst z; exact s1_9_safe
  · subst z; exact s1_7_safe
  · subst z; exact s1_8_safe
  · subst z; exact s1_10_safe
  · subst z; exact s1_11_safe
  · subst z; exact s1_2_safe
  · subst z; exact s1_3_safe
  · subst z; exact s1_6_safe
  · subst z; exact s1_0_safe
  · subst z; exact s1_1_safe
  · subst z; exact s1_4_safe
  · subst z; exact s1_5_safe
theorem initial_safe : Safe 13 0 s0_0 := s0_0_safe
theorem no_terminal {k z} (h : Reach 0 s0_0 k z) (hk : k ≤ 13) : terminal z = false := safe_reach h 13 hk initial_safe
#print axioms no_terminal
end HGP13.SectorPilot284
