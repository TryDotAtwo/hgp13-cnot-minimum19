import Passive
import Budget

namespace HGP13.PassiveCost

def best : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

def AtMost (c : Option Nat) (k : Nat) : Prop := ∃ n, c = some n ∧ n ≤ k

/-- Absence denotes infinity; no arbitrary numeric sentinel is used. -/
def cost : List Row → Row → Option Nat
  | [], z => if z = 0 then some 0 else none
  | v :: d, z => best (cost d z) ((cost d (z ^^^ v)).map Nat.succ)

def Represent (d : List Row) (z : Row) (k : Nat) : Prop :=
  ∃ b : List Row, b.Sublist d ∧ xorSum b = z ∧ b.length ≤ k

theorem best_atMost (a b : Option Nat) (k : Nat) :
    AtMost (best a b) k ↔ AtMost a k ∨ AtMost b k := by
  cases a <;> cases b <;> simp [best,AtMost] <;> omega

theorem succ_atMost (a : Option Nat) (k : Nat) :
    AtMost (a.map Nat.succ) k ↔ ∃ n, n + 1 ≤ k ∧ AtMost a n := by
  cases a with
  | none => simp [AtMost]
  | some a =>
    constructor
    · rintro ⟨n,hn,hk⟩
      have he : a + 1 = n := Option.some.inj hn
      exact ⟨a,by omega,a,rfl,Nat.le_refl _⟩
    · rintro ⟨n,hn,m,hm,hk⟩
      have he : a = m := Option.some.inj hm
      exact ⟨a + 1,rfl,by omega⟩

theorem xor_cancel_left (a b : Row) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc]
  simp

theorem xor_solve (a b z : Row) : a ^^^ b = z ↔ b = z ^^^ a := by
  constructor
  · intro h
    rw [← h,BitVec.xor_comm a b,BitVec.xor_assoc]
    simp
  · intro h
    rw [h,BitVec.xor_comm z a,xor_cancel_left]

theorem represent_cons (v : Row) (d : List Row) (z : Row) (k : Nat) :
    Represent (v :: d) z k ↔ Represent d z k ∨ ∃ n, n + 1 ≤ k ∧ Represent d (z ^^^ v) n := by
  constructor
  · rintro ⟨b,hb,hz,hk⟩
    rcases List.sublist_cons_iff.mp hb with hb | ⟨a,he,ha⟩
    · exact Or.inl ⟨b,hb,hz,hk⟩
    · subst b
      apply Or.inr
      refine ⟨a.length,?_,a,ha,?_,Nat.le_refl _⟩
      · exact hk
      · exact (xor_solve v (xorSum a) z).mp hz
  · rintro (⟨b,hb,hz,hk⟩ | ⟨n,hn,b,hb,hz,hk⟩)
    · exact ⟨b,hb.cons v,hz,hk⟩
    · refine ⟨v :: b,hb.cons_cons v,?_,by simp only [List.length_cons]; omega⟩
      exact (xor_solve v (xorSum b) z).mpr hz

/-- Exact 0/1 recurrence: it finds a representation within a budget
if and only if one exists among the sublists. -/
theorem cost_atMost_iff (d : List Row) (z : Row) (k : Nat) :
    AtMost (cost d z) k ↔ Represent d z k := by
  induction d generalizing z k with
  | nil =>
    by_cases hz : z = 0
    · subst z; simp [cost,AtMost,Represent,xorSum]
    · have hz' : z ≠ (0#13) := hz
      simp [cost,AtMost,Represent,xorSum,hz',Ne.symm hz']
  | cons v d ih =>
    simp only [cost,best_atMost,succ_atMost,ih,represent_cons]

theorem cost_attains (d : List Row) (z : Row) (n : Nat) (h : cost d z = some n) :
    ∃ b : List Row, b.Sublist d ∧ xorSum b = z ∧ b.length = n := by
  obtain ⟨b,hb,hz,hn⟩ := (cost_atMost_iff d z n).mp ⟨n,h,Nat.le_refl _⟩
  have bound := (cost_atMost_iff d z b.length).mpr ⟨b,hb,hz,Nat.le_refl _⟩
  obtain ⟨m,hm,hmn⟩ := bound
  have eq : m = n := by rw [h] at hm; exact Option.some.inj hm.symm
  exact ⟨b,hb,hz,by omega⟩

theorem cost_minimal (d b : List Row) (z : Row) (n : Nat)
    (hc : cost d z = some n) (hb : b.Sublist d) (hz : xorSum b = z) : n ≤ b.length := by
  obtain ⟨m,hm,hn⟩ := (cost_atMost_iff d z b.length).mpr ⟨b,hb,hz,Nat.le_refl _⟩
  have eq : m = n := by rw [hc] at hm; exact Option.some.inj hm.symm
  omega

theorem cost_none_iff (d : List Row) (z : Row) :
    cost d z = none ↔ ¬ ∃ b : List Row, b.Sublist d ∧ xorSum b = z := by
  constructor
  · intro hc ⟨b,hb,hz⟩
    obtain ⟨n,hn,_⟩ := (cost_atMost_iff d z b.length).mpr ⟨b,hb,hz,Nat.le_refl _⟩
    rw [hc] at hn
    contradiction
  · intro hn
    cases hc : cost d z with
    | none => rfl
    | some n =>
      obtain ⟨b,hb,hz,_⟩ := cost_attains d z n hc
      exact False.elim (hn ⟨b,hb,hz⟩)


theorem xorSum_erase (p : List Row) (a : Row) (ha : a ∈ p) :
    xorSum p = a ^^^ xorSum (p.erase a) := by
  induction p with
  | nil => simp at ha
  | cons b p ih =>
    by_cases he : b = a
    · subst b; simp [xorSum]
    · have ht : a ∈ p := (List.mem_cons.mp ha).resolve_left (Ne.symm he)
      rw [List.erase_cons_tail (by simpa using he),xorSum,ih ht]
      simp only [xorSum]
      rw [← BitVec.xor_assoc,BitVec.xor_comm b a,BitVec.xor_assoc]

/-- Cancel pairs, retaining a duplicate-free list with the same full XOR. -/
def cancelPairs : List Row → List Row
  | [] => []
  | a :: p => let q := cancelPairs p; if a ∈ q then q.erase a else a :: q

theorem cancelPairs_spec (p : List Row) :
    (cancelPairs p).Nodup ∧ cancelPairs p ⊆ p ∧
      xorSum (cancelPairs p) = xorSum p ∧ (cancelPairs p).length ≤ p.length := by
  induction p with
  | nil => simp [cancelPairs,xorSum]
  | cons a p ih =>
    obtain ⟨hn,hs,hx,hl⟩ := ih
    by_cases ha : a ∈ cancelPairs p
    · simp only [cancelPairs,ha,ite_true]
      refine ⟨List.Pairwise.erase a hn,?_,?_,?_⟩
      · intro z hz; exact List.mem_cons_of_mem _ (hs (List.mem_of_mem_erase hz))
      · have he := xorSum_erase (cancelPairs p) a ha
        rw [xorSum,← hx,he,xor_cancel_left]
      · have he := List.length_erase_le (l := cancelPairs p) (a := a)
        simp only [List.length_cons]
        omega
    · simp only [cancelPairs,ha,ite_false]
      refine ⟨List.nodup_cons.mpr ⟨ha,hn⟩,?_,?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with hz | hz
        · exact List.mem_cons.mpr (Or.inl hz)
        · exact List.mem_cons_of_mem _ (hs hz)
      · simp only [xorSum,hx]
      · simp only [List.length_cons]; omega

/-- Reorder a duplicate-free representation into catalogue order. -/
theorem subset_to_sublist (d b : List Row) (hn : b.Nodup) (hs : b ⊆ d) :
    ∃ c : List Row, c.Sublist d ∧ xorSum c = xorSum b ∧ c.length = b.length := by
  induction d generalizing b with
  | nil =>
    have hb : b = [] := by simpa using hs
    subst b
    exact ⟨[],List.Sublist.refl _,rfl,rfl⟩
  | cons a d ih =>
    by_cases ha : a ∈ b
    · have sub : b.erase a ⊆ d := by
        intro z hz
        have hm := hs (List.mem_of_mem_erase hz)
        have he : z ≠ a := by
          intro eq
          subst z
          have no : a ∉ b.erase a := by rw [hn.erase_eq_filter]; simp
          exact no hz
        exact (List.mem_cons.mp hm).resolve_left he
      obtain ⟨c,hc,hx,hl⟩ := ih (b.erase a) (List.Pairwise.erase a hn) sub
      refine ⟨a :: c,hc.cons_cons a,?_,?_⟩
      · rw [xorSum,hx,← xorSum_erase b a ha]
      · rw [List.length_cons,hl,List.length_erase_of_mem ha]
        have pos := List.length_pos_of_mem ha
        omega
    · have sub : b ⊆ d := by
        intro z hz
        have he : z ≠ a := by intro he; subst z; exact ha hz
        exact (List.mem_cons.mp (hs hz)).resolve_left he
      obtain ⟨c,hc,hx,hl⟩ := ih b hn sub
      exact ⟨c,hc.cons a,hx,hl⟩

/-- Arbitrary repetitions cannot beat the 0/1 optimum. -/
theorem cost_le_arbitrary (d b : List Row) (hs : b ⊆ d) :
    AtMost (cost d (xorSum b)) b.length := by
  obtain ⟨hn,hsub,hx,hl⟩ := cancelPairs_spec b
  obtain ⟨c,hc,hcx,hcl⟩ := subset_to_sublist d (cancelPairs b) hn (fun _ hz => hs (hsub hz))
  apply (cost_atMost_iff d (xorSum b) b.length).mpr
  exact ⟨c,hc,hcx.trans hx,by omega⟩


/-- The exact number of updates to one target. -/
def targetCount (j : Wire) (p : Program) : Nat := (p.filter (fun g => g.2 == j)).length

theorem contributions_count (p : Program) (x : Matrix) (j : Wire) :
    (contributions j x p).length = targetCount j p := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    by_cases he : g.2 = j
    · simp [contributions,targetCount,he,ih]
    · simp [contributions,targetCount,he,ih]

/-- A history cover contains full rows, including all private coefficients. -/
def CoversHistory (keep : Wire → Bool) (x : Matrix) (p : Program) (d : List Row) : Prop :=
  ∀ a b, p = a ++ b → ∀ i, keep i = true → run x a i ∈ d

theorem contributions_in_history (p : Program) (x : Matrix) (j : Wire) (keep : Wire → Bool) (d : List Row)
    (controls : ∀ g ∈ p, keep g.1 = true) (cover : CoversHistory keep x p d) :
    contributions j x p ⊆ d := by
  induction p generalizing x with
  | nil => simp [contributions]
  | cons g p ih =>
    have hc : ∀ k ∈ p, keep k.1 = true := fun k hk => controls k (List.mem_cons_of_mem _ hk)
    have ht : CoversHistory keep (step x g) p d := by
      intro a b he i hi
      exact cover (g :: a) b (by simp [he]) i hi
    have sub := ih (step x g) hc ht
    have head : x g.1 ∈ d := cover [] (g :: p) rfl g.1 (controls g List.mem_cons_self)
    by_cases he : g.2 = j
    · simp only [contributions,he,ite_true]
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · exact hz ▸ head
      · exact sub hz
    · simpa only [contributions,he,ite_false] using sub

theorem actual_target_cost_bound (p : Program) (x : Matrix) (j : Wire) (keep : Wire → Bool) (d : List Row)
    (controls : ∀ g ∈ p, keep g.1 = true) (cover : CoversHistory keep x p d) :
    AtMost (cost d (x j ^^^ run x p j)) (targetCount j p) := by
  have hh := cost_le_arbitrary d (contributions j x p) (contributions_in_history p x j keep d controls cover)
  rw [row_accounting,xor_cancel_left,← contributions_count p x j]
  exact hh


theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem indicator_sum (js : List Wire) (j : Wire) (hn : js.Nodup) :
    (js.map (fun i => if j = i then 1 else 0)).sum = if j ∈ js then 1 else 0 := by
  induction js with
  | nil => simp
  | cons i js ih =>
    obtain ⟨hi,ht⟩ := List.nodup_cons.mp hn
    by_cases he : j = i
    · subst j; simp [ih ht,hi]
    · simp [he,ih ht]

theorem targetCount_cons (j : Wire) (g : Gate) (p : Program) :
    targetCount j (g :: p) = (if g.2 = j then 1 else 0) + targetCount j p := by
  by_cases he : g.2 = j <;> simp [targetCount,he,Nat.add_comm]

theorem targets_count_total (js : List Wire) (p : Program) (hn : js.Nodup) :
    (js.map (fun j => targetCount j p)).sum = (p.filter (fun g => js.contains g.2)).length := by
  induction p with
  | nil =>
    have hz : (js.map (fun _ => (0 : Nat))).sum = 0 := by
      clear hn
      induction js with
      | nil => rfl
      | cons j js ih => simp [ih]
    simpa [targetCount] using hz
  | cons g p ih =>
    simp only [targetCount_cons,sum_map_add,indicator_sum js g.2 hn,ih]
    by_cases he : g.2 ∈ js <;> simp [he,Nat.add_comm]

theorem passive_count_partition (keep : Wire → Bool) (js : List Wire) (p : Program)
    (hn : js.Nodup) (coverage : ∀ j, j ∈ js ↔ keep j = false) :
    p.length = (p.filter (fun g => keep g.2)).length + (js.map (fun j => targetCount j p)).sum := by
  have hf : p.filter (fun g => js.contains g.2) = p.filter (fun g => !keep g.2) := by
    apply List.filter_congr
    intro g _
    apply Bool.eq_iff_iff.mpr
    simp [coverage]
  rw [targets_count_total js p hn,hf]
  exact (CountHelpers.filter_partition (fun g : Gate => keep g.2) p).symm

theorem total_cost_lower_bound (keep : Wire → Bool) (js : List Wire) (p : Program)
    (d : List Row) (m : Matrix) (n : Wire → Nat)
    (controls : ∀ g ∈ p, keep g.1 = true) (cover : CoversHistory keep identity p d)
    (distinct : js.Nodup) (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (final : run identity p = m) (costs : ∀ j ∈ js, cost d (identity j ^^^ m j) = some (n j)) :
    (p.filter (fun g => keep g.2)).length + (js.map n).sum ≤ p.length := by
  have each : ∀ j ∈ js, n j ≤ targetCount j p := by
    intro j hj
    obtain ⟨k,hk,hn⟩ := actual_target_cost_bound p identity j keep d controls cover
    rw [final,costs j hj] at hk
    have eq := Option.some.inj hk
    omega
  have hs := sum_map_le js n (fun j => targetCount j p) each
  have hp := passive_count_partition keep js p distinct coverage
  omega


/-- The optimum is attained by a genuine set of distinct available forms. -/
theorem cost_attains_distinct (d : List Row) (z : Row) (n : Nat) (hc : cost d z = some n) :
    ∃ b : List Row, b.Nodup ∧ b ⊆ d ∧ xorSum b = z ∧ b.length = n := by
  obtain ⟨b,hb,hz,hn⟩ := cost_attains d z n hc
  obtain ⟨distinct,subset,same,bound⟩ := cancelPairs_spec b
  have sub : cancelPairs b ⊆ d := fun _ hw => hb.subset (subset hw)
  have hcost := cost_le_arbitrary d (cancelPairs b) sub
  obtain ⟨k,hk,kl⟩ := hcost
  rw [same,hz,hc] at hk
  have eq := Option.some.inj hk
  exact ⟨cancelPairs b,distinct,sub,same.trans hz,by omega⟩

theorem cost_positive (d : List Row) (z : Row) (n : Nat)
    (hc : cost d z = some n) (hz : z ≠ 0) : 1 ≤ n := by
  obtain ⟨b,_,hb,hn⟩ := cost_attains d z n hc
  by_cases he : n = 0
  · have empty : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst b
    exact False.elim (hz hb.symm)
  · omega

theorem sum_ones (js : List Wire) : (js.map (fun _ => (1 : Nat))).sum = js.length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [ih,Nat.add_comm]

theorem changed_target_positive (p : Program) (j : Wire) (changed : run identity p j ≠ identity j) :
    1 ≤ targetCount j p := by
  by_cases hz : targetCount j p = 0
  · have empty : contributions j identity p = [] :=
      List.eq_nil_of_length_eq_zero (by rw [contributions_count,hz])
    have eq := row_accounting p identity j
    exact False.elim (changed (by simpa [empty,xorSum] using eq))
  · omega

/-- Source equation (9), before substituting the number of active outputs. -/
theorem core_length_bound (keep : Wire → Bool) (js : List Wire) (p : Program)
    (distinct : js.Nodup) (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (changed : ∀ j ∈ js, run identity p j ≠ identity j) :
    (p.filter (fun g => keep g.2)).length + js.length ≤ p.length := by
  have hs := sum_map_le js (fun _ => 1) (fun j => targetCount j p)
    (fun j hj => changed_target_positive p j (changed j hj))
  rw [sum_ones] at hs
  have partition := passive_count_partition keep js p distinct coverage
  omega

end HGP13.PassiveCost



