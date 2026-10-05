import PassiveCost
import CleanPersistence

namespace HGP13.PassiveInsertion
open PassiveCost CleanPersistence

/-- Add a fixed full row to one coordinate. -/
def addAt (x : Matrix) (j : Wire) (w : Row) : Matrix :=
  fun i => if i = j then x i ^^^ w else x i

theorem addAt_other (x : Matrix) (j i : Wire) (w : Row) (hi : i ≠ j) : addAt x j w i = x i := by
  simp [addAt,hi]

theorem step_addAt (x : Matrix) (j : Wire) (w : Row) (g : Gate) (hc : g.1 ≠ j) :
    step (addAt x j w) g = addAt (step x g) j w := by
  funext i
  by_cases hit : i = g.2
  · subst i
    by_cases ht : g.2 = j
    · simp only [step,ite_true,addAt,ht,hc,ite_false]
      rw [BitVec.xor_assoc,BitVec.xor_comm w (x g.1),← BitVec.xor_assoc]
    · simp [step,addAt,ht,hc]
  · simp [step,addAt,hit]

theorem run_addAt (p : Program) (x : Matrix) (j : Wire) (w : Row)
    (hc : ∀ g ∈ p, g.1 ≠ j) : run (addAt x j w) p = addAt (run x p) j w := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    rw [run_cons,step_addAt x j w g (hc g List.mem_cons_self)]
    exact ih (step x g) (fun k hk => hc k (List.mem_cons_of_mem _ hk))

theorem step_is_addAt (x : Matrix) (c j : Wire) : step x (c,j) = addAt x j (x c) := by
  rfl

/-- A transfer can be inserted at a historical occurrence of its control
without changing any other final row. -/
theorem insert_transfer (a b : Program) (c j : Wire)
    (hc : ∀ g ∈ b, g.1 ≠ j) :
    run identity (a ++ (c,j) :: b) =
      addAt (run identity (a ++ b)) j (run identity a c) := by
  rw [run_append,run_cons,step_is_addAt,run_addAt b _ j _ hc,run_append]

/-- One historical insertion preserves the exact erased core word. -/
theorem insert_historical (keep : Wire → Bool) (p : Program) (j : Wire) (w : Row)
    (legal : Legal p) (controls : ∀ g ∈ p, keep g.1 = true) (passive : keep j = false)
    (history : CoreHistory keep p w) :
    ∃ q : Program, Legal q ∧ (∀ g ∈ q, keep g.1 = true) ∧
      q.filter (fun g => keep g.2) = p.filter (fun g => keep g.2) ∧
      q.length = p.length + 1 ∧ run identity q = addAt (run identity p) j w := by
  obtain ⟨a,b,he,c,hc,hw⟩ := history
  subst p
  have cj : c ≠ j := by intro he; subst c; rw [passive] at hc; contradiction
  refine ⟨a ++ (c,j) :: b,?_,?_,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact legal g (List.mem_append_left _ hg)
    · rcases List.mem_cons.mp hg with he | hg
      · subst g; exact cj
      · exact legal g (List.mem_append_right _ hg)
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact controls g (List.mem_append_left _ hg)
    · rcases List.mem_cons.mp hg with he | hg
      · subst g; exact hc
      · exact controls g (List.mem_append_right _ hg)
  · simp [passive]
  · simp [List.length_append,List.length_cons,Nat.add_assoc]
  · rw [insert_transfer a b c j]
    · rw [hw]
    · intro g hg he
      have hh := controls g (List.mem_append_right _ hg)
      rw [he,passive] at hh
      contradiction

/-- Identical erased words have exactly the same full core history. -/
theorem same_core_history (keep : Wire → Bool) (p q : Program) (w : Row)
    (pc : ∀ g ∈ p, keep g.1 = true) (qc : ∀ g ∈ q, keep g.1 = true)
    (he : p.filter (fun g => keep g.2) = q.filter (fun g => keep g.2)) :
    CoreHistory keep p w ↔ CoreHistory keep q w := by
  rw [← core_history_erasure_iff keep p w pc,← core_history_erasure_iff keep q w qc,he]

/-- Sequential insertions are valid even when chosen forms occurred at
unrelated times. Their temporal order is not assumed to match list order. -/
theorem insert_representation (keep : Wire → Bool) (p : Program) (j : Wire) (values : List Row)
    (legal : Legal p) (controls : ∀ g ∈ p, keep g.1 = true) (passive : keep j = false)
    (history : ∀ w ∈ values, CoreHistory keep p w) :
    ∃ q : Program, Legal q ∧ (∀ g ∈ q, keep g.1 = true) ∧
      q.filter (fun g => keep g.2) = p.filter (fun g => keep g.2) ∧
      q.length = p.length + values.length ∧ run identity q = addAt (run identity p) j (xorSum values) := by
  induction values with
  | nil =>
    refine ⟨p,legal,controls,rfl,by simp,?_⟩
    funext i
    simp [addAt,xorSum]
  | cons w values ih =>
    obtain ⟨q,ql,qc,qf,qn,qr⟩ := ih (fun v hv => history v (List.mem_cons_of_mem _ hv))
    have wh := (same_core_history keep p q w controls qc qf.symm).mp (history w List.mem_cons_self)
    obtain ⟨s,sl,sc,sf,sn,sr⟩ := insert_historical keep q j w ql qc passive wh
    refine ⟨s,sl,sc,sf.trans qf,?_,?_⟩
    · simp only [List.length_cons]; omega
    · rw [sr,qr]
      funext i
      by_cases hi : i = j
      · simp only [addAt,hi,ite_true,xorSum]
        rw [BitVec.xor_assoc,BitVec.xor_comm (xorSum values) w]
      · simp [addAt,hi]

/-- An attained dynamic-programming optimum can be realized by legal
historical insertions at exactly that additional cost. -/
theorem insert_optimal (keep : Wire → Bool) (p : Program) (j : Wire) (d : List Row) (z : Row) (n : Nat)
    (legal : Legal p) (controls : ∀ g ∈ p, keep g.1 = true) (passive : keep j = false)
    (history : ∀ w ∈ d, CoreHistory keep p w) (hc : cost d z = some n) :
    ∃ q : Program, Legal q ∧ (∀ g ∈ q, keep g.1 = true) ∧
      q.filter (fun g => keep g.2) = p.filter (fun g => keep g.2) ∧
      q.length = p.length + n ∧ run identity q = addAt (run identity p) j z := by
  obtain ⟨b,hb,hz,hn⟩ := cost_attains d z n hc
  obtain ⟨q,ql,qc,qf,qn,qr⟩ := insert_representation keep p j b legal controls passive
    (fun w hw => history w (hb.subset hw))
  exact ⟨q,ql,qc,qf,by rw [hn] at qn; exact qn,by rw [hz] at qr; exact qr⟩


/-- Independent optimal insertions for all chosen passive targets. -/
theorem insert_many_optimal (keep : Wire → Bool) (p : Program) (js : List Wire)
    (d : List Row) (z : Wire → Row) (n : Wire → Nat)
    (legal : Legal p) (controls : ∀ g ∈ p, keep g.1 = true) (distinct : js.Nodup)
    (passive : ∀ j ∈ js, keep j = false) (history : ∀ w ∈ d, CoreHistory keep p w)
    (costs : ∀ j ∈ js, cost d (z j) = some (n j)) :
    ∃ q : Program, Legal q ∧ (∀ g ∈ q, keep g.1 = true) ∧
      q.filter (fun g => keep g.2) = p.filter (fun g => keep g.2) ∧
      q.length = p.length + (js.map n).sum ∧
      ∀ i, run identity q i = if i ∈ js then run identity p i ^^^ z i else run identity p i := by
  induction js with
  | nil => exact ⟨p,legal,controls,rfl,by simp,by intro i; simp⟩
  | cons j js ih =>
    obtain ⟨notin,nd⟩ := List.nodup_cons.mp distinct
    obtain ⟨q,ql,qc,qf,qn,qr⟩ := ih nd
      (fun i hi => passive i (List.mem_cons_of_mem _ hi))
      (fun i hi => costs i (List.mem_cons_of_mem _ hi))
    have dh : ∀ w ∈ d, CoreHistory keep q w := fun w hw =>
      (same_core_history keep p q w controls qc qf.symm).mp (history w hw)
    obtain ⟨s,sl,sc,sf,sn,sr⟩ := insert_optimal keep q j d (z j) (n j) ql qc
      (passive j List.mem_cons_self) dh (costs j List.mem_cons_self)
    refine ⟨s,sl,sc,sf.trans qf,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons]; omega
    · intro i
      rw [sr]
      by_cases hi : i = j
      · subst i; simp [addAt,qr,notin]
      · simp [addAt,hi,qr]

/-- A core with its final rows fixed can be completed to the entire operator
by optimal independent passive insertions. -/
theorem complete_core (keep : Wire → Bool) (p : Program) (js : List Wire)
    (d : List Row) (m : Matrix) (n : Wire → Nat)
    (legal : Legal p) (controls : ∀ g ∈ p, keep g.1 = true)
    (targets : ∀ g ∈ p, keep g.2 = true) (distinct : js.Nodup)
    (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (history : ∀ w ∈ d, CoreHistory keep p w)
    (costs : ∀ j ∈ js, cost d (identity j ^^^ m j) = some (n j))
    (finalCore : ∀ i, keep i = true → run identity p i = m i) :
    ∃ q : Program, Legal q ∧ (∀ g ∈ q, keep g.1 = true) ∧
      q.filter (fun g => keep g.2) = p ∧
      q.length = p.length + (js.map n).sum ∧ run identity q = m := by
  obtain ⟨q,ql,qc,qf,qn,qr⟩ := insert_many_optimal keep p js d (fun j => identity j ^^^ m j) n
    legal controls distinct (fun j hj => (coverage j).mp hj) history costs
  have pf : p.filter (fun g => keep g.2) = p := List.filter_eq_self.mpr targets
  refine ⟨q,ql,qc,qf.trans pf,qn,?_⟩
  funext i
  rw [qr]
  by_cases hi : i ∈ js
  · rw [ite_eq_left hi]
    have passive := (coverage i).mp hi
    have untouched : i ∉ p.map Prod.snd := by
      intro hm
      obtain ⟨g,hg,he⟩ := List.mem_map.mp hm
      have ht := targets g hg
      rw [he,passive] at ht
      contradiction
    rw [Budget.run_untargeted p identity i untouched,xor_cancel_left]
  · rw [ite_eq_right hi]
    have hk : keep i = true := by
      cases he : keep i with
      | true => rfl
      | false => exact False.elim (hi ((coverage i).mpr he))
    exact finalCore i hk


def currentRows (keep : Wire → Bool) (x : Matrix) : List Row :=
  ((List.finRange 13).filter keep).map x

def historyRows (keep : Wire → Bool) (x : Matrix) : Program → List Row
  | [] => currentRows keep x
  | g :: p => currentRows keep x ++ historyRows keep (step x g) p

theorem currentRows_members (keep : Wire → Bool) (x : Matrix) (w : Row) :
    w ∈ currentRows keep x ↔ ∃ i, keep i = true ∧ x i = w := by
  simp [currentRows]

theorem historyRows_members (keep : Wire → Bool) (p : Program) (x : Matrix) (w : Row) :
    w ∈ historyRows keep x p ↔ ∃ a b, p = a ++ b ∧ ∃ i, keep i = true ∧ run x a i = w := by
  induction p generalizing x with
  | nil =>
    simp only [historyRows,currentRows_members]
    constructor
    · rintro ⟨i,hi,hw⟩; exact ⟨[],[],rfl,i,hi,hw⟩
    · rintro ⟨a,b,he,i,hi,hw⟩
      have ha : a = [] := (show a = [] ∧ b = [] from by simpa using he.symm).1
      subst a
      exact ⟨i,hi,hw⟩
  | cons g p ih =>
    simp only [historyRows,List.mem_append,currentRows_members,ih]
    constructor
    · rintro (⟨i,hi,hw⟩ | ⟨a,b,he,i,hi,hw⟩)
      · exact ⟨[],g :: p,rfl,i,hi,hw⟩
      · exact ⟨g :: a,b,by simp [he],i,hi,hw⟩
    · rintro ⟨a,b,he,i,hi,hw⟩
      cases a with
      | nil => exact Or.inl ⟨i,hi,hw⟩
      | cons k a =>
        have hk : k = g := (List.cons.inj he).1.symm
        subst k
        have hp := (List.cons.inj he).2
        exact Or.inr ⟨a,b,hp,i,hi,hw⟩

theorem historyRows_exact (keep : Wire → Bool) (p : Program) (w : Row) :
    w ∈ historyRows keep identity p ↔ CoreHistory keep p w :=
  historyRows_members keep p identity w

theorem erased_history_covers (keep : Wire → Bool) (p core : Program)
    (controls : ∀ g ∈ p, keep g.1 = true)
    (erased : p.filter (fun g => keep g.2) = core) :
    CoversHistory keep identity p (historyRows keep identity core) := by
  intro a b he i hi
  have hm : CoreHistory keep p (run identity a i) := ⟨a,b,he,i,hi,rfl⟩
  have hc := core_history_survives_erasure keep p _ controls hm
  rw [erased] at hc
  exact (historyRows_exact keep core _).mpr hc

def Completion (keep : Wire → Bool) (core : Program) (m : Matrix) (p : Program) : Prop :=
  Legal p ∧ (∀ g ∈ p, keep g.1 = true) ∧
    p.filter (fun g => keep g.2) = core ∧ run identity p = m

/-- Exact passive-elimination theorem: the lower bound is attained by a
legal completion with this exact core, and applies to every completion. -/
theorem exact_passive_minimum (keep : Wire → Bool) (core : Program) (js : List Wire)
    (m : Matrix) (n : Wire → Nat)
    (legal : Legal core) (controls : ∀ g ∈ core, keep g.1 = true)
    (targets : ∀ g ∈ core, keep g.2 = true) (distinct : js.Nodup)
    (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (costs : ∀ j ∈ js, cost (historyRows keep identity core) (identity j ^^^ m j) = some (n j))
    (finalCore : ∀ i, keep i = true → run identity core i = m i) :
    (∃ p, Completion keep core m p ∧ p.length = core.length + (js.map n).sum) ∧
      ∀ p, Completion keep core m p → core.length + (js.map n).sum ≤ p.length := by
  constructor
  · obtain ⟨p,pl,pc,pf,pn,pm⟩ := complete_core keep core js (historyRows keep identity core) m n
      legal controls targets distinct coverage (fun w hw => (historyRows_exact keep core w).mp hw) costs finalCore
    exact ⟨p,⟨pl,pc,pf,pm⟩,pn⟩
  · intro p hp
    obtain ⟨_,pc,pf,pm⟩ := hp
    have h := total_cost_lower_bound keep js p (historyRows keep identity core) m n pc
      (erased_history_covers keep p core pc pf) distinct coverage pm costs
    simpa only [pf] using h


def basisRows : List Row := [1,2,4,8,16,32,256]

def basisRepresentation (w : Row) : List Row := basisRows.filter (fun b => (w &&& b) != 0)

theorem basis_rows_identity : basisRows = (Budget.sources ++ [8]).map identity := by decide

theorem original_basis_representation : ∀ j ∈ Budget.privateOutputs,
    xorSum (basisRepresentation (identity j ^^^ target j)) = identity j ^^^ target j := by decide

theorem transpose_basis_representation : ∀ j ∈ Budget.privateOutputs,
    xorSum (basisRepresentation (identity j ^^^ TransposeTarget.matrix j)) = identity j ^^^ TransposeTarget.matrix j := by decide

theorem basis_in_history (keep : Wire → Bool) (p : Program)
    (sources : ∀ i ∈ Budget.sources, keep i = true) (center : keep 8 = true) :
    basisRows ⊆ historyRows keep identity p := by
  intro w hw
  rw [basis_rows_identity] at hw
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hw
  apply (historyRows_exact keep p w).mpr
  refine ⟨[],p,rfl,i,?_,he⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact sources i hi
  · have he : i = 8 := by simpa using hi
    exact he ▸ center

theorem wire_partition : ∀ i : Wire, i ∈ Budget.sources ∨ i = 8 ∨ i ∈ Budget.privateOutputs := by decide

theorem passive_is_private (keep : Wire → Bool) (j : Wire)
    (sources : ∀ i ∈ Budget.sources, keep i = true) (center : keep 8 = true)
    (passive : keep j = false) : j ∈ Budget.privateOutputs := by
  rcases wire_partition j with hs | hc | hp
  · have hh := sources j hs; rw [passive] at hh; contradiction
  · subst j; rw [passive] at center; contradiction
  · exact hp

theorem basis_cost_exists (keep : Wire → Bool) (p : Program) (m : Matrix)
    (sources : ∀ i ∈ Budget.sources, keep i = true) (center : keep 8 = true)
    (representation : ∀ j ∈ Budget.privateOutputs,
      xorSum (basisRepresentation (identity j ^^^ m j)) = identity j ^^^ m j)
    (j : Wire) (hj : keep j = false) :
    ∃ n, cost (historyRows keep identity p) (identity j ^^^ m j) = some n := by
  have member : basisRepresentation (identity j ^^^ m j) ⊆ historyRows keep identity p := by
    intro w hw
    exact basis_in_history keep p sources center (List.mem_filter.mp hw).1
  obtain ⟨n,hn,_⟩ := cost_le_arbitrary _ _ member
  rw [representation j (passive_is_private keep j sources center hj)] at hn
  exact ⟨n,hn⟩

theorem choose_costs (keep : Wire → Bool) (p : Program) (js : List Wire) (m : Matrix)
    (existsCost : ∀ j, keep j = false → ∃ n, cost (historyRows keep identity p) (identity j ^^^ m j) = some n)
    (coverage : ∀ j, j ∈ js ↔ keep j = false) :
    ∃ n : Wire → Nat, ∀ j ∈ js, cost (historyRows keep identity p) (identity j ^^^ m j) = some (n j) := by
  classical
  have each : ∀ j, ∃ n, j ∈ js → cost (historyRows keep identity p) (identity j ^^^ m j) = some n := by
    intro j
    by_cases hj : j ∈ js
    · obtain ⟨n,hn⟩ := existsCost j ((coverage j).mp hj)
      exact ⟨n,fun _ => hn⟩
    · exact ⟨0,fun h => False.elim (hj h)⟩
  exact ⟨fun j => Classical.choose (each j),fun j hj => Classical.choose_spec (each j) hj⟩

/-- Concrete original orientation: existence of all passive optima follows
from the retained seven initial basis rows. -/
theorem original_exact_passive_minimum (keep : Wire → Bool) (core : Program) (js : List Wire)
    (legal : Legal core) (controls : ∀ g ∈ core, keep g.1 = true)
    (targets : ∀ g ∈ core, keep g.2 = true) (distinct : js.Nodup)
    (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (sources : ∀ i ∈ Budget.sources, keep i = true) (center : keep 8 = true)
    (finalCore : ∀ i, keep i = true → run identity core i = target i) :
    ∃ n : Wire → Nat,
      (∀ j ∈ js, cost (historyRows keep identity core) (identity j ^^^ target j) = some (n j)) ∧
      (∃ p, Completion keep core target p ∧ p.length = core.length + (js.map n).sum) ∧
      ∀ p, Completion keep core target p → core.length + (js.map n).sum ≤ p.length := by
  obtain ⟨n,hn⟩ := choose_costs keep core js target
    (basis_cost_exists keep core target sources center original_basis_representation) coverage
  exact ⟨n,hn,exact_passive_minimum keep core js target n legal controls targets distinct coverage hn finalCore⟩

theorem transpose_exact_passive_minimum (keep : Wire → Bool) (core : Program) (js : List Wire)
    (legal : Legal core) (controls : ∀ g ∈ core, keep g.1 = true)
    (targets : ∀ g ∈ core, keep g.2 = true) (distinct : js.Nodup)
    (coverage : ∀ j, j ∈ js ↔ keep j = false)
    (sources : ∀ i ∈ Budget.sources, keep i = true) (center : keep 8 = true)
    (finalCore : ∀ i, keep i = true → run identity core i = TransposeTarget.matrix i) :
    ∃ n : Wire → Nat,
      (∀ j ∈ js, cost (historyRows keep identity core) (identity j ^^^ TransposeTarget.matrix j) = some (n j)) ∧
      (∃ p, Completion keep core TransposeTarget.matrix p ∧ p.length = core.length + (js.map n).sum) ∧
      ∀ p, Completion keep core TransposeTarget.matrix p → core.length + (js.map n).sum ≤ p.length := by
  obtain ⟨n,hn⟩ := choose_costs keep core js TransposeTarget.matrix
    (basis_cost_exists keep core TransposeTarget.matrix sources center transpose_basis_representation) coverage
  exact ⟨n,hn,exact_passive_minimum keep core js TransposeTarget.matrix n legal controls targets distinct coverage hn finalCore⟩

end HGP13.PassiveInsertion


