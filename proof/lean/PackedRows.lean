import SectorCoordinates
import PassiveInsertion

namespace HGP13.PackedRows
open CoordinateRestriction SectorCoordinates SectorCover

/-- Low-bit-first encoding in precisely the selected column order. -/
def pack {n : Nat} (e : Fin n → Wire) (r : Row) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => r.getLsbD (e i).val))).cast List.length_ofFn

theorem pack_bit {n : Nat} (e : Fin n → Wire) (r : Row) (i : Fin n) :
    (pack e r).getLsbD i.val = r.getLsbD (e i).val := by
  simp only [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

theorem pack_xor {n : Nat} (e : Fin n → Wire) (a b : Row) :
    pack e (a ^^^ b) = pack e a ^^^ pack e b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ha := pack_bit e a ⟨i,hi⟩
  have hb := pack_bit e b ⟨i,hi⟩
  have hab := pack_bit e (a ^^^ b) ⟨i,hi⟩
  simpa only [BitVec.getLsbD_xor,ha,hb] using hab

theorem pack_zero {n : Nat} (e : Fin n → Wire) : pack e 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using pack_bit e 0 ⟨i,hi⟩

theorem pack_faithful {n : Nat} (e : Fin n → Wire) (a b : Row)
    (ha : RowSupported e a) (hb : RowSupported e b) :
    pack e a = pack e b ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let w : Wire := ⟨j,hj⟩
    by_cases hw : ∃ i, e i = w
    · obtain ⟨i,hi⟩ := hw
      have hh := congrArg (fun r : BitVec n => r.getLsbD i.val) h
      rw [pack_bit,pack_bit,hi] at hh
      exact hh
    · have hn : ∀ i, e i ≠ w := fun i hi => hw ⟨i,hi⟩
      exact (ha w hn).trans (hb w hn).symm
  · rintro rfl
    rfl

theorem pack_zero_iff {n : Nat} (e : Fin n → Wire) (a : Row)
    (ha : RowSupported e a) : pack e a = 0 ↔ a = 0 := by
  rw [← pack_zero e]
  exact pack_faithful e a 0 ha (by intro j hj; simp)

theorem pack_nat_xor {n : Nat} (e : Fin n → Wire) (a b : Row) :
    (pack e (a ^^^ b)).toNat = (pack e a).toNat ^^^ (pack e b).toNat := by
  rw [pack_xor]
  rfl

theorem pack_nat_bound {n : Nat} (e : Fin n → Wire) (a : Row) :
    (pack e a).toNat < 2^n := (pack e a).isLt

def packedMatrix {n : Nat} (e : Fin n → Wire) (x : Matrix) : Fin n → BitVec n :=
  fun i => pack e (x (e i))

def packedStep {n : Nat} (x : Fin n → BitVec n) (g : SmallGate n) : Fin n → BitVec n :=
  fun i => if i = g.2 then x i ^^^ x g.1 else x i

def packedRun {n : Nat} (x : Fin n → BitVec n) (p : List (SmallGate n)) :=
  p.foldl packedStep x

theorem packed_step {n : Nat} (e : Fin n → Wire) (inj : Function.Injective e)
    (x : Matrix) (g : SmallGate n) :
    packedMatrix e (step x (liftGate e g)) = packedStep (packedMatrix e x) g := by
  funext i
  have he : e i = e g.2 ↔ i = g.2 := ⟨fun h => inj h,congrArg e⟩
  simp only [packedMatrix,packedStep,step,liftGate,he]
  split <;> simp only [pack_xor]

theorem packed_run {n : Nat} (e : Fin n → Wire) (inj : Function.Injective e)
    (x : Matrix) (p : List (SmallGate n)) :
    packedMatrix e (run x (p.map (liftGate e))) = packedRun (packedMatrix e x) p := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    simp only [List.map_cons,run_cons]
    rw [ih,packed_step e inj]
    rfl

theorem packed_initial_bit {n : Nat} (e : Fin n → Wire) (inj : Function.Injective e)
    (i j : Fin n) : (packedMatrix e identity i).getLsbD j.val = decide (i = j) := by
  rw [packedMatrix,pack_bit]
  change coefficient identity (e i) (e j) = _
  rw [Transposition.coefficient_identity]
  have he : e i = e j ↔ i = j := ⟨fun h => inj h,congrArg e⟩
  simp [Transposition.unit,he]

/-- Historical form membership is reflected, not merely preserved. -/
theorem history_membership {n : Nat} (e : Fin n → Wire) (history : List Row) (r : Row)
    (hs : ∀ a ∈ history, RowSupported e a) (hr : RowSupported e r) :
    pack e r ∈ history.map (pack e) ↔ r ∈ history := by
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := List.mem_map.mp h
    have har := (pack_faithful e a r (hs a ha) hr).mp he
    rwa [← har]
  · intro h
    exact List.mem_map.mpr ⟨r,h,rfl⟩

/-- Concrete packed-row reduction of every hypothetical short full realization. -/
theorem every_short_packed (p : Program) (hp : Legal p)
    (real : run identity p = target) (hl : p.length ≤ 18) :
    ∃ s ∈ sectors, Compatible s p ∧
      ∃ q : List (SmallGate (layout s).length),
        q.map (liftGate (embed s)) = core s p ∧
        q.length ≤ 12 + s.carriers.length ∧ (∀ g ∈ q, g.1 ≠ g.2) ∧
        packedRun (packedMatrix (embed s) identity) q = packedMatrix (embed s) (goal s) := by
  obtain ⟨s,hs,hc,q,hq,hlen,hleg,_⟩ := every_short_normalized p hp real hl
  refine ⟨s,hs,hc,q,hq,hlen,hleg,?_⟩
  rw [← packed_run (embed s) (embed_injective s hs),hq]
  have agree := erase_passive_preserves_core (keep s) (word s p)
    (control_retained s p hc) identity identity (fun _ _ => rfl)
  funext i
  have hk : keep s (embed s i) = true :=
    List.contains_iff_mem.mpr ((embed_image s _).mp ⟨i,rfl⟩)
  have hh := (agree _ hk).symm
  rw [word_realizes s p real] at hh
  exact congrArg (pack (embed s)) hh

def baseColumn (i : Fin 7) : Wire := if i.val = 6 then 8 else ⟨i.val,by omega⟩

theorem projection_bit (r : Row) (i : Fin 7) :
    (Projection.project r).getLsbD i.val = r.getLsbD (baseColumn i).val := by
  have bits : ∀ a b c d e f g : Bool, ∀ j : Fin 7,
      (((if g then 64 else 0) ^^^ ((if f then 32 else 0) ^^^
        ((if e then 16 else 0) ^^^ ((if d then 8 else 0) ^^^
        ((if c then 4 else 0) ^^^ ((if b then 2 else 0) ^^^
        ((if a then 1 else 0) ^^^ 0))))))) : BitVec 7).getLsbD j.val =
        [a,b,c,d,e,f,g][j.val]! := by decide
  have hh := bits (r.getLsbD 0) (r.getLsbD 1) (r.getLsbD 2)
    (r.getLsbD 3) (r.getLsbD 4) (r.getLsbD 5) (r.getLsbD 8) i
  change (Projection.project r).getLsbD i.val =
    [r.getLsbD 0,r.getLsbD 1,r.getLsbD 2,r.getLsbD 3,
      r.getLsbD 4,r.getLsbD 5,r.getLsbD 8][i.val]! at hh
  rw [hh]
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem layout_base_length (s : Sector) : 7 ≤ (layout s).length := by
  simp [layout,Budget.sources]

theorem embed_base (s : Sector) (i : Fin 7) :
    embed s ⟨i.val,Nat.lt_of_lt_of_le i.isLt (layout_base_length s)⟩ = baseColumn i := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- The executable low-seven-bit projection is the original proof projection. -/
theorem packed_projection (s : Sector) (r : Row) :
    (pack (embed s) r).setWidth 7 = Projection.project r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth]
  have hb := pack_bit (embed s) r ⟨i,Nat.lt_of_lt_of_le hi (layout_base_length s)⟩
  have he := embed_base s ⟨i,hi⟩
  have hp := projection_bit r ⟨i,hi⟩
  rw [he,← hp] at hb
  simpa only [hi,decide_true,Bool.true_and] using hb

/-- Scalar form of the search's membership and insertion operations. -/
def has (h v : Nat) : Bool := ((h >>> v) &&& 1) == 1
def remember (h v : Nat) : Nat := h ||| (1 <<< v)
def encodeHistory : List Nat → Nat
  | [] => 0
  | v :: vs => remember (encodeHistory vs) v

theorem has_testBit (h v : Nat) : has h v = h.testBit v := by
  unfold has
  rw [Nat.and_comm,Nat.one_and_eq_mod_two,Bool.beq_eq_decide_eq,
    Nat.decide_shiftRight_mod_two_eq_one]

theorem has_remember (h v w : Nat) :
    has (remember h v) w = (has h w || decide (v = w)) := by
  simp only [has_testBit,remember,Nat.testBit_or,Nat.shiftLeft_eq,Nat.one_mul,
    Nat.testBit_two_pow]

theorem has_history (values : List Nat) (v : Nat) :
    has (encodeHistory values) v = true ↔ v ∈ values := by
  induction values with
  | nil => simp [encodeHistory,has_testBit]
  | cons a values ih =>
    simp only [encodeHistory,has_remember,Bool.or_eq_true,decide_eq_true_eq,ih,
      List.mem_cons]
    simp [eq_comm,or_comm]

theorem packed_history_bits {n : Nat} (e : Fin n → Wire) (history : List Row) (r : Row)
    (hs : ∀ a ∈ history, RowSupported e a) (hr : RowSupported e r) :
    has (encodeHistory (history.map (fun a => (pack e a).toNat))) (pack e r).toNat = true ↔
      r ∈ history := by
  rw [has_history]
  constructor
  · intro hm
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
    have hb : pack e a = pack e r := BitVec.eq_of_toNat_eq he
    have har := (pack_faithful e a r (hs a ha) hr).mp hb
    rwa [← har]
  · intro hm
    exact List.mem_map.mpr ⟨r,hm,rfl⟩

def limb (h k : Nat) : Nat := (h >>> (64*k)) &&& (2^64-1)

/-- The 64-bit word access used by the verifier reads the same scalar-history bit. -/
theorem limb_has (h v : Nat) : has (limb h (v/64)) (v%64) = has h v := by
  have hr : v%64 < 64 := Nat.mod_lt _ (by decide)
  have hv : 64*(v/64) + v%64 = v := by omega
  simp only [has_testBit,limb,Nat.testBit_and,Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  simp [hr,hv]

def hasWords (words : Nat → Nat) (v : Nat) := has (words (v/64)) (v%64)
def rememberWords (words : Nat → Nat) (v : Nat) : Nat → Nat :=
  fun k => if k = v/64 then remember (words k) (v%64) else words k

theorem hasWords_remember (words : Nat → Nat) (v w : Nat) :
    hasWords (rememberWords words v) w = (hasWords words w || decide (v = w)) := by
  unfold hasWords rememberWords
  by_cases hq : w/64 = v/64
  · rw [ite_eq_left hq,has_remember]
    have he : v%64 = w%64 ↔ v = w := by omega
    simp only [he]
  · rw [ite_eq_right hq]
    have hn : v ≠ w := by omega
    simp [hn]

theorem packed_word_index_bound (s : Sector) (hs : s ∈ sectors) (r : Row) :
    (pack (embed s) r).toNat / 64 < 8 := by
  have hb := pack_nat_bound (embed s) r
  have hp := layout_properties s hs
  have h7 := layout_base_length s
  have hd : (layout s).length = 7 ∨ (layout s).length = 8 ∨ (layout s).length = 9 := by omega
  have hpow : 2^(layout s).length ≤ 512 := by
    rcases hd with hd | hd | hd <;> rw [hd] <;> decide
  omega

theorem actual_history_supported (s : Sector) (p : Program) (hc : Compatible s p) :
    ∀ r ∈ PassiveInsertion.historyRows (keep s) identity (core s p),
      RowSupported (embed s) r := by
  intro r hr
  obtain ⟨a,b,hab,i,hki,hrow⟩ :=
    (PassiveInsertion.historyRows_exact (keep s) (core s p) r).mp hr
  have hh := (core_prefix_invariants s p a b hc hab).1
  have him : i ∈ layout s := List.contains_iff_mem.mp hki
  obtain ⟨k,hk⟩ := (embed_image s i).mpr him
  intro j hj
  have hb := hh k j hj
  simpa only [coefficient,hk,hrow] using hb

theorem actual_history_bits (s : Sector) (p : Program) (hc : Compatible s p)
    (r : Row) (hr : RowSupported (embed s) r) :
    has (encodeHistory ((PassiveInsertion.historyRows (keep s) identity (core s p)).map
      (fun a => (pack (embed s) a).toNat))) (pack (embed s) r).toNat = true ↔
      CleanPersistence.CoreHistory (keep s) (core s p) r := by
  rw [packed_history_bits (embed s) _ r (actual_history_supported s p hc) hr]
  exact PassiveInsertion.historyRows_exact (keep s) (core s p) r

def produced (x : Matrix) : Program → List Row
  | [] => []
  | g :: p => step x g g.2 :: produced (step x g) p

theorem current_after (keep : Wire → Bool) (x : Matrix) (g : Gate) (r : Row)
    (h : r ∈ PassiveInsertion.currentRows keep (step x g)) :
    r ∈ PassiveInsertion.currentRows keep x ∨ r = step x g g.2 := by
  obtain ⟨i,hi,he⟩ := (PassiveInsertion.currentRows_members keep (step x g) r).mp h
  by_cases ht : i = g.2
  · exact Or.inr (by simpa [ht] using he.symm)
  · apply Or.inl
    apply (PassiveInsertion.currentRows_members keep x r).mpr
    exact ⟨i,hi,(step_other x g i ht).symm.trans he⟩

theorem produced_history (keep : Wire → Bool) (p : Program) (x : Matrix)
    (targets : ∀ g ∈ p, keep g.2 = true) (r : Row) :
    r ∈ PassiveInsertion.currentRows keep x ++ produced x p ↔
      r ∈ PassiveInsertion.historyRows keep x p := by
  induction p generalizing x with
  | nil => simp [produced,PassiveInsertion.historyRows]
  | cons g p ih =>
    have ht := targets g (by simp)
    have tail : ∀ a ∈ p, keep a.2 = true := fun a ha => targets a (by simp [ha])
    have hn : step x g g.2 ∈ PassiveInsertion.currentRows keep (step x g) :=
      (PassiveInsertion.currentRows_members keep (step x g) _).mpr ⟨g.2,ht,rfl⟩
    simp only [PassiveInsertion.historyRows,List.mem_append]
    rw [← ih (step x g) tail]
    simp only [produced,List.mem_append,List.mem_cons]
    constructor
    · rintro (ha | hr | hp)
      · exact Or.inl ha
      · exact Or.inr (Or.inl (hr ▸ hn))
      · exact Or.inr (Or.inr hp)
    · rintro (ha | ha | hp)
      · exact Or.inl ha
      · rcases current_after keep x g r ha with hb | hb
        · exact Or.inl hb
        · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hp)

def traceHistory {n : Nat} (e : Fin n → Wire) (x : Matrix) : Program → Nat → Nat
  | [], h => h
  | g :: p, h => traceHistory e (step x g) p (remember h (pack e (step x g g.2)).toNat)

theorem traceHistory_bit {n : Nat} (e : Fin n → Wire) (p : Program) (x : Matrix)
    (h v : Nat) :
    has (traceHistory e x p h) v =
      (has h v || (produced x p).any (fun r => (pack e r).toNat == v)) := by
  induction p generalizing x h with
  | nil => simp [traceHistory,produced]
  | cons g p ih =>
    simp only [traceHistory,ih,has_remember,produced,List.any_cons]
    simp [Bool.or_assoc,Bool.beq_eq_decide_eq]

theorem traceHistory_encode {n : Nat} (e : Fin n → Wire) (p : Program) (x : Matrix)
    (initial : List Nat) :
    traceHistory e x p (encodeHistory initial) =
      encodeHistory (initial ++ (produced x p).map (fun r => (pack e r).toNat)) := by
  apply Nat.eq_of_testBit_eq
  intro v
  rw [← has_testBit,← has_testBit,traceHistory_bit]
  apply Bool.eq_iff_iff.mpr
  simp [Bool.or_eq_true,has_history,List.mem_map,List.any_eq_true]

theorem actual_trace_history (s : Sector) (p : Program) (hc : Compatible s p)
    (r : Row) (hr : RowSupported (embed s) r) :
    has (traceHistory (embed s) identity (core s p)
      (encodeHistory ((PassiveInsertion.currentRows (keep s) identity).map
        (fun a => (pack (embed s) a).toNat)))) (pack (embed s) r).toNat = true ↔
      CleanPersistence.CoreHistory (keep s) (core s p) r := by
  have targets : ∀ g ∈ core s p, keep s g.2 = true :=
    fun g hg => (List.mem_filter.mp hg).2
  have hm := produced_history (keep s) (core s p) identity targets
  have supported : ∀ a ∈ PassiveInsertion.currentRows (keep s) identity ++
      produced identity (core s p), RowSupported (embed s) a := by
    intro a ha
    exact actual_history_supported s p hc a ((hm a).mp ha)
  rw [traceHistory_encode,← List.map_append,
    packed_history_bits (embed s) _ r supported hr,hm r]
  exact PassiveInsertion.historyRows_exact (keep s) (core s p) r

end HGP13.PackedRows

