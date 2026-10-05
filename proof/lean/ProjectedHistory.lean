import PackedRows

namespace HGP13.ProjectedHistory
open PackedRows SectorCoordinates SectorCover

/-- Fold the four 128-bit blocks of the 512-bit full-form history. -/
def foldHistory (h : Nat) :=
  (h ||| (h >>> 128) ||| (h >>> 256) ||| (h >>> 384)) &&& (2^128-1)

theorem fold_has (h p : Nat) (hp : p < 128) :
    has (foldHistory h) p = true ↔
      has h p = true ∨ has h (p+128) = true ∨
      has h (p+256) = true ∨ has h (p+384) = true := by
  simp only [foldHistory,has_testBit,Nat.testBit_and,Nat.testBit_or,
    Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one]
  simp [hp,Nat.add_comm,or_assoc]

theorem fold_encode (values : List Nat) (bound : ∀ v ∈ values, v < 512)
    (p : Nat) (hp : p < 128) :
    has (foldHistory (encodeHistory values)) p = true ↔
      ∃ v ∈ values, v%128 = p := by
  rw [fold_has _ p hp]
  simp only [has_history]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨p,h,by omega⟩
    · exact ⟨p+128,h,by omega⟩
    · exact ⟨p+256,h,by omega⟩
    · exact ⟨p+384,h,by omega⟩
  · rintro ⟨v,hv,he⟩
    have hb := bound v hv
    have hd : v = p ∨ v = p+128 ∨ v = p+256 ∨ v = p+384 := by omega
    rcases hd with rfl | rfl | rfl | rfl <;> simp [hv]

theorem packed_mod128 (s : Sector) (r : Row) :
    (pack (embed s) r).toNat % 128 = (Projection.project r).toNat := by
  have h := congrArg BitVec.toNat (packed_projection s r)
  simpa only [BitVec.toNat_setWidth,Nat.reducePow] using h

theorem packed_values_bound (s : Sector) (hs : s ∈ sectors) (r : Row) :
    (pack (embed s) r).toNat < 512 := by
  have h := packed_word_index_bound s hs r
  omega

theorem packed_fold_membership (s : Sector) (hs : s ∈ sectors) (history : List Row)
    (p : Nat) (hp : p < 128) :
    has (foldHistory (encodeHistory (history.map (fun r => (pack (embed s) r).toNat)))) p = true ↔
      ∃ r ∈ history, (Projection.project r).toNat = p := by
  rw [fold_encode _ (by
    intro v hv
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hv
    exact packed_values_bound s hs r) p hp]
  constructor
  · rintro ⟨v,hv,he⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv
    exact ⟨r,hr,(packed_mod128 s r).symm.trans he⟩
  · rintro ⟨r,hr,he⟩
    exact ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,(packed_mod128 s r).trans he⟩

theorem actual_projected_history (s : Sector) (hs : s ∈ sectors)
    (p : Program) (v : Nat) (hv : v < 128) :
    has (foldHistory (traceHistory (embed s) identity (core s p)
      (encodeHistory ((PassiveInsertion.currentRows (keep s) identity).map
        (fun r => (pack (embed s) r).toNat))))) v = true ↔
      ∃ r, CleanPersistence.CoreHistory (keep s) (core s p) r ∧
        (Projection.project r).toNat = v := by
  rw [traceHistory_encode,← List.map_append,packed_fold_membership s hs _ v hv]
  have ht : ∀ g ∈ core s p, keep s g.2 = true := fun g hg => (List.mem_filter.mp hg).2
  simp only [produced_history (keep s) (core s p) identity ht,
    PassiveInsertion.historyRows_exact]

theorem has_or (a b v : Nat) : has (a ||| b) v = (has a v || has b v) := by
  simp only [has_testBit,Nat.testBit_or]

theorem limb_bit (h k j : Nat) (hj : j < 64) :
    has (limb h k) j = has h (64*k+j) := by
  simp only [has_testBit,limb,Nat.testBit_and,Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  simp [hj]

/-- The two output words of the verifier's i%2 accumulation of eight input words. -/
def projectedWord (h b : Nat) : Nat :=
  limb h b ||| limb h (b+2) ||| limb h (b+4) ||| limb h (b+6)

theorem word_fold_has (h p : Nat) (hp : p < 128) :
    has (projectedWord h (p/64)) (p%64) = true ↔ has (foldHistory h) p = true := by
  have hr : p%64 < 64 := Nat.mod_lt _ (by decide)
  have h0 : 64*(p/64)+p%64 = p := by omega
  have h2 : 64*(p/64+2)+p%64 = p+128 := by omega
  have h4 : 64*(p/64+4)+p%64 = p+256 := by omega
  have h6 : 64*(p/64+6)+p%64 = p+384 := by omega
  simp only [projectedWord,has_or,limb_bit _ _ _ hr,h0,h2,h4,h6,
    Bool.or_eq_true,fold_has h p hp,or_assoc]

theorem projected_word_indices (p : Nat) (hp : p < 128) :
    p/64 < 2 ∧ p/64+6 < 8 := by omega

theorem actual_projected_words (s : Sector) (hs : s ∈ sectors)
    (p : Program) (v : Nat) (hv : v < 128) :
    has (projectedWord (traceHistory (embed s) identity (core s p)
      (encodeHistory ((PassiveInsertion.currentRows (keep s) identity).map
        (fun r => (pack (embed s) r).toNat)))) (v/64)) (v%64) = true ↔
      ∃ r, CleanPersistence.CoreHistory (keep s) (core s p) r ∧
        (Projection.project r).toNat = v := by
  rw [word_fold_has _ v hv]
  exact actual_projected_history s hs p v hv

def initialBits (s : Sector) :=
  encodeHistory ((PassiveInsertion.currentRows (keep s) identity).map
    (fun r => (pack (embed s) r).toNat))

def initialLiterals (s : Sector) :=
  encodeHistory ((List.range (7+s.carriers.length)).map (fun i => 2^i))

def rowCodes (s : Sector) (x : Matrix) :=
  (changing s).map (fun i => (pack (embed s) (x i)).toNat)

def initialRowLiterals (s : Sector) :=
  s.active.map (fun i => 2^i.val) ++ [64] ++
    (List.range s.carriers.length).map (fun i => 2^(7+i))

def projectedGoals (s : Sector) := if s.transposed then TransposeFree.goals else FreeXor.maskGoals

def targetRowLiterals (s : Sector) :=
  s.active.map (fun i => 2^i.val) ++ [(projectedGoals s)[6]!.toNat] ++
    s.carriers.zipIdx.map (fun (i,k) =>
      2^(7+k) ^^^ (projectedGoals s)[Budget.privateOutputs.idxOf i]!.toNat)

def initialFixedCodes (s : Sector) :=
  (Budget.sources.filter (fun i => !s.active.contains i)).map
    (fun i => (pack (embed s) (identity i)).toNat)

def fixedLiterals (s : Sector) :=
  (Budget.sources.filter (fun i => !s.active.contains i)).map (fun i => 2^i.val)

def LiteralCorrect (s : Sector) : Prop :=
  initialBits s = initialLiterals s ∧
  rowCodes s identity = initialRowLiterals s ∧
  initialFixedCodes s = fixedLiterals s ∧
  rowCodes s (goal s) = targetRowLiterals s

instance (s : Sector) : Decidable (LiteralCorrect s) := by
  unfold LiteralCorrect
  infer_instance

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem literals_checked : sectors.all (fun s => decide (LiteralCorrect s)) = true := by
  decide

theorem sector_literals (s : Sector) (hs : s ∈ sectors) : LiteralCorrect s :=
  of_decide_eq_true (List.all_eq_true.mp literals_checked s hs)

theorem literal_history_projection (s : Sector) (hs : s ∈ sectors)
    (p : Program) (v : Nat) (hv : v < 128) :
    has (projectedWord (traceHistory (embed s) identity (core s p)
      (initialLiterals s)) (v/64)) (v%64) = true ↔
      ∃ r, CleanPersistence.CoreHistory (keep s) (core s p) r ∧
        (Projection.project r).toNat = v := by
  rw [← (sector_literals s hs).1]
  exact actual_projected_words s hs p v hv

end HGP13.ProjectedHistory
