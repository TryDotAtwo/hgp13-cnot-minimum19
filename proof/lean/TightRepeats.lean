import TransposeBudget

namespace HGP13.TightRepeats
open Budget Projection FreeXor

/-- A cardinality-saturated inclusion of a duplicate-free list is a permutation. -/
theorem perm_of_nodup_subset_length {α : Type} [DecidableEq α]
    (s t : List α) (hs : s.Nodup) (sub : s ⊆ t) (len : s.length = t.length) : s.Perm t := by
  induction s generalizing t with
  | nil =>
    have ht : t = [] := List.eq_nil_of_length_eq_zero (by simpa using len.symm)
    simp [ht]
  | cons a s ih =>
    obtain ⟨hn,hs⟩ := List.nodup_cons.mp hs
    have ha : a ∈ t := sub List.mem_cons_self
    apply List.cons_perm_iff_perm_erase.mpr
    refine ⟨ha,ih (t.erase a) hs ?_ ?_⟩
    · intro z hz
      have ne : z ≠ a := by intro he; subst z; exact hn hz
      exact (List.mem_erase_of_ne ne).mpr (sub (List.mem_cons_of_mem _ hz))
    · rw [List.length_erase_of_mem ha]
      simp only [List.length_cons] at len
      omega

theorem original_repeats_permutation (p : Program) (h : run identity p = target)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 2) :
    (privateOutputs ++ touchedSources p).Perm (repeatTargets (record identity (0 :: maskBasis) p)) := by
  apply perm_of_nodup_subset_length _ _ (required_targets_nodup p) (required_repeat_targets p h)
  have he := (ExactBudget.two_sources_saturation p h hl hu).2.2
  have hr := repeated_count p h
  unfold ExactBudget.extraRepeats at he
  simp only [List.length_append,show privateOutputs.length = 6 from rfl]
  omega

theorem transpose_repeats_permutation (p : Program) (h : run identity p = TransposeTarget.matrix)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 2) :
    (privateOutputs ++ touchedSources p).Perm (repeatTargets (record identity (0 :: maskBasis) p)) := by
  apply perm_of_nodup_subset_length _ _ (required_targets_nodup p)
    (TransposeTarget.required_repeat_targets p h)
  have he := (TransposeBudget.two_sources_saturation p h hl hu).2.2
  have hr := TransposeTarget.repeated_count p h
  unfold ExactBudget.extraRepeats at he
  simp only [List.length_append,show privateOutputs.length = 6 from rfl]
  omega

theorem mapped_nodup_injective {α β : Type} (f : α → β) (l : List α)
    (hn : (l.map f).Nodup) (a b : α) (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    obtain ⟨hc,ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with hac | hat
    · rcases List.mem_cons.mp hb with hbc | hbt
      · exact hac.trans hbc.symm
      · exact False.elim (hc (List.mem_map.mpr ⟨b,hbt,he.symm.trans (congrArg f hac)⟩))
    · rcases List.mem_cons.mp hb with hbc | hbt
      · exact False.elim (hc (List.mem_map.mpr ⟨a,hat,he.trans (congrArg f hbc)⟩))
      · exact ih ht hat hbt

theorem repeat_event_unique (es : List Event) (hn : (repeatTargets es).Nodup)
    (a b : Event) (ha : a ∈ es) (hb : b ∈ es)
    (hfa : a.fresh = false) (hfb : b.fresh = false) (he : a.target = b.target) : a = b := by
  exact mapped_nodup_injective Event.target (es.filter (fun e => !e.fresh)) hn a b
    (List.mem_filter.mpr ⟨ha,by simp [hfa]⟩)
    (List.mem_filter.mpr ⟨hb,by simp [hfb]⟩) he

/-- The mandatory first nonzero copy has a nonzero result, not merely a repeat flag. -/
theorem first_nonzero_event (p : Program) (x : Matrix) (seen : List (BitVec 7)) (j : Wire)
    (supported : ∀ i, project (x i) ∈ seen)
    (start : project (x j) = 0) (finish : project (run x p j) ≠ 0) :
    ∃ e ∈ record x seen p, e.target = j ∧ e.fresh = false ∧ project e.row ≠ 0 := by
  induction p generalizing x seen with
  | nil => exact False.elim (finish start)
  | cons g p ih =>
    by_cases hz : project (step x g j) = 0
    · obtain ⟨e,he,hj,hf,hn⟩ := ih (step x g) _ (step_supported x g seen supported) hz finish
      exact ⟨e,List.mem_cons_of_mem _ he,hj,hf,hn⟩
    · have hj : j = g.2 := by
        by_cases hj : j = g.2
        · exact hj
        · exact False.elim (hz (by simpa [step,hj] using start))
      have hc : project (step x g g.2) ∈ seen := by
        have hs : project (x g.2) = 0 := by simpa [hj] using start
        simpa [step,project_add,hs] using supported g.1
      refine ⟨headEvent x seen g,List.mem_cons_self,hj.symm,?_,?_⟩
      · simp [headEvent,hc]
      · simpa [headEvent,hj] using hz

/-- Every repeated source row must be its full final restoration. -/
theorem repeated_source_is_final (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (hn : (repeatTargets (record x seen p)).Nodup) (j : Wire)
    (hf : project (run x p j) ∈ seen)
    (e : Event) (he : e ∈ record x seen p) (hj : e.target = j) (hr : e.fresh = false)
    (ht : j ∈ p.map Prod.snd) : e.row = run x p j := by
  obtain ⟨f,hfm,hft,hfr⟩ := last_target_result p x seen j ht
  have hff := initially_seen_is_repeat p x seen f hfm (by rw [hfr]; exact hf)
  have eq := repeat_event_unique _ hn e f he hfm hr hff (hj.trans hft.symm)
  exact eq ▸ hfr

/-- All repeated private-output events are the mandatory nonzero copies. -/
theorem repeated_private_nonzero (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (hn : (repeatTargets (record x seen p)).Nodup) (j : Wire)
    (supported : ∀ i, project (x i) ∈ seen)
    (start : project (x j) = 0) (finish : project (run x p j) ≠ 0)
    (e : Event) (he : e ∈ record x seen p) (hj : e.target = j) (hr : e.fresh = false) :
    project e.row ≠ 0 := by
  obtain ⟨f,hfm,hft,hff,hfn⟩ := first_nonzero_event p x seen j supported start finish
  have eq := repeat_event_unique _ hn e f he hfm hr hff (hj.trans hft.symm)
  exact eq ▸ hfn


theorem event_target_in_program (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (e : Event) (he : e ∈ record x seen p) : e.target ∈ p.map Prod.snd := by
  induction p generalizing x seen with
  | nil => simp [record] at he
  | cons g p ih =>
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (step x g) _ he)

theorem saturated_repeat_classification (p : Program)
    (perm : (privateOutputs ++ touchedSources p).Perm (repeatTargets (record identity (0 :: maskBasis) p)))
    (fixed : ∀ j ∈ sources, run identity p j = identity j)
    (nonzero : ∀ j ∈ privateOutputs, project (run identity p j) ≠ 0)
    (e : Event) (he : e ∈ record identity (0 :: maskBasis) p) (hr : e.fresh = false) :
    (e.target ∈ privateOutputs ∧ project e.row ≠ 0) ∨
      (e.target ∈ touchedSources p ∧ e.row = identity e.target) := by
  have hn := perm.nodup (required_targets_nodup p)
  have hm := perm.mem_iff.mpr (repeat_target_mem _ e he hr)
  rcases List.mem_append.mp hm with hj | hj
  · exact Or.inl ⟨hj,repeated_private_nonzero p identity _ hn e.target initial_supported
      (private_starts_zero _ hj) (nonzero _ hj) e he rfl hr⟩
  · have hs := (List.mem_filter.mp hj).1
    have hv := repeated_source_is_final p identity _ hn e.target
      (by rw [fixed _ hs]; exact initial_supported _) e he rfl hr
      (event_target_in_program p identity _ e he)
    exact Or.inr ⟨hj,hv.trans (fixed _ hs)⟩

theorem source_projection_nonzero : ∀ j ∈ sources, project (identity j) ≠ 0 := by decide

theorem saturated_no_zero (p : Program)
    (perm : (privateOutputs ++ touchedSources p).Perm (repeatTargets (record identity (0 :: maskBasis) p)))
    (fixed : ∀ j ∈ sources, run identity p j = identity j)
    (nonzero : ∀ j ∈ privateOutputs, project (run identity p j) ≠ 0) :
    ∀ e ∈ record identity (0 :: maskBasis) p, project e.row ≠ 0 := by
  intro e he hz
  have hr := initially_seen_is_repeat p identity (0 :: maskBasis) e he
    (by rw [hz]; exact List.mem_cons_self)
  rcases saturated_repeat_classification p perm fixed nonzero e he hr with hp | hs
  · exact hp.2 hz
  · have hne := source_projection_nonzero e.target (List.mem_filter.mp hs.1).1
    exact hne (by rw [← hs.2]; exact hz)

theorem original_no_zero (p : Program) (h : run identity p = target)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 2) :
    ∀ e ∈ record identity (0 :: maskBasis) p, project e.row ≠ 0 := by
  apply saturated_no_zero p (original_repeats_permutation p h hl hu)
  · intro j hj; rw [h]; exact sources_fixed j hj
  · intro j hj; rw [h]; exact private_ends_nonzero j hj

theorem transpose_no_zero (p : Program) (h : run identity p = TransposeTarget.matrix)
    (hl : p.length ≤ 18) (hu : (touchedSources p).length = 2) :
    ∀ e ∈ record identity (0 :: maskBasis) p, project e.row ≠ 0 := by
  apply saturated_no_zero p (transpose_repeats_permutation p h hl hu)
  · intro j hj; rw [h]; exact TransposeTarget.sources_fixed j hj
  · intro j hj; rw [h]; exact TransposeTarget.private_ends_nonzero j hj


def seenAfter (x : Matrix) (seen : List (BitVec 7)) : Program → List (BitVec 7)
  | [] => seen
  | g :: p => seenAfter (step x g) (project (step x g g.2) :: seen) p

theorem record_append (p q : Program) (x : Matrix) (seen : List (BitVec 7)) :
    record x seen (p ++ q) = record x seen p ++ record (run x p) (seenAfter x seen p) q := by
  induction p generalizing x seen with
  | nil => rfl
  | cons g p ih => simp only [List.cons_append,record,ih,List.cons_append,run_cons,seenAfter]

theorem repeat_append (a b : List Event) : repeatTargets (a ++ b) = repeatTargets a ++ repeatTargets b := by
  simp [repeatTargets]

theorem seenAfter_supported (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (hs : ∀ i, project (x i) ∈ seen) : ∀ i, project (run x p i) ∈ seenAfter x seen p := by
  induction p generalizing x seen with
  | nil => exact hs
  | cons g p ih => exact ih (step x g) _ (step_supported x g seen hs)

/-- A repeated private-output update must start from projection zero. -/
theorem repeated_private_starts_zero (q r : Program) (g : Gate)
    (hn : (repeatTargets (record identity (0 :: maskBasis) (q ++ g :: r))).Nodup)
    (hj : g.2 ∈ privateOutputs)
    (hr : (headEvent (run identity q) (seenAfter identity (0 :: maskBasis) q) g).fresh = false) :
    project (run identity q g.2) = 0 := by
  by_cases hz : project (run identity q g.2) = 0
  · exact hz
  · obtain ⟨e,he,ht,hf⟩ := first_nonzero_repeat q identity (0 :: maskBasis) g.2
      initial_supported (private_starts_zero _ hj) hz
    have left : g.2 ∈ repeatTargets (record identity (0 :: maskBasis) q) := by
      rw [← ht]; exact repeat_target_mem _ e he hf
    rw [record_append,repeat_append] at hn
    have right : g.2 ∈ repeatTargets
        (record (run identity q) (seenAfter identity (0 :: maskBasis) q) (g :: r)) :=
      repeat_target_mem _ _ List.mem_cons_self hr
    exact False.elim ((List.nodup_append.mp hn).2.2 _ left _ right rfl)

/-- Full local restrictions, including the pre-update projection. -/
def Allowed (x : Matrix) (seen : List (BitVec 7)) (g : Gate) : Prop :=
  (headEvent x seen g).fresh = true ∨
    (g.2 ∈ privateOutputs ∧ project (x g.2) = 0 ∧ project (step x g g.2) ≠ 0) ∨
    (g.2 ∈ sources ∧ step x g g.2 = identity g.2)

theorem saturated_local_allowed (q r : Program) (g : Gate)
    (perm : (privateOutputs ++ touchedSources (q ++ g :: r)).Perm
      (repeatTargets (record identity (0 :: maskBasis) (q ++ g :: r))))
    (fixed : ∀ j ∈ sources, run identity (q ++ g :: r) j = identity j)
    (nonzero : ∀ j ∈ privateOutputs, project (run identity (q ++ g :: r) j) ≠ 0) :
    Allowed (run identity q) (seenAfter identity (0 :: maskBasis) q) g := by
  let e := headEvent (run identity q) (seenAfter identity (0 :: maskBasis) q) g
  have he : e ∈ record identity (0 :: maskBasis) (q ++ g :: r) := by
    rw [record_append]
    exact List.mem_append_right _ List.mem_cons_self
  cases hf : e.fresh with
  | true => exact Or.inl hf
  | false =>
    rcases saturated_repeat_classification _ perm fixed nonzero e he hf with hp | hs
    · exact Or.inr (Or.inl ⟨hp.1,repeated_private_starts_zero q r g
        (perm.nodup (required_targets_nodup _)) hp.1 hf,hp.2⟩)
    · exact Or.inr (Or.inr ⟨(List.mem_filter.mp hs.1).1,hs.2⟩)


def PrivateIntact (x : Matrix) : Prop :=
  ∀ j ∈ privateOutputs, project (x j) = 0 →
    x j = identity j ∧ ∀ i, i ≠ j → coefficient x i j = false

theorem identity_bit (i j : Wire) : coefficient identity i j = decide (i = j) := by
  revert i j
  decide

theorem private_intact_initial : PrivateIntact identity := by
  intro j _ _
  refine ⟨rfl,?_⟩
  intro i hi
  simp [identity_bit,hi]

theorem allowed_nonzero (x : Matrix) (seen : List (BitVec 7)) (g : Gate)
    (hz : (0 : BitVec 7) ∈ seen) (ha : Allowed x seen g) : project (step x g g.2) ≠ 0 := by
  intro he
  rcases ha with hf | hp | hs
  · have hf' : project (step x g g.2) ∉ seen := by simpa [headEvent] using hf
    exact hf' (he ▸ hz)
  · exact hp.2.2 he
  · exact source_projection_nonzero _ hs.1 (by rw [← hs.2]; exact he)

/-- A still-zero private row cannot distribute its private coefficient. -/
theorem private_intact_step (x : Matrix) (seen : List (BitVec 7)) (g : Gate)
    (hz : (0 : BitVec 7) ∈ seen) (supported : ∀ i, project (x i) ∈ seen)
    (ha : Allowed x seen g) (intact : PrivateIntact x) : PrivateIntact (step x g) := by
  intro j hj hzero
  have hnonzero := allowed_nonzero x seen g hz ha
  have jt : j ≠ g.2 := by
    intro he
    subst j
    exact hnonzero hzero
  have oldzero : project (x j) = 0 := by simpa [step,jt] using hzero
  obtain ⟨oldrow,oldbits⟩ := intact j hj oldzero
  have cj : g.1 ≠ j := by
    intro ce
    have unchanged : project (step x g g.2) = project (x g.2) := by
      simp [step,project_add,ce,oldzero]
    rcases ha with hf | hp | hs
    · have hf' : project (step x g g.2) ∉ seen := by simpa [headEvent] using hf
      exact hf' (unchanged ▸ supported g.2)
    · exact hp.2.2 (unchanged.trans hp.2.1)
    · have tj : g.2 ≠ j := Ne.symm jt
      have c0 := oldbits g.2 tj
      have c1 : coefficient x g.1 j = true := by
        change (x g.1).getLsbD j.val = true
        rw [ce,oldrow]
        simpa [coefficient] using identity_bit j j
      have after : coefficient (step x g) g.2 j = true := by
        rw [step_coefficient]
        simp [c0,c1]
      have restored : coefficient (step x g) g.2 j = false := by
        change (step x g g.2).getLsbD j.val = false
        rw [hs.2]
        simpa [coefficient,tj] using identity_bit g.2 j
      rw [restored] at after
      contradiction
  refine ⟨by simpa [step,jt] using oldrow,?_⟩
  intro i hi
  rw [step_coefficient]
  simp [oldbits i hi,oldbits g.1 cj]

def LawfulTrace (x : Matrix) (seen : List (BitVec 7)) (p : Program) : Prop :=
  ∀ q g r, p = q ++ g :: r → Allowed (run x q) (seenAfter x seen q) g

theorem private_intact_run (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (hz : (0 : BitVec 7) ∈ seen) (supported : ∀ i, project (x i) ∈ seen)
    (ha : LawfulTrace x seen p) (intact : PrivateIntact x) : PrivateIntact (run x p) := by
  induction p generalizing x seen with
  | nil => exact intact
  | cons g p ih =>
    have hg := ha [] g p rfl
    have ht : LawfulTrace (step x g) (project (step x g g.2) :: seen) p := by
      intro q b r he
      have hh := ha (g :: q) b r (by simp [he])
      exact hh
    exact ih (step x g) _ (List.mem_cons_of_mem _ hz) (step_supported x g seen supported)
      ht (private_intact_step x seen g hz supported hg intact)

theorem lawfulTrace_prefix (q r : Program) (x : Matrix) (seen : List (BitVec 7))
    (h : LawfulTrace x seen (q ++ r)) : LawfulTrace x seen q := by
  intro a g b he
  apply h a g (b ++ r)
  simp [he,List.append_assoc]

theorem saturated_lawfulTrace (p : Program)
    (perm : (privateOutputs ++ touchedSources p).Perm (repeatTargets (record identity (0 :: maskBasis) p)))
    (fixed : ∀ j ∈ sources, run identity p j = identity j)
    (nonzero : ∀ j ∈ privateOutputs, project (run identity p j) ≠ 0) :
    LawfulTrace identity (0 :: maskBasis) p := by
  intro q g r he
  subst p
  exact saturated_local_allowed q r g perm fixed nonzero

/-- Source Lemma 8.1, at every prefix, in the original orientation. -/
theorem original_fresh_private_bit (q r : Program)
    (h : run identity (q ++ r) = target) (hl : (q ++ r).length ≤ 18)
    (hu : (touchedSources (q ++ r)).length = 2) :
    PrivateIntact (run identity q) := by
  have hp := saturated_lawfulTrace (q ++ r) (original_repeats_permutation _ h hl hu)
    (by intro j hj; rw [h]; exact sources_fixed j hj)
    (by intro j hj; rw [h]; exact private_ends_nonzero j hj)
  exact private_intact_run q identity (0 :: maskBasis) List.mem_cons_self initial_supported
    (lawfulTrace_prefix q r identity _ hp) private_intact_initial

/-- Source Lemma 8.1, at every prefix, in the transposed orientation. -/
theorem transpose_fresh_private_bit (q r : Program)
    (h : run identity (q ++ r) = TransposeTarget.matrix) (hl : (q ++ r).length ≤ 18)
    (hu : (touchedSources (q ++ r)).length = 2) :
    PrivateIntact (run identity q) := by
  have hp := saturated_lawfulTrace (q ++ r) (transpose_repeats_permutation _ h hl hu)
    (by intro j hj; rw [h]; exact TransposeTarget.sources_fixed j hj)
    (by intro j hj; rw [h]; exact TransposeTarget.private_ends_nonzero j hj)
  exact private_intact_run q identity (0 :: maskBasis) List.mem_cons_self initial_supported
    (lawfulTrace_prefix q r identity _ hp) private_intact_initial


def Clean (row : Row) : Prop := ∀ j ∈ privateOutputs, row.getLsbD j.val = false

theorem source_projection_basis : ∀ j ∈ sources, project (identity j) ∈ maskBasis := by decide

/-- Repeating a nonbasis projection is exactly a copy into an intact private
output, with a newly added private coefficient. -/
theorem repeated_nonbasis_copy (x : Matrix) (seen : List (BitVec 7)) (g : Gate)
    (legal : g.1 ≠ g.2) (allowed : Allowed x seen g) (intact : PrivateIntact x)
    (repeated : project (step x g g.2) ∈ seen)
    (nonbasis : project (step x g g.2) ∉ maskBasis) :
    g.2 ∈ privateOutputs ∧ x g.2 = identity g.2 ∧
      coefficient x g.1 g.2 = false ∧ coefficient (step x g) g.2 g.2 = true := by
  rcases allowed with hf | hp | hs
  · have hn : project (step x g g.2) ∉ seen := by simpa [headEvent] using hf
    exact False.elim (hn repeated)
  · obtain ⟨hr,hb⟩ := intact g.2 hp.1 hp.2.1
    have hc := hb g.1 legal
    refine ⟨hp.1,hr,hc,?_⟩
    have ht : coefficient x g.2 g.2 = true := by
      change (x g.2).getLsbD g.2.val = true
      rw [hr]
      simpa [coefficient] using identity_bit g.2 g.2
    rw [step_coefficient]
    simp [ht,hc]
  · exact False.elim (nonbasis (hs.2 ▸ source_projection_basis g.2 hs.1))

theorem clean_nonbasis_is_new (x : Matrix) (seen : List (BitVec 7)) (g : Gate)
    (legal : g.1 ≠ g.2) (allowed : Allowed x seen g) (intact : PrivateIntact x)
    (clean : Clean (step x g g.2)) (nonbasis : project (step x g g.2) ∉ maskBasis) :
    project (step x g g.2) ∉ seen := by
  intro hr
  obtain ⟨hj,_,_,hb⟩ := repeated_nonbasis_copy x seen g legal allowed intact hr nonbasis
  have hc := clean g.2 hj
  change coefficient (step x g) g.2 g.2 = false at hc
  rw [hc] at hb
  contradiction

theorem original_clean_nonbasis_is_new (q r : Program) (g : Gate)
    (hp : Legal (q ++ g :: r)) (h : run identity (q ++ g :: r) = target)
    (hl : (q ++ g :: r).length ≤ 18) (hu : (touchedSources (q ++ g :: r)).length = 2)
    (clean : Clean (step (run identity q) g g.2))
    (nonbasis : project (step (run identity q) g g.2) ∉ maskBasis) :
    project (step (run identity q) g g.2) ∉ seenAfter identity (0 :: maskBasis) q := by
  apply clean_nonbasis_is_new _ _ g (hp g (List.mem_append_right _ List.mem_cons_self))
  · exact saturated_local_allowed q r g (original_repeats_permutation _ h hl hu)
      (by intro j hj; rw [h]; exact sources_fixed j hj)
      (by intro j hj; rw [h]; exact private_ends_nonzero j hj)
  · exact original_fresh_private_bit q (g :: r) h hl hu
  · exact clean
  · exact nonbasis

theorem transpose_clean_nonbasis_is_new (q r : Program) (g : Gate)
    (hp : Legal (q ++ g :: r)) (h : run identity (q ++ g :: r) = TransposeTarget.matrix)
    (hl : (q ++ g :: r).length ≤ 18) (hu : (touchedSources (q ++ g :: r)).length = 2)
    (clean : Clean (step (run identity q) g g.2))
    (nonbasis : project (step (run identity q) g g.2) ∉ maskBasis) :
    project (step (run identity q) g g.2) ∉ seenAfter identity (0 :: maskBasis) q := by
  apply clean_nonbasis_is_new _ _ g (hp g (List.mem_append_right _ List.mem_cons_self))
  · exact saturated_local_allowed q r g (transpose_repeats_permutation _ h hl hu)
      (by intro j hj; rw [h]; exact TransposeTarget.sources_fixed j hj)
      (by intro j hj; rw [h]; exact TransposeTarget.private_ends_nonzero j hj)
  · exact transpose_fresh_private_bit q (g :: r) h hl hu
  · exact clean
  · exact nonbasis


theorem seenAfter_members (p : Program) (x : Matrix) (seen : List (BitVec 7)) (z : BitVec 7) :
    z ∈ seenAfter x seen p ↔ z ∈ seen ++ trace x p := by
  induction p generalizing x seen with
  | nil => simp [seenAfter,trace]
  | cons g p ih =>
    simp only [seenAfter,trace,ih,List.mem_append,List.mem_cons,or_assoc,or_comm]

theorem repeated_final_control (x : Matrix) (seen : List (BitVec 7)) (g : Gate) (m : Matrix)
    (legal : g.1 ≠ g.2) (allowed : Allowed x seen g) (intact : PrivateIntact x)
    (repeated : project (step x g g.2) ∈ seen)
    (nonbasis : project (step x g g.2) ∉ maskBasis) (final : step x g g.2 = m g.2)
    (cleanGoal : ∀ j ∈ privateOutputs, Clean (identity j ^^^ m j)) :
    g.2 ∈ privateOutputs ∧ x g.2 = identity g.2 ∧
      x g.1 = identity g.2 ^^^ m g.2 ∧ Clean (x g.1) := by
  obtain ⟨hj,hr,_,_⟩ := repeated_nonbasis_copy x seen g legal allowed intact repeated nonbasis
  have hm : identity g.2 ^^^ x g.1 = m g.2 := by simpa [step,hr] using final
  have hc : x g.1 = identity g.2 ^^^ m g.2 := by
    rw [← hm,← BitVec.xor_assoc]
    simp
  exact ⟨hj,hr,hc,hc ▸ cleanGoal g.2 hj⟩

theorem original_clean_goals : ∀ j ∈ privateOutputs, Clean (identity j ^^^ target j) := by
  unfold Clean
  decide

theorem transpose_clean_goals : ∀ j ∈ privateOutputs, Clean (identity j ^^^ TransposeTarget.matrix j) := by
  unfold Clean
  decide

/-- A final row with a nonbasis projection is either a first appearance,
or a copy of its clean goal into the still intact private output. -/
theorem final_row_dichotomy (x : Matrix) (seen : List (BitVec 7)) (g : Gate) (m : Matrix)
    (legal : g.1 ≠ g.2) (allowed : Allowed x seen g) (intact : PrivateIntact x)
    (nonbasis : project (step x g g.2) ∉ maskBasis) (final : step x g g.2 = m g.2)
    (cleanGoal : ∀ j ∈ privateOutputs, Clean (identity j ^^^ m j)) :
    project (step x g g.2) ∉ seen ∨
      (g.2 ∈ privateOutputs ∧ x g.2 = identity g.2 ∧
        x g.1 = identity g.2 ^^^ m g.2 ∧ Clean (x g.1)) := by
  by_cases hr : project (step x g g.2) ∈ seen
  · exact Or.inr (repeated_final_control x seen g m legal allowed intact hr nonbasis final cleanGoal)
  · exact Or.inl hr


theorem original_final_row_dichotomy (q r : Program) (g : Gate)
    (hp : Legal (q ++ g :: r)) (h : run identity (q ++ g :: r) = target)
    (hl : (q ++ g :: r).length ≤ 18) (hu : (touchedSources (q ++ g :: r)).length = 2)
    (nonbasis : project (step (run identity q) g g.2) ∉ maskBasis)
    (final : step (run identity q) g g.2 = target g.2) :
    project (step (run identity q) g g.2) ∉ seenAfter identity (0 :: maskBasis) q ∨
      (g.2 ∈ privateOutputs ∧ run identity q g.2 = identity g.2 ∧
        run identity q g.1 = identity g.2 ^^^ target g.2 ∧ Clean (run identity q g.1)) := by
  apply final_row_dichotomy _ _ g target (hp g (List.mem_append_right _ List.mem_cons_self))
  · exact saturated_local_allowed q r g (original_repeats_permutation _ h hl hu)
      (by intro j hj; rw [h]; exact sources_fixed j hj)
      (by intro j hj; rw [h]; exact private_ends_nonzero j hj)
  · exact original_fresh_private_bit q (g :: r) h hl hu
  · exact nonbasis
  · exact final
  · exact original_clean_goals

theorem transpose_final_row_dichotomy (q r : Program) (g : Gate)
    (hp : Legal (q ++ g :: r)) (h : run identity (q ++ g :: r) = TransposeTarget.matrix)
    (hl : (q ++ g :: r).length ≤ 18) (hu : (touchedSources (q ++ g :: r)).length = 2)
    (nonbasis : project (step (run identity q) g g.2) ∉ maskBasis)
    (final : step (run identity q) g g.2 = TransposeTarget.matrix g.2) :
    project (step (run identity q) g g.2) ∉ seenAfter identity (0 :: maskBasis) q ∨
      (g.2 ∈ privateOutputs ∧ run identity q g.2 = identity g.2 ∧
        run identity q g.1 = identity g.2 ^^^ TransposeTarget.matrix g.2 ∧ Clean (run identity q g.1)) := by
  apply final_row_dichotomy _ _ g TransposeTarget.matrix (hp g (List.mem_append_right _ List.mem_cons_self))
  · exact saturated_local_allowed q r g (transpose_repeats_permutation _ h hl hu)
      (by intro j hj; rw [h]; exact TransposeTarget.sources_fixed j hj)
      (by intro j hj; rw [h]; exact TransposeTarget.private_ends_nonzero j hj)
  · exact transpose_fresh_private_bit q (g :: r) h hl hu
  · exact nonbasis
  · exact final
  · exact transpose_clean_goals

end HGP13.TightRepeats

