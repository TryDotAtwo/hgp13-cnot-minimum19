import TightRepeats
import Passive

namespace HGP13.CleanPersistence
open Budget Projection FreeXor TightRepeats

theorem seenAfter_contains (p : Program) (x : Matrix) (seen : List (BitVec 7)) :
    seen ⊆ seenAfter x seen p := by
  intro z hz
  exact (seenAfter_members p x seen z).mpr (List.mem_append_left _ hz)

theorem seenAfter_append (p q : Program) (x : Matrix) (seen : List (BitVec 7)) :
    seenAfter x seen (p ++ q) = seenAfter (run x p) (seenAfter x seen p) q := by
  induction p generalizing x seen with
  | nil => rfl
  | cons g p ih => exact ih (step x g) _

theorem lawfulTrace_suffix (p q : Program) (x : Matrix) (seen : List (BitVec 7))
    (h : LawfulTrace x seen (p ++ q)) : LawfulTrace (run x p) (seenAfter x seen p) q := by
  intro a g b he
  have hh := h (p ++ a) g b (by simp [he,List.append_assoc])
  simpa only [run_append,seenAfter_append] using hh

/-- Once a clean nonbasis projection is in history, any future occurrence
of that exact full row must already occupy the same coordinate now. -/
theorem clean_row_backward (p : Program) (x : Matrix) (seen : List (BitVec 7)) (w : Row)
    (legal : Legal p) (lawful : LawfulTrace x seen p)
    (zero : (0 : BitVec 7) ∈ seen) (supported : ∀ i, project (x i) ∈ seen)
    (intact : PrivateIntact x) (clean : Clean w) (nonbasis : project w ∉ maskBasis)
    (appeared : project w ∈ seen) : ∀ i, run x p i = w → x i = w := by
  induction p generalizing x seen with
  | nil => intro i hi; exact hi
  | cons g p ih =>
    have hg : Allowed x seen g := lawful [] g p rfl
    have ht : LawfulTrace (step x g) (project (step x g g.2) :: seen) p := by
      intro a b r he
      exact lawful (g :: a) b r (by simp [he])
    intro i hi
    have hs := ih (step x g) _ (legal_tail legal) ht
      (List.mem_cons_of_mem _ zero) (step_supported x g seen supported)
      (private_intact_step x seen g zero supported hg intact)
      (List.mem_cons_of_mem _ appeared) i hi
    by_cases hit : i = g.2
    · have hw : step x g g.2 = w := by simpa [hit] using hs
      have hn := clean_nonbasis_is_new x seen g (legal g List.mem_cons_self) hg intact
        (hw ▸ clean) (hw ▸ nonbasis)
      exact False.elim (hn (hw ▸ appeared))
    · simpa [step,hit] using hs

theorem saturated_clean_row_backward (q r : Program) (w : Row)
    (legal : Legal (q ++ r))
    (perm : (privateOutputs ++ touchedSources (q ++ r)).Perm
      (repeatTargets (record identity (0 :: maskBasis) (q ++ r))))
    (fixed : ∀ j ∈ sources, run identity (q ++ r) j = identity j)
    (nonzero : ∀ j ∈ privateOutputs, project (run identity (q ++ r) j) ≠ 0)
    (clean : Clean w) (nonbasis : project w ∉ maskBasis)
    (appeared : project w ∈ seenAfter identity (0 :: maskBasis) q) :
    ∀ i, run identity (q ++ r) i = w → run identity q i = w := by
  have lawful := saturated_lawfulTrace (q ++ r) perm fixed nonzero
  have intact := private_intact_run q identity (0 :: maskBasis) List.mem_cons_self initial_supported
    (lawfulTrace_prefix q r identity _ lawful) private_intact_initial
  have lr : Legal r := fun g hg => legal g (List.mem_append_right _ hg)
  intro i hi
  exact clean_row_backward r (run identity q) _ w lr (lawfulTrace_suffix q r identity _ lawful)
    (seenAfter_contains q identity _ List.mem_cons_self)
    (seenAfter_supported q identity _ initial_supported) intact clean nonbasis appeared i
    (by simpa only [run_append] using hi)

theorem original_clean_row_backward (q r : Program) (w : Row)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = target)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (clean : Clean w) (nonbasis : project w ∉ maskBasis)
    (appeared : project w ∈ seenAfter identity (0 :: maskBasis) q) :
    ∀ i, target i = w → run identity q i = w := by
  intro i hi
  exact saturated_clean_row_backward q r w hp (original_repeats_permutation _ h hl hu)
    (by intro j hj; rw [h]; exact sources_fixed j hj)
    (by intro j hj; rw [h]; exact private_ends_nonzero j hj)
    clean nonbasis appeared i (by rw [h]; exact hi)

theorem transpose_clean_row_backward (q r : Program) (w : Row)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = TransposeTarget.matrix)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (clean : Clean w) (nonbasis : project w ∉ maskBasis)
    (appeared : project w ∈ seenAfter identity (0 :: maskBasis) q) :
    ∀ i, TransposeTarget.matrix i = w → run identity q i = w := by
  intro i hi
  exact saturated_clean_row_backward q r w hp (transpose_repeats_permutation _ h hl hu)
    (by intro j hj; rw [h]; exact TransposeTarget.sources_fixed j hj)
    (by intro j hj; rw [h]; exact TransposeTarget.private_ends_nonzero j hj)
    clean nonbasis appeared i (by rw [h]; exact hi)

theorem original_central_condition (q r : Program)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = target)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (appeared : project (target 8) ∈ seenAfter identity (0 :: maskBasis) q) :
    run identity q 8 = target 8 :=
  original_clean_row_backward q r (target 8) hp h hl hu (by unfold Clean; decide) (by decide) appeared 8 rfl

theorem transpose_central_condition (q r : Program)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = TransposeTarget.matrix)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (appeared : project (TransposeTarget.matrix 8) ∈ seenAfter identity (0 :: maskBasis) q) :
    run identity q 8 = TransposeTarget.matrix 8 :=
  transpose_clean_row_backward q r (TransposeTarget.matrix 8) hp h hl hu (by unfold Clean; decide) (by decide) appeared 8 rfl


/-- Zero projection cannot be recovered after any update in a lawful trace. -/
theorem zero_row_backward (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (lawful : LawfulTrace x seen p) (zero : (0 : BitVec 7) ∈ seen) :
    ∀ i, project (run x p i) = 0 → x i = run x p i := by
  induction p generalizing x seen with
  | nil => intro i _; rfl
  | cons g p ih =>
    have hg : Allowed x seen g := lawful [] g p rfl
    have ht : LawfulTrace (step x g) (project (step x g g.2) :: seen) p := by
      intro a b r he
      exact lawful (g :: a) b r (by simp [he])
    intro i hi
    have hs := ih (step x g) _ ht (List.mem_cons_of_mem _ zero) i hi
    by_cases hit : i = g.2
    · have hz : project (step x g g.2) = 0 := by rw [← hit,hs]; exact hi
      exact False.elim (allowed_nonzero x seen g zero hg hz)
    · exact (step_other x g i hit).symm.trans hs

theorem last_update_decomposition (p : Program) (x : Matrix) (j : Wire)
    (ht : j ∈ p.map Prod.snd) :
    ∃ a g b, p = a ++ g :: b ∧ g.2 = j ∧ step (run x a) g j = run x p j := by
  induction p generalizing x with
  | nil => simp at ht
  | cons g p ih =>
    by_cases htail : j ∈ p.map Prod.snd
    · obtain ⟨a,k,b,he,hj,hf⟩ := ih (step x g) htail
      exact ⟨g :: a,k,b,by simp [he],hj,hf⟩
    · have hj : g.2 = j := by simpa [htail,eq_comm] using ht
      refine ⟨[],g,p,rfl,hj,?_⟩
      exact (run_untargeted p (step x g) j htail).symm

/-- If a private final projection is already in history but its row is
unfinished, a current clean carrier must exist on a future control wire. -/
theorem unfinished_output_carrier (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (m : Matrix) (j : Wire) (keep : Wire → Bool)
    (legal : Legal p) (lawful : LawfulTrace x seen p)
    (zero : (0 : BitVec 7) ∈ seen) (supported : ∀ i, project (x i) ∈ seen)
    (intact : PrivateIntact x) (controls : ∀ g ∈ p, keep g.1 = true)
    (finish : run x p j = m j) (unfinished : x j ≠ m j)
    (appeared : project (m j) ∈ seen) (nonbasis : project (m j) ∉ maskBasis)
    (cleanGoal : ∀ i ∈ privateOutputs, Clean (identity i ^^^ m i)) :
    x j = identity j ∧ ∃ i, keep i = true ∧ x i = identity j ^^^ m j ∧ Clean (x i) := by
  have ht : j ∈ p.map Prod.snd := by
    by_cases ht : j ∈ p.map Prod.snd
    · exact ht
    · exact False.elim (unfinished ((run_untargeted p x j ht).symm.trans finish))
  obtain ⟨a,g,b,he,hj,hf⟩ := last_update_decomposition p x j ht
  subst p
  have gm : g ∈ a ++ g :: b := List.mem_append_right _ List.mem_cons_self
  have ha := lawfulTrace_prefix a (g :: b) x seen lawful
  have ai := private_intact_run a x seen zero supported ha intact
  have final : step (run x a) g g.2 = m g.2 := by rw [hj,hf]; exact finish
  have ar := seenAfter_contains a x seen appeared
  have allowedNow := lawful a g b rfl
  obtain ⟨jp,jrow,carrier,cclean⟩ := repeated_final_control (run x a) (seenAfter x seen a) g m
    (legal g gm) allowedNow ai (by rw [final,hj]; exact ar) (by rw [final,hj]; exact nonbasis)
    final cleanGoal
  have pj : j ∈ privateOutputs := hj ▸ jp
  have jrow' : run x a j = identity j := by simpa [hj] using jrow
  have old : x j = identity j :=
    (zero_row_backward a x seen ha zero j (by rw [jrow']; exact private_starts_zero j pj)).trans jrow'
  let w := identity j ^^^ m j
  have projected : project w = project (m j) := by
    simp [w,project_add,private_starts_zero j pj]
  have cw : Clean w := cleanGoal j pj
  have la : Legal a := fun k hk => legal k (List.mem_append_left _ hk)
  have ci : x g.1 = w := clean_row_backward a x seen w la ha zero supported intact cw
    (by rw [projected]; exact nonbasis) (by rw [projected]; exact appeared) g.1
    (by simpa [w,hj] using carrier)
  exact ⟨old,g.1,controls g gm,ci,ci ▸ cw⟩


theorem saturated_output_condition (q r : Program) (m : Matrix) (j : Wire) (keep : Wire → Bool)
    (legal : Legal (q ++ r)) (h : run identity (q ++ r) = m)
    (perm : (privateOutputs ++ touchedSources (q ++ r)).Perm
      (repeatTargets (record identity (0 :: maskBasis) (q ++ r))))
    (fixed : ∀ i ∈ sources, run identity (q ++ r) i = identity i)
    (nonzero : ∀ i ∈ privateOutputs, project (run identity (q ++ r) i) ≠ 0)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (cleanGoal : ∀ i ∈ privateOutputs, Clean (identity i ^^^ m i))
    (unfinished : run identity q j ≠ m j)
    (appeared : project (m j) ∈ seenAfter identity (0 :: maskBasis) q)
    (nonbasis : project (m j) ∉ maskBasis) :
    run identity q j = identity j ∧ ∃ i, keep i = true ∧
      run identity q i = identity j ^^^ m j ∧ Clean (run identity q i) := by
  have lawful := saturated_lawfulTrace (q ++ r) perm fixed nonzero
  have intact := private_intact_run q identity (0 :: maskBasis) List.mem_cons_self initial_supported
    (lawfulTrace_prefix q r identity _ lawful) private_intact_initial
  exact unfinished_output_carrier r (run identity q) _ m j keep
    (fun g hg => legal g (List.mem_append_right _ hg))
    (lawfulTrace_suffix q r identity _ lawful)
    (seenAfter_contains q identity _ List.mem_cons_self)
    (seenAfter_supported q identity _ initial_supported) intact
    (fun g hg => controls g (List.mem_append_right _ hg))
    (by rw [← run_append,h]) unfinished appeared nonbasis cleanGoal

theorem original_private_nonbasis : ∀ j ∈ privateOutputs, project (target j) ∉ maskBasis := by decide

theorem transpose_private_nonbasis : ∀ j ∈ privateOutputs, project (TransposeTarget.matrix j) ∉ maskBasis := by decide

theorem original_output_condition (q r : Program) (j : Wire) (keep : Wire → Bool)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = target)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (hj : j ∈ privateOutputs) (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (unfinished : run identity q j ≠ target j)
    (appeared : project (target j) ∈ seenAfter identity (0 :: maskBasis) q) :
    run identity q j = identity j ∧ ∃ i, keep i = true ∧
      run identity q i = identity j ^^^ target j ∧ Clean (run identity q i) :=
  saturated_output_condition q r target j keep hp h (original_repeats_permutation _ h hl hu)
    (by intro i hi; rw [h]; exact sources_fixed i hi)
    (by intro i hi; rw [h]; exact private_ends_nonzero i hi)
    controls original_clean_goals unfinished appeared (original_private_nonbasis j hj)

theorem transpose_output_condition (q r : Program) (j : Wire) (keep : Wire → Bool)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = TransposeTarget.matrix)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (hj : j ∈ privateOutputs) (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (unfinished : run identity q j ≠ TransposeTarget.matrix j)
    (appeared : project (TransposeTarget.matrix j) ∈ seenAfter identity (0 :: maskBasis) q) :
    run identity q j = identity j ∧ ∃ i, keep i = true ∧
      run identity q i = identity j ^^^ TransposeTarget.matrix j ∧ Clean (run identity q i) :=
  saturated_output_condition q r TransposeTarget.matrix j keep hp h (transpose_repeats_permutation _ h hl hu)
    (by intro i hi; rw [h]; exact TransposeTarget.sources_fixed i hi)
    (by intro i hi; rw [h]; exact TransposeTarget.private_ends_nonzero i hi)
    controls transpose_clean_goals unfinished appeared (transpose_private_nonbasis j hj)

/-- Semantic history of full core rows at all actual prefixes. -/
def CoreHistory (keep : Wire → Bool) (q : Program) (w : Row) : Prop :=
  ∃ a b, q = a ++ b ∧ ∃ i, keep i = true ∧ run identity a i = w

theorem core_history_projected (keep : Wire → Bool) (q : Program) (w : Row)
    (h : CoreHistory keep q w) : project w ∈ seenAfter identity (0 :: maskBasis) q := by
  obtain ⟨a,b,he,i,_,hw⟩ := h
  subst q
  rw [seenAfter_append]
  apply seenAfter_contains
  rw [← hw]
  exact seenAfter_supported a identity _ initial_supported i

/-- Erasing passive targets preserves the current rows used by the conditions. -/
theorem erased_prefix_agrees (keep : Wire → Bool) (q r : Program)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true) :
    AgreeOn keep (run identity q) (run identity (q.filter (fun g => keep g.2))) :=
  erase_passive_preserves_core keep q
    (fun g hg => controls g (List.mem_append_left _ hg)) identity identity (fun _ _ => rfl)

theorem original_core_central_condition (keep : Wire → Bool) (q r : Program)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = target)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true) (center : keep 8 = true)
    (appeared : ∃ w, CoreHistory keep q w ∧ project w = project (target 8)) :
    run identity (q.filter (fun g => keep g.2)) 8 = target 8 := by
  obtain ⟨w,hw,he⟩ := appeared
  have hs := core_history_projected keep q w hw
  rw [he] at hs
  exact ((erased_prefix_agrees keep q r controls) 8 center).symm.trans
    (original_central_condition q r hp h hl hu hs)

theorem transpose_core_central_condition (keep : Wire → Bool) (q r : Program)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = TransposeTarget.matrix)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true) (center : keep 8 = true)
    (appeared : ∃ w, CoreHistory keep q w ∧ project w = project (TransposeTarget.matrix 8)) :
    run identity (q.filter (fun g => keep g.2)) 8 = TransposeTarget.matrix 8 := by
  obtain ⟨w,hw,he⟩ := appeared
  have hs := core_history_projected keep q w hw
  rw [he] at hs
  exact ((erased_prefix_agrees keep q r controls) 8 center).symm.trans
    (transpose_central_condition q r hp h hl hu hs)


theorem transport_output_condition (keep : Wire → Bool) (x y m : Matrix) (j : Wire)
    (agree : AgreeOn keep x y) (hj : keep j = true)
    (condition : x j = identity j ∧ ∃ i, keep i = true ∧ x i = identity j ^^^ m j ∧ Clean (x i)) :
    y j = identity j ∧ ∃ i, keep i = true ∧ y i = identity j ^^^ m j ∧ Clean (y i) := by
  obtain ⟨hx,i,hi,hw,hc⟩ := condition
  exact ⟨(agree j hj).symm.trans hx,i,hi,(agree i hi).symm.trans hw,agree i hi ▸ hc⟩

theorem original_core_output_condition (keep : Wire → Bool) (q r : Program) (j : Wire)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = target)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (hj : j ∈ privateOutputs) (kept : keep j = true)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (unfinished : run identity (q.filter (fun g => keep g.2)) j ≠ target j)
    (appeared : ∃ w, CoreHistory keep q w ∧ project w = project (target j)) :
    run identity (q.filter (fun g => keep g.2)) j = identity j ∧
      ∃ i, keep i = true ∧ run identity (q.filter (fun g => keep g.2)) i = identity j ^^^ target j ∧
        Clean (run identity (q.filter (fun g => keep g.2)) i) := by
  obtain ⟨w,hw,he⟩ := appeared
  have hs := core_history_projected keep q w hw
  rw [he] at hs
  have agree := erased_prefix_agrees keep q r controls
  apply transport_output_condition keep _ _ target j agree kept
  exact original_output_condition q r j keep hp h hl hu hj controls
    (by rw [agree j kept]; exact unfinished) hs

theorem transpose_core_output_condition (keep : Wire → Bool) (q r : Program) (j : Wire)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = TransposeTarget.matrix)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (hj : j ∈ privateOutputs) (kept : keep j = true)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (unfinished : run identity (q.filter (fun g => keep g.2)) j ≠ TransposeTarget.matrix j)
    (appeared : ∃ w, CoreHistory keep q w ∧ project w = project (TransposeTarget.matrix j)) :
    run identity (q.filter (fun g => keep g.2)) j = identity j ∧
      ∃ i, keep i = true ∧ run identity (q.filter (fun g => keep g.2)) i = identity j ^^^ TransposeTarget.matrix j ∧
        Clean (run identity (q.filter (fun g => keep g.2)) i) := by
  obtain ⟨w,hw,he⟩ := appeared
  have hs := core_history_projected keep q w hw
  rw [he] at hs
  have agree := erased_prefix_agrees keep q r controls
  apply transport_output_condition keep _ _ TransposeTarget.matrix j agree kept
  exact transpose_output_condition q r j keep hp h hl hu hj controls
    (by rw [agree j kept]; exact unfinished) hs

theorem core_history_survives_erasure (keep : Wire → Bool) (q : Program) (w : Row)
    (controls : ∀ g ∈ q, keep g.1 = true) (history : CoreHistory keep q w) :
    CoreHistory keep (q.filter (fun g => keep g.2)) w := by
  obtain ⟨a,b,he,i,hi,hw⟩ := history
  subst q
  refine ⟨a.filter (fun g => keep g.2),b.filter (fun g => keep g.2),by simp, i,hi,?_⟩
  exact ((erased_prefix_agrees keep a b controls) i hi).symm.trans hw


/-- After a nonbasis projection has appeared globally, its presence in the
core cannot begin without an already present core carrier. -/
theorem core_projection_backward (p : Program) (x : Matrix) (seen : List (BitVec 7))
    (z : BitVec 7) (keep : Wire → Bool) (lawful : LawfulTrace x seen p)
    (controls : ∀ g ∈ p, keep g.1 = true) (nonbasis : z ∉ maskBasis) (appeared : z ∈ seen) :
    (∃ i, keep i = true ∧ project (run x p i) = z) → ∃ i, keep i = true ∧ project (x i) = z := by
  induction p generalizing x seen with
  | nil => exact id
  | cons g p ih =>
    have hg : Allowed x seen g := lawful [] g p rfl
    have ht : LawfulTrace (step x g) (project (step x g g.2) :: seen) p := by
      intro a b r he
      exact lawful (g :: a) b r (by simp [he])
    intro witness
    obtain ⟨i,hi,hv⟩ := ih (step x g) _ ht
      (fun k hk => controls k (List.mem_cons_of_mem _ hk)) (List.mem_cons_of_mem _ appeared) witness
    by_cases hit : i = g.2
    · have result : project (step x g g.2) = z := by simpa [hit] using hv
      rcases hg with fresh | copied | restored
      · have hn : project (step x g g.2) ∉ seen := by simpa [headEvent] using fresh
        exact False.elim (hn (result ▸ appeared))
      · refine ⟨g.1,controls g List.mem_cons_self,?_⟩
        simpa [step,project_add,copied.2.1] using result
      · exact False.elim (nonbasis (result ▸ (restored.2 ▸ source_projection_basis _ restored.1)))
    · exact ⟨i,hi,by simpa [step,hit] using hv⟩

theorem core_history_extend (keep : Wire → Bool) (q r : Program) (w : Row)
    (h : CoreHistory keep q w) : CoreHistory keep (q ++ r) w := by
  obtain ⟨a,b,he,i,hi,hw⟩ := h
  exact ⟨a,b ++ r,by simp [he,List.append_assoc],i,hi,hw⟩

/-- A globally fresh nonbasis value created on a passive target can never
occur in the core, either before or after this creation. -/
theorem passive_fresh_no_core_history (q r : Program) (g : Gate) (keep : Wire → Bool)
    (lawful : LawfulTrace identity (0 :: maskBasis) (q ++ g :: r))
    (controls : ∀ k ∈ q ++ g :: r, keep k.1 = true) (passive : keep g.2 = false)
    (fresh : (headEvent (run identity q) (seenAfter identity (0 :: maskBasis) q) g).fresh = true)
    (nonbasis : project (step (run identity q) g g.2) ∉ maskBasis) :
    ¬ ∃ w, CoreHistory keep (q ++ g :: r) w ∧
      project w = project (step (run identity q) g g.2) := by
  let z := project (step (run identity q) g g.2)
  have absent : z ∉ seenAfter identity (0 :: maskBasis) q := by simpa [z,headEvent] using fresh
  have before : ∀ i, project (run identity q i) ≠ z := by
    intro i he
    exact absent (he ▸ seenAfter_supported q identity _ initial_supported i)
  have after : ∀ i, keep i = true → project (step (run identity q) g i) ≠ z := by
    intro i hi
    have hit : i ≠ g.2 := by intro he; subst i; rw [passive] at hi; contradiction
    simpa [step,hit] using before i
  rintro ⟨w,⟨a,b,hab,i,hi,hw⟩,hz⟩
  have aq : a <+: q ++ g :: r := ⟨b,hab.symm⟩
  have qq : q <+: q ++ g :: r := ⟨g :: r,rfl⟩
  rcases List.prefix_or_prefix_of_prefix aq qq with left | right
  · obtain ⟨v,hv⟩ := left
    have old : CoreHistory keep q w := ⟨a,v,hv.symm,i,hi,hw⟩
    apply absent
    change project (step (run identity q) g g.2) ∈ _
    rw [← hz]
    exact core_history_projected keep q w old
  · obtain ⟨v,hv⟩ := right
    have split : g :: r = v ++ b := by
      have eq : q ++ g :: r = q ++ (v ++ b) := by rw [← List.append_assoc, hv]; exact hab
      exact List.append_cancel_left eq
    cases v with
    | nil =>
      have ae : a = q := by simpa using hv.symm
      exact before i (by rw [← ae,hw]; exact hz)
    | cons k v =>
      have kg : k = g := (List.cons.inj split).1.symm
      subst k
      have vb : r = v ++ b := (List.cons.inj split).2
      have tailLawful : LawfulTrace (step (run identity q) g)
          (z :: seenAfter identity (0 :: maskBasis) q) v := by
        intro c d e he
        have hh := lawful (q ++ g :: c) d (e ++ b) (by simp [vb,he,List.append_assoc])
        simpa only [run_append,run_cons,seenAfter_append,seenAfter] using hh
      have vc : ∀ k ∈ v, keep k.1 = true := by
        intro k hk
        apply controls k
        apply List.mem_append_right
        exact List.mem_cons_of_mem _ (by rw [vb]; exact List.mem_append_left _ hk)
      have occurrence : ∃ j, keep j = true ∧ project (run (step (run identity q) g) v j) = z := by
        refine ⟨i,hi,?_⟩
        have row : run (step (run identity q) g) v i = w := by
          simpa only [← hv,run_append,run_cons] using hw
        rw [row]; exact hz
      obtain ⟨j,hj,hzj⟩ := core_projection_backward v (step (run identity q) g)
        (z :: seenAfter identity (0 :: maskBasis) q) z keep tailLawful vc nonbasis List.mem_cons_self occurrence
      exact after j hj hzj


theorem saturated_passive_history_condition (q r : Program) (m : Matrix) (j : Wire) (keep : Wire → Bool)
    (legal : Legal (q ++ r)) (h : run identity (q ++ r) = m)
    (perm : (privateOutputs ++ touchedSources (q ++ r)).Perm
      (repeatTargets (record identity (0 :: maskBasis) (q ++ r))))
    (fixed : ∀ i ∈ sources, run identity (q ++ r) i = identity i)
    (nonzero : ∀ i ∈ privateOutputs, project (run identity (q ++ r) i) ≠ 0)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (cleanGoal : ∀ i ∈ privateOutputs, Clean (identity i ^^^ m i))
    (hj : j ∈ privateOutputs) (passive : keep j = false)
    (nonbasis : project (m j) ∉ maskBasis)
    (appeared : ∃ w, CoreHistory keep q w ∧ project w = project (m j)) :
    CoreHistory keep q (identity j ^^^ m j) := by
  obtain ⟨w,history,projected⟩ := appeared
  have seen : project (m j) ∈ seenAfter identity (0 :: maskBasis) q :=
    projected ▸ core_history_projected keep q w history
  by_cases unfinished : run identity q j ≠ m j
  · obtain ⟨_,i,hi,hw,_⟩ := saturated_output_condition q r m j keep legal h perm fixed nonzero
      controls cleanGoal unfinished seen nonbasis
    exact ⟨q,[],by simp,i,hi,hw⟩
  · have finished : run identity q j = m j := by simpa using unfinished
    have hn : project (m j) ≠ 0 := by rw [← h]; exact nonzero j hj
    have ht : j ∈ q.map Prod.snd := by
      by_cases ht : j ∈ q.map Prod.snd
      · exact ht
      · have eq := run_untargeted q identity j ht
        exact False.elim (hn (by rw [← finished,eq]; exact private_starts_zero j hj))
    obtain ⟨a,g,b,he,gj,result⟩ := last_update_decomposition q identity j ht
    subst q
    have lawful := saturated_lawfulTrace ((a ++ g :: b) ++ r) perm fixed nonzero
    have whole : LawfulTrace identity (0 :: maskBasis) (a ++ g :: (b ++ r)) := by
      simpa only [List.append_assoc,List.cons_append] using lawful
    have cs : ∀ k ∈ a ++ g :: (b ++ r), keep k.1 = true := by
      simpa only [List.append_assoc,List.cons_append] using controls
    have lg : Legal (a ++ g :: (b ++ r)) := by
      simpa only [List.append_assoc,List.cons_append] using legal
    have globalHistory : CoreHistory keep (a ++ g :: (b ++ r)) w := by
      simpa only [List.append_assoc,List.cons_append] using core_history_extend keep (a ++ g :: b) r w history
    have final : step (run identity a) g g.2 = m g.2 := by rw [gj,result]; exact finished
    have notfresh : (headEvent (run identity a) (seenAfter identity (0 :: maskBasis) a) g).fresh = false := by
      cases hf : (headEvent (run identity a) (seenAfter identity (0 :: maskBasis) a) g).fresh with
      | false => rfl
      | true =>
        have absent := passive_fresh_no_core_history a (b ++ r) g keep whole cs
          (by rw [gj]; exact passive) hf (by rw [final,gj]; exact nonbasis)
        exact False.elim (absent ⟨w,globalHistory,by rw [final,gj]; exact projected⟩)
    have ai := private_intact_run a identity (0 :: maskBasis) List.mem_cons_self initial_supported
      (lawfulTrace_prefix a (g :: (b ++ r)) identity _ whole) private_intact_initial
    have repeated : project (step (run identity a) g g.2) ∈ seenAfter identity (0 :: maskBasis) a := by
      simpa [headEvent] using notfresh
    obtain ⟨_,_,carrier,_⟩ := repeated_final_control (run identity a) _ g m
      (lg g (List.mem_append_right _ List.mem_cons_self)) (whole a g (b ++ r) rfl) ai repeated
      (by rw [final,gj]; exact nonbasis) final cleanGoal
    exact ⟨a,g :: b,rfl,g.1,cs g (List.mem_append_right _ List.mem_cons_self),by simpa [gj] using carrier⟩

theorem original_passive_history_condition (keep : Wire → Bool) (q r : Program) (j : Wire)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = target)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (hj : j ∈ privateOutputs) (passive : keep j = false)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (appeared : ∃ w, CoreHistory keep q w ∧ project w = project (target j)) :
    CoreHistory keep (q.filter (fun g => keep g.2)) (identity j ^^^ target j) := by
  apply core_history_survives_erasure keep q _ (fun g hg => controls g (List.mem_append_left _ hg))
  exact saturated_passive_history_condition q r target j keep hp h
    (original_repeats_permutation _ h hl hu)
    (by intro i hi; rw [h]; exact sources_fixed i hi)
    (by intro i hi; rw [h]; exact private_ends_nonzero i hi)
    controls original_clean_goals hj passive (original_private_nonbasis j hj) appeared

theorem transpose_passive_history_condition (keep : Wire → Bool) (q r : Program) (j : Wire)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = TransposeTarget.matrix)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (hj : j ∈ privateOutputs) (passive : keep j = false)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true)
    (appeared : ∃ w, CoreHistory keep q w ∧ project w = project (TransposeTarget.matrix j)) :
    CoreHistory keep (q.filter (fun g => keep g.2)) (identity j ^^^ TransposeTarget.matrix j) := by
  apply core_history_survives_erasure keep q _ (fun g hg => controls g (List.mem_append_left _ hg))
  exact saturated_passive_history_condition q r TransposeTarget.matrix j keep hp h
    (transpose_repeats_permutation _ h hl hu)
    (by intro i hi; rw [h]; exact TransposeTarget.sources_fixed i hi)
    (by intro i hi; rw [h]; exact TransposeTarget.private_ends_nonzero i hi)
    controls transpose_clean_goals hj passive (transpose_private_nonbasis j hj) appeared


theorem core_history_reflects_erasure (keep : Wire → Bool) (q : Program) (w : Row)
    (controls : ∀ g ∈ q, keep g.1 = true)
    (history : CoreHistory keep (q.filter (fun g => keep g.2)) w) : CoreHistory keep q w := by
  obtain ⟨a,b,he,i,hi,hw⟩ := history
  obtain ⟨c,d,hq,hc,_⟩ := List.filter_eq_append_iff.mp he
  refine ⟨c,d,hq,i,hi,?_⟩
  have agree := erase_passive_preserves_core keep c
    (fun g hg => controls g (by rw [hq]; exact List.mem_append_left _ hg)) identity identity
    (fun _ _ => rfl)
  exact (agree i hi).trans (by rw [hc]; exact hw)

theorem core_history_erasure_iff (keep : Wire → Bool) (q : Program) (w : Row)
    (controls : ∀ g ∈ q, keep g.1 = true) :
    CoreHistory keep (q.filter (fun g => keep g.2)) w ↔ CoreHistory keep q w :=
  ⟨core_history_reflects_erasure keep q w controls,core_history_survives_erasure keep q w controls⟩

def ProjectedHistory (keep : Wire → Bool) (q : Program) (z : BitVec 7) : Prop :=
  ∃ w, CoreHistory keep q w ∧ project w = z

theorem projected_history_reflects (keep : Wire → Bool) (q : Program) (z : BitVec 7)
    (controls : ∀ g ∈ q, keep g.1 = true)
    (h : ProjectedHistory keep (q.filter (fun g => keep g.2)) z) : ProjectedHistory keep q z := by
  obtain ⟨w,hw,hz⟩ := h
  exact ⟨w,core_history_reflects_erasure keep q w controls hw,hz⟩

/-- The three semantic core-history pruning conditions, on full rows. -/
def CoreConditions (keep : Wire → Bool) (q : Program) (m : Matrix) : Prop :=
  (ProjectedHistory keep q (project (m 8)) → run identity q 8 = m 8) ∧
  (∀ j ∈ privateOutputs, keep j = true → run identity q j ≠ m j →
    ProjectedHistory keep q (project (m j)) →
    run identity q j = identity j ∧ ∃ i, keep i = true ∧
      run identity q i = identity j ^^^ m j ∧ Clean (run identity q i)) ∧
  (∀ j ∈ privateOutputs, keep j = false → ProjectedHistory keep q (project (m j)) →
    CoreHistory keep q (identity j ^^^ m j))

theorem original_core_conditions (keep : Wire → Bool) (q r : Program)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = target)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true) (center : keep 8 = true) :
    CoreConditions keep (q.filter (fun g => keep g.2)) target := by
  have liftHistory := fun z => projected_history_reflects keep q z
    (fun g hg => controls g (List.mem_append_left _ hg))
  refine ⟨?_,?_,?_⟩
  · intro appeared
    exact original_core_central_condition keep q r hp h hl hu controls center (liftHistory _ appeared)
  · intro j hj hk unfinished appeared
    exact original_core_output_condition keep q r j hp h hl hu hj hk controls unfinished (liftHistory _ appeared)
  · intro j hj hk appeared
    exact original_passive_history_condition keep q r j hp h hl hu hj hk controls (liftHistory _ appeared)

theorem transpose_core_conditions (keep : Wire → Bool) (q r : Program)
    (hp : Legal (q ++ r)) (h : run identity (q ++ r) = TransposeTarget.matrix)
    (hl : (q ++ r).length ≤ 18) (hu : (touchedSources (q ++ r)).length = 2)
    (controls : ∀ g ∈ q ++ r, keep g.1 = true) (center : keep 8 = true) :
    CoreConditions keep (q.filter (fun g => keep g.2)) TransposeTarget.matrix := by
  have liftHistory := fun z => projected_history_reflects keep q z
    (fun g hg => controls g (List.mem_append_left _ hg))
  refine ⟨?_,?_,?_⟩
  · intro appeared
    exact transpose_core_central_condition keep q r hp h hl hu controls center (liftHistory _ appeared)
  · intro j hj hk unfinished appeared
    exact transpose_core_output_condition keep q r j hp h hl hu hj hk controls unfinished (liftHistory _ appeared)
  · intro j hj hk appeared
    exact transpose_passive_history_condition keep q r j hp h hl hu hj hk controls (liftHistory _ appeared)

end HGP13.CleanPersistence



