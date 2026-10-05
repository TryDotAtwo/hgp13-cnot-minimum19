import Std

namespace HGP13.CountHelpers

theorem filter_partition {α : Type} (f : α → Bool) (p : List α) :
    (p.filter f).length + (p.filter (fun z => !f z)).length = p.length := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    cases h : f z <;>
      simp only [List.filter_cons, h, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] at * <;> omega

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · simp
    · exact eraseDups_nodup (l.filter (fun b => !b == a))
termination_by l.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == a) l
  simp only [List.length_cons]
  omega

end HGP13.CountHelpers
