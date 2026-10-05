import OriginalPrefixesLite
import FullWordPath

namespace HGP13.PrefixDeletionControl

def sector : SectorCover.Sector := ⟨false,[0,1],[6,7]⟩
def extra : List Catalogues.Value := [(9 : Catalogues.Value),11,22]
def observed : List Nat := [9,11,22]
def deletedLookup (k x : Nat) : Bool :=
  if k == 3 && x == 148886 then false else OriginalPrefixesLite.lookup k x

theorem triple_catalogued :
    Catalogues.Catalogued (ProjectedHistory.projectedGoals sector) 3 extra := by
  refine ⟨by decide,by decide,?_,by decide +kernel⟩
  intro z hz
  have he : z = 9 ∨ z = 11 ∨ z = 22 := by simpa [extra] using hz
  rcases he with he | he | he <;> subst z <;> decide

theorem observed_key : SharedSearch.encode observed = 148886 := by decide

theorem original_accepts_key : OriginalPrefixesLite.lookup 3 148886 = true := by decide

/-- Removing one genuinely catalogued triple makes the independent lookup
completeness contract false, regardless of any graph-reachability result. -/
theorem deletion_breaks_completeness :
    ¬ FullWordPath.PrefixComplete sector deletedLookup := by
  intro h
  have hv := h extra observed 3 triple_catalogued
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rw [observed_key] at hv
  simp [deletedLookup] at hv

end HGP13.PrefixDeletionControl
