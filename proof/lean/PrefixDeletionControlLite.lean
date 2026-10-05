import OriginalPrefixesLite
import IdealPrefixLookup

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

theorem key_is_ideal : IdealPrefixLookup.ideal sector 3 148886 = true := by
  rw [← observed_key]
  exact IdealPrefixLookup.ideal_accepts sector extra observed 3 triple_catalogued
    (by decide) (by decide) (by decide) (by decide)

/-- Removing one genuinely catalogued triple makes the independent lookup
completeness contract false, regardless of any graph-reachability result. -/
theorem deletion_breaks_completeness :
    ¬ FullWordPath.PrefixComplete sector deletedLookup := by
  exact IdealPrefixLookup.not_prefix_complete_of_missing_ideal
    sector deletedLookup 3 148886 (by decide) (by decide) key_is_ideal (by decide)

end HGP13.PrefixDeletionControl
