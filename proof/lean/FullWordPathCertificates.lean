import FullWordPath
import PrefixPackedFourth

namespace HGP13.FullWordPathCertificates
open FullWordPath

theorem prefix_complete_of_three_checks (s : SectorCover.Sector)
    (lookup : Nat → Nat → Bool)
    (cert33 cert34 : PrefixTreeCertificate.Cert4)
    (cert44 : PrefixPackedFourth.Cert4)
    (h33 : PrefixTreeCertificate.verifyThree
      (ProjectedHistory.projectedGoals s) (lookup 3) cert33 = true)
    (h34 : PrefixTreeCertificate.verifyThree
      (ProjectedHistory.projectedGoals s) (lookup 4) cert34 = true)
    (h44 : PrefixPackedFourth.verifyFour
      (ProjectedHistory.projectedGoals s) (lookup 4) cert44 = true) :
    PrefixComplete s lookup := by
  intro extra observed capacity hc hmin hmax hcaplo hcaphi hn hs
  have hcase : capacity = 3 ∨ capacity = 4 := by omega
  rcases hcase with h3 | h4
  · subst capacity
    have he : extra.length = 3 := by omega
    have hc3 : Catalogues.Catalogued (ProjectedHistory.projectedGoals s) 3 extra := by
      simpa only [he] using hc
    simpa using PrefixTreeCertificate.verifyThree_lookup
      (ProjectedHistory.projectedGoals s) extra observed (lookup 3)
      cert33 hc3 hn hs h33
  · subst capacity
    have hlen : extra.length = 3 ∨ extra.length = 4 := by omega
    rcases hlen with he | he
    · have hc3 : Catalogues.Catalogued (ProjectedHistory.projectedGoals s) 3 extra := by
        simpa only [he] using hc
      simpa using PrefixTreeCertificate.verifyThree_lookup
        (ProjectedHistory.projectedGoals s) extra observed (lookup 4)
        cert34 hc3 hn hs h34
    · have hc4 : Catalogues.Catalogued (ProjectedHistory.projectedGoals s) 4 extra := by
        simpa only [he] using hc
      simpa using PrefixPackedFourth.verifyFour_lookup
        (ProjectedHistory.projectedGoals s) extra observed (lookup 4)
        cert44 hc4 hn hs h44

theorem short_word_accepted_path_of_certificates (s : SectorCover.Sector)
    (hs : s ∈ SectorCover.sectors) (lookup : Nat → Nat → Bool)
    (cert33 cert34 : PrefixTreeCertificate.Cert4)
    (cert44 : PrefixPackedFourth.Cert4)
    (h33 : PrefixTreeCertificate.verifyThree
      (ProjectedHistory.projectedGoals s) (lookup 3) cert33 = true)
    (h34 : PrefixTreeCertificate.verifyThree
      (ProjectedHistory.projectedGoals s) (lookup 4) cert34 = true)
    (h44 : PrefixPackedFourth.verifyFour
      (ProjectedHistory.projectedGoals s) (lookup 4) cert44 = true)
    (p : Program) (hp : Legal p) (hc : SectorCover.Compatible s p)
    (real : run identity p = HGP13.target) (short : p.length ≤ 18) :
    ∃ q : List (CoreRowEncoding.IndexedGate (SectorCoordinates.changing s)
      (SectorIndexing.fixedWires s)),
      q.map (CoreRowEncoding.fullGate (SectorCoordinates.changing s)
        (SectorIndexing.fixedWires s)) = SectorCoordinates.core s p ∧
      q.length ≤ 12 + s.carriers.length ∧
      TransitionChecks.Path (SharedSearch.ofSector s lookup) 0
        (SharedSearch.initial (SharedSearch.ofSector s lookup))
        (q.map CoreRowEncoding.label)
        (TransitionChecks.rawRun (SharedSearch.ofSector s lookup)
          (SharedSearch.initial (SharedSearch.ofSector s lookup))
          (q.map CoreRowEncoding.label)) ∧
      SharedSearch.terminal (SharedSearch.ofSector s lookup)
        (TransitionChecks.rawRun (SharedSearch.ofSector s lookup)
          (SharedSearch.initial (SharedSearch.ofSector s lookup))
          (q.map CoreRowEncoding.label)) = true := by
  exact FullWordPath.short_word_accepted_path s hs lookup
    (prefix_complete_of_three_checks s lookup cert33 cert34 cert44 h33 h34 h44)
    p hp hc real short

end HGP13.FullWordPathCertificates
