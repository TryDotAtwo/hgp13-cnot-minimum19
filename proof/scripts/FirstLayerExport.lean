import ConcreteFiniteBoundary

open HGP13

def main : IO Unit := do
  for (s, i) in SectorCover.sectors.zipIdx do
    let c := SharedSearch.ofSector s (ConcreteFiniteBoundary.lookup s)
    let first := (SharedSearch.next c 0 (SharedSearch.initial c)).eraseDups
    IO.println s!"{i} {first.length}"
