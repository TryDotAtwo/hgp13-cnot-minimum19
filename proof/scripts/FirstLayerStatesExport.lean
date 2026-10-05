import ConcreteFiniteBoundary

open HGP13

def stateLine (i : Nat) (s : SharedSearch.State) : String :=
  let rows := String.intercalate "" (s.rows.map (fun v => toString v ++ ","))
  let limbs := String.intercalate "" ((List.range 8).map fun j =>
    toString ((s.history >>> (64*j)) &&& (2^64-1)) ++ ",")
  s!"STATE {i} {rows}|{limbs}|{s.changed},{s.returned},{s.copied},{s.extra}"

def main : IO Unit := do
  for (s, i) in SectorCover.sectors.zipIdx do
    let c := SharedSearch.ofSector s (ConcreteFiniteBoundary.lookup s)
    let first := (SharedSearch.next c 0 (SharedSearch.initial c)).eraseDups
    for z in first do
      IO.println (stateLine i z)
  IO.println s!"DIAGNOSTIC_FIRST_LAYER_ONLY {SectorCover.sectors.length}"
