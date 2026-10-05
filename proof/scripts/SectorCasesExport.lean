import SectorCover

open HGP13

def sectorCaseLine (s : SectorCover.Sector) : String :=
  let orientation := if s.transposed then "1" else "0"
  let family :=
    if s.active.length == 2 then
      if s.carriers.length == 2 then "0" else "1"
    else if s.carriers.length == 1 then "2" else "3"
  let source := String.intercalate "" (s.active.map (fun x => toString x.val ++ ","))
  let relay := String.intercalate "" (s.carriers.map (fun x => toString (Budget.privateOutputs.idxOf x) ++ ","))
  orientation ++ " " ++ family ++ " " ++ source ++ " " ++ relay

def main : IO Unit := do
  for s in SectorCover.sectors do
    IO.println (sectorCaseLine s)
