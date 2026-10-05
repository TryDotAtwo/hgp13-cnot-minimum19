import Sector234Encoding
namespace HGP13.Sector234Potentials
open Sector234Encoding FullPackedPotential SectorCoordinates
def targets : List Row := [liftMask (21 : BitVec 8),liftMask (62 : BitVec 8),liftMask (104 : BitVec 8),liftMask (50 : BitVec 8),liftMask (96 : BitVec 8)]
def history0 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (65 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table0 : Nat := 13407807929942597099574024994652009236544250925038981638234119929759352767241525042873635674003674259565610857913677230547146377168764329368339442934868372
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked0 : check (embed sector) history0 table0 = true := by decide +kernel
theorem bound0 : 18 < 7 + (targets.map (fun z => tableWeight table0 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes0 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history0 z = some (costs z)) :
    18 < 7 + (targets.map costs).sum :=
  excludes_completion (embed sector) history0 targets table0 7 costs checked0 hc bound0
def history1 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (21 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (65 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table1 : Nat := 13407807929942597099574024994652009236544250925038981638234153304556790974130454690816865492717371750334822684138118957968372884261704624539838212532201876
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked1 : check (embed sector) history1 table1 = true := by decide +kernel
theorem bound1 : 18 < 7 + (targets.map (fun z => tableWeight table1 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes1 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history1 z = some (costs z)) :
    18 < 7 + (targets.map costs).sum :=
  excludes_completion (embed sector) history1 targets table1 7 costs checked1 hc bound1
def history2 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (66 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table2 : Nat := 13407807929942597099574024983990498571422297446785757799734240118205118674732640667005234543802602812434608102241345464677342633373724845736883158298257812
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked2 : check (embed sector) history2 table2 = true := by decide +kernel
theorem bound2 : 18 < 7 + (targets.map (fun z => tableWeight table2 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes2 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history2 z = some (costs z)) :
    18 < 7 + (targets.map costs).sum :=
  excludes_completion (embed sector) history2 targets table2 7 costs checked2 hc bound2
def history3 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (21 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (66 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table3 : Nat := 13407807929942597099574024983990498571422297446785757799734273493002556881621570314948464362516300303180248898566803639719854402282343461943137594214312340
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked3 : check (embed sector) history3 table3 = true := by decide +kernel
theorem bound3 : 18 < 7 + (targets.map (fun z => tableWeight table3 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes3 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history3 z = some (costs z)) :
    18 < 7 + (targets.map costs).sum :=
  excludes_completion (embed sector) history3 targets table3 7 costs checked3 hc bound3
def history4 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (3 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (129 : BitVec 8),liftMask (145 : BitVec 8)]
def table4 : Nat := 13407807929942597099574024994821239563924122467228360289685500726201477931930753228193444598111255500707515222999008512302836940252006720933602385357023572
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked4 : check (embed sector) history4 table4 = true := by decide +kernel
theorem bound4 : 18 < 7 + (targets.map (fun z => tableWeight table4 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes4 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history4 z = some (costs z)) :
    18 < 7 + (targets.map costs).sum :=
  excludes_completion (embed sector) history4 targets table4 7 costs checked4 hc bound4
def history5 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (3 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (144 : BitVec 8),liftMask (145 : BitVec 8)]
def table5 : Nat := 13407807929942597099574024983821268244042425904587205153810346711137197682239782972564347009328766057452873789723388371533511404520953390215895679375092052
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked5 : check (embed sector) history5 table5 = true := by decide +kernel
theorem bound5 : 18 < 7 + (targets.map (fun z => tableWeight table5 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes5 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history5 z = some (costs z)) :
    18 < 7 + (targets.map costs).sum :=
  excludes_completion (embed sector) history5 targets table5 7 costs checked5 hc bound5
def history6 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (66 : BitVec 8),liftMask (67 : BitVec 8),liftMask (82 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table6 : Nat := 13407807929942597099574024983990498571422297446785757799734240118205118674732640667004803184655928008340529732733811879691724909401374650784405904731793812
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked6 : check (embed sector) history6 table6 = true := by decide +kernel
theorem bound6 : 18 < 8 + (targets.map (fun z => tableWeight table6 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes6 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history6 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history6 targets table6 8 costs checked6 hc bound6
def history7 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (21 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (66 : BitVec 8),liftMask (67 : BitVec 8),liftMask (82 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table7 : Nat := 13407807929942597099574024983990498571422297446785757799734273493002556881621570314948033003369625891411015301433325172824037921863950168636386319346035092
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked7 : check (embed sector) history7 table7 = true := by decide +kernel
theorem bound7 : 18 < 8 + (targets.map (fun z => tableWeight table7 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes7 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history7 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history7 targets table7 8 costs checked7 hc bound7
def history8 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (80 : BitVec 8),liftMask (82 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table8 : Nat := 13407807929942597099574024994652009236544250925038981638234119929759352767241525042873177354910357388622594159960494014020295690352965390032065703027796372
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked8 : check (embed sector) history8 table8 = true := by decide +kernel
theorem bound8 : 18 < 8 + (targets.map (fun z => tableWeight table8 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes8 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history8 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history8 targets table8 8 costs checked8 hc bound8
def history9 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (21 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (80 : BitVec 8),liftMask (82 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table9 : Nat := 13407807929942597099574024994652009236544250925038981638234153304556790974130454690816407173624055296236953533996057771972850880802822886412216012219476372
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked9 : check (embed sector) history9 table9 = true := by decide +kernel
theorem bound9 : 18 < 8 + (targets.map (fun z => tableWeight table9 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes9 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history9 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history9 targets table9 8 costs checked9 hc bound9
def history10 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (66 : BitVec 8),liftMask (67 : BitVec 8),liftMask (82 : BitVec 8),liftMask (86 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table10 : Nat := 13407807929942597099574024290823074395656113030455064349983554633140319455240978314911831700500810391920025604316407597490047649962947195110453098591152532
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked10 : check (embed sector) history10 table10 = true := by decide +kernel
theorem bound10 : 18 < 8 + (targets.map (fun z => tableWeight table10 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes10 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history10 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history10 targets table10 8 costs checked10 hc bound10
def history11 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (80 : BitVec 8),liftMask (82 : BitVec 8),liftMask (86 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table11 : Nat := 13407807929942597099574024301484585060778066508708288188483434444694553547749862690780205870755239796722392738471222046942890456960012213551241519465884052
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked11 : check (embed sector) history11 table11 = true := by decide +kernel
theorem bound11 : 18 < 8 + (targets.map (fun z => tableWeight table11 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes11 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history11 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history11 targets table11 8 costs checked11 hc bound11
def history12 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (3 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (130 : BitVec 8),liftMask (145 : BitVec 8),liftMask (146 : BitVec 8)]
def table12 : Nat := 13407807929942597099574024994821239563924122467081576378236370282311362923570635122348981799662602179472275977118011442919544899461701203327203414796511572
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked12 : check (embed sector) history12 table12 = true := by decide +kernel
theorem bound12 : 18 < 8 + (targets.map (fun z => tableWeight table12 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes12 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history12 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history12 targets table12 8 costs checked12 hc bound12
def history13 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (3 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (12 : BitVec 8),liftMask (16 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (128 : BitVec 8),liftMask (144 : BitVec 8),liftMask (145 : BitVec 8),liftMask (146 : BitVec 8)]
def table13 : Nat := 13407807929942597099574024983821268244042425904440421242386848111678156998314818962231703215834296872832036342646129640396216580365326321652737177163508052
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked13 : check (embed sector) history13 table13 = true := by decide +kernel
theorem bound13 : 18 < 8 + (targets.map (fun z => tableWeight table13 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes13 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history13 z = some (costs z)) :
    18 < 8 + (targets.map costs).sum :=
  excludes_completion (embed sector) history13 targets table13 8 costs checked13 hc bound13
def history14 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (21 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (66 : BitVec 8),liftMask (67 : BitVec 8),liftMask (82 : BitVec 8),liftMask (86 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table14 : Nat := 13407807929942597099574024290823074395656113030455064349983554633140319455240978314911831700500810391918529026639780752901725947055831114328324491719600532
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked14 : check (embed sector) history14 table14 = true := by decide +kernel
theorem bound14 : 18 < 9 + (targets.map (fun z => tableWeight table14 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes14 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history14 z = some (costs z)) :
    18 < 9 + (targets.map costs).sum :=
  excludes_completion (embed sector) history14 targets table14 9 costs checked14 hc bound14
def history15 : List Row := [liftMask (1 : BitVec 8),liftMask (2 : BitVec 8),liftMask (4 : BitVec 8),liftMask (8 : BitVec 8),liftMask (16 : BitVec 8),liftMask (17 : BitVec 8),liftMask (21 : BitVec 8),liftMask (32 : BitVec 8),liftMask (64 : BitVec 8),liftMask (67 : BitVec 8),liftMask (80 : BitVec 8),liftMask (82 : BitVec 8),liftMask (86 : BitVec 8),liftMask (128 : BitVec 8),liftMask (145 : BitVec 8)]
def table15 : Nat := 13407807929942597099574024301484585060778066508708288188483434444694553547749862690780205870755239796720896160794246753210841713066309637171102781945801108
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checked15 : check (embed sector) history15 table15 = true := by decide +kernel
theorem bound15 : 18 < 9 + (targets.map (fun z => tableWeight table15 (PackedRows.pack (embed sector) z))).sum := by decide +kernel
theorem excludes15 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history15 z = some (costs z)) :
    18 < 9 + (targets.map costs).sum :=
  excludes_completion (embed sector) history15 targets table15 9 costs checked15 hc bound15
end HGP13.Sector234Potentials
