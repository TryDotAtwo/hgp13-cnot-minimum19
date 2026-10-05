import PackedTerminalPotential
namespace HGP13.SectorTerminal359
set_option maxRecDepth 20000
open PackedTerminalPotential
/- Only the listed terminal histories are certified. Search coverage remains OPEN. -/
def targets : List Row := [21,62,296,17,50,288]
def history0 : List Row := [1,2,4,8,16,32,256,258,259,260]
def table0 : Nat := 115792089237316193308187699690842915760819297749680269729374717962791280028052
set_option maxHeartbeats 2000000 in
theorem checked0 : check history0 table0 = true := by decide
theorem bound0 : 18 < 4 + (targets.map (fun z => tableWeight table0 (Projection.project z))).sum := by decide
theorem excludes0 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history0 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history0 targets table0 4 costs checked0 hc bound0
def history1 : List Row := [1,2,4,8,16,32,256,257,259,260]
def table1 : Nat := 115792089237316193383512920533021372187845376617145444705378146601750175000980
set_option maxHeartbeats 2000000 in
theorem checked1 : check history1 table1 = true := by decide
theorem bound1 : 18 < 4 + (targets.map (fun z => tableWeight table1 (Projection.project z))).sum := by decide
theorem excludes1 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history1 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history1 targets table1 4 costs checked1 hc bound1
def history2 : List Row := [1,2,4,5,8,16,32,256,258,259]
def table2 : Nat := 115792089237316194915125744323983319537375646922270669198558396324704344974740
set_option maxHeartbeats 2000000 in
theorem checked2 : check history2 table2 = true := by decide
theorem bound2 : 18 < 4 + (targets.map (fun z => tableWeight table2 (Projection.project z))).sum := by decide
theorem excludes2 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history2 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history2 targets table2 4 costs checked2 hc bound2
def history3 : List Row := [1,2,4,8,16,20,32,256,258,259]
def table3 : Nat := 115792089237316194915125714018285368192221878757420554995447022180663443450260
set_option maxHeartbeats 2000000 in
theorem checked3 : check history3 table3 = true := by decide
theorem bound3 : 18 < 4 + (targets.map (fun z => tableWeight table3 (Projection.project z))).sum := by decide
theorem excludes3 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history3 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history3 targets table3 4 costs checked3 hc bound3
def history4 : List Row := [1,2,4,8,16,20,32,256,257,259]
def table4 : Nat := 115792089237316194990450939350196855545129153527728495835358681233039056038292
set_option maxHeartbeats 2000000 in
theorem checked4 : check history4 table4 = true := by decide
theorem bound4 : 18 < 4 + (targets.map (fun z => tableWeight table4 (Projection.project z))).sum := by decide
theorem excludes4 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history4 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history4 targets table4 4 costs checked4 hc bound4
def history5 : List Row := [1,2,4,8,12,16,32,256,258,259]
def table5 : Nat := 115792089237316194915125744323520891633388059647848461664831930443860563061140
set_option maxHeartbeats 2000000 in
theorem checked5 : check history5 table5 = true := by decide
theorem bound5 : 18 < 4 + (targets.map (fun z => tableWeight table5 (Projection.project z))).sum := by decide
theorem excludes5 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history5 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history5 targets table5 4 costs checked5 hc bound5
def history6 : List Row := [1,2,4,6,8,16,32,256,258,259]
def table6 : Nat := 115792089237316194915125744323983319537375646922270669141889998517074261547412
set_option maxHeartbeats 2000000 in
theorem checked6 : check history6 table6 = true := by decide
theorem bound6 : 18 < 4 + (targets.map (fun z => tableWeight table6 (Projection.project z))).sum := by decide
theorem excludes6 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history6 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history6 targets table6 4 costs checked6 hc bound6
def history7 : List Row := [1,2,4,8,16,32,256,258,259,263]
def table7 : Nat := 115792089237316092071090887802997477837769299876485101980766627202036436412820
set_option maxHeartbeats 2000000 in
theorem checked7 : check history7 table7 = true := by decide
theorem bound7 : 18 < 4 + (targets.map (fun z => tableWeight table7 (Projection.project z))).sum := by decide
theorem excludes7 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history7 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history7 targets table7 4 costs checked7 hc bound7
def history8 : List Row := [1,2,4,8,16,32,36,256,258,259]
def table8 : Nat := 115792089237316064753144159345771000986895310994858132317669775955213503031700
set_option maxHeartbeats 2000000 in
theorem checked8 : check history8 table8 = true := by decide
theorem bound8 : 18 < 4 + (targets.map (fun z => tableWeight table8 (Projection.project z))).sum := by decide
theorem excludes8 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history8 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history8 targets table8 4 costs checked8 hc bound8
def history9 : List Row := [1,2,4,8,16,32,256,257,259,261]
def table9 : Nat := 115792089237316188562698786633600162251972904007538192587141105748903490873748
set_option maxHeartbeats 2000000 in
theorem checked9 : check history9 table9 = true := by decide
theorem bound9 : 18 < 4 + (targets.map (fun z => tableWeight table9 (Projection.project z))).sum := by decide
theorem excludes9 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history9 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history9 targets table9 4 costs checked9 hc bound9
def history10 : List Row := [1,2,4,8,16,32,36,256,257,259]
def table10 : Nat := 115792089237316084111725911295832764962813929137397497319595924018078367213972
set_option maxHeartbeats 2000000 in
theorem checked10 : check history10 table10 = true := by decide
theorem bound10 : 18 < 4 + (targets.map (fun z => tableWeight table10 (Projection.project z))).sum := by decide
theorem excludes10 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history10 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history10 targets table10 4 costs checked10 hc bound10
def history11 : List Row := [1,2,4,6,8,16,32,256,257,259]
def table11 : Nat := 115792089237316194990450965166161775964401725789735844117893427156033156520340
set_option maxHeartbeats 2000000 in
theorem checked11 : check history11 table11 = true := by decide
theorem bound11 : 18 < 4 + (targets.map (fun z => tableWeight table11 (Projection.project z))).sum := by decide
theorem excludes11 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history11 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history11 targets table11 4 costs checked11 hc bound11
def history12 : List Row := [1,2,4,8,16,32,256,258,259,262]
def table12 : Nat := 115792089237316169204117030193736859460923203887865263994773151506075537238420
set_option maxHeartbeats 2000000 in
theorem checked12 : check history12 table12 = true := by decide
theorem bound12 : 18 < 4 + (targets.map (fun z => tableWeight table12 (Projection.project z))).sum := by decide
theorem excludes12 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history12 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history12 targets table12 4 costs checked12 hc bound12
def history13 : List Row := [1,2,4,8,12,16,32,256,257,259]
def table13 : Nat := 115792089237316194990450965165767856995011455770727394126855728879757775464852
set_option maxHeartbeats 2000000 in
theorem checked13 : check history13 table13 = true := by decide
theorem bound13 : 18 < 4 + (targets.map (fun z => tableWeight table13 (Projection.project z))).sum := by decide
theorem excludes13 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history13 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history13 targets table13 4 costs checked13 hc bound13
def history14 : List Row := [1,2,4,8,16,32,256,257,259,263]
def table14 : Nat := 115792089237316092146416108645175934264795378743950276956770055840995331385748
set_option maxHeartbeats 2000000 in
theorem checked14 : check history14 table14 = true := by decide
theorem bound14 : 18 < 4 + (targets.map (fun z => tableWeight table14 (Projection.project z))).sum := by decide
theorem excludes14 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history14 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history14 targets table14 4 costs checked14 hc bound14
def history15 : List Row := [1,2,4,5,8,16,32,256,257,259]
def table15 : Nat := 115792089237316194990450965166161775964401725789735844174561824963663239947668
set_option maxHeartbeats 2000000 in
theorem checked15 : check history15 table15 = true := by decide
theorem bound15 : 18 < 4 + (targets.map (fun z => tableWeight table15 (Projection.project z))).sum := by decide
theorem excludes15 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history15 z = some (costs z)) :
    18 < 4 + (targets.map costs).sum :=
  excludes_completion history15 targets table15 4 costs checked15 hc bound15
def history16 : List Row := [1,2,4,8,16,32,256,257,259,288,292]
def table16 : Nat := 115792082308504142405580947249170808315799456103100948282632179557030297201044
set_option maxHeartbeats 2000000 in
theorem checked16 : check history16 table16 = true := by decide
theorem bound16 : 18 < 6 + (targets.map (fun z => tableWeight table16 (Projection.project z))).sum := by decide
theorem excludes16 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history16 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history16 targets table16 6 costs checked16 hc bound16
def history17 : List Row := [1,2,4,8,16,32,256,258,259,288,292]
def table17 : Nat := 115792082308504142405580947231632520009455419133004810483701824426812128225684
set_option maxHeartbeats 2000000 in
theorem checked17 : check history17 table17 = true := by decide
theorem bound17 : 18 < 6 + (targets.map (fun z => tableWeight table17 (Projection.project z))).sum := by decide
theorem excludes17 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history17 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history17 targets table17 6 costs checked17 hc bound17
def history18 : List Row := [1,2,4,8,16,32,256,259,288,290,291,292]
def table18 : Nat := 115792080151675395596180368154500502280255470501041910985870456859016341072276
set_option maxHeartbeats 2000000 in
theorem checked18 : check history18 table18 = true := by decide
theorem bound18 : 18 < 6 + (targets.map (fun z => tableWeight table18 (Projection.project z))).sum := by decide
theorem excludes18 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history18 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history18 targets table18 6 costs checked18 hc bound18
def history19 : List Row := [1,2,4,8,16,32,256,259,288,289,291,292]
def table19 : Nat := 115792080475199692190985230133271317398068183714694589257182492705418124044692
set_option maxHeartbeats 2000000 in
theorem checked19 : check history19 table19 = true := by decide
theorem bound19 : 18 < 6 + (targets.map (fun z => tableWeight table19 (Projection.project z))).sum := by decide
theorem excludes19 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history19 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history19 targets table19 6 costs checked19 hc bound19
def history20 : List Row := [1,2,4,8,12,16,32,256,258,259,288]
def table20 : Nat := 115792089210250522941843664104721740415248079747065241859029037830706385512852
set_option maxHeartbeats 2000000 in
theorem checked20 : check history20 table20 = true := by decide
theorem bound20 : 18 < 6 + (targets.map (fun z => tableWeight table20 (Projection.project z))).sum := by decide
theorem excludes20 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history20 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history20 targets table20 6 costs checked20 hc bound20
def history21 : List Row := [1,2,4,8,16,32,256,258,259,274,275,278]
def table21 : Nat := 115791976652578912893653944043587523763038459003499024618680570501665015851412
set_option maxHeartbeats 2000000 in
theorem checked21 : check history21 table21 = true := by decide
theorem bound21 : 18 < 6 + (targets.map (fun z => tableWeight table21 (Projection.project z))).sum := by decide
theorem excludes21 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history21 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history21 targets table21 6 costs checked21 hc bound21
def history22 : List Row := [1,2,4,8,16,32,256,258,259,274,278]
def table22 : Nat := 115791978378015499591301020983822064226229653942235437522718929585663097039252
set_option maxHeartbeats 2000000 in
theorem checked22 : check history22 table22 = true := by decide
theorem bound22 : 18 < 6 + (targets.map (fun z => tableWeight table22 (Projection.project z))).sum := by decide
theorem excludes22 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history22 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history22 targets table22 6 costs checked22 hc bound22
def history23 : List Row := [1,2,4,8,12,16,32,256,259,288,289,291]
def table23 : Nat := 115792087369784830466033881275032353605856066998807474282947295375662066035092
set_option maxHeartbeats 2000000 in
theorem checked23 : check history23 table23 = true := by decide
theorem bound23 : 18 < 6 + (targets.map (fun z => tableWeight table23 (Projection.project z))).sum := by decide
theorem excludes23 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history23 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history23 targets table23 6 costs checked23 hc bound23
def history24 : List Row := [1,2,4,8,12,16,32,256,258,259,288,290]
def table24 : Nat := 115792088777199771771064891668682889810498924419824375615622970397416334420372
set_option maxHeartbeats 2000000 in
theorem checked24 : check history24 table24 = true := by decide
theorem bound24 : 18 < 6 + (targets.map (fun z => tableWeight table24 (Projection.project z))).sum := by decide
theorem excludes24 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history24 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history24 targets table24 6 costs checked24 hc bound24
def history25 : List Row := [1,2,4,8,12,16,32,256,257,259,288]
def table25 : Nat := 115792089210250522941843664122328536610842002791452177327824570933035183761812
set_option maxHeartbeats 2000000 in
theorem checked25 : check history25 table25 = true := by decide
theorem bound25 : 18 < 6 + (targets.map (fun z => tableWeight table25 (Projection.project z))).sum := by decide
theorem excludes25 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history25 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history25 targets table25 6 costs checked25 hc bound25
def history26 : List Row := [1,2,4,8,16,32,256,257,259,288,289,292]
def table26 : Nat := 115792082200662710207312659922913869943195218365216722192194834274896369543572
set_option maxHeartbeats 2000000 in
theorem checked26 : check history26 table26 = true := by decide
theorem bound26 : 18 < 6 + (targets.map (fun z => tableWeight table26 (Projection.project z))).sum := by decide
theorem excludes26 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history26 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history26 targets table26 6 costs checked26 hc bound26
def history27 : List Row := [1,2,4,8,12,16,32,256,258,259,274,275]
def table27 : Nat := 115792087080520461541105273925827347416139519886413860582992035978694122662292
set_option maxHeartbeats 2000000 in
theorem checked27 : check history27 table27 = true := by decide
theorem bound27 : 18 < 6 + (targets.map (fun z => tableWeight table27 (Projection.project z))).sum := by decide
theorem excludes27 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history27 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history27 targets table27 6 costs checked27 hc bound27
def history28 : List Row := [1,2,4,8,12,16,32,256,259,288,290,291]
def table28 : Nat := 115792087044996767087949801948003215652294200503376824600392744800694527715732
set_option maxHeartbeats 2000000 in
theorem checked28 : check history28 table28 = true := by decide
theorem bound28 : 18 < 6 + (targets.map (fun z => tableWeight table28 (Projection.project z))).sum := by decide
theorem excludes28 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history28 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history28 targets table28 6 costs checked28 hc bound28
def history29 : List Row := [1,2,4,8,12,16,32,256,258,259,274]
def table29 : Nat := 115792088805957048240321650245151384099803074030124489314636977966606996597140
set_option maxHeartbeats 2000000 in
theorem checked29 : check history29 table29 = true := by decide
theorem bound29 : 18 < 6 + (targets.map (fun z => tableWeight table29 (Projection.project z))).sum := by decide
theorem excludes29 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history29 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history29 targets table29 6 costs checked29 hc bound29
def history30 : List Row := [1,2,4,8,16,32,256,259,272,274,275,278]
def table30 : Nat := 115791976625618966326936836232674951959374603146996941113643782033827275860372
set_option maxHeartbeats 2000000 in
theorem checked30 : check history30 table30 = true := by decide
theorem bound30 : 18 < 6 + (targets.map (fun z => tableWeight table30 (Projection.project z))).sum := by decide
theorem excludes30 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history30 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history30 targets table30 6 costs checked30 hc bound30
def history31 : List Row := [1,2,4,8,16,32,256,258,259,272,274,278]
def table31 : Nat := 115791978351055552924150285400876236834501861280890672042272965834809809693076
set_option maxHeartbeats 2000000 in
theorem checked31 : check history31 table31 = true := by decide
theorem bound31 : 18 < 6 + (targets.map (fun z => tableWeight table31 (Projection.project z))).sum := by decide
theorem excludes31 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history31 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history31 targets table31 6 costs checked31 hc bound31
def history32 : List Row := [1,2,4,8,16,32,256,258,259,288,290,292]
def table32 : Nat := 115792081877138413612507797926604766519038468181467906121952443298276417595796
set_option maxHeartbeats 2000000 in
theorem checked32 : check history32 table32 = true := by decide
theorem bound32 : 18 < 6 + (targets.map (fun z => tableWeight table32 (Projection.project z))).sum := by decide
theorem excludes32 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history32 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history32 targets table32 6 costs checked32 hc bound32
def history33 : List Row := [1,2,4,8,12,16,32,256,259,272,274,275]
def table33 : Nat := 115792087053560514974363645812207847480160539757885731603676054382233803942292
set_option maxHeartbeats 2000000 in
theorem checked33 : check history33 table33 = true := by decide
theorem bound33 : 18 < 6 + (targets.map (fun z => tableWeight table33 (Projection.project z))).sum := by decide
theorem excludes33 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history33 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history33 targets table33 6 costs checked33 hc bound33
def history34 : List Row := [1,2,4,8,12,16,32,256,258,259,272,274]
def table34 : Nat := 115792088778997101573146394359407283329630400756202001711884661357880040614292
set_option maxHeartbeats 2000000 in
theorem checked34 : check history34 table34 = true := by decide
theorem bound34 : 18 < 6 + (targets.map (fun z => tableWeight table34 (Projection.project z))).sum := by decide
theorem excludes34 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history34 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history34 targets table34 6 costs checked34 hc bound34
def history35 : List Row := [1,2,4,8,12,16,32,256,257,259,288,289]
def table35 : Nat := 115792089101987835149148971013318823959654713959641960766973054074712670988692
set_option maxHeartbeats 2000000 in
theorem checked35 : check history35 table35 = true := by decide
theorem bound35 : 18 < 6 + (targets.map (fun z => tableWeight table35 (Projection.project z))).sum := by decide
theorem excludes35 (costs : Row → Nat)
    (hc : ∀ z ∈ targets, PassiveCost.cost history35 z = some (costs z)) :
    18 < 6 + (targets.map costs).sum :=
  excludes_completion history35 targets table35 6 costs checked35 hc bound35
end HGP13.SectorTerminal359
