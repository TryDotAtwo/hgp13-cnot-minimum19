"""Deterministic vector proof diagrams. Requires reportlab, no image model.

Circuit and explicit matrix are derived from the supplied Lean/C++ sources.
Figures illustrate the argument; they are not proof certificates.
"""
from pathlib import Path
import hashlib, json, math, re
from reportlab.pdfgen import canvas
from reportlab.lib.colors import HexColor, white

ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'figures'; OUT.mkdir(exist_ok=True)
INK='#162B40'; BLUE='#23649B'; TEAL='#197969'; ORANGE='#A75813'
PALE='#EEF4FA'; GRAY='#5B6773'; LINE='#AFBCC8'

def start(name,w,h):
    c=canvas.Canvas(str(OUT/(name+'.pdf')),pagesize=(w,h),invariant=1)
    c.setTitle(name.replace('_',' ')); c.setAuthor('Ivan Litvak')
    c.setLineCap(1); return c

def text(c,x,y,s,size=13,color=INK,bold=False,align='center'):
    c.setFillColor(HexColor(color)); c.setFont('Helvetica-Bold' if bold else 'Helvetica',size)
    method={'center':c.drawCentredString,'left':c.drawString,'right':c.drawRightString}[align]
    method(x,y,s)

def box(c,x,y,w,h,lines,color=BLUE,fill=PALE,size=13):
    c.setStrokeColor(HexColor(color)); c.setFillColor(HexColor(fill)); c.setLineWidth(1)
    c.roundRect(x,y,w,h,6,fill=1,stroke=1)
    if isinstance(lines,str):lines=[lines]
    for i,line in enumerate(lines):
        text(c,x+w/2,y+h/2+(len(lines)-1)*8-i*16-4,line,size)

def arrow(c,x1,y1,x2,y2,color=GRAY,dashed=False):
    c.setStrokeColor(HexColor(color));c.setFillColor(HexColor(color));c.setLineWidth(1.15)
    c.setDash([4,3] if dashed else [])
    c.line(x1,y1,x2,y2);c.setDash([])
    a=math.atan2(y2-y1,x2-x1); r=6
    p=c.beginPath();p.moveTo(x2,y2)
    p.lineTo(x2-r*math.cos(a-.45),y2-r*math.sin(a-.45))
    p.lineTo(x2-r*math.cos(a+.45),y2-r*math.sin(a+.45));p.close()
    c.drawPath(p,fill=1,stroke=0)

cpp=(ROOT/'hgp13_verify.cpp').read_text(encoding='utf-8')
m=re.search(r'TARGET\s*=\s*\{([^}]+)\}',cpp)
target=[int(x) for x in re.findall(r'\d+',m[1])]
lean=(ROOT/'lean/HGP13.lean').read_text(encoding='utf-8')
lean_rows=re.search(r'def targetRows : List Row :=\s*\[([^]]+)\]',lean)[1]
assert [int(x) for x in re.findall(r'\d+',lean_rows)]==target
section=re.search(r'def witness : Program :=(.*?)(?=\n/--)',lean,re.S)[1]
gates=[tuple(map(int,p)) for p in re.findall(r'\((\d+),(\d+)\)',section)]
rows=[1<<i for i in range(13)]
for a,b in gates:
    assert a!=b and 0<=a<13 and 0<=b<13
    rows[b]^=rows[a]
assert len(gates)==19 and rows==target
matrix=[' & '.join(str((r>>j)&1) for j in range(13)) for r in target]
(ROOT/'matrix.tex').write_text('\\begin{pmatrix}\n'+' \\\\\n'.join(matrix)+'\n\\end{pmatrix}\n')

# The circuit has the original physical coordinate order, not a free permutation.
c=start('cnot_circuit',760,415)
text(c,380,395,'A 19-step witness in the original coordinate order',16,bold=True)
names=['a','b','c','d','e','f','y0','y1','t','y2','y3','y4','y5']
for i,label in enumerate(names):
    y=355-i*24
    color=BLUE if i<6 else ORANGE if i==8 else GRAY
    text(c,51,y-4,f'{i}: {label}',13,color,align='right')
    c.setStrokeColor(HexColor(LINE));c.setLineWidth(.65);c.line(63,y,737,y)
for k,(control,target_wire) in enumerate(gates):
    x=82+k*35;yc=355-control*24;yt=355-target_wire*24
    color=ORANGE if k>=17 else INK
    c.setStrokeColor(HexColor(color));c.setFillColor(HexColor(color));c.setLineWidth(1.3)
    c.line(x,yc,x,yt);c.circle(x,yc,3.1,fill=1,stroke=0)
    c.setFillColor(white);c.circle(x,yt,5.8,fill=1,stroke=1)
    c.line(x-5.8,yt,x+5.8,yt);c.line(x,yt-5.8,x,yt+5.8)
    text(c,x,375,str(k+1),12,color)
text(c,65,27,'Time runs left to right.  Solid dot: control.  Circled plus: target.',12,align='left')
text(c,65,9,'Orange gates restore b and a.  Every gate, including each restoration, costs one.',12,ORANGE,align='left')
c.save()

c=start('proof_map',640,415)
box(c,180,355,280,43,['Suppose a circuit has L <= 18'],size=15)
box(c,110,284,420,48,['Projection: seven required forms + at least three auxiliaries',
                       'Free XOR complexity = 10'])
arrow(c,320,355,320,332)
box(c,140,210,360,49,['Count copies and source restorations',
                      'L >= 16 + u,  L >= 16 + v;  hence u,v <= 2'])
arrow(c,320,284,320,259)
box(c,15,118,185,63,['u = v = 0','Analytic lower bound','L >= 20'],color=ORANGE,fill='#FFF5EA')
box(c,226,118,397,63,['All other cases: 363 covering sectors',
                      'Full core rows + exact passive-output cost',
                      'Necessary conditions only'])
arrow(c,222,210,107,181);arrow(c,410,210,424,181)
box(c,242,39,365,45,['Finite exclusion: no terminal cost <= 18'],color=TEAL,fill='#ECF7F3')
arrow(c,424,118,424,84)
text(c,107,72,'Contradiction',14,ORANGE,bold=True)
arrow(c,107,118,107,93)
text(c,320,9,'Therefore L >= 19.  The explicit witness supplies L <= 19.',14,bold=True)
c.save()

F=[73,82,3,6,27,54,100]; P=[1<<i for i in range(7)]
H={0}
for r in [73,82,100]:H|={x^r for x in list(H)}
outside=[x for x in P+F if x not in H]
assert len(H)==8 and len(outside)==9
assert all((a^b) not in H for i,a in enumerate(outside) for b in outside[i+1:])
c=start('quotient_argument',640,285)
text(c,320,267,'Why at least three auxiliary forms are necessary',16,bold=True)
labels=['a','b','c','t','d = a+t','e = b+t','f = c+t','a+b','b+c']
text(c,157,239,'Nine distinct nonzero cosets in V/H',13,bold=True)
for k,label in enumerate(labels):
    col=k%3;row=k//3
    box(c,10+col*100,177-row*53,92,39,label,size=12)
box(c,342,169,279,61,['H = span(r0, r1, r2)', 'dim H = 3; no initial basis form is in H'],color=TEAL,fill='#ECF7F3',size=12)
box(c,342,76,279,65,['New x in a previously occupied coset:',
                     'x + representative lies in H',
                     'at most one new independent difference'],size=12)
arrow(c,310,152,342,108)
text(c,320,40,'All computed H-values lie in the span W of same-coset differences.',13)
text(c,320,15,'The targets require dim W >= 3; each auxiliary increases it by at most 1.',13,bold=True)
c.save()

c=start('operation_budget',640,206)
text(c,320,187,'Every operation creates a new projection or repeats an old one',15,bold=True)
groups=[(12,160,'7 target forms',BLUE),(172,100,'a auxiliaries',BLUE),
        (280,140,'6 first copies',TEAL),(428,96,'u returns',TEAL),(532,96,'e others',GRAY)]
for x,w,label,color in groups:box(c,x,92,w,49,label,color=color,size=13)
text(c,142,155,'FIRST APPEARANCES',11,BLUE,bold=True)
text(c,454,155,'REPEATED RESULTS',11,TEAL,bold=True)
text(c,320,59,'L = 7 + a + 6 + u + e = 13 + a + u + e,    a >= 3, e >= 0',15,bold=True)
text(c,320,31,'If L <= 18 and u = 2, then L = 18, a = 3 and e = 0.',14)
text(c,320,10,'No extra repeat is available.  Transposition gives the separate bound in v.',12)
c.save()

c=start('sector_cover',640,246)
text(c,320,225,'Coverage of all activity pairs allowed by L <= 18',15,bold=True)
text(c,181,200,'v: private outputs used as controls',12)
cells={(0,0):('analytic','>=20',ORANGE),(1,0):('original','1 / 0',TEAL),
       (0,1):('transpose','1 / 0',TEAL),(1,1):('original','1 / 1',BLUE)}
for u in range(3):
    text(c,27,151-u*56,f'u={u}',12)
    for v in range(3):
        if u==2:entry=('original','2 / 2',BLUE)
        elif v==2:entry=('transpose','2 / 1',TEAL)
        else:entry=cells[u,v]
        box(c,53+v*89,131-u*56,81,46,[entry[0],entry[1]],color=entry[2],size=11)
for v in range(3):text(c,93+v*89,182,f'v={v}',12)
text(c,476,184,'Sector family sizes',14,bold=True)
for y,s in [(154,'|A|=2, |R|=2: 15 x 15 = 225'),
            (124,'|A|=2, |R|=1: 15 x 6 = 90'),
            (94,'|A|=1, |R|=1: 6 x 6 = 36'),
            (64,'|A|=1, |R|=0: 2 x 6 = 12')]:text(c,476,y,s,12)
text(c,476,28,'225 + 90 + 36 + 12 = 363',14,bold=True)
text(c,177,3,'Cell labels give the searched |A| / |R|.',11)
c.save()

c=start('clean_carrier',640,237)
text(c,320,217,'Zero slack: repeating a nonbasis projection only makes a first copy',15,bold=True)
box(c,17,136,161,47,['Control row','(p, mu)'],size=14)
box(c,243,136,157,47,['Uninitialized output j','(0, e_j)'],size=13)
box(c,467,136,156,47,['After the copy','(p, mu + e_j)'],size=14)
text(c,210,152,'+',24);arrow(c,400,159,467,159)
text(c,320,112,'The bit e_j is fresh: it occurs on no other row before initialization.',13)
box(c,24,32,281,55,['A dirty p cannot become clean',
                    'by copying the same projection.'],color=ORANGE,fill='#FFF5EA')
box(c,335,32,281,55,['A lost clean nonbasis p',
                     'cannot be recreated when e = 0.'],color=TEAL,fill='#ECF7F3')
text(c,320,8,'Private coefficients are retained; the argument does not prepare any input as zero.',12)
c.save()

c=start('passive_elimination',640,296)
text(c,320,276,'Removing passive updates preserves the entire core history',15,bold=True)
for y,label in [(222,'core row 1'),(184,'core row 2'),(105,'passive j')]:
    text(c,92,y-4,label,12,align='right')
    c.setStrokeColor(HexColor(LINE));c.setLineWidth(1);c.line(105,y,400,y)
for x,y,label in [(154,222,'v1'),(250,184,'v2'),(351,222,'v3')]:
    c.setFillColor(HexColor(BLUE));c.circle(x,y,3.3,fill=1,stroke=0)
    arrow(c,x,y-6,x,111,TEAL,dashed=True)
    text(c,x+9,y+6,label,12,BLUE,align='left')
    c.setStrokeColor(HexColor(TEAL));c.circle(x,105,5.5,fill=0,stroke=1)
text(c,244,66,'v1 + v2 + v3 = required added row f_j',12)
box(c,425,155,199,75,['D = all full control values',
                      'seen anywhere in the history',
                      '(initial basis included)'],size=12)
box(c,425,53,199,67,['delta_D(f_j)',
                     '= smallest subset size',
                     'whose XOR is f_j'],color=TEAL,fill='#ECF7F3',size=12)
text(c,320,24,'For a core history ending at its target: total cost = K + sum_j delta_D(f_j).',13,bold=True)
text(c,320,5,'D is used for passive insertions only; core gates use current control values.',12)
c.save()

c=start('remaining_bound',640,217)
text(c,320,196,'The remaining-cost bound counts unavailable intermediate increments',15,bold=True)
box(c,14,111,175,54,['r rows differ','L = r + k'],size=14)
box(c,229,111,182,54,['At most k of those rows','can be updated twice'],size=13)
box(c,450,111,176,54,['At most k operations','create nonendpoint rows'],size=13)
arrow(c,189,138,229,138);arrow(c,411,138,450,138)
text(c,320,79,'Of b distinct increments absent from both endpoints, at least b-k remain.',13)
text(c,320,47,'Each remaining increment must occur as a control at a single target update.',13)
text(c,320,15,'Thus b - k <= k, so L >= r + ceil(b/2).',16,bold=True)
c.save()

manifest={'matrix_rows':target,'gates':gates,'circuit_matches_matrix':True,
          'lean_cpp_targets_agree':True,
          'quotient_cosets_verified':True,'figures':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(OUT.glob('*.pdf'))}}
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Generated {len(manifest["figures"])} vector figures and the explicit matrix; circuit checked.')
