import re
from pathlib import Path
p=Path(__file__).parent
s=(p/'Pilot284.lean').read_text(encoding='utf-8')
head=s.split('def s7_0 : State')[0]
m=re.search(r'def (s\d+_\d+) : State := ([^\n]+)\ntheorem \1_edges : next (\d+) \1 = \[s',s)
assert m
name,value,depth=m.groups()
(p/'OmittedTransition.lean').write_text(head+f'\ndef {name} : State := {value}\nexample : next {depth} {name} = [] := by decide\nend HGP13.SectorPilot284\n',encoding='utf-8')
print('Negative fixture removes every successor of',name,'at depth',depth)
