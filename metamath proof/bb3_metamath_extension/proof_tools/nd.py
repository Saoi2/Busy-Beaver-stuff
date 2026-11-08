"""DAG proof construction; every saved node is a Metamath $p proof."""
import arithmetic as a
b=a.b
from itertools import count
import textwrap
ids=count()
OUTPUT_PREFIX=""
# Make all quantified proof variables fresh for the schematic arithmetic parameters.
PARAMS=['mn','mh','d0','d1','d2','d3','d4','d5','B0','C0','B1','C1','B2','C2','B3','C3']
VARS=['ti','tq','tl','tb','tr','iq','il','ib','ir','si','sq','sl','sb','sr','nq','nl','nb','nr','fq','fl','fb','fr','iv','pq','pl','pb','pr','oq','ol','ob','orr','cq','cl','cb','cr','vq','vl','vb','vr','bu','iu','ju','evl','evr','pv','pd','clu','cru','nlq','nrq','code0','code1','code2','code3','hn','hh','hB0','hC0','hB1','hC1','hB2','hC2','hB3','hC3']
for name,typ in [(n,'term') for n in PARAMS]+[(n,'var') for n in VARS]:
 b.lines.extend(['$v '+name+' $.','f-'+name+' $f '+typ+' '+name+' $.'])
 b.metas[name]=typ;b.floats[name]='f-'+name
b.lines.append('$d '+' '.join(s for s,c in b.metas.items() if c=='var')+' $.')
b.lines.extend('$d '+e+' '+s+' $.' for e,c in b.metas.items() if c=='var' for s,cc in b.metas.items() if cc in ('term','wff','ctx'))
raw_apply=b.apply;raw_syntax=b.syntax
cache={};scache={}
def stored(conclusion,p,prefix):
 name=OUTPUT_PREFIX+prefix+str(next(ids));used=set(conclusion.split())&set(b.metas)
 b.lines.append(name+' $p '+conclusion+' $=\n  '+'\n  '.join(textwrap.wrap(' '.join(p.labels),width=100,break_long_words=False,break_on_hyphens=False))+' $.')
 b.rules[name]=(conclusion,[],[s for s in b.metas if s in used],[])
 return raw_apply(name)
def syntax(ast,typ=None):
 if len(b.tok(ast))<40:return raw_syntax(ast,typ)
 key=(ast,typ)
 if key in scache:return scache[key]
 p=raw_syntax(ast,typ);p=stored(p.conclusion,p,'syn-');scache[key]=p;return p
b.syntax=syntax

def apply(name,m={},hs=()):
 p=raw_apply(name,m,hs)
 if p.conclusion.startswith('|- ') and len(p.labels)>50:
  if p.conclusion in cache:return cache[p.conclusion]
  p=stored(p.conclusion,p,'dag-');cache[p.conclusion]=p
 return p
b.apply=apply

def classify(ast):
 op=ast[0]
 if op=='not':return b.apply('bnd-not',{'ph':ast[1]},[classify(ast[1])])
 if op=='A.':
  guard,body=ast[2][1:];assert ast[2][0]=='->' and guard[0]=='<' and guard[1]==ast[1]
  return b.apply('bnd-all',{'x':ast[1],'t':guard[2],'ph':body},[classify(body)])
 if op=='E.':
  guard,body=ast[2][1:];assert ast[2][0]=='/\\' and guard[0]=='<' and guard[1]==ast[1]
  return b.apply('bnd-ex',{'x':ast[1],'t':guard[2],'ph':body},[classify(body)])
 if op in ('/\\','\\/','->','<->'):
  return b.apply('bnd-'+{'/\\':'and','\\/':'or','->':'imp','<->':'iff'}[op],{'ph':ast[1],'ps':ast[2]},[classify(ast[1]),classify(ast[2])])
 return b.classification(ast)

class Ctx:
 def __init__(self,parent=None,assumption=None):
  self.parent=parent;self.assumption=assumption;self.g=b.NIL if parent is None else b.Cons(parent.g,assumption);self.facts={}
  if parent:self.facts[assumption]=b.assume(parent.g,assumption)
 def push(self,ph):return Ctx(self,ph)
 def put(self,ph,p):
  assert p.conclusion==b.J(self.g,ph),(p.conclusion,b.J(self.g,ph))
  self.facts[ph]=p;return p
 def get(self,ph):
  if ph in self.facts:return self.facts[ph]
  if self.parent:
   p=b.weaken(self.parent.g,self.parent.get(ph),ph,self.assumption);self.facts[ph]=p;return p
  raise KeyError(b.tok(ph))
 def theorem(self,ph,p):return self.put(ph,b.apply('nd-empty-weaken',{'ga':self.g,'ph':ph},[p]))
 def mp(self,ante,cons,p=None,q=None):
  return self.put(cons,b.mp(self.g,ante,cons,p or self.get(b.Imp(ante,cons)),q or self.get(ante)))
 def both(self,ph,ps,p=None,q=None):return self.put(b.And(ph,ps),b.both(self.g,ph,ps,p or self.get(ph),q or self.get(ps)))
 def left(self,ph,ps,p=None):return self.put(ph,b.apply('nd-and-left',{'ga':self.g,'ph':ph,'ps':ps},[p or self.get(b.And(ph,ps))]))
 def right(self,ph,ps,p=None):return self.put(ps,b.apply('nd-and-right',{'ga':self.g,'ph':ph,'ps':ps},[p or self.get(b.And(ph,ps))]))
 def intro(self,ph,ps,child):return self.put(b.Imp(ph,ps),a.intro(self.g,ph,ps,child.get(ps)))
 def all_intro(self,x,ph,p=None):return self.put(b.All(x,ph),a.all_intro(self.g,x,ph,p or self.get(ph)))
 def all_elim(self,x,body,value,p=None):
  out,sp=b.subst(body,x,value,True)
  return out,self.put(out,b.apply('nd-all-elim',{'ga':self.g,'x':x,'ph':body,'t':value,'ps':out},[p or self.get(b.All(x,body)),sp]))
 def ex_intro(self,x,body,value,p=None):
  out,_=b.subst(body,x,value,True)
  return self.put(b.Ex(x,body),b.exists_intro(self.g,x,body,value,p or self.get(out)))
 def ex_elim(self,x,body,fresh,goal,child,p=None):
  return self.put(goal,a.eliminate(self.g,x,body,fresh,goal,p or self.get(b.Ex(x,body)),child.get(goal)))
 def explode(self,ph,goal,p=None,q=None):return self.put(goal,a.contradiction(self.g,ph,goal,p or self.get(ph),q or self.get(b.Not(ph))))

def AND(parts):
 if not parts:return b.Eq(b.Z,b.Z)
 if len(parts)==1:return parts[0]
 return b.And(parts[0],AND(parts[1:]))
def OR(parts):
 if len(parts)==1:return parts[0]
 return b.Or(parts[0],OR(parts[1:]))
def conj(ctx,parts):
 if not parts:return ctx.put(b.Eq(b.Z,b.Z),b.refl(ctx.g,b.Z))
 if len(parts)==1:return ctx.get(parts[0])
 conj(ctx,parts[1:]);return ctx.both(parts[0],AND(parts[1:]))
def unpack(ctx,parts,p=None):
 if len(parts)==1:
  if p is not None:ctx.put(parts[0],p)
  return
 ctx.left(parts[0],AND(parts[1:]),p);q=ctx.right(parts[0],AND(parts[1:]),p);unpack(ctx,parts[1:],q)
def disj(ctx,parts,index,p=None):
 if len(parts)==1:
  if p is not None:ctx.put(parts[0],p)
  return ctx.get(parts[0])
 if index==0:return ctx.put(OR(parts),b.apply('nd-or-left',{'ga':ctx.g,'ph':parts[0],'ps':OR(parts[1:])},[p or ctx.get(parts[0])]))
 q=disj(ctx,parts[1:],index-1,p)
 return ctx.put(OR(parts),b.apply('nd-or-right',{'ga':ctx.g,'ph':parts[0],'ps':OR(parts[1:])},[q]))
def cases(ctx,parts,goal,fn,offset=0,p=None):
 if len(parts)==1:
  if p:ctx.put(parts[0],p)
  return ctx.put(goal,fn(ctx,offset))
 left=ctx.push(parts[0]);lp=fn(left,offset);left.put(goal,lp)
 right=ctx.push(OR(parts[1:]));rp=cases(right,parts[1:],goal,fn,offset+1)
 return ctx.put(goal,b.apply('nd-or-elim',{'ga':ctx.g,'ph':parts[0],'ps':OR(parts[1:]),'ch':goal},[p or ctx.get(OR(parts)),lp,rp]))

def BALL(v,bound,body):return b.All(v,b.Imp(b.Lt(v,bound),body))
def BEX(v,bound,body):return b.Ex(v,b.And(b.Lt(v,bound),body))
def balls(vs,bound,body):
 for v in reversed(vs):body=BALL(v,bound,body)
 return body
def bexs(vs,bound,body):
 for v in reversed(vs):body=BEX(v,bound,body)
 return body
def inst_balls(ctx,vs,bound,body,values,p=None):
 current=balls(vs,bound,body);p=p or ctx.get(current)
 for var,val in zip(vs,values):
  out,p=ctx.all_elim(var,current[2],val,p)
  assert out[0]=='->'
  p=ctx.mp(out[1],out[2],p);current=out[2]
 return current,p
