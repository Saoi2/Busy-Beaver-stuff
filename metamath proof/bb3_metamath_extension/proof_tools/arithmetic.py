"""Proof-producing arithmetic helpers. No arithmetic oracle is trusted."""
import foundation as b
from functools import lru_cache
from itertools import count
from pathlib import Path
seq=count()
OUTPUT_PREFIX=""
# Extra object variables for capture-avoiding proof construction.
for name in ['e0','e1','e2','e3','i','j','n','h','q','ll','rr','bit','bb0','cc0','bb1','cc1','bb2','cc2','bb3','cc3','aa','dd']:
 b.lines.extend(['$v '+name+' $.','f-'+name+' $f var '+name+' $.'])
 b.metas[name]='var';b.floats[name]='f-'+name
b.lines.append('$d '+' '.join(s for s,c in b.metas.items() if c=='var')+' $.')
b.lines.extend('$d '+e+' '+s+' $.' for e in ['e0','e1','e2','e3'] for s,c in b.metas.items() if c in ('term','wff','ctx'))
E=b.V('e0')
Z,O=b.Z,b.O
A,M,Q,L=b.Add,b.Mul,b.Eq,b.Lt
N=b.NIL

def record(a,p,name=None):
 name=name or OUTPUT_PREFIX+'arith-'+str(next(seq))
 b.theorem(name,a,p)
 return b.apply(name)
def lift(p,g):
 assert p.conclusion.startswith('|- [] => ')
 # Recover formula from caller-provided metadata instead where convenient.
 a=proof_ast[p.conclusion]
 return b.apply('nd-empty-weaken',{'ga':g,'ph':a},[p])
proof_ast={}
def save(a,p,name=None):
 p=record(a,p,name);proof_ast[p.conclusion]=a;return p

def cong2(op,a,c,d,e,p,r,g=N):
 return b.apply('eq-'+('add' if op=='+' else 'mul')+'-cong',{'ga':g,'t':a,'u':c,'v':d,'w':e},[p,r])
def sym(a,c,p,g=N):return b.sym(g,a,c,p)
def trans(a,c,d,p,r,g=N):return b.trans(g,a,c,d,p,r)
def refl(a,g=N):return b.refl(g,a)
def ax(k,**kw):return b.ax(k,N,**kw)
def flatten(a,op):return flatten(a[1],op)+flatten(a[2],op) if a[0]==op else [a]
def fold(parts,op):
 if not parts:return Z if op=='+' else O
 if len(parts)==1:return parts[0]
 return (op,parts[0],fold(parts[1:],op))
def key(a):return b.tok(a)
@lru_cache(None)
def associate(a,op):
 if a[0]!=op:return a,refl(a)
 l,lp=associate(a[1],op);r,rp=associate(a[2],op)
 cur=(op,l,r);p=cong2(op,a[1],l,a[2],r,lp,rp)
 if l[0]==op:
  newer=(op,l[1],(op,l[2],r));assoc=ax('A1' if op=='+' else 'A4',t=l[1],u=l[2],v=r)
  p=trans(a,cur,newer,p,assoc)
  out,np=associate(newer,op);return out,trans(a,newer,out,p,np)
 return cur,p
@lru_cache(None)
def swap_at(a,op,index):
 parts=flatten(a,op);assert index+1<len(parts)
 if index:
  tail,p=swap_at(a[2],op,index-1);return (op,a[1],tail),cong2(op,a[1],a[1],a[2],tail,refl(a[1]),p)
 if len(parts)==2:
  out=(op,parts[1],parts[0]);return out,ax('A2' if op=='+' else 'A5',t=parts[0],u=parts[1])
 x,y=parts[:2];r=fold(parts[2:],op);left=(op,(op,x,y),r);mid=(op,(op,y,x),r);out=(op,y,(op,x,r))
 p=sym(left,a,ax('A1' if op=='+' else 'A4',t=x,u=y,v=r))
 p=trans(a,left,mid,p,cong2(op,(op,x,y),(op,y,x),r,r,ax('A2' if op=='+' else 'A5',t=x,u=y),refl(r)))
 return out,trans(a,mid,out,p,ax('A1' if op=='+' else 'A4',t=y,u=x,v=r))
@lru_cache(None)
def sort_assoc(a,op):
 cur,p=associate(a,op);parts=flatten(cur,op)
 for j in range(len(parts)):
  for i in range(len(parts)-1):
   if key(parts[i])>key(parts[i+1]):
    nxt,r=swap_at(cur,op,i);p=trans(a,cur,nxt,p,r);cur=nxt;parts[i],parts[i+1]=parts[i+1],parts[i]
 return cur,p
@lru_cache(None)
def normalize(a):
 if a[0] not in ('+','*'):return a,refl(a)
 op=a[0];l,lp=normalize(a[1]);r,rp=normalize(a[2]);cur=(op,l,r);p=cong2(op,a[1],l,a[2],r,lp,rp)
 if op=='*' and (l[0]=='+' or r[0]=='+'):
  if r[0]=='+':
   mid=A(M(l,r[1]),M(l,r[2]));dp=ax('A8',t=l,u=r[1],v=r[2])
  else:
   rev=M(r,l);mid=A(M(r,l[1]),M(r,l[2]));dp=trans(cur,rev,mid,ax('A5',t=l,u=r),ax('A8',t=r,u=l[1],v=l[2]))
  p=trans(a,cur,mid,p,dp);out,np=normalize(mid)
  return out,save(Q(a,out),trans(a,mid,out,p,np))
 # Identity / absorption, then sort associative operands.
 if op=='+' and (l==Z or r==Z):
  out=r if l==Z else l
  ep=ax('A3',t=l) if r==Z else trans(cur,A(r,Z),r,ax('A2',t=Z,u=r),ax('A3',t=r))
  return out,save(Q(a,out),trans(a,cur,out,p,ep))
 if op=='*' and (l in (Z,O) or r in (Z,O)):
  if r in (Z,O):out=Z if r==Z else l;ep=ax('A7' if r==Z else 'A6',t=l)
  else:
   out=Z if l==Z else r;rev=M(r,l)
   ep=trans(cur,rev,out,ax('A5',t=l,u=r),ax('A7' if l==Z else 'A6',t=r))
  return out,save(Q(a,out),trans(a,cur,out,p,ep))
 out,np=sort_assoc(cur,op)
 return out,save(Q(a,out),trans(a,cur,out,p,np))
def equal(a,c,name=None):
 aa,p=normalize(a);cc,r=normalize(c);assert aa==cc,(b.tok(a),b.tok(c),b.tok(aa),b.tok(cc))
 return save(Q(a,c),trans(a,aa,c,p,sym(c,aa,r)),name)
def replace(g,body,old,new,eq,p):
 # body is a formula with e0 as its replacement marker.
 ph,sp=b.subst(body,E,old,True);ps,sq=b.subst(body,E,new,True)
 return b.apply('eq-replace',{'ga':g,'x':E,'ph':body,'t':old,'u':new,'ps':ph,'ch':ps},[eq,sp,sq,p])
def intro(g,ph,ps,p):return b.apply('nd-imp-intro',{'ga':g,'ph':ph,'ps':ps},[p])
def all_intro(g,x,ph,p):return b.apply('nd-all-intro',{'ga':g,'x':x,'ph':ph},[p])
def contradiction(g,ph,ps,p,r):return b.apply('nd-explosion',{'ga':g,'ph':ph,'ps':ps},[p,r])
def not_intro(g,ph,ps,p,r):return b.apply('nd-not-intro',{'ga':g,'ph':ph,'ps':ps},[p,r])
def weaken_to(p,a,g,fromg=N):
 # Add assumptions from the outer stack recursively.
 if g==fromg:return p
 assert g[0]=='cons'
 pp=weaken_to(p,a,g[1],fromg)
 return b.weaken(g[1],pp,a,g[2])
def boundless_lt(g,a,c,w,eq):
 # eq proves c=(a+w)+1; O7 gives a<c.
 var=b.V('e1');body=Q(c,A(A(a,var),O))
 ep=b.exists_intro(g,var,body,w,eq)
 iff=b.ax('O7',g,t=a,u=c,x=var)
 imp=b.apply('nd-iff-right',{'ga':g,'ph':L(a,c),'ps':b.Ex(var,body)},[iff])
 return b.mp(g,b.Ex(var,body),L(a,c),imp,ep)
def num(n):return Z if n==0 else O if n==1 else A(num(n-1),O)

# Ordered additive cancellation, using only trichotomy, O5, and equality.
def addition_cancel():
 t,u,v=b.t,b.u,b.v;prem=Q(A(t,v),A(u,v));g=b.Cons(N,prem);ep=b.assume(N,prem)
 target=Q(t,u);tri=b.Or(L(t,u),b.Or(target,L(u,t)))
 tr=b.ax('O3',g,t=t,u=u)
 g1=b.Cons(g,L(t,u));lt=b.mp(g1,L(t,u),L(A(t,v),A(u,v)),b.ax('O5',g1,t=t,u=u,v=v),b.assume(g,L(t,u)))
 e=weaken_to(ep,prem,g1,g)
 bad=replace(g1,L(A(t,v),E),A(u,v),A(t,v),b.sym(g1,A(t,v),A(u,v),e),lt)
 no=b.ax('O1',g1,t=A(t,v));p1=contradiction(g1,L(A(t,v),A(t,v)),target,bad,no)
 g2=b.Cons(g,b.Or(target,L(u,t)))
 g21=b.Cons(g2,target);p21=b.assume(g2,target)
 g22=b.Cons(g2,L(u,t));lt2=b.mp(g22,L(u,t),L(A(u,v),A(t,v)),b.ax('O5',g22,t=u,u=t,v=v),b.assume(g2,L(u,t)))
 e=weaken_to(ep,prem,g22,g)
 bad2=replace(g22,L(E,A(t,v)),A(u,v),A(t,v),b.sym(g22,A(t,v),A(u,v),e),lt2)
 p22=contradiction(g22,L(A(t,v),A(t,v)),target,bad2,b.ax('O1',g22,t=A(t,v)))
 p2=b.apply('nd-or-elim',{'ga':g2,'ph':target,'ps':L(u,t),'ch':target},[b.assume(g,b.Or(target,L(u,t))),p21,p22])
 p=b.apply('nd-or-elim',{'ga':g,'ph':L(t,u),'ps':b.Or(target,L(u,t)),'ch':target},[tr,p1,p2])
 return save(b.Imp(prem,target),intro(N,prem,target,p),'add-cancel')
addition_cancel()

def projection(g,formula,p,path):
 for index in path:
  assert formula[0]=='/\\'
  rule='nd-and-left' if index==0 else 'nd-and-right'
  p=b.apply(rule,{'ga':g,'ph':formula[1],'ps':formula[2]},[p])
  formula=formula[index+1]
 return p
def rewrite_term(g,a,old,new,eq):
 if a==old:return new,eq
 if a[0] not in ('+','*'):return a,refl(a,g)
 ll,p=rewrite_term(g,a[1],old,new,eq);rr,r=rewrite_term(g,a[2],old,new,eq)
 return (a[0],ll,rr),cong2(a[0],a[1],ll,a[2],rr,p,r,g)
def constrained_equal(g,a,c,constraints):
 aa=a;cc=c;p=refl(a,g);r=refl(c,g)
 for old,new,eq in constraints:
  na,pa=rewrite_term(g,aa,old,new,eq);nc,pc=rewrite_term(g,cc,old,new,eq)
  p=trans(a,aa,na,p,pa,g);r=trans(c,cc,nc,r,pc,g);aa,cc=na,nc
 canonical=equal(aa,cc);cp=b.apply('nd-empty-weaken',{'ga':g,'ph':Q(aa,cc)},[canonical])
 return trans(a,aa,c,p,trans(aa,cc,c,cp,sym(c,cc,r,g),g),g)
def lt_witness(g,a,c,p):
 var=b.V('e1');body=Q(c,A(A(a,var),O))
 iff=b.ax('O7',g,t=a,u=c,x=var)
 imp=b.apply('nd-iff-left',{'ga':g,'ph':L(a,c),'ps':b.Ex(var,body)},[iff])
 return var,body,b.mp(g,L(a,c),b.Ex(var,body),imp,p)
def eliminate(g,var,body,fresh,target,p,branch):
 actual,sp=b.subst(body,var,fresh,True)
 return b.apply('nd-ex-elim',{'ga':g,'x':var,'y':fresh,'ph':body,'ps':actual,'ch':target},[p,sp,branch])
def div_unique():
 # t=m, u=a, v=b, w=r, r=s.
 m,a,c,r,s=b.t,b.u,b.v,b.w,b.rr
 left=A(M(m,a),r);right=A(M(m,c),s)
 prem=b.And(Q(left,right),b.And(L(r,m),L(s,m)))
 g=b.Cons(N,prem);pp=b.assume(N,prem)
 eq=projection(g,prem,pp,[0]);rbound=projection(g,prem,pp,[1,0]);sbound=projection(g,prem,pp,[1,1])
 target=Q(a,c)
 def bad_case(base,aa,cc,ar,cs,qlt,arbound,original_eq):
  # Prove a contradiction from aa<cc, ar<m and m*aa+ar=m*cc+cs.
  x,body,exist=lt_witness(base,aa,cc,qlt);z=b.V('e2')
  bz,_=b.subst(body,x,z,True);g1=b.Cons(base,bz);bzp=b.assume(base,bz)
  arbound=weaken_to(arbound,L(ar,m),g1,base)
  xx,body2,exist2=lt_witness(g1,ar,m,arbound);witness=b.V('e3')
  bw,_=b.subst(body2,xx,witness,True);g2=b.Cons(g1,bw);bwp=b.assume(g1,bw)
  cnew=A(A(aa,z),O);mnew=A(A(ar,witness),O)
  oldleft=A(M(m,aa),ar);oldright=A(M(m,cc),cs)
  gap=A(A(witness,M(m,z)),cs)
  identity=constrained_equal(g2,oldright,A(A(oldleft,gap),O),[(cc,cnew,weaken_to(bzp,bz,g2,g1)),(m,mnew,bwp)])
  lt=boundless_lt(g2,oldleft,oldright,gap,identity)
  eq2=weaken_to(original_eq,Q(oldleft,oldright),g2,base)
  bad=replace(g2,L(oldleft,E),oldright,oldleft,sym(oldleft,oldright,eq2,g2),lt)
  no=b.ax('O1',g2,t=oldleft)
  conclusion=contradiction(g2,L(oldleft,oldleft),target,bad,no)
  conclusion=eliminate(g1,xx,body2,witness,target,exist2,conclusion)
  return eliminate(base,x,body,z,target,exist,conclusion)
 g1=b.Cons(g,L(a,c))
 p1=bad_case(g1,a,c,r,s,b.assume(g,L(a,c)),weaken_to(rbound,L(r,m),g1,g),weaken_to(eq,Q(left,right),g1,g))
 other=b.Or(target,L(c,a));g2=b.Cons(g,other)
 g21=b.Cons(g2,target);p21=b.assume(g2,target)
 g22=b.Cons(g2,L(c,a));rev=sym(left,right,weaken_to(eq,Q(left,right),g22,g),g22)
 p22=bad_case(g22,c,a,s,r,b.assume(g2,L(c,a)),weaken_to(sbound,L(s,m),g22,g),rev)
 p2=b.apply('nd-or-elim',{'ga':g2,'ph':target,'ps':L(c,a),'ch':target},[b.assume(g,other),p21,p22])
 tri=b.ax('O3',g,t=a,u=c)
 qp=b.apply('nd-or-elim',{'ga':g,'ph':L(a,c),'ps':other,'ch':target},[tri,p1,p2])
 lc=A(r,M(m,c));rc=A(s,M(m,c))
 lproof=constrained_equal(g,left,lc,[(a,c,qp)])
 rproof=constrained_equal(g,right,rc,[])
 ce=trans(lc,left,rc,sym(left,lc,lproof,g),trans(left,right,rc,eq,rproof,g),g)
 cancel=b.apply('nd-empty-weaken',{'ga':g,'ph':b.Imp(Q(lc,rc),Q(r,s))},[b.apply('add-cancel',{'t':r,'u':s,'v':M(m,c)})])
 rp=b.mp(g,Q(lc,rc),Q(r,s),cancel,ce)
 result=b.And(target,Q(r,s));out=b.both(g,target,Q(r,s),qp,rp)
 return save(b.Imp(prem,result),intro(N,prem,result,out),'division-unique')
div_unique()

# Check all elementary proof construction before extending the machine proof.
def write(path=None):
 (Path(path) if path else b.ROOT/'bb2.mm').write_text('\n\n'.join(b.lines)+'\n')
if __name__=='__main__':
 for n in range(9):equal(A(num(n),O),num(n+1))
 equal(M(num(2),A(b.t,O)),A(A(b.t,b.t),num(2)))
 write()
