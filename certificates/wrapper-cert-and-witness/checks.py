import itertools, math, json, pathlib
from fractions import Fraction
import sympy as s
out={}
p=2**61-1;N=p-1;m=N//7;H=2**60-2**56-1
phi=int(s.totient(m));divs=2**len(s.factorint(m));C=43*1518500250
main=Fraction(6*H*phi,N);err=6*divs*C
lo=main.numerator//main.denominator-err
out['primitive_generator_37']=all(pow(37,N//int(r),p)!=1 for r in s.factorint(N))
assert out['primitive_generator_37']
out['nh_raw_unequal_zero_extension']={'w':2,'colliding_keys':sum(a*b==0 for a in range(4) for b in range(4)),'total_keys':16}
out['polymur']={'N_factors':{str(a):b for a,b in s.factorint(N).items()},'phi_m':phi,'squarefree_divisors_m':divs,'interval_H':H,'main_fraction':str(main),'character_sum_upper':C,'error_upper':err,'K_lower':lo,'log2_K_lower':math.log2(lo),'score_lower':math.log2(lo/9)}
T=s.Matrix([[0,0,1,4,1,1,2,2,1],[1,1,0,0,1,4,1,2,2],[1,4,1,1,0,0,2,1,2]])
def v2(v):
 v=abs(int(v));return 10000 if not v else (v&-v).bit_length()-1
coeff=[]
for F in itertools.combinations(range(9),3):
 rowc=[]
 for r in range(1,4):
  rowc.append(sum(2**min(v2(T.extract(R,J).det()) for J in itertools.combinations(F,r)) for R in itertools.combinations(range(3),r)))
 coeff.append((F,rowc))
maxc=[max(c[i] for F,c in coeff) for i in range(3)]
out['halftime_minors']={'count':len(coeff),'max_full_v2':max(v2(T[:,F].det()) for F,c in coeff),'max_partial_kernel_sums':maxc,'witnesses':[{'columns':F,'coefficients':c} for F,c in coeff if c==maxc]}
# False ASU proof-step witness.
perm=[4,0,1,3,2]
witness=[(k,z) for k in range(5) for z in range(5) if (perm[k]+z)%5==0 and (perm[2*k%5]+z)%5==1]
out['asu_witness']=witness
# Mersenne projection defeats generic fibre-scaled AXU.
u=[1,2,4,8,16]
out['projection_witness']={'xor_differences':[a^(a+31) for a in u],'mod31_equal':all(a%31==(a+31)%31 for a in u)}
# NH unequal-length truncated product exact enumeration.
for w in (2,3,4):
 Q=2**w;mod=Q*Q//4;counts=[0]*mod
 for a in range(Q):
  for b in range(Q): counts[a*b%mod]+=1
 out['truncated_NH_w'+str(w)]={'zero_count':counts[0],'max_count':max(counts),'total':Q*Q}
# Odd multiply shift.
a=[v for v in range(16) if v%2]
out['odd_multiply_shift']={'w':4,'r':2,'x':1,'y':3,'collision_keys':[v for v in a if (v%16)//4==((3*v)%16)//4]}
# Prefix recurrence coefficients over a small field and circuit decoder.
def recurrence_coeff(msg,p):
 A=[0];B=[1];C=[0]
 def mul(v,b):return [(b*v[0])%p]+[(v[i-1]+b*(v[i] if i<len(v) else 0))%p for i in range(1,len(v)+1)]
 for a,b in msg:
  A=mul(A,b);A[0]=(A[0]+a)%p
  B=mul(B,b);C[0]=(C[0]+1)%p;C=mul(C,b)
 return tuple(A),tuple(B),tuple(C)
for p0,n in [(2,4),(3,3)]:
 polys={recurrence_coeff(tuple(zip(v[::2],v[1::2])),p0) for v in itertools.product(range(p0),repeat=2*n)}
 out['recurrence_'+str(p0)+'_'+str(n)]={'distinct':len(polys),'messages':p0**(2*n)}
Q=2**32;p36=2**36-5
EU=Fraction(1,Q)+Fraction(1,2**35)+Fraction(2**54+6,2**100)+32*Fraction(2**28+1,2**64)
out['UHASH']={'EU':str(EU),'bits':-math.log2(float(EU))}
q=2**64;r=q-257
EV=Fraction(4,q)+Fraction(1,r)+Fraction(1,2**116)
out['VHASH']={'bits_repaired':-math.log2(float(EV))}
out['Halftime_score_leaf']=96+math.log2(168/20)
# Intended distance-3 systematic encoder (P=sum x_i, Q=sum A_i x_i).
def rank2(cols):
 piv={}
 for a in cols:
  while a:
   j=a.bit_length()-1
   if j not in piv:piv[j]=a;break
   a^=piv[j]
 return len(piv)
As=[[1,2,4],[4,5,2],[5,7,6],[2,6,5],[3,4,1],[6,3,7],[7,1,3]]
rs=[rank2(a) for a in As]+[rank2([x^y for x,y in zip(a,b)]) for a,b in itertools.combinations(As,2)]
out['intended_Encode3']={'matrices_as_columns':As,'ranks':rs}
a=Fraction(1,2**32);b=EU-a
out['UHASH_improved']={str(t):{'bound':str(a+(1-a)*b**t),'bits':-math.log2(float(a+(1-a)*b**t))} for t in range(1,5)}
# Binary irreducibility and Mersenne primality checks, exact arithmetic.
def f2mod(a,b):
 while a.bit_length()>=b.bit_length():a ^= b << (a.bit_length()-b.bit_length())
 return a
def f2mul(a,b,mod):
 c=0
 while b:
  if b&1:c^=a
  a<<=1;b>>=1
 return f2mod(c,mod)
def f2gcd(a,b):
 while b:a,b=b,f2mod(a,b)
 return a
for degree,mod in [(64,(1<<64)|27),(127,(1<<127)|3)]:
 x=2;ys=[]
 for i in range(1,degree+1):x=f2mul(x,x,mod);ys.append(x)
 factors=list(s.factorint(degree))
 out['irreducible_GF'+str(degree)]={'frobenius_equal':ys[-1]==2,'gcd_values':[f2gcd(ys[degree//r-1]^2,mod) for r in factors]}
for exponent in (61,89,127):
 modulus=(1<<exponent)-1;v=4
 for _ in range(exponent-2):v=(v*v-2)%modulus
 out['lucas_lehmer_'+str(exponent)]=v
# The degree-5 coefficient map and explicit decoder over GF(4).
def gf4(a,b):return f2mul(a,b,7)
def encode5(c):
 c0,c1,c2,c3,c4=c;b=c0^c1;d=gf4(c0,c1)
 return (c4^gf4(c2,d^c3),d^c3^gf4(c0,c2),c0^gf4(c2,b),b^c2,1^c2)
def decode5(e):
 e0,e1,e2,e3,e4=e;c2=e4^1;b=e3^c2;c0=e2^gf4(c2,b);c1=b^c0;c3=e1^gf4(c0,c1)^gf4(c0,c2);c4=e0^gf4(c2,gf4(c0,c1)^c3)
 return c0,c1,c2,c3,c4
cs=list(itertools.product(range(4),repeat=5));es=[encode5(c) for c in cs]
out['chain5_GF4']={'vectors':len(cs),'distinct_images':len(set(es)),'decoder_correct':all(decode5(e)==c for c,e in zip(cs,es))}
# Width-2 Halftime constants.
T2=s.Matrix([[1,0,1,1,2,1,4],[0,1,1,2,1,4,1]])
out['halftime_width2']={'max_full_kernel':max(2**v2(T2[:,F].det()) for F in itertools.combinations(range(7),2)),'max_single_kernel_sum':max(sum(2**min(v2(T2[i,j]) for j in F) for i in range(2)) for F in itertools.combinations(range(7),2))}
# Full counts for paired and vector multiply-shift at w=2,W=3,r=2.
msgs=list(itertools.product(range(4),repeat=2));keys=list(itertools.product(range(8),repeat=3))
for paired in (False,True):
 vals=[]
 for x,y in msgs:
  vals.append([(((a+y)*(b+x)+c if paired else a*x+b*y+c)%8)//2 for a,b,c in keys])
 ok=True
 for i,j in itertools.combinations(range(len(msgs)),2):
  counts=[0]*16
  for a,b in zip(vals[i],vals[j]):counts[4*a+b]+=1
  ok &= set(counts)=={32}
 out['pairwise_independence_'+str(paired)]={'all_output_pairs_count_32_of_512':ok}
# Claims already proved algebraically, here checked for transcription.
assert out['polymur']['K_lower']==189729088763903999
assert out['halftime_minors']['max_partial_kernel_sums']==[6,9,4]
assert out['halftime_width2']=={'max_full_kernel':4,'max_single_kernel_sum':5}
assert all(v==3 for v in rs)
assert all(out['lucas_lehmer_'+str(e)]==0 for e in (61,89,127))
assert out['chain5_GF4']['decoder_correct'] and len(set(es))==1024
assert all(out['irreducible_GF'+str(d)]['frobenius_equal'] and out['irreducible_GF'+str(d)]['gcd_values']==[1] for d in (64,127))
assert all(out['pairwise_independence_'+str(p)]['all_output_pairs_count_32_of_512'] for p in (False,True))
pathlib.Path('review-support/halftime-minors.json').write_text(json.dumps([{'columns':F,'kernel_sums':c} for F,c in coeff],indent=2)+'\n')
pathlib.Path('review-support/results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
