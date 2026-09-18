from pathlib import Path
p=Path('review-support/checks.py')
s=p.read_text()
needle="pathlib.Path('review-support/halftime-minors.json').write_text"
extra='''# Binary irreducibility and Mersenne primality checks, exact arithmetic.
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
'''
s=s.replace(needle,extra+needle)
p.write_text(s)
