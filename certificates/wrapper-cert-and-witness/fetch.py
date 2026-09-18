import urllib.request, pathlib, subprocess, hashlib
root=pathlib.Path('review-support/sources')
urls={
'polymur-README.md':'https://raw.githubusercontent.com/orlp/polymur-hash/master/README.md',
'polymur-proof.md':'https://raw.githubusercontent.com/orlp/polymur-hash/master/extras/universality-proof.md',
'polymur-hash.h':'https://raw.githubusercontent.com/orlp/polymur-hash/master/polymur-hash.h',
'umash_reference.py':'https://raw.githubusercontent.com/backtrace-labs/umash/master/umash_reference.py',
'umash-README.md':'https://raw.githubusercontent.com/backtrace-labs/umash/master/README.md',
'umash.pdf':'https://raw.githubusercontent.com/backtrace-labs/umash/master/umash.pdf',
'halftime.pdf':'https://arxiv.org/pdf/2104.08865',
'halftime-hash.hpp':'https://raw.githubusercontent.com/jbapple/HalftimeHash/main/halftime-hash.hpp',
'rfc4418.txt':'https://www.rfc-editor.org/rfc/rfc4418.txt',
'umac-full.pdf':'https://web.cs.ucdavis.edu/~rogaway/papers/umac-full.pdf',
'umac-thesis.pdf':'https://web.cs.ucdavis.edu/~rogaway/umac/umac_thesis.pdf',
'vmac-2006.pdf':'https://krovetz.net/csus/papers/vmac.pdf',
'vhash-security.pdf':'https://eprint.iacr.org/2007/338.pdf',
'vmac-draft.txt':'https://www.ietf.org/archive/id/draft-krovetz-vmac-01.txt',
'dietzfelbinger.pdf':'https://hjemmesider.diku.dk/~jyrki/Paper/CP-11.4.1997.pdf',
'multiply-shift.pdf':'https://arxiv.org/pdf/1504.06804',
'clhash.pdf':'https://arxiv.org/pdf/1503.03465',
'simple-tabulation.pdf':'https://arxiv.org/pdf/1011.5200',
'pema.pdf':'https://cr.yp.to/antiforgery/pema-20071022.pdf',
'carter-wegman.pdf':'https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/7/36891/files/2020/10/CarterWegmanJrCompSci1979UniversalHashClasses.pdf',
}
manifest=[]
for name,url in urls.items():
 p=root/name
 try:
  data=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Proof-review/1.0'}),timeout=35).read()
  p.write_bytes(data)
  manifest.append(f'{name}\t{hashlib.sha256(data).hexdigest()}\t{url}')
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  print(name,len(data),flush=True)
 except Exception as e:print('FAILED',name,repr(e),flush=True)
(root/'MANIFEST.tsv').write_text('\n'.join(manifest)+'\n')
