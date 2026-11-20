import sys,time
from gapeval import *
from math import comb
q=8380417;n=256
P={'44':(2**17,95232,78,44,4,4),'65':(2**19,261888,196,16,6,5),'87':(2**19,261888,120,16,8,7)}
def ENr(e,K,Bd,D,d):
    S=sum(Bd**u*D**(n-u)*GBk(e,q,n,1,d,u) for u in range(n+1))
    return max(S**K-(D+Bd)**(K*n),0)
def check(nm,w,e,dm1,dm2):
    g1,g2,b,mb,K,L=P[nm]; Dc=mb*(2*(g2-b)-1); Bd=q-Dc
    G=(2*g1)**(L-1); pn=G+w; pn2=G+w+2; pd=w*G; M=max(dm1,dm2)+1
    num=sum(comb(n,d)*pn**d*pd**(M-d)*ENr(e,K,Bd**2,Dc**2,d) for d in range(1,dm1+1))
    num+=comb(n,dm1+1)*pn**(dm1+1)*pd**(M-dm1-1)*q**(2*K*n)
    num+=sum(comb(n,d)*(pn2**d-pn**d)*pd**(M-d)*ENr(e,K,Bd,Dc,d)**2 for d in range(1,dm2+1))
    num+=comb(n,dm2+1)*(pn2**(dm2+1)-pn**(dm2+1))*pd**(M-dm2-1)*q**(2*K*n)
    rhs=Dc**(2*K*n)*pd**M
    k=0
    while 2**(k+1)*num<=rhs: k+=1
    return k
for a in sys.argv[1:]:
    nm,e,dm1,dm2=a.split(','); g1=P[nm][0]
    t=time.time(); print(a,'max k =',check(nm,2*g1,int(e),int(dm1),int(dm2)),'%.0fs'%(time.time()-t),flush=True)
