# Sharp alt-r0 bound with item 3: head slot conditions cost 1/q times the packing constant
# cst = (w + 2nB)^n / w^n (main term) and cst^2 (exceptional term: two heads).
# 2^k [ cn w^n (sum_d C(n,d) pn^d pd^(M-d) ENr(b^2) + C(n,d1+1) pn^(d1+1) pd^(M-d1-1) q^(2Kn))
#     + cn^2 (sum_d C(n,d) (pn'^d - pn^d) pd^(M-d) ENr(b)^2 + C(n,d2+1)(pn'^(d2+1)-pn^(d2+1)) pd^(M-d2-1) q^(2Kn)) ]
#   <= Dc^(2Kn) pd^M w^(2n),   p = pn/pd = 1/q + 1/G, pe = pn'/pd = p + 2/(qG), G = (2 g1)^(L-1)
import sys
from gapeval import GBk
from math import comb, log2
q=8380417;n=256
P={'44':(2**17,95232,78,44,4,4),'65':(2**19,261888,196,16,6,5),'87':(2**19,261888,120,16,8,7)}
cache={}
def ENr(K,Bd,D,d,e=330):
    key=(K,Bd,D,d)
    if key not in cache:
        S=sum(Bd**u*D**(n-u)*GBk(e,q,n,1,d,u) for u in range(n+1)); cache[key]=max(S**K-(D+Bd)**(K*n),0)
    return cache[key]
def maxk(nm,w,B,d1,d2):
    g1,g2,b,mb,K,L=P[nm]; Dc=mb*(2*(g2-b)-1); Bd=q-Dc; G=(2*g1)**(L-1)
    pn=G+q; pn2=G+q+2; pd=q*G; M=max(d1,d2)+1; cn=(w+2*n*B)**n
    main=sum(comb(n,d)*pn**d*pd**(M-d)*ENr(K,Bd**2,Dc**2,d) for d in range(1,d1+1))+comb(n,d1+1)*pn**(d1+1)*pd**(M-d1-1)*q**(2*K*n)
    exc=sum(comb(n,d)*(pn2**d-pn**d)*pd**(M-d)*ENr(K,Bd,Dc,d)**2 for d in range(1,d2+1))+comb(n,d2+1)*(pn2**(d2+1)-pn**(d2+1))*pd**(M-d2-1)*q**(2*K*n)
    num=cn*w**n*main+cn**2*exc; rhs=Dc**(2*K*n)*pd**M*w**(2*n); k=0
    while 2**(k+1)*num<=rhs: k+=1
    return k
for nm in P:
    g1,g2,b,mb,K,L=P[nm]
    for wl,w in (('full',2*g1),('z',2*(g1-b)-1)):
        best=max((maxk(nm,w,5,d1,d2),d1,d2) for d1 in range(18,28) for d2 in range(12,26))
        print(nm,wl,'k=%d d1=%d d2=%d'%best,flush=True)
