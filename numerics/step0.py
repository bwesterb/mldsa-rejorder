from fractions import Fraction as Fr
from gapeval import GBk
from math import comb, log2, exp
q=8380417;n=256
P={'44':(2**17,95232,78,44,4,4),'65':(2**19,261888,196,16,6,5),'87':(2**19,261888,120,16,8,7)}
def lg(x):
    x=Fr(x); return log2(x.numerator)-log2(x.denominator) if x>0 else float('-inf')
cache={}
def E(bt,K,d,e=330):
    key=(bt,K,d)
    if key not in cache:
        S=sum(bt**u*GBk(e,q,n,1,d,u) for u in range(n+1)); cache[key]=S**K-(1+bt)**(K*n)
    return cache[key]
def sharp(nm,p,pe,cst=1,cste=1,dms=range(14,34),dms2=range(10,24)):
    g1,g2,b,mb,K,L=P[nm]; Dc=mb*(2*(g2-b)-1); bt=Fr(q-Dc,Dc); mu=Fr(Dc,q)**(K*n)
    main=min(cst*(sum(comb(n,d)*p**d*mu**2*E(bt**2,K,d) for d in range(1,dm+1))+comb(n,dm+1)*p**(dm+1)) for dm in dms)
    exc=min(cste*(sum(comb(n,d)*(pe**d-p**d)*mu**2*E(bt,K,d)**2 for d in range(1,dm+1))+comb(n,dm+1)*(pe**(dm+1)-p**(dm+1))) for dm in dms2)
    return lg(main),lg(exc),lg(main+exc)
print("== item 3 (variance, log2) ==")
for nm in P:
    g1,g2,b,mb,K,L=P[nm]; w=2*g1; tau=Fr(1,(2*g1)**(L-1))
    old=sharp(nm,Fr(1,w)+tau,Fr(1,w)+tau+2*tau/w)
    B=5; cst=Fr((w+2*n*B)**n, w**n)
    new=sharp(nm,Fr(1,q)+tau,Fr(1,q)+tau+2*tau/q,cst=cst,cste=cst**2)
    print(nm,'old main/exc/total %.0f %.0f %.0f | new %.0f %.0f %.0f (const 2^%.1f)'%(old+new+(lg(cst),)))
print("== item 4 (RejOrder via product Fourier) ==")
for nm in P:
    g1,g2,b,mb,K,L=P[nm]; Dc=mb*(2*(g2-b)-1); bt=Fr(q-Dc,Dc); mu=Fr(Dc,q)**(K*n); pR=1-Fr(Dc,q)
    rho=Fr(q+1,(2*g1)**L)
    best=None
    for dm in range(4,40):
        V=sum(comb(n,d)*rho**d*E(bt,K,d)**2 for d in range(1,dm+1))+comb(n,dm+1)*rho**(dm+1)/mu**2
        if best is None or V<best[0]: best=(V,dm)
    V,dm=best; leak=lg(V)/2+log2(2/float(pR)+L*n)
    print(nm,'rel. variance 2^%.0f (dm=%d) -> leak ~ 2^%.0f   (RejOrder now: %s)'%(lg(V),dm,leak,{'44':-289,'65':-418,'87':-568}[nm]))
