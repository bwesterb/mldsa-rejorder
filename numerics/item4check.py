# Integer inequality for item 4:  2^(2j) [ sum_d C(n,d) rn^d rd^(dm+1-d) ENr^2 + C(n,dm+1) rn^(dm+1) Dc^(2Kn) ] <= rd^(dm+1) Dc^(2Kn)
# with rho = rn/rd = (q+1)/(2 g1)^L. Then E_A Dev_i <= 2^-j and E_A leak <= (2m + l) 2^-j.
import sys
from gapeval import GBk
from math import comb, log2
q=8380417;n=256
P={'44':(2**17,95232,78,44,4,4),'65':(2**19,261888,196,16,6,5),'87':(2**19,261888,120,16,8,7)}
def ENr(e,K,Bd,D,d):
    S=sum(Bd**u*D**(n-u)*GBk(e,q,n,1,d,u) for u in range(n+1)); return max(S**K-(D+Bd)**(K*n),0)
def maxj(nm,dm,e=330):
    g1,g2,b,mb,K,L=P[nm]; Dc=mb*(2*(g2-b)-1); Bd=q-Dc; rn=q+1; rd=(2*g1)**L
    num=sum(comb(n,d)*rn**d*rd**(dm+1-d)*ENr(e,K,Bd,Dc,d)**2 for d in range(1,dm+1))+comb(n,dm+1)*rn**(dm+1)*Dc**(2*K*n)
    rhs=rd**(dm+1)*Dc**(2*K*n); j=0
    while 2**(2*(j+1))*num<=rhs: j+=1
    return j, log2(2*K*n+L*n)
for nm in P:
    best=max((maxj(nm,dm)+(dm,)) for dm in range(10,26))
    j,lp,dm=best
    print(nm,'dm=%d j=%d  E leak <= (2m+l)/2^j ~ 2^-%.1f'%(dm,j,j-lp))
