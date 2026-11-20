# Exact Python mirror of RejOrder's GapEval definitions.
from math import comb,log2
from functools import lru_cache
def sumF(f,k): return sum(f(i) for i in range(k))
def digit(e,N,t): return (N>>(e*t)) & ((1<<e)-1)
def geomK(e,g): return sumF(lambda z: 1<<(e*z), g+1)
@lru_cache(None)
def compK(e,g,u,d): return digit(e,geomK(e,g)**u,d) if (g+1)**u < 2**e else (g+1)**u
def chooseC(m,t): return comb(m,t)
@lru_cache(None)
def NBk(e,n,u,g): return min(chooseC(n,u), n*compK(e,g,u,max(n-u,0))//u if u>0 else 0) if u>0 else min(chooseC(n,u), 0)
def GBk(e,q,n,c,s_,u):
    return chooseC(n,u)+(q**c-1)*sumF(lambda g: q**(c*(s_-1-g))*NBk(e,n,u,g) if s_<g+1+u else 0, s_)
def sumGB(e,q,n,c,sig,s): return sumF(lambda u: GBk(e,q,n,c,sig,u), s+1)
def packGB(e,e2,q,n,c,sig,s): return sumF(lambda u: GBk(e,q,n,c,sig,u)<<(e2*u), s+1)
def coefK_all(e,e2,q,n,K,c,sig,s):
    S=sumGB(e,q,n,c,sig,s)**K
    if S < 2**e2:
        P=packGB(e,e2,q,n,c,sig,s)**K
        return [digit(e2,P,t) for t in range(s+1)]
    return [S]*(s+1)
