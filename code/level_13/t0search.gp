kro(a,p)=kronecker(a,p);
ssA(p) = { my(n=p\12, d=(1-kro(-3,p))/2, e=(1-kro(-1,p))/2, c);
  c = sum(k=0,n, binomial(2*n+e,2*k+e)*binomial(2*n-2*k,n-k)*(-432)^(n-k)*(J-1728)^k);
  c = c*Mod(1,p); (J^d*(J-1728)^e*c)/pollead(c); }
m0 = J^2 - 174668400*J + 10755802087387200;
hits=List();
forprime(p=5,6000, if(p==13,next); if(poldegree(gcd(ssA(p), m0*Mod(1,p)))>0, listput(hits,p)));
print("primes p<=6000 with j(t=0) supersingular: ", Vec(hits));
