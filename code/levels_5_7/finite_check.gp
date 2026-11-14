\\ finite_check.gp -- bounded validation of the corrected Nakaya Conjecture 1 and of every
\\ intermediate statement used in the proof.  PARI/GP >= 2.15 (ellissupersingular).
\\ Run:  gp -q finite_check.gp          (BOUND, LEGB, ELLB may be edited below)
\\ This is NOT part of the proof; it is an independent sanity check.

BOUND = 2000;   \\ all admissible primes p <= BOUND are tested at both levels
LEGB  = 250;    \\ ss_p cross-checked against the Legendre-family Hasse polynomial for p <= LEGB
ELLB  = 60;     \\ ss_p cross-checked against brute-force supersingularity tests over F_(p^2) for p <= ELLB

kro(a,p) = kronecker(a,p);
rad(P,p) = { my(F=factormod(P,p)); lift(prod(i=1,#F~, F[i,1]))*Mod(1,p); }

\\ --- classical supersingular polynomial: three independent constructions -------------
\\ (a) closed formula (Nakaya 2019, Theorem 1; Kaneko-Zagier / Deuring)
ssA(p) = { my(n=p\12, d=(1-kro(-3,p))/2, e=(1-kro(-1,p))/2, c);
  c = sum(k=0,n, binomial(2*n+e,2*k+e)*binomial(2*n-2*k,n-k)*(-432)^(n-k)*(J-1728)^k);
  c = c*Mod(1,p); (J^d*(J-1728)^e*c)/pollead(c); }
\\ (b) Legendre family: y^2=x(x-1)(x-l) is supersingular iff sum binomial((p-1)/2,k)^2 l^k = 0
ssB(p) = { my(n=(p-1)/2, H, R);
  H = sum(k=0,n, binomial(n,k)^2*l^k)*Mod(1,p);
  R = polresultant(H, (256*(l^2-l+1)^3 - J*l^2*(l-1)^2)*Mod(1,p), l);
  R = rad(R,p); R/pollead(R); }
\\ (c) brute force over F_(p^2)
ssC(p) = { my(g=ffgen(p^2,'g), z, pr=1, E, v, r, u);
  for(a=0,p-1, for(b=0,p-1, z=a+b*g; E=ellinit(ellfromj(z)); if(ellissupersingular(E), pr*=(J-z))));
  v=Vec(pr); r=vector(#v);
  for(i=1,#v, u=if(type(v[i])=="t_FFELT", v[i].pol, v[i]); if(poldegree(u)>0, error("coefficient not in Fp")); r[i]=polcoeff(u,0));
  Pol(r, J)*Mod(1,p); }

RN(N) = { if(N==5, J^2-J*(X^5-80*X^4+1890*X^3-12600*X^2+7776*X+3456)+(X^2+216*X+144)^3,
                 J^2-J*X*(X^2-21*X+8)*(X^4-42*X^3+454*X^2-1008*X-1280)+X^2*(X^2+224*X+448)^3); }

\\ --- generic Heun recurrence (Nakaya p.488), coefficients c_0..c_nmax in any ring -----
heun(a,qq,al,be,ga,de,nmax) = { my(ep=al+be+1-ga-de, c=vector(nmax+1), prev=0*a, cur=a^0, nx);
  c[1]=cur;
  for(n=0,nmax-1,
    nx = ((n*((n-1+ga)*(1+a)+a*de+ep)+qq)*cur - (n-1+al)*(n-1+be)*prev)/((n+1)*(n+ga)*a);
    c[n+2]=nx; prev=cur; cur=nx);
  c; }
\\ --- rational normal form: w s P + (s + de w s)P - (A w + B)P = 0, s = 1 - T w - U w^2
\\     (n+1)^2 g_(n+1) = (T n (n+de) + B) g_n + (U (n-1)(n-1+2 de) + A) g_(n-1)
ratrec(T,U,de,AA,BB,p) = { my(g=vector(p), prev=Mod(0,p), cur=Mod(1,p), nx);
  g[1]=cur;
  for(n=0,p-2,
    nx = ((T*n*(n+de)+BB)*cur + (U*(n-1)*(n-1+2*de)+AA)*prev)/(n+1)^2;
    g[n+2]=nx; prev=cur; cur=nx);
  g; }
\\ Cooper's Apery-like numbers u*_5(n), u*_7(n), precomputed once as exact integers
NU = 2*(BOUND\3)+8;
US5 = vector(NU+1, i, my(n=i-1); binomial(2*n,n)*sum(k=0,n, binomial(n,k)^2*binomial(n+k,k)));
US7 = vector(NU+1, i, my(n=i-1); sum(k=0,n, binomial(n,k)^2*binomial(2*k,n)*binomial(n+k,k)));
ustar(N,n) = if(N==5, US5[n+1], US7[n+1]);

nfail = 0; ntest = 0;
bad(msg) = { nfail++; print("FAIL ", msg); }

one(N,p) = {
  my(P1=Mod(1,p), ss, S, chi, off, mu, m, e, T, U, AA, BB, de, g, deg, br, cand, ok=1);
  ss = ssA(p);
  if(p<=LEGB, if(ss != ssB(p), bad(Str("ssA != ssB at p=",p))));
  if(p<=ELLB, if(ss != ssC(p), bad(Str("ssA != ssC at p=",p))));
  \\ independent definition: monic radical of the modular resultant
  S = rad(polresultant(ss, RN(N)*P1, J), p); S = S/pollead(S);
  if(N==7, chi=kro(-3,p); mu=(1-kro(-7,p))/2; m=(p-chi)/3-mu; e=(p-1)\3; T=26; U=27; br=((X+1)*(X-27))^mu,
           chi=kro(-1,p); mu=(1-kro(-5,p))/2; m=(p-chi)/4-mu; e=(p-1)\4; T=44; U=16; br=(X^2-44*X-16)^mu);
  off = (1-chi)/2; de = mu + Mod(1,p)/2; deg = m - off;
  if(N==7, AA=if(mu,60,6); BB=if(mu,15,2), AA=if(mu,35,3); BB=if(mu,25,3));
  \\ (1) degree bookkeeping
  if(deg != e-mu, bad(Str("deg != e-mu  N=",N," p=",p)));
  if(poldegree(S) != m+2*mu, bad(Str("degree formula N=",N," p=",p)));
  \\ (2) rational normal form: full range n <= p-1, vanishing beyond deg, identity
  g = ratrec(T,U,de,AA,BB,p);
  for(n=deg+1,p-1, if(g[n+1]!=0, bad(Str("g_n != 0 beyond degree: N=",N," p=",p," n=",n)); break));
  \\ closing equation at w^(p-1) (coefficient of g_p is p^2 = 0)
  if((T*(p-1)*(p-1+de)+BB)*g[p] + (U*(p-2)*(p-2+2*de)+AA)*g[p-1] != 0, bad(Str("closing eq N=",N," p=",p)));
  cand = X^m*br*sum(n=0,deg, g[n+1]*X^(-n));
  if(cand*P1 != S, bad(Str("MAIN IDENTITY (rational form) N=",N," p=",p)));
  \\ (3) Heun form with the corrected parameters, in Fp (N=7) or Fp[phi] (N=5, both conjugates)
  my(betaI = mu + Mod(1,p)/2 + chi*Mod(1,p)/if(N==7,6,4), alI = off - m);
  if(N==7,
     my(c = heun(Mod(-27,p), Mod(-(13*mu+2),p), Mod(alI,p), betaI, Mod(1,p), de, p-1));
     for(n=0,p-1, if(c[n+1]*Mod(27,p)^n != g[n+1], bad(Str("Heun vs rational N=7 p=",p," n=",n)); break)),
     foreach([t, 1-t], ph0,
       my(ph = Mod(ph0*P1, (t^2-t-1)*P1), a=-ph^10, kap=4*ph^5, c);
       c = heun(a, -(22*mu+3)*ph^5/4, alI*ph^0, betaI*ph^0, ph^0, de*ph^0, p-1);
       for(n=0,p-1, if(c[n+1]*kap^n != g[n+1]*ph^0, bad(Str("Heun vs rational / descent N=5 p=",p," n=",n," phi=",ph0)); break))));
  \\ (4) the printed formula (alpha = -m), truncated at degree m as in the handoff
  my(pr, prc);
  if(N==7,
     prc = heun(Mod(-27,p), Mod(-(13*mu+2),p), Mod(-m,p), betaI, Mod(1,p), de, m);
     pr = X^m*br*sum(n=0,m, prc[n+1]*27^n*X^(-n)),
     my(ph = Mod(t*P1, (t^2-t-1)*P1), kap=4*ph^5);
     prc = heun(-ph^10, -(22*mu+3)*ph^5/4, -m*ph^0, betaI*ph^0, ph^0, de*ph^0, m);
     pr = X^m*br*sum(n=0,m, lift(prc[n+1]*kap^n)*X^(-n)));
  my(prmatch = (lift(lift(pr))*P1 == S), predicted = (off==0) || (N==7 && p==5));
  if(prmatch != predicted, bad(Str("printed-formula classification N=",N," p=",p," match=",prmatch)));
  \\ (5) proof internals: E_(p-1)/f^((p-1)/2) mod p as a rational function of h
  my(d3=(1-kro(-3,p))/2, e4=(1-kro(-1,p))/2, mm=(p-1-4*d3-6*e4)/12, ft, jn, e4n, e6n, A, K, Nb, Q, Xh);
  ft = ss/(J^d3*(J-1728)^e4);
  if(denominator(ft)!=1 || poldegree(ft)!=mm, bad(Str("KZ shape N=",N," p=",p)));
  if(N==7, A=13;K=49; jn=(h^2+13*h+49)*(h^2+245*h+2401)^3; e4n=h^2+245*h+2401; e6n=h^4-490*h^3-21609*h^2-235298*h-823543,
           A=22;K=125; jn=(h^2+250*h+3125)^3; e4n=h^2+250*h+3125; e6n=h^2-500*h-15625);
  \\ Horner evaluation modulo p of h^(N*mm) * ft(jn/h^N)
  my(jnp=jn*P1, hN=h^N*P1, acc=0*P1);
  forstep(i=mm,0,-1, acc = acc*jnp + polcoeff(ft,i,J)*hN^(mm-i));
  Nb = (e4n^d3*e6n^e4)*P1*acc;
  Q = sum(n=0,deg, g[n+1]*X^(deg-n));
  my(dh=(h^2+A*h+K)*P1, QX=0*P1);   \\ h^deg * Q(X(h)) by Horner
  forstep(i=deg,0,-1, QX = QX*dh + polcoeff(Q,i,X)*(h*P1)^(deg-i));
  if(mu==0, if(Nb != QX*P1, bad(Str("N(h) = h^e Q(X(h))  N=",N," p=",p))),
            if(Nb != (h^2-K)*QX*P1, bad(Str("N(h) = h^(e-1)(h^2-K) Q1(X(h))  N=",N," p=",p))));
  \\ squarefreeness of N(h) and of the Heun polynomial; non-vanishing at X=0 and at the Fricke points
  if(poldegree(gcd(Nb, deriv(Nb,h))) > 0, bad(Str("N(h) not squarefree N=",N," p=",p)));
  if(polcoeff(Q,0,X)==0, bad(Str("Q(0)=0 N=",N," p=",p)));
  if(poldegree(gcd(Q*P1, (X^2-T*X-U)*P1))>0, bad(Str("Q vanishes at a Fricke point N=",N," p=",p)));
  \\ (6) Conjecture 3 (Apery-like square formula) as a corollary
  my(M2 = 2*(m+mu));
  if(S^2 != br*sum(n=0,M2, ustar(N,n)*X^(M2-n))*P1, bad(Str("Conjecture 3 N=",N," p=",p)));
  ntest++;
}
{
  forprime(p=5, BOUND, if(p!=7, one(7,p)); if(p>=7, one(5,p)));
  print("tests run: ", ntest, "   (level 7: p=5 and 11<=p<=", BOUND, "; level 5: 7<=p<=", BOUND, ")");
  print("==== finite_check.gp: ", if(nfail==0, "ALL CHECKS PASSED", Str(nfail, " FAILURES")), " ====");
}
