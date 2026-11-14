\\ identities.gp -- exact checks of the characteristic-zero identities used in the proof
\\ of the corrected Nakaya Conjecture 1 (levels 5 and 7).  PARI/GP >= 2.13.
\\ Run:  gp -q identities.gp      (prints PASS/FAIL lines and a final summary)
\\ Every q-series identity is checked to O(q^PREC); the proof needs only the stated
\\ pole bound B (difference of two functions on X_0(N) with <= B poles vanishing to order > B).

PREC = 200;
default(seriesprecision, PREC+5);
nfail = 0;
chk(name, ok) = { print(if(ok,"PASS  ","FAIL  "), name); if(!ok, nfail++); }
\\ series identities: require the difference to vanish identically AND to be known to order >= 150
chs(name, dif) = { my(v=valuation(dif,q)); print(if(dif==0 && v>=150,"PASS  ","FAIL  "), name, "   [difference = O(q^", v, ")]"); if(!(dif==0 && v>=150), nfail++); }

D(F) = q*deriv(F,q);
Eis(k) = 1 - 2*k/bernfrac(k)*sum(n=1,PREC, sigma(n,k-1)*q^n) + O(q^(PREC+1));
E2s = Eis(2); E4s = Eis(4); E6s = Eis(6);
Dels = q*eta(q+O(q^(PREC+1)))^24;
js   = E4s^3/Dels;

\\ level data: [N, A, K, jnum(h), e4num, e6num]; X = h + A + K/h ; h^2+A*h+K vanishes at X=0
\\ j(tau) = jnum(h)/h^N
data(N) = {
  if(N==7, return([7, 13, 49, (h^2+13*h+49)*(h^2+245*h+2401)^3, h^2+245*h+2401, h^4-490*h^3-21609*h^2-235298*h-823543]));
  if(N==5, return([5, 22, 125, (h^2+250*h+3125)^3, h^2+250*h+3125, h^2-500*h-15625]));
}
RN(N) = {
  if(N==5, return(J^2-J*(X^5-80*X^4+1890*X^3-12600*X^2+7776*X+3456)+(X^2+216*X+144)^3));
  if(N==7, return(J^2-J*X*(X^2-21*X+8)*(X^4-42*X^3+454*X^2-1008*X-1280)+X^2*(X^2+224*X+448)^3));
}

level(N) = {
  my(d=data(N), A=d[2], K=d[3], jn=d[4], e4n=d[5], e6n=d[6], c=24/(N-1), hs, fs, den, Phi, Phi0, Xs, ws, T, U, s);
  print("---- level ", N, " ----");
  hs = (eta(q+O(q^(PREC+1)))/eta(q^N+O(q^(PREC+1))))^c/q;
  fs = (N*subst(E2s,q,q^N) - E2s)/(N-1);
  den = hs^2 + A*hs + K;
  \\ (I1) D h = -f h   (exact consequence of D log eta = E2/24)
  chs(Str("I1  D(h) = -f*h                         N=",N), D(hs)+fs*hs);
  \\ (I2) j = jnum(h)/h^N           pole bound B = N+1
  chs(Str("I2  j = jnum(h)/h^N                     N=",N), js - subst(jn,h,hs)/hs^N);
  \\ (I3) E4 = f^2 e4num(h)/(h^2+A h+K)             B = 4
  chs(Str("I3  E4 = f^2*e4num/(h^2+Ah+K)           N=",N), E4s - fs^2*subst(e4n,h,hs)/den);
  \\ (I4) E6 = f^3 e6num(h)/(h^2+A h+K)^(N==7?2:1)  B = 8
  chs(Str("I4  E6 = f^3*e6num/(h^2+Ah+K)^k         N=",N), E6s - fs^3*subst(e6n,h,hs)/den^if(N==7,2,1));
  \\ (I5) Delta = f^6 h^N/(h^2+A h+K)^(N==7?4:3)    B = 16
  chs(Str("I5  Delta = f^6*h^N/(h^2+Ah+K)^k        N=",N), Dels - fs^6*hs^N/den^if(N==7,4,3));
  \\ (I6) (2 f D^2 f - 3 (Df)^2)/(4 f^4) = Phi0(h)   B = 9
  Phi  = (2*fs*D(D(fs)) - 3*D(fs)^2)/(4*fs^4);
  Phi0 = if(N==7, 2*hs*(hs^2+16*hs+49), 3*hs*(hs^2+23*hs+125))/den^2;
  chs(Str("I6  (2fD^2f-3(Df)^2)/(4f^4) = Phi0(h)   N=",N), Phi - Phi0);
  \\ (I7) Phi0 in terms of X = h+A+K/h :  2(X+3)/X^2  resp. 3(X+1)/X^2   (rational-function identity)
  my(Xh = (h^2+A*h+K)/h, P0 = if(N==7, 2*h*(h^2+16*h+49), 3*h*(h^2+23*h+125))/(h^2+A*h+K)^2);
  chk(Str("I7  Phi0 = c(X+d)/X^2                   N=",N), P0 == if(N==7, 2*(Xh+3), 3*(Xh+1))/Xh^2);
  \\ (I8) (h-K/h)^2 = X^2 - T X - U
  T = if(N==7,26,44); U = if(N==7,27,16);
  chk(Str("I8  (h-K/h)^2 = X^2-T*X-U               N=",N), (h-K/h)^2 == Xh^2 - T*Xh - U);
  \\ (I9) R_N(J, X(h)) = (J - j(h)) (J - j(K/h))   (polynomial identity after clearing h)
  my(jh = jn/h^N, jh2 = subst(jn,h,K/h)/(K/h)^N);
  chk(Str("I9  R_N(J,X(h)) = (J-j(h))(J-j(K/h))    N=",N), subst(RN(N),X,Xh) == (J-jh)*(J-jh2));
  \\ (I10) j - 1728 = e6num^2 * (h^2+A h+K)^(N==5) / h^N
  chk(Str("I10 j-1728 = e6num^2*(..)/h^N           N=",N), jn - 1728*h^N == e6n^2*if(N==5, h^2+A*h+K, 1));
  \\ (I11) f = sum u*_N(n) / X^n  (Cooper's Apery-like numbers; used only for the Conjecture 3 corollary)
  Xs = hs + A + K/hs; ws = 1/Xs;
  my(u(n) = if(N==5, binomial(2*n,n)*sum(k=0,n, binomial(n,k)^2*binomial(n+k,k)), sum(k=0,n, binomial(n,k)^2*binomial(2*k,n)*binomial(n+k,k))));
  chk(Str("I11 f = sum u*(n) X^-n (to O(q^60))     N=",N), valuation(fs - sum(n=0,60, u(n)*ws^n), q) > 60);
  \\ discriminants / resultants: only the primes 2,3,N may occur
  my(G = jn - J*h^N, dG = poldisc(G,h), fa);
  print("     disc_h(jnum - J h^N) = ", factor(content(dG)), " * ", factor(dG/content(dG)));
  fa = factor(content(dG))[,1]~;
  chk(Str("B1  disc_h(jnum-J*h^N) = c*J^a*(J-1728)^b, c in <2,3,N>   N=",N), setminus(Set(fa), Set([2,3,N])) == [] && #select(x->poldegree(x)>0 && x!=J && x!=J-1728, factor(dG/content(dG))[,1]~) == 0);
  my(lst = [poldisc(e4n,h), poldisc(e6n,h), polresultant(e4n,e6n,h), polresultant(e4n,h^2+A*h+K,h), polresultant(e6n,h^2+A*h+K,h), poldisc(h^2+A*h+K,h), polresultant(h^2-K, h^2+A*h+K, h), 4*K]);
  print("     small discriminants/resultants: ", apply(x->factor(x), lst));
  chk(Str("B2  all auxiliary discriminants/resultants supported on {2,3,N}  N=",N), vecprod(apply(x->(setminus(Set(factor(abs(x))[,1]~), Set([2,3,N]))==[]), lst)) == 1);
}
level(7); level(5);

\\ ---- Heun <-> rational normal form, and the gauge shift (pure algebra) ----
\\ Heun operator H[a,qq;al,be,ga,de] P = z(z-1)(z-a) P'' + (ga(z-1)(z-a)+de z(z-a)+ep z(z-1)) P' + (al*be*z-qq) P,
\\ ep = al+be+1-ga-de.  With z = kappa*w it must equal  (a/kappa) * ( w s P_ww + (s + de w s') P_w - (Aw + B) P ),
\\ s = 1 - T w - U w^2 .  We test on a generic polynomial P(w) of degree 6 with indeterminate coefficients.
heunop(a,qq,al,be,ga,de,P,z) = { my(ep=al+be+1-ga-de);
  z*(z-1)*(z-a)*deriv(deriv(P,z),z) + (ga*(z-1)*(z-a)+de*z*(z-a)+ep*z*(z-1))*deriv(P,z) + (al*be*z-qq)*P; }
ratop(T,U,de,AA,BB,P) = { my(s=1-T*w-U*w^2);
  w*s*deriv(deriv(P,w),w) + (s+de*w*deriv(s,w))*deriv(P,w) - (AA*w+BB)*P; }
gen = sum(i=0,6, eval(Str("c",i))*z^i);
{
  \\ level 7
  for(mu=0,1,
    my(a=-27, kap=27, qq=-(13*mu+2), al=mu+1/3, be=mu+2/3, de=mu+1/2, L, R);
    L = subst(heunop(a,qq,al,be,1,de,gen,z), z, kap*w);
    R = ratop(26,27,de, if(mu,60,6), if(mu,15,2), subst(gen,z,kap*w));
    chk(Str("H1  Heun(level 7, mu=",mu,") = rational normal form"), L == (a/kap)*R ));
  \\ level 5 over Q(phi)
  my(ph = Mod(t, t^2-t-1));
  for(mu=0,1,
    my(a=-ph^10, kap=4*ph^5, qq=-(22*mu+3)*ph^5/4, al=mu+1/4, be=mu+3/4, de=mu+1/2, L, R);
    L = subst(heunop(a,qq,al,be,1,de,gen,z), z, kap*w);
    R = ratop(44,16,de, if(mu,35,3), if(mu,25,3), subst(gen,z,kap*w));
    chk(Str("H2  Heun(level 5, mu=",mu,") = rational normal form"), L == (a/kap)*R ));
  \\ conjugate sqrt(5):  phi -> 1-phi
  my(ph2 = Mod(1-t, t^2-t-1));
  for(mu=0,1,
    my(a=-ph2^10, kap=4*ph2^5, qq=-(22*mu+3)*ph2^5/4, al=mu+1/4, be=mu+3/4, de=mu+1/2, L, R);
    L = subst(heunop(a,qq,al,be,1,de,gen,z), z, kap*w);
    R = ratop(44,16,de, if(mu,35,3), if(mu,25,3), subst(gen,z,kap*w));
    chk(Str("H3  Heun(level 5, conjugate phi, mu=",mu,") = same rational normal form"), L == (a/kap)*R ));
}
\\ gauge shift:  if P solves ratop(T,U,1/2,A0,B0) then H = s^(-1/2) P solves ratop(T,U,3/2,A1,B1);
\\ equivalently  s * ratop_1(H) expressed through P.  Test: for generic H, ratop_0(s^(1/2) H) = s^(1/2) ratop_1(H).
\\ We verify the equivalent polynomial identity obtained by writing s^(1/2) H =: P, i.e. with S = s^(1/2):
\\ ratop_0(S*H)/S = w s H'' + (s + (3/2) w s') H' + ( (s' + w s'')/2 - (A0 w + B0) ) H .
{
  my(Hg = sum(i=0,6, eval(Str("c",i))*w^i));
  foreach([[26,27,6,2,60,15],[44,16,3,3,35,25]], v,
    my(T=v[1],U=v[2],s=1-T*w-U*w^2, sp=deriv(s,w), spp=deriv(sp,w), lhs, rhs);
    \\ ratop_0(S H)/S computed by hand-expansion with S'/S = s'/(2s), S''/S = s''/(2s) - s'^2/(4 s^2)
    my(H1=deriv(Hg,w), H2=deriv(H1,w));
    lhs = w*s*(H2 + 2*(sp/(2*s))*H1 + (spp/(2*s) - sp^2/(4*s^2))*Hg) + (s + w*sp/2)*(H1 + (sp/(2*s))*Hg) - (v[3]*w+v[4])*Hg;
    rhs = ratop(T,U,3/2,v[5],v[6],Hg);
    chk(Str("G1  gauge shift s^(-1/2): (A,B)=(",v[3],",",v[4],") -> (",v[5],",",v[6],")  [T,U]=",[T,U]), lhs == rhs));
}
print("==== identities.gp: ", if(nfail==0, "ALL CHECKS PASSED", Str(nfail, " FAILURES")), " ====");
