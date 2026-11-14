\\ finite13.gp -- bounded validation of the level-13 theorem and of each intermediate statement.
\\ Not part of the proof.  Run: gp -q finite13.gp    (edit BOUND)
BOUND = 2000;
kro(a,p) = kronecker(a,p);
rad(P,p) = { my(F=factormod(P,p)); lift(prod(i=1,#F~, F[i,1]))*Mod(1,p); }
ssA(p) = { my(n=p\12, d=(1-kro(-3,p))/2, e=(1-kro(-1,p))/2, c);
  c = sum(k=0,n, binomial(2*n+e,2*k+e)*binomial(2*n-2*k,n-k)*(-432)^(n-k)*(J-1728)^k);
  c = c*Mod(1,p); (J^d*(J-1728)^e*c)/pollead(c); }
d2 = h^2+6*h+13; d3 = h^2+5*h+13;
v4 = h^4+247*h^3+3380*h^2+15379*h+28561;
v6 = h^6-494*h^5-20618*h^4-237276*h^3-1313806*h^2-3712930*h-4826809;
jn = d3*v4^3;
R13 = polresultant(h^2 - t*h + 13, J*h^13 - jn, h)/13^13;
m0 = J^2 - 174668400*J + 10755802087387200;   \\ minimal polynomial of j at t = 0
s = 1-52*w^2; l2 = 1+6*w; l3 = 1+5*w; Rw = (1+23*w+165*w^2+381*w^3)/((1+6*w)^2*(1+5*w)^2);
opABC(ep,dl,mu) = { my(ab=-(1+2*ep)/4, bb=-(1+dl)/3, C, A, B, C0);
  C = 6*ab/l2 + 5*bb/l3 - mu*deriv(s,w)/(2*s);
  A = w*s*l2*l3; B = l2*l3*(s + w*deriv(s,w)/2 - 2*w*s*C);
  C0 = l2*l3*(w*s*(C^2 - deriv(C,w)) - (s + w*deriv(s,w)/2)*C - Rw); [A,B,C0]; }
OPS = vector(8, i, my(b=binary(i-1+8)); opABC(b[2],b[3],b[4]));   \\ index 1+4ep+2dl+mu
nfail = 0; ntest = 0; thetahits = List();
bad(msg) = { nfail++; print("FAIL ", msg); }
one(p) = {
  my(P1=Mod(1,p), ep=(1-kro(-1,p))/2, dl=(1-kro(-3,p))/2, mu=(1-kro(-13,p))/2, k=p\12,
     a=3*k+dl+ep, b=4*k+dl+2*ep, e=a+b, n=e-mu, o=OPS[1+4*ep+2*dl+mu], A, B, C0, g, val, ss, S, Q, cand, Pw, res, theta);
  if(4*a != p-1-2*ep || 3*b != p-1-dl, bad(Str("a,b closed forms p=",p)));
  A = Vec(Polrev(Vecrev(o[1]))*P1); A = Vecrev(o[1]*P1); B = Vecrev(o[2]*P1); C0 = Vecrev(o[3]*P1);
  g = vector(p, i, 0*P1); g[1] = P1;
  for(z=0, p-2,
    val = 0*P1;
    for(i=0, #A-1, my(j=z-i+2); if(j>=0 && j<=z && i!=1, val += A[i+1]*j*(j-1)*g[j+1]));
    for(i=0, #B-1, my(j=z-i+1); if(j>=0 && j<=z, if(!(i==0), val += B[i+1]*j*g[j+1])));
    for(i=0, #C0-1, my(j=z-i); if(j>=0, val += C0[i+1]*g[j+1]));
    \\ coefficient of g_{z+1}: A1*(z+1)*z + B0*(z+1) = (z+1)^2
    g[z+2] = -val/(z+1)^2);
  for(m=n+1, p-1, if(g[m+1]!=0, bad(Str("g_m != 0 beyond n: p=",p," m=",m)); break));
  Pw = sum(i=0, n, g[i+1]*w^i);
  res = o[1]*P1*deriv(deriv(Pw,w),w) + o[2]*P1*deriv(Pw,w) + o[3]*P1*Pw;
  if(res != 0, bad(Str("full ODE residual p=",p)));
  ss = ssA(p);
  S = rad(polresultant(ss, R13*P1, J), p); S = S/pollead(S);
  Q = sum(i=0, n, g[i+1]*t^(n-i));
  cand = (t+6)^ep*(t+5)^dl*(t^2-52)^mu*Q;
  if(cand*P1 != S, bad(Str("MAIN IDENTITY p=",p)));
  if(poldegree(S) != e+ep+dl+mu, bad(Str("degree p=",p)));
  \\ degree of P_p: g_n = Q(0) vanishes exactly when j(t=0) is supersingular (p != 5)
  theta = (p!=5) && (poldegree(gcd(ss, m0*P1)) > 0);
  if((g[n+1]==0) != theta, bad(Str("theta prediction p=",p)));
  if(theta, listput(thetahits, p); if(g[n]==0, bad(Str("g_(n-1)=0 too, p=",p))));
  \\ internal identities of the proof
  my(ft = ss/(J^dl*(J-1728)^ep), jnp=jn*P1, hN=(h*P1)^13, acc=0*P1, Nb, QX=0*P1, tn=(h^2+13)*P1);
  if(denominator(ft)!=1 || poldegree(ft)!=k, bad(Str("KZ shape p=",p)));
  forstep(i=k,0,-1, acc = acc*jnp + polcoeff(ft,i,J)*hN^(k-i));
  Nb = (v4^dl*v6^ep)*P1*acc;
  forstep(i=n,0,-1, QX = QX*tn + polcoeff(Q,i,t)*(h*P1)^(n-i));   \\ h^n Q(t(h))
  if(Nb != (h^2-13)^mu*QX*P1, bad(Str("N_p = h^n (h^2-13)^mu Q(t(h)) p=",p)));
  if(poldegree(Nb) != 2*e, bad(Str("deg N_p p=",p)));
  if(poldegree(gcd(Nb, deriv(Nb,h))) > 0, bad(Str("N_p not squarefree p=",p)));
  if(poldegree(gcd(Nb, h*d2*d3*P1)) > 0, bad(Str("N_p not coprime to h d2 d3 p=",p)));
  my(lhs = subst(lift(Nb), h, 13/h)*h^(2*e));
  if(lhs*P1 != kro(-13,p)*13^e*Nb, bad(Str("Fricke parity p=",p)));
  ntest++;
}
{
  forprime(p=5, BOUND, if(p!=13, one(p)));
  print("tests run: ", ntest, "  (all primes 5 <= p <= ", BOUND, ", p != 13)");
  print("primes where deg P_p = n-1 (j at t=0 supersingular): ", Vec(thetahits));
  print("==== finite13.gp: ", if(nfail==0, "ALL CHECKS PASSED", Str(nfail, " FAILURES")), " ====");
}
