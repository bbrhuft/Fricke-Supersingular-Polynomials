\\ identities13.gp -- exact checks of the characteristic-zero identities used in the level-13 proof.
\\ PARI/GP >= 2.13.  Run: gp -q identities13.gp
PREC = 200;
default(seriesprecision, PREC+5);
nfail = 0;
chk(name, ok) = { print(if(ok,"PASS  ","FAIL  "), name); if(!ok, nfail++); }
chs(name, dif) = { my(v=valuation(dif,q)); print(if(dif==0 && v>=150,"PASS  ","FAIL  "), name, "   [difference = O(q^", v, ")]"); if(!(dif==0 && v>=150), nfail++); }
D(F) = q*deriv(F,q);
Eis(k) = 1 - 2*k/bernfrac(k)*sum(n=1,PREC, sigma(n,k-1)*q^n) + O(q^(PREC+1));
E2s = Eis(2); E4s = Eis(4); E6s = Eis(6);
Dels = q*eta(q+O(q^(PREC+1)))^24;
js = E4s^3/Dels;

d2 = h^2+6*h+13; d3 = h^2+5*h+13;
v4 = h^4+247*h^3+3380*h^2+15379*h+28561;
v6 = h^6-494*h^5-20618*h^4-237276*h^3-1313806*h^2-3712930*h-4826809;
jn = d3*v4^3;

print("---- level 13 ----");
hs  = (eta(q+O(q^(PREC+1)))/eta(q^13+O(q^(PREC+1))))^2/q;
fs  = (13*subst(E2s,q,q^13) - E2s)/12;
ev(P) = subst(P,h,hs);
chs("J1  D(h) = -f*h", D(hs)+fs*hs);
chs("J2  j = d3*v4^3/h^13", js - ev(jn)/hs^13);
chs("J3  E4 = f^2*v4/(d2*d3)", E4s - fs^2*ev(v4)/(ev(d2)*ev(d3)));
chs("J4  E6 = f^3*v6/(d2*d3^2)", E6s - fs^3*ev(v6)/(ev(d2)*ev(d3)^2));
chs("J5  Delta = f^6*h^13/(d2^3*d3^4)", Dels - fs^6*hs^13/(ev(d2)^3*ev(d3)^4));
\\ uniformizing equation input: Phi = w(1+23w+165w^2+381w^3)/(l2^2 l3^2), w = h/(h^2+13)
ws = hs/(hs^2+13);
Phi = (2*fs*D(D(fs)) - 3*D(fs)^2)/(4*fs^4);
Rw(x) = (1+23*x+165*x^2+381*x^3)/((1+6*x)^2*(1+5*x)^2);
chs("J6  (2fD^2f-3(Df)^2)/(4f^4) = w*R(w)", Phi - ws*Rw(ws));
chk("J7  j - 1728 = d2*v6^2/h^13", jn - 1728*h^13 == d2*v6^2);
chk("J8  (h-13/h)^2 = t^2-52 with t=h+13/h", (h-13/h)^2 == (h+13/h)^2-52);
chk("J9  d2 = h*(t+6), d3 = h*(t+5)", d2 == h*((h+13/h)+6) && d3 == h*((h+13/h)+5));
chk("J10 d2(13/h)=13 d2/h^2, d3(13/h)=13 d3/h^2", subst(d2,h,13/h) == 13*d2/h^2 && subst(d3,h,13/h) == 13*d3/h^2);
\\ modular relation R13(J,t) := Res_h(h^2 - t h + 13, J h^13 - jn)/13^13
R13 = polresultant(h^2 - t*h + 13, J*h^13 - jn, h)/13^13;
chk("J11 R13 is monic of degree 2 in J with integer coefficients", poldegree(R13,J)==2 && polcoeff(R13,2,J)==1 && denominator(content(R13))==1);
chk("J12 R13(J,h+13/h) = (J-j(h))(J-j(13/h))", subst(R13,t,h+13/h) == (J-jn/h^13)*(J-subst(jn,h,13/h)/(13/h)^13));
trR = -polcoeff(R13,1,J); nmR = polcoeff(R13,0,J);
print("     trR = ", factor(trR)); print("     nmR  = ", factor(nmR));
{ chk("J13 R13 agrees with the pilot's trace/norm",
    trR == (t+5)*(t^4+7*t^3-32*t^2-254*t-180)*(t^8+14*t^7-15*t^6-956*t^5-2895*t^4+12974*t^3+60805*t^2-10836*t-194076)
 && nmR == (t+5)^2*(t^4+254*t^3+5077*t^2+34092*t+75492)^3); }
\\ q-expansion of t: t = q^-1 - 2 + O(q), so Nakaya's normalized j_13^* (constant term 0) is t + 2
chk("J14 t = q^-1 - 2 + O(q)", valuation(hs + 13/hs - 1/q + 2, q) >= 1);
\\ discriminants and resultants for the squarefreeness argument
{ dG = poldisc(jn - J*h^13, h); }
print("     disc_h(jn - J h^13) = ", factor(content(dG)), " * ", factor(dG/content(dG)));
{ chk("B1  disc_h(jn - J h^13) = c J^a (J-1728)^b with c supported on {2,3,13}",
    setminus(Set(factor(content(dG))[,1]~), Set([2,3,13])) == [] &&
    #select(x->poldegree(x)>0 && x!=J && x!=J-1728, factor(dG/content(dG))[,1]~) == 0); }
{ lst = [poldisc(v4), poldisc(v6), poldisc(d2), poldisc(d3), polresultant(v4,v6), polresultant(v4,d2), polresultant(v4,d3),
       polresultant(v6,d2), polresultant(v6,d3), polresultant(d2,d3), polresultant(h^2-13,d2), polresultant(h^2-13,d3),
       polcoeff(v4,0), polcoeff(v6,0), polcoeff(jn,0), 52*4+0, (-6)^2-52, (-5)^2-52]; }
print("     auxiliary quantities: ", apply(x->factor(x), lst));
{ chk("B2  all auxiliary discriminants/resultants supported on {2,3,13}",
    vecprod(apply(x->(setminus(Set(factor(abs(x))[,1]~), Set([2,3,13]))==[]), lst)) == 1); }

\\ ---- the eight gauged operators ----
s = 1-52*w^2; l2 = 1+6*w; l3 = 1+5*w; R = Rw(w);
LGop(Y) = w*s*deriv(deriv(Y,w),w) + (s + w*deriv(s,w)/2)*deriv(Y,w) - R*Y;
opABC(ep,dl,mu) = { my(ab=-(1+2*ep)/4, bb=-(1+dl)/3, C, A, B, C0);
  C = 6*ab/l2 + 5*bb/l3 - mu*deriv(s,w)/(2*s);
  A = w*s*l2*l3;
  B = l2*l3*(s + w*deriv(s,w)/2 - 2*w*s*C);
  C0 = l2*l3*(w*s*(C^2 - deriv(C,w)) - (s + w*deriv(s,w)/2)*C - R);
  [A, B, C0]; }
\\ G(w) as a power series in w: invert w(q) and take sqrt(f)
{
  my(N=150, wq = ws + O(q^(N+1)), qw, Gw);
  qw = serreverse(wq);          \\ q as a series in the variable q (read as w)
  Gw = subst(sqrt(fs + O(q^(N+1))), q, qw);   \\ G(w), variable named q
  Gw = subst(Gw, q, w);
  chk("G0  G(w) = sqrt(f) has coefficients in Z[1/2] (to w^150)", vecprod(apply(c->(denominator(c)==2^valuation(denominator(c),2)), Vec(Gw))) == 1);
  chk("G1  L_G G = 0 in Q[[w]] (to w^148)", valuation(LGop(Gw), w) >= 148);
  for(ep=0,1, for(dl=0,1, for(mu=0,1,
    my(o = opABC(ep,dl,mu), A=o[1], B=o[2], C0=o[3], ab=-(1+2*ep)/4, bb=-(1+dl)/3, Y);
    my(poly = (type(A)=="t_POL" || poldegree(A)>=0) && denominator(B)==1 && denominator(C0)==1 && type(B)=="t_POL" && type(C0)=="t_POL");
    chk(Str("O", ep,dl,mu, "  operator (A,B,C0) polynomial, degrees ", [poldegree(A),poldegree(B),poldegree(C0)], ", A0=0, A1=B0=1"),
        poly && poldegree(A)==5 && poldegree(B)<=4 && poldegree(C0)<=3 && polcoeff(A,0)==0 && polcoeff(A,1)==1 && polcoeff(B,0)==1
        && setminus(Set(concat(apply(c->factor(denominator(c))[,1]~, concat(Vec(B),Vec(C0))))), Set([2,3])) == []);
    Y = (l2+O(w^N))^ab * (l3+O(w^N))^bb * (s+O(w^N))^(-mu/2) * Gw;
    chk(Str("Y", ep,dl,mu, "  (A d^2 + B d + C0) [l2^ab l3^bb s^(-mu/2) G] = 0 (to w^145)"),
        valuation(A*deriv(deriv(Y,w),w) + B*deriv(Y,w) + C0*Y, w) >= 145))));
}
\\ double-pole condition: for symbolic exponents the operator is polynomial iff ab, bb are local exponents
{
  my(C, C0);
  C = 6*xa/l2 + 5*xb/l3;
  C0 = l2*l3*(w*s*(C^2 - deriv(C,w)) - (s + w*deriv(s,w)/2)*C - R);
  my(r2 = subst(numerator(C0*(l2*l3)), w, -1/6), r3 = subst(numerator(C0*(l2*l3)), w, -1/5));
  print("     double-pole residue at l2=0: ", factor(r2), " ;  at l3=0: ", factor(r3));
  chk("E1  local exponents: l2 -> {-1/4,-3/4}, l3 -> {-1/3,-2/3}",
      subst(subst(r2,xa,-1/4),xb,0)==0 && subst(subst(r2,xa,-3/4),xb,0)==0 && subst(subst(r3,xb,-1/3),xa,0)==0 && subst(subst(r3,xb,-2/3),xa,0)==0);
}
print("==== identities13.gp: ", if(nfail==0, "ALL CHECKS PASSED", Str(nfail, " FAILURES")), " ====");
