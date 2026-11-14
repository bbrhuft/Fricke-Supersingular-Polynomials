\\ p11_counterexample.gp -- exact reproduction of the discrepancy in the printed Conjecture 1(2) at p = 11.
{
  my(a=-27, qq=-2, be=1/3, ga=1, de=1/2, RN7, ss, S, F);
  RN7 = J^2-J*X*(X^2-21*X+8)*(X^4-42*X^3+454*X^2-1008*X-1280)+X^2*(X^2+224*X+448)^3;
  \\ ss_11(J) = J (J - 1728) = J (J - 1) mod 11
  F = factormod(polresultant(J*(J-1728)*Mod(1,11), RN7*Mod(1,11), J), 11);
  S = lift(prod(i=1,#F~, F[i,1]));
  print("S_(7,11)(X) = ", S, "   factors: ", lift(F[,1]~));
  foreach([[-4,"printed  alpha=-m7=-4"],[-3,"corrected alpha=delta_p-m7=-3"]], v,
    my(al=v[1], ep=al+be+1-ga-de, c1, c2, c3);
    c1 = qq/(ga*a);
    c2 = ((1*((0+ga)*(1+a)+a*de+ep)+qq)*c1 - (0+al)*(0+be)*1)/(2*(1+ga)*a);
    c3 = ((2*((1+ga)*(1+a)+a*de+ep)+qq)*c2 - (1+al)*(1+be)*c1)/(3*(2+ga)*a);
    print(v[2], ":  c1=", c1, "  c2=", c2, "  c3=", c3,
          "   =>  X^4*(1 + 27c1/X + 27^2c2/X^2 + 27^3c3/X^3) = X^4 + ", lift(Mod(27*c1,11)), " X^3 + ", lift(Mod(27^2*c2,11)), " X^2 + ", lift(Mod(27^3*c3,11)), " X  (mod 11)"));
}
