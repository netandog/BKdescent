R<x>:=PolynomialRing(Rationals());
f:=x^5-16*x+8;
K<a>:=NumberField(f);
S<t>:=PolynomialRing(K);
L<b>:=ext<K|Factorisation(S!f)[2][1]>;
// at some point, write code to define K(alpha+beta) intrinsically ...
H:=Factorisation(Norm(MinimalPolynomial(a+b)))[1][1];
// defining poly of a+b.
K0<ab>:=NumberField(H);
O:=MaximalOrder(K0);
I:=ideal<O|2>;
S,g:=SUnitGroup(I);
A:=[K0!g(S.i):i in [1..Ngens(S)]];
S,g:=UnitGroup(K0);
B:=[K0!g(S.i):i in [1..Ngens(S)]];
SS,g:=SUnitGroup(ideal<MaximalOrder(K)|2*139*449>);
A0:=[K!g(SS.i):i in [1..Ngens(S)]];

print "#A,#A0",#A,#A0;

FindMod2Class:=function(A,x);
n:=#A;
VV:=VectorSpace(GF(2),n);
for v in VV do
w:=[Integers()!v[i]:i in [1..n]];
c:=&*[A[i]^w[i]:i in [1..n]];
if IsSquare(c*x) then
v0:=v;
end if;
end for;
return v0;
end function;

for i in [1..#B] do
c:=&+[B[i][j]*(a+b)^(j-1):j in [1..10]];
c:=Norm(c);
//print FindMod2Class(A0,c);
end for;

// ---- some local 2-adic calculations for K0

O:=RingOfIntegers(K0);
B:=Basis(O);
n:=#B;
M:=[Matrix(GF(2),n,n,[[GF(2)!((B[i]*B[j])[k]):k in [1..n]]:j in [1..n]]):i in [1..n]];

piM:=M[3];
pi:=B[3];
// to compute unit groups we write elements in terms of their pi-adic expansion
VV:=VectorSpace(GF(2),n);
U:={v:v in VV|(&+[v[i]*M[i]:i in [1..n]])^3 eq 1};
U:=[u:u in U];
BU:=[];
for i in [1..#U] do
 beta:=&+[Integers()!U[i][j]*B[j]:j in [1..n]];
 beta:=beta+2*ExactQuotient(beta^3-1,2)*beta;
 BU:=Append(BU,beta);
end for;
pi:=B[3];
MBU:=[&+[M[i]*U[j][i]:i in [1..n]]:j in [1..3]];

MakePiAdicExpansion:=function(f,B,M,BU,MBU,pi,N);
//print "f",f;
n:=#B;
L:=[];
g:=[f[i]:i in [1..n]];
//print "g",g;
for i in [1..N] do
if Determinant(&+[GF(2)!g[i]*M[i]:i in [1..n]]) eq 0 then
// print i,0;
 L:=Append(L,0);
else
 for j in [1..#BU] do
  if Determinant(MBU[j]+&+[GF(2)!g[i]*M[i]:i in [1..n]]) eq 0 then
   L:=Append(L,j);
//   print i,j;
  end if;
 end for;
 end if;
// print "L",L;
 if L[i] ne 0 then
 h:=&+[Integers()!IntegerRing(64)!g[i]*B[i]:i in [1..n]]-BU[L[i]];
 else 
 h:=&+[Integers()!IntegerRing(64)!g[i]*B[i]:i in [1..n]];
  end if;
 h:=ExactQuotient(h,pi);
// print g,h;
 g:=[Integers()!IntegerRing(64)!(h[i]):i in [1..n]];
 end for;
 return L;
 end function;

TwoClModSq:=function(f,B,M,BU,MBU,pi:findroot:=false);
u:=2/pi^5;
uclass:=MakePiAdicExpansion(u,B,M,BU,MBU,pi,3)[1];
LL:=[];
LL2:=[];
L:=MakePiAdicExpansion(f,B,M,BU,MBU,pi,8);
if L[1] eq 0 then
 print "This doesn't have valuation zero";
 return 0;
end if;
g:=f*BU[L[1]]^2;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,3);
if L[2] ne 0 then
g:=g*(1+pi*BU[L[2]]);
LL:=Append(LL,L[2]);
else
LL:=Append(LL,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,8);
if L[3] ne 0 then
g:=g*(1+pi*BU[L[3]]^2)^2;
LL2:=Append(LL2,L[3]);
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,8);
if L[4] ne 0 then
g:=g*(1+pi^3*BU[L[4]]);
LL:=Append(LL,L[4]);
else
LL:=Append(LL,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,8);
if L[5] ne 0 then
g:=g*(1+pi^2*BU[L[5]]^2)^2;
LL2:=Append(LL2,L[5]);
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,8);
if L[6] ne 0 then
g:=g*(1+pi^5*BU[L[6]]);
LL:=Append(LL,L[6]);
else
LL:=Append(LL,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,8);
if L[7] ne 0 then
g:=g*(1+pi^3*BU[L[7]]^2)^2;
LL2:=Append(LL2,L[7]);
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,8);
if L[8] ne 0 then
g:=g*(1+pi^7*BU[L[8]]);
LL:=Append(LL,L[8]);
else
LL:=Append(LL,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,9);
if L[9] ne 0 then
g:=g*(1+pi^4*BU[L[9]]^2)^2;
LL2:=Append(LL2,L[9]);
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,10);
if L[10] ne 0 then
g:=g*(1+pi^9*BU[L[10]]);
LL:=Append(LL,L[10]);
else
LL:=Append(LL,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,11);
if L[11] in {0,uclass} then
LL:=Append(LL,0);
if L[11] eq uclass then
LL2:=Append(LL2,1);
else
LL2:=Append(LL2,0);
end if;
else
LL:=Append(LL,1);
end if;
if findroot eq true then
if #B eq 3 then
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,12);
if L[12] ne 0 then
nuclass:=Integers()!(GF(3)!(-uclass+L[12]))+2;
LL2:=Append(LL2,nuclass);
g:=g*(1+pi^6*BU[L[nuclass]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,13);
if L[13] ne 0 then
nuclass:=Integers()!(GF(3)!(-uclass+L[13]))+2;
LL2:=Append(LL2,nuclass);
g:=g*(1+pi^7*BU[L[nuclass]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,14);
if L[14] ne 0 then
nuclass:=Integers()!(GF(3)!(-uclass+L[14]))+2;
LL2:=Append(LL2,nuclass);
g:=g*(1+pi^8*BU[L[nuclass]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,15);
if L[15] ne 0 then
nuclass:=Integers()!(GF(3)!(-uclass+L[15]))+2;
LL2:=Append(LL2,nuclass);
g:=g*(1+pi^9*BU[L[nuclass]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,16);
if L[16] ne 0 then
nuclass:=Integers()!(GF(3)!(-uclass+L[16]))+2;
LL2:=Append(LL2,nuclass);
g:=g*(1+pi^10*BU[L[nuclass]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,17);
if L[17] ne 0 then
nuclass:=Integers()!(GF(3)!(-uclass+L[17]))+2;
LL2:=Append(LL2,nuclass);
g:=g*(1+pi^11*BU[L[nuclass]])^2;
else
LL2:=Append(LL2,0);
end if;
else

L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,12);
if L[12] ne 0 then
LL2:=Append(LL2,L[12]);
g:=g*(1+pi^6*BU[L[12]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,13);
if L[13] ne 0 then
LL2:=Append(LL2,L[13]);
g:=g*(1+pi^7*BU[L[13]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,14);
if L[14] ne 0 then
LL2:=Append(LL2,L[14]);
g:=g*(1+pi^8*BU[L[14]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,15);
if L[15] ne 0 then
LL2:=Append(LL2,L[15]);
g:=g*(1+pi^9*BU[L[15]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,16);
if L[16] ne 0 then
LL2:=Append(LL2,L[16]);
g:=g*(1+pi^10*BU[L[16]])^2;
else
LL2:=Append(LL2,0);
end if;
L:=MakePiAdicExpansion(g,B,M,BU,MBU,pi,17);
if L[17] ne 0 then
LL2:=Append(LL2,L[17]);
g:=g*(1+pi^11*BU[L[17]])^2;
else
LL2:=Append(LL2,0);
end if;
end if;
end if;
return LL,LL2;
end function;

ModTwoLoc:=function(v,B,M,BU,MBU,KB,pi:giveLL2:=false);
n:=#B;
BMX:=Matrix(Rationals(),n,n,[[(KB!B[i])[j]:j in [1..n]]:i in [1..n]]);
w:=Vector(Rationals(),n,[v[i]:i in [1..n]]);
w:=w*BMX^(-1);
D:=Minimum([Valuation(w[i],2):i in [1..n]]);
w:=2^(-D)*w;
valn:=5*D;
w0:=&+[w[i]*B[i]:i in [1..n]];
w0:=w0*2^D/pi^(5*D);
for i in [1..5] do
 if Determinant(&+[GF(2)!w[i]*M[i]:i in [1..n]]) eq 0 then
  w0:=w0/pi;
  valn:=valn+1;
  w:=[w0[i]:i in [1..n]];
 end if;
end for;
if giveLL2 eq false then
 abc:=TwoClModSq(w0,B,M,BU,MBU,pi);
 return valn,abc;
else
 abc1,abc2:=TwoClModSq(w0,B,M,BU,MBU,pi:findroot:=true);
 return valn,abc1,abc2;
end if;
end function;

FindTheRoot:=function(v,B,M,BU,MBU,KB,pi);
valn:=Valuation(Norm(v),2);
e:=ExactQuotient(valn,2);
c:=v/pi^(2*e);
L:=[0,0,0];
if Valuation(Norm(c-1),2) eq 2 then
 L[1]:=1;
 c:=c/(1+pi)^2;
end if;
if Valuation(Norm(c-1),2) eq 4 then
 L[2]:=1;
 c:=c/(1+pi^2)^2;
end if;
if Valuation(Norm(c-1),2) eq 6 then
 L[3]:=1;
 c:=c/(1+pi^3)^2;
end if;
Logc:=&+[-(1-c)^i/i:i in [1..50]];
Logc:=&+[Rationals()!pAdicField(2,32)!Logc[i]*(Parent(v).1)^(i-1):i in [1..5]];
I:=1/2*Logc;
expI:=&+[I^i/Factorial(i):i in [0..50]];
expI:=&+[Rationals()!pAdicField(2,32)!expI[i]*(Parent(v).1)^(i-1):i in [1..5]];
//print "e",e;
//print "L",L;
//print "expI",expI;
return pi^e*(1+pi)^L[1]*(1+pi^2)^L[2]*(1+pi^3)^L[3]*expI;
end function;



FindTheRootOld:=function(v,B,M,BU,MBU,KB,pi);
u:=2/pi^5;
uclass:=MakePiAdicExpansion(u,B,M,BU,MBU,pi,3)[1];
aa,bb,cc:=ModTwoLoc(v,B,M,BU,MBU,KB,pi:giveLL2:=true);
//print cc;
v:=Parent(pi)!1;
for i in [1..4] do
if cc[i] ne 0 then
v:=v*(1+pi^i*BU[cc[i]]^2);
end if;
end for;
if cc[5] ne 0 then
 if uclass ne 1 then
  v:=v*(1+pi^5*BU[1]);
 else
  v:=v*(1+pi^5);
 end if;
end if;
for i in [6..11] do
 if cc[i] ne 0 then
 v:=v*(1+BU[cc[i]]*pi^i);
 end if;
end for;
a2:=ExactQuotient(aa,2);
return v*pi^a2;
end function;

// ---- some local 2-adic calculations for K

O0:=RingOfIntegers(K);
B0:=Basis(O0);
n0:=#B0;
M0:=[Matrix(GF(2),n0,n0,[[GF(2)!((B0[i]*B0[j])[k]):k in [1..n0]]:j in [1..n0]]):i in [1..n0]];
B0U:=[B0[1]];
MB0U:=[M0[1]];
pi0:=B0[3];

rootfinder:=function(a,b,d);
 // if a1+a2*rd is a square, finds a root.
 // where rd =sqrt(d)
if a eq 0 then
if IsSquare(b/d) then
o,e:=IsSquare(b/d);
return true,e,Parent(a)!0;
else
return false,0,0;
end if;
end if;
nm:=a^2-d*b^2;
if IsSquare(nm) eq true then
o,c:=IsSquare(nm);
print "c",c;
if IsSquare(2*(a+c)) and a ne -c then
o,e:=IsSquare(2*(a+c));
print "e",e;
return  true,(a+c)/e,b/e;
elif IsSquare(2*(a-c)) and a ne c then
o,e:=IsSquare(2*(a-c));
print "e",e;
return  true,(a-c)/e,b/e;
else
return false,0,0;
end if;
else
return false,0,0;
end if;
end function;

rootfinder2adicK:=function(alpha,beta,d);
 // if a1+a2*rd is a square, finds a root.
 // where rd =sqrt(d)
// like rootfinder, but working in KotimesQ_2,
// so we check for / find roots using Mod2Loc etc.
if alpha eq 0 then
 if IsSquare(beta/d) then
  o,e:=IsSquare(beta/d);
  return true,e,Parent(alpha)!0;
 else
  return false,0,0;
 end if;
end if;
nm:=alpha^2-d*beta^2;
print "norm",nm;
a1,a2:=ModTwoLoc(nm,B0,M0,B0U,MB0U,K,pi0);
print a1,a2;
if Integers()!GF(2)!a1+&+a2 eq 0 then
 print "its zero";
 print FindTheRoot(nm,B0,M0,B0U,MB0U,K,pi0);
 c:=K!FindTheRoot(nm,B0,M0,B0U,MB0U,K,pi0);
 print "c",c;
 if K!alpha+K!c ne 0 then
  print "alpha",alpha,"c",c;
  b1,b2:=ModTwoLoc(2*(alpha+c),B0,M0,B0U,MB0U,K,pi0);
  print "b1b2",b1,b2;
  if Integers()!GF(2)!b1+&+b2 eq 0 then
   e:=Parent(a)!FindTheRoot(2*(alpha+c),B0,M0,B0U,MB0U,K,pi0);
   return  true,(alpha+c)/e,beta/e;
  elif K!alpha-K!c ne 0 then
   b1,b2:=ModTwoLoc(2*(alpha-c),B0,M0,B0U,MB0U,K,pi0);
   if Integers()!GF(2)!b1+&+b2 eq 0 then
    e:=Parent(a)!FindTheRoot(2*(alpha-c),B0,M0,B0U,MB0U,K,pi0);
    print "wot",2*(alpha-c);
    print "abce",alpha,c,e,beta;
    return  true,(alpha+c)/e,beta/e;
   else return false,0,0; 
   end if;
  else return false,0,0;
  end if;
 else // if a ne -c
  b1,b2:=ModTwoLoc(2*(alpha-c),B0,M0,B0U,MB0U,K,pi0);
  if b1+&+b2 eq 0 then
   e:=Parent(alpha)!FindTheRoot(2*(alpha-c),B0,M0,B0U,MB0U,K,pi0);
   print "abce",alpha,c,e,beta;
   return  true,(alpha-c)/e,beta/e;
  else return false,0,0;
  end if;
 end if;
else
 return false,0,0;
end if;
end function;
 



// ---

MakeHVector:=function(v,B,M,BU,MBU,KB,pi);
valn,L:=ModTwoLoc(v,B,M,BU,MBU,KB,pi);
v:=Vector(GF(2),12,[0:i in [1..12]]);
v[1]:=GF(2)!valn;
if L[6] ne 0 then
v[2]:=1;
end if;
for i in [1..5] do
if L[i] eq 1 then
v[2*i+1]:=1;
end if;
if L[i] eq 2 then
v[2*i+2]:=1;
end if;
if L[i] eq 3 then
v[2*i+2]:=1;
v[2*i+1]:=1;
end if;
end for;
return v;
end function;

// -- find class

findL0element:=function(c);
// given g(a) in K, writes g(a)+g(b) in terms of basis of L0.
HH:=PolynomialRing(K0)!Norm(MinimalPolynomial(a*b));
ct:=-Coefficient(Factorisation(HH)[1][1],0);
sympolys:=[K0!2,ab,ab^2-2*ct,ab^3-3*ab*ct,ab^4-4*ct*ab^2+2*ct^2];
return &+[K0!c[i]*sympolys[i]:i in [1..5]];
end function;

findL0element2:=function(c);
// given g(a) in K, writes g(a)*g(b) in terms of basis of L0.
end function;


testclass:=function(i,constan:pl:=0);
plusminus:=0;
const0:=constan-a;
const1:=K!2^4;
const2:=K0!2;
 a2b2:=findL0element(a^2);
 c1:=(K!i-a)/const0;
 if pl gt 0 then print c1;
 end if;
 c2,c3:=ModTwoLoc(c1,B0,M0,B0U,MB0U,K,pi0);
 if pl gt 0 then print "first mod2loc",ModTwoLoc(c1,B0,M0,B0U,MB0U,K,pi0);
 end if;
 if Integers()!GF(2)!c2+&+c3 eq 0 then
  ua:=K!FindTheRoot(c1,B0,M0,B0U,MB0U,K,pi0);
  if pl gt 0 then print "ua",ua; end if;
  c40:=1+(ua*(const0)-&+[(ua*const0)[i]*b^(i-1):i in [1..5]])/(b-a);
  if pl gt 0 then
   print "c40",c40;
  end if;
  if c40 eq 0 then
   c40:=Parent(b)!2;
   ua:=-ua;
  end if;
  c51:=findL0element(ua);
  c53:=findL0element(ua*const0^2);
  c54:=findL0element(const0);
  c55:=findL0element(const0^2);
  c52:=1+(c53-1/2*(c54^2-c55)*c51)/(-ab^2+2*a2b2);
  c6:=Norm(c40)/const1;
  if pl gt 0 then
   print "Is this even square?",IsSquare(pAdicField(2,100)!Norm(c6));
  end if;
  c7,c8:=ModTwoLoc(c6,B0,M0,B0U,MB0U,K,pi0);
  if pl gt 1 then
  print c51,c52,c7,c8; end if;
  if Integers()!GF(2)!c7+&+c8 eq 0 then
   if pl gt 0 then print c52/Parent(c52)!const2;
 print "root",K!FindTheRoot(c6,B0,M0,B0U,MB0U,K,pi0);  
 end if;
   vv:=MakeHVector(c52/Parent(c52)!const2,B,M,BU,MBU,K0,pi);
   return true,vv;
  else
  ua:=-K!FindTheRoot(c1,B0,M0,B0U,MB0U,K,pi0);
  c40:=1+(ua*(const0)-&+[(ua*const0)[i]*b^(i-1):i in [1..5]])/(b-a);
  if pl gt 0 then print "c40 again",c40; end if;
  c51:=findL0element(ua);
  c53:=findL0element(ua*const0^2);
  c52:=1+(c53-1/2*(c54^2-c55)*c51)/(-ab^2+2*a2b2);
  c6:=Norm(c40)/const1;
  c7,c8:=ModTwoLoc(c6,B0,M0,B0U,MB0U,K,pi0);
  if pl gt 1 then
  print c51,c52,c7,c8; end if;
  if Integers()!GF(2)!c7+&+c8 eq 0 then
   if pl gt 0 then print "now this works",c52/Parent(c52)!const2;
   print "root",K!FindTheRoot(c6,B0,M0,B0U,MB0U,K,pi0);
   end if;
   vv:=MakeHVector(c52/Parent(c52)!const2,B,M,BU,MBU,K0,pi);
   return true,vv;
  end if;

  end if;
 end if;
return false,0;
end function;


testclassquadratic:=function(i1,i2,constan,d);
// basepoint calculations

const0:=constan-a;
const1:=Norm(1-(const0-&+[const0[i]*b^(i-1):i in [1..5]])/(b-a));
if const1 ne 0 then
 a2b2:=findL0element(a^2);
 const2:=1-(3*a2b2-ab^2)/(-ab^2+2*a2b2);
else
 const1:=Norm(1+(const0-&+[const0[i]*b^(i-1):i in [1..5]])/(b-a));
 a2b2:=findL0element(a^2);
 const2:=1+(3*a2b2-ab^2)/(-ab^2+2*a2b2);
end if;

// point calculations.

//load "roots.m";

a1,a2,a3:=rootfinder2adicK((i1-a)/const0,(K!i2)/const0,d);
if a1 eq true then
 ua1:=a2;
 ua2:=a3; 
 c401:=1-(ua1*(const0)-&+[(ua1*const0)[i]*b^(i-1):i in [1..5]])/(b-a);
 c402:=(ua2*const0-&+[(ua2*const0)[i]*b^(i-1):i in [1..5]])/(b-a);
 // more complicated to calculate the norm in this case
  Lt<Lx>:=PolynomialRing(L);
  normpoly:=Norm(c401+Lx*c402);
  normc41:=K!0;
  normc42:=K!0;
  for i in [1..Degree(normpoly)] do
   if IsEven(i) then
    normc41:=normc41+d^ExactQuotient(i,2)*Coefficient(normpoly,i);
   else
    normc42:=normc42+d^ExactQuotient(i-1,2)*Coefficient(normpoly,i);
   end if;
  end for;
  a1,a2,a3:=rootfinder2adicK(normc41/const0,normc42/const0,d);
  c511:=findL0element(ua1);
  c512:=findL0element(ua2);
  c50:=findL0element(a^2);
  c521:=1-(3/2*c50*c511-1/2*ab^2*c511)/(-ab^2+2*c50);
  c522:=-(3/2*c50*c512-1/2*ab^2*c512)/(-ab^2+2*c50);
  if a1 eq true then
   vv:=MakeHVector(c521^2-d*c522,B,M,BU,MBU,K0,pi);
   return true,vv;
  end if;
 else
  return false,0;
 end if;
end function;
// --- examples

S:=[];
constans:=[0,2,-2,4,6];

projectedclass:=function(i,constan:pl:=0);
plusminus:=0;
const0:=constan-a;
const1:=K!2^4;
const2:=K0!2;
 a2b2:=findL0element(a^2);
 c1:=(K!i-a)/const0;
 if pl gt 0 then print c1;
 end if;
 c2,c3:=ModTwoLoc(c1,B0,M0,B0U,MB0U,K,pi0);
 if pl gt 0 then print c2,c3;
 end if;
 if Integers()!GF(2)!c2+&+c3 eq 0 then
  ua:=K!FindTheRoot(c1,B0,M0,B0U,MB0U,K,pi0);
  c40:=1+(ua*(const0)-&+[(ua*const0)[i]*b^(i-1):i in [1..5]])/(b-a);
  if c40 eq 0 then
   c40:=Parent(b)!2;
   ua:=-ua;
  end if;
  c51:=findL0element(ua);
  c53:=findL0element(ua*const0^2);
  c54:=findL0element(const0);
  c55:=findL0element(const0^2);
  c52:=1+(c53-1/2*(c54^2-c55)*c51)/(-ab^2+2*a2b2);
  c6:=Norm(c40)/const1;
  c7,c8:=ModTwoLoc(c6,B0,M0,B0U,MB0U,K,pi0);
  if pl gt 1 then
  print c51,c52,c7,c8; end if;
  if Integers()!GF(2)!c7+&+c8 eq 0 then
   if pl gt 0 then print c52/Parent(c52)!const2;
 print "root",K!FindTheRoot(c6,B0,M0,B0U,MB0U,K,pi0);  
 end if;
   vv:=MakeHVector(c52/Parent(c52)!const2,B,M,BU,MBU,K0,pi);
   return true,vv;
  else
  ua:=-K!FindTheRoot(c1,B0,M0,B0U,MB0U,K,pi0);
  c40:=1+(ua*(const0)-&+[(ua*const0)[i]*b^(i-1):i in [1..5]])/(b-a);
  c51:=findL0element(ua);
  c53:=findL0element(ua*const0^2);
  c52:=1+(c53-1/2*(c54^2-c55)*c51)/(-ab^2+2*a2b2);
  c6:=Norm(c40)/const1;
  c7,c8:=ModTwoLoc(c6,B0,M0,B0U,MB0U,K,pi0);
  if pl gt 1 then
  print c51,c52,c7,c8; end if;
  if Integers()!GF(2)!c7+&+c8 eq 0 then
   if pl gt 0 then print c52/Parent(c52)!const2;
   print "root",K!FindTheRoot(c6,B0,M0,B0U,MB0U,K,pi0);
   end if;
   vv:=MakeHVector(c52/Parent(c52)!const2,B,M,BU,MBU,K0,pi);
   return true,vv;
  end if;

  end if;
 end if;
return false,0;
end function;


// ---------------------------------

f2:=2*f;
CrystallineList:=[];
Q2:=pAdicField(2,100);
 for i in constans do
  for j0 in [-1000..1000] do
   j:=j0/2;
   if IsSquare(Q2!Evaluate(f2,j)) then
    t1,t2:=projectedclass(i,j);
    if t1 eq true then
     Clist:=Append(CrystallineList,t2);
     Mx:=Matrix(GF(2),#Clist,12,[[Clist[i][j]:j in [1..12]]:i in [1..#Clist]]);
     if Rank(Mx) gt Rank(Submatrix(Mx,1,1,#Clist-1,12)) then
      CrystallineList:=Append(CrystallineList,t2);
      print #CrystallineList;
     end if;
    end if;
   end if;
  end for;
 end for;
CList:=Append(CrystallineList,MakeHVector(K0!-1,B,M,BU,MBU,K0,pi));
