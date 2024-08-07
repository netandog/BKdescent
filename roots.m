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
 
