// input n-generator subgroup of SL(2, Q) and a prime p
// output: 
//   true, _                      if G is both discrete and free in SL(2, Q_p)
//   false, witness               if not both 
//   failed, number of steps	if iterations go above certain limit
//   inconclusive, current gens   if further investigation needed

IsDiscreteAndFree := function (G, p: Limit := 10^3)
   assert Type (G) eq GrpMat; 
   g := [G.i: i in [1..Ngens (G)]];

   // initialise generators of SLP group 
   S := SLPGroup (Ngens (G));
   s := [S.i: i in [1..Ngens (G)]];

   // define translation length of matrix in SL(2, Q_p)
   TL := function (m) 
      return -2*Min (0, Valuation (pAdicField (p)!Trace (m)));
   end function; 

   // this is the quantity that reduces at each step:
   // the sum of translation lengths of all n generators
   // and all pairs of products g_i*g_j and g_i^-1*g_j
   Sum := function(g)
      sum := 0;
      for i in [1..#g] do
         sum +:= TL (g[i]);
         for j in [i+1..#g] do
            a := TL (g[i]*g[j]); b := TL (g[i]^-1*g[j]);
            sum +:= a + b;
         end for;
      end for;
      return sum;
   end function;

   // the following two functions check whether or not
   // each pair and each triple of generators satisfies
   // the Ping Pong Lemma. If both return true then the
   // group is indeed both discrete and free
   

   CheckPairs := function (g)
      for i in [1..#g] do
         for j in [i+1..#g] do
            li := TL (g[i]); lj := TL (g[j]); 
            a := TL (g[i]*g[j]); b := TL (g[i]^-1 * g[j]); m := Min (a, b);
            if m le Abs (li - lj) and Max (li, lj) eq li and m eq a then
               return false, i, i, 1, j;
            elif m le Abs (li - lj) and Max (li, lj) eq li and m eq b then
               return false, i, i, -1, j;
            elif m le Abs (li - lj) and Max (li, lj) eq lj and m eq a then
               return false, j, i, 1, j;
            elif m le Abs (li - lj) and Max (li, lj) eq lj and m eq b then
               return false, j, i, -1, j;
            end if;
         end for;
      end for;
      return true, _ , _ , _ , _;
   end function;

   CheckTrips := function (g)
      for i in [1..#g] do
         for j in [i+1..#g] do
            for k in [j+1..#g] do
               a := g[i]; b := g[j]; c := g[k]; 
               m1 := TL (a*b*c);    m2 := TL (a^-1*b*c);    m3 := TL (a*b^-1*c);    m4 := TL (a^-1*b^-1*c);
               m5 := TL (a*b*c^-1); m6 := TL (a^-1*b*c^-1); m7 := TL (a*b^-1*c^-1); m8 := TL (a^-1*b^-1*c^-1);
               m, pos := Min ([ m1, m2, m3, m4, m5, m6, m7, m8 ]);
               ei := pos in {1, 3, 5, 7} select 1 else -1;
               ej := pos in {1, 2, 5, 6} select 1 else -1;
               ek := pos in {1, 2, 3, 4} select 1 else -1;

               if m eq 0 then
                  return false, 0, i, ei, j, ej, k, ek;
               elif m le Max ([Abs (TL (a^ei*b^ej) - TL(c^ek)), Abs (TL (a^ei*c^ek) - TL(b^ej)), Abs (TL (b^ej*c^ek) - TL(a^ei))]) then
                  return false, 1, i, ei, j, ej, k, ek;
               end if;
            end for;
         end for;
      end for;
      return true, _ , _ , _ , _ , _ , _ , _;
   end function;

   // this function checks if there is j in {1,..,n} and
   // subsets s1, s2 of {1,..,n}\{j} such that replacing
   // each g_i (i in s1) by g_j*g_i and each g_i (i in s2)
   // by g_i*g_j^-1 reduces the quantity Sum
 
   // if there is such j, s1, s2, then the function returns
   // false and instructions on which product 
   // replacements to perform. Otherwise returns true

   Check := function (g)
      for j in [1..#g] do 
         N := { s : s in Exclude([1..#g],j) };
         S := {@ s : s in Subsets(N) @}; 
         for s1, s2 in S do
            h := g;
            for i in [1..#g] do
               if i in s1 then
                  h[i] := h[j]*h[i];
               end if;
               if i in s2 then
                  h[i] := h[i]*h[j]^-1;
               end if;
            end for;
            if Sum(h) lt Sum(g) then
               return false, s1, s2, j;
            end if;
         end for;
      end for;
      return true, _, _, _;
   end function; 

   // this is the start of the algorithm
   // we first check if any generators 
   // are elliptic and return false if so

   nmr := 0;
   repeat
      nmr +:= 1;
      for i in [1..#g] do
         if TL (g[i]) eq 0 then 
            return false, g[i], s[i];
         end if;
      end for;

      // here we check if the Check function passes or fails
      // if it fails, then one performs the relevant product replacements


      flag, a, b, c := Check(g);

      if not flag then
         for i in [1..#g] do
            if i in a then
               g[i] := g[c]*g[i]; s[i] := s[c]*s[i];
            end if;
            if i in b then
               g[i] := g[i]*g[c]^-1; s[i] := s[i]*s[c]^-1;
            end if;
         end for;
      end if;

   until flag or nmr gt Limit;

   if not flag then error "Failed"; end if;
   "Number of tries is ", nmr;

   // the following part should eventually be able to replaced by
   // "return true, _, _"

   if CheckTrips(g) and CheckPairs(g) then
      return true, _, _;
   else
      return "inconclusive", g, s;
   end if;

end function;

