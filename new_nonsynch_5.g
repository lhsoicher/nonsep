LogTo("new_nonsynch_5.log");

degrees_to_check:=[2..624];
only_two_closed:=false;

# Program to determine the nonseparating, and of these, the
# nonsynchronizing, primitive permutation groups having degree 
# in  degrees_to_check.  Only two-closed groups are counted iff the 
# boolean  only_two_closed  has value true. 
#
# Leonard Soicher, 30/11/2024.
#
if not IsSubset([2..4095],degrees_to_check) then
   Error("the GAP primitive groups library restricts the degree to be in [2..4095]"); 
fi;
LoadPackage("grape");
LoadPackage("design");
LoadPackage("fining"); 
LoadPackage("agt");

maxdegree:=Maximum(degrees_to_check);
#
# Now set up a list  nonsynchgraphs  containing graphs 
# in certain known sequences of nonsynchronizing graphs,
# together with a list of corresponding comments.
#
nonsynchgraphs:=[]; 
nonsynchgraphcomments:=[];
#
# Insert the Hamming graphs H(d,q) with d>=2,q>=3, 
# such that these graphs have order <= maxdegree.
# These graphs all have clique number = chromatic number. 
#
d:=2;
q:=3;
while q^d<=maxdegree do
   while q^d<=maxdegree do
      Add(nonsynchgraphs,HammingGraph(d,q));
      Add(nonsynchgraphcomments,
         Concatenation("Hamming graph H(",String(d),",",String(q),")"));
      q:=q+1;
   od;
   d:=d+1;
   q:=3;
od;
#
# Insert the complements of the Kneser graphs K(mr,r) with 
# m>=3,r>=2, such that these graphs have order <= maxdegree.
# These graphs all have clique number = chromatic number. 
# 
# At the same time, insert the graphs on the partitions of 
# [1..mr] into m parts of size r, with m>=3, r>=2, mr>6,
# where two distinct vertices are joined by an edge precisely
# when they have no part in common. These graphs are
# nonsynchronizing due to a result of Peter J. Cameron. See:
# https://cameroncounts.wordpress.com/2019/01/06/a-family-of-non-synchronizing-groups/
# 
r:=2;
m:=3;
while Binomial(m*r,r)<=maxdegree do
   while Binomial(m*r,r)<=maxdegree do
      G:=SymmetricGroup([1..m*r]);
      compKneser:=Graph(G,Combinations([1..m*r],r),OnSets,
         function(x,y) return x<>y and Intersection(x,y)<>[]; end,true);
      Add(nonsynchgraphs,compKneser);
      Add(nonsynchgraphcomments,Concatenation("complement of Kneser graph K(",
         String(m*r),",",String(r),")"));
      if m*r>6 and Factorial(m*r)/(Factorial(r)^m*Factorial(m)) <= maxdegree then
         # make graph on the partitions of [1..m*r] into m parts of size r
         partition:=List([1..m],x->[(x-1)*r+1..x*r]);
         gamma:=Graph(G,Set(Orbit(G,partition,OnSetsDisjointSets)),
            OnSetsDisjointSets,     
            function(x,y) return Intersection(x,y)=[]; end,true);
         Add(nonsynchgraphs,gamma);
         Add(nonsynchgraphcomments,Concatenation(
            "graph on the partitions of [1..",String(m*r),
            "] into subsets of size ",String(r),
            " with two partitions joined by an edge iff they have no part in common")); 
      fi;
      m:=m+1;
   od; 
   r:=r+1;
   m:=3;
od;
#
# Now let m>=13 and m congruent to 1 (mod 6). 
# Then the Johnson graph J(m,3) is non-synchronizing.
# See Section 6.1 of J. Arau´jo, P.J. Cameron and B. Steinberg,
# Between primitive and 2-transitive: Synchronization 
# and its friends, EMS Surv. Math. Sci. 4 (2017), 101-184.
#
m:=13;
while Binomial(m,3)<=maxdegree do
   Add(nonsynchgraphs,JohnsonGraph(m,3));
   Add(nonsynchgraphcomments,
      Concatenation("Johnson graph J(",String(m),",3)"));
   m:=m+6;
od;
#
# The line graph of PG(3,q) is non-synchronizing 
# since PG(3,q) has a resolution (or packing). See:
# R.H.F. Denniston, Some packings of projective spaces,
# Atti Accad. Naz. Lincei, VIII. Ser., Rend., 
# Cl. Sci. Fis. Mat. Nat. 52 (1972), 36-40.
# 
q:=2;
pg:=PG(3,q); 
lines:=AsSet(List(Lines(pg)));;
while Length(lines)<=maxdegree do
   G:=CollineationGroup(pg);
   gamma:=Graph(G,lines,OnProjSubspaces,
      function(x,y) return x<>y and Meet(x,y)<>EmptySubspace(pg); end,
      true); 
   Add(nonsynchgraphs,gamma);
   Add(nonsynchgraphcomments,
      Concatenation("the line graph of PG(3,",String(q),")")); 
   repeat
      q:=q+1;
   until IsPrimePowerInt(q);
   pg:=PG(3,q);
   lines:=AsSet(List(Lines(pg)));
od;
#
# We next determine the graphs $NU_3(q)$ (for q>2) 
# on the points in PG(2,q^2) not in H:=HermitianPolarSpace(2,q^2), 
# with two distinct such points joined by an edge iff the
# line on these points in PG(2,q^2) is a tangent to H. 
# That these graphs are non-synchronizing
# was discovered by LHS. See Section 3.1.6 in: 
# A. E. Brouwer and H. Van Maldeghem, Strongly Regular Graphs, 
# Cambridge University Press, Cambridge, 2022.
#
q:=3;
H:=HermitianPolarSpace(2,q^2);
ProjPlane:=AmbientSpace(H);
pointsH:=AsSet(List(Points(H)));;
N:=Difference(List(Points(ProjPlane)),pointsH);;
while Length(N)<=maxdegree do
   G:=CollineationGroup(H);
   gamma:=Graph(G, N, OnProjSubspaces,
   function(x,y) 
   local line;
   if x=y then
      return false;
   else
      line:=List(Points(Span(x,y)));
      return Size(Intersection(line,pointsH))=1; 
   fi;
   end,
   true); 
   Add(nonsynchgraphs,gamma);
   Add(nonsynchgraphcomments,
      Concatenation("the graph NU_3(",String(q),")"));
   repeat
      q:=q+1;
   until IsPrimePowerInt(q);
   H:=HermitianPolarSpace(2,q^2);
   ProjPlane:=AmbientSpace(H);
   pointsH:=AsSet(List(Points(H)));
   N:=Difference(List(Points(ProjPlane)),pointsH);
od;
#
# The point graph of H:=HermitianPolarSpace(3,q^2) is non-synchronizing 
# since  H  has a fan, that is, a partition of the point set into ovoids. 
# Such a fan is obtained by a general construction described in: 
# A. E. Brouwer and H. A. Wilbrink, Ovoids and fans in the
# generalized quadrangle Q(4,2), Geometriae Dedicata 36
# (1990), 121-124.
#
q:=2;
H:=HermitianPolarSpace(3,q^2);
points:=AsSet(List(Points(H)));;
while Length(points)<=maxdegree do
   lines:=List(Lines(H));
   pointgraph:=Graph(CollineationGroup(H),points,OnProjSubspaces,
      function(x,y) return x<>y and ForAny(lines,L->x*L and y*L); end,
      true); 
   Add(nonsynchgraphs,pointgraph);
   Add(nonsynchgraphcomments,
      Concatenation("the point graph of HermitianPolarSpace(3,",String(q^2),
         "), which has a fan"));
   repeat
      q:=q+1;
   until IsPrimePowerInt(q);
   H:=HermitianPolarSpace(3,q^2);
   points:=AsSet(List(Points(H)));
od;
#
# The complement of the point graph of  S:=SymplecticSpace(3,2^a) 
# is non-synchronizing for all a>=1, since  S  has both an ovoid and a spread. 
# See: J. De Beule, A. Klein, K. Metsch, and L. Storme,
# Partial ovoids and partial spreads of classical finite polar spaces,
# Serdica Math. J. 34 (2008), 689-714.
#
# We start at q=2^2 to avoid adding a graph isomorphic to one listed earlier.
#
q:=4; 
S:=SymplecticSpace(3,q);
points:=AsSet(List(Points(S)));;
while Length(points)<=maxdegree do
   lines:=List(Lines(S));
   pointgraph:=Graph(CollineationGroup(S),points,OnProjSubspaces,
      function(x,y) return x<>y and ForAny(lines,L->x*L and y*L); end,
      true); 
   Add(nonsynchgraphs,ComplementGraph(pointgraph));
   Add(nonsynchgraphcomments,
      Concatenation("the complement of the point graph of SymplecticSpace(3,",
         String(q),"), which has an ovoid and a spread"));
   q:=2*q;
   S:=SymplecticSpace(3,q);
   points:=AsSet(List(Points(S)));
od;
#
# Now insert various other graphs here shown to be nonsynchronizing.
#
adhocnonsynchgraphs_start:=Length(nonsynchgraphs)+1;

GroupInvariantOmegaColouring := function(H,gamma)
#
# Suppose  gamma  is a simple graph, such that  gamma.group  is transitive
# on the vertices of  gamma,  and  H  is a subgroup of  gamma.group. 
#
# Then this function returns an  H-invariant  vertex  omega(gamma)-colouring 
# of  gamma  if such a colouring exists,  and otherwise returns  fail. 
#
local n,omega,delta,blocks,setcover,colouring;
if not IsSimpleGraph(gamma) or not IsTransitive(gamma.group,[1..gamma.order]) then
   Error("<gamma> must be a simple graph, with <gamma>.group transitive on its vertices");
fi;
if not IsSubgroup(gamma.group,H) then
   Error("<H> must be a subgroup of <gamma>.group");
fi;
n:=gamma.order;
omega:=CliqueNumber(gamma); 
if n mod omega <> 0 then
   return fail;
fi;
delta:=ComplementGraph(gamma);
blocks:=CompleteSubgraphsOfGivenSize(delta,n/omega,2);
setcover:=GRAPE_ExactSetCover(G,blocks,n,H); 
if setcover = fail then 
   return fail;
fi;
colouring:=List([1..n],x->First([1..Length(setcover)],y->x in setcover[y]));
# Check
if not IsVertexColouring(gamma,colouring,omega) then
   Error("colouring should be a (proper) vertex omega-colouring of gamma");
fi;
if not IsBound(gamma.minimumVertexColouring) then
   gamma.minimumVertexColouring:=Immutable(colouring);
fi;
return colouring;
end;

n:=175;;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,50*2520*2);
if Length(L)<>1 then
   Error("This group should be unique");
fi; 
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegrees(x)=[12] and CliqueNumber(x)=7);; 
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
gamma:=L[1];;
omega:=CliqueNumber(gamma);
delta:=ComplementGraph(gamma);;
CC:=Set(ConjugacyClasses(G),x->Group(Representative(x)));;
CC:=Filtered(CC,x->Size(x)=5);;
for H in CC do
   N:=Normalizer(G,H);
   C:=CollapsedCompleteOrbitsGraph(H,delta,N);
   K:=CompleteSubgraphsOfGivenSize(C,n/omega,2,false,true,List(C.names,Length));
   KK:=List(K,x->Union(C.names{x}));
   setcover:=GRAPE_ExactSetCover(N,KK,n);
   if setcover<>fail then
      break;
   fi;
od;
colouring:=List([1..n],x->First([1..Length(setcover)],y->x in setcover[y]));;
if not IsVertexColouring(gamma,colouring,omega) then
   Error("colouring  should be a proper vertex omega-colouring of  gamma");
fi;
# Now  gamma  has a proper vertex omega-colouring, where  
# omega  is the clique number of  gamma,  so  gamma has 
# clique number = chromatic number.
gamma.minimumVertexColouring:=Immutable(colouring);;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));
 
n:=248;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,32*31*15);
if Length(L)<>1 then
   Error("This group should be unique");
fi; 
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),
      x->VertexDegrees(x)=[150] and CliqueNumber(x)=31);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
gamma:=L[1];;
H:=SylowSubgroup(gamma.group,31);;
Size(H);
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=280;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,604800*2);
if Length(L)<>1 then
   Error("This group should be unique");
fi; 
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegrees(x)=[135] and CliqueNumber(x)=28);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
gamma:=L[1];;
H:=SylowSubgroup(gamma.group,7);;
Size(H);
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=315;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,63*2^5*720);
if Length(L)<>1 then
   Error("This group should be unique");
fi; 
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegrees(x)=[152] and CliqueNumber(x)=45);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
gamma:=L[1];;
H:=DerivedSubgroup(SylowSubgroup(G,3));;
StructureDescription(H);
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=462;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,Factorial(12));
if Length(L)<>1 then
   Error("This group should be unique");
fi; 
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegrees(x)=[36] and CliqueNumber(x)=7);; 
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
delta:=L[1];;
gamma:=ComplementGraph(delta);;
alpha:=CliqueNumber(delta);
if n mod alpha <> 0 then
   Error("n should be divisible by alpha");
fi;
K:=CompleteSubgraphsOfGivenSize(gamma,n/alpha,0);;
if K=[] then
   Error("gamma should have a (maximum) (n/alpha)-clique"); 
fi;
gamma.maximumClique:=Immutable(K[1]);;
H:=SylowSubgroup(G,11);;
Size(H);
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=495;
P:=AllPrimitiveGroups(NrMovedPoints,n);
G:=P[4];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegrees(x)=[22]);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
delta:=L[1];;
gamma:=ComplementGraph(delta);;
alpha:=CliqueNumber(delta);
if n mod alpha <> 0 then
   Error("n should be divisible by alpha");
fi;
K:=CompleteSubgraphsOfGivenSize(gamma,n/alpha,0,true);;
if K=[] then
   Error("gamma should have a (maximum) (n/alpha)-clique"); 
fi;
gamma.maximumClique:=Immutable(K[1]);;
H:=SylowSubgroup(G,11);;
Size(H);
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

G:=P[6];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegrees(x)=[96] and CliqueNumber(x)=9);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
delta:=L[1];;
gamma:=ComplementGraph(delta);;
alpha:=CliqueNumber(delta);
if n mod alpha <> 0 then
   Error("n should be divisible by alpha");
fi;
K:=CompleteSubgraphsOfGivenSize(gamma,n/alpha,0);;
if K=[] then
   Error("gamma should have a (maximum) (n/alpha)-clique"); 
fi;
gamma.maximumClique:=Immutable(K[1]);;
H:=SylowSubgroup(G,11);;
Size(H);
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=525;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,604800*2);
if Length(L)<>1 then
   Error("This group should be unique");
fi;
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegree(x,1)=12 and CliqueNumber(x)=5);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
gamma:=L[1];;
omega:=CliqueNumber(gamma);
delta:=ComplementGraph(gamma);;
CC:=Set(ConjugacyClasses(G),x->Group(Representative(x)));;
CC:=Filtered(CC,x->Size(x)=5);;
for H in CC do
   N:=Normalizer(G,H);
   C:=CollapsedCompleteOrbitsGraph(H,delta,N);
   K:=CompleteSubgraphsOfGivenSize(C,n/omega,2,false,true,List(C.names,Length));
   KK:=List(K,x->Union(C.names{x}));
   setcover:=GRAPE_ExactSetCover(N,KK,n);
   if setcover<>fail then
      break;
   fi;
od;
colouring:=List([1..n],x->First([1..Length(setcover)],y->x in setcover[y]));;
if not IsVertexColouring(gamma,colouring,omega) then
   Error("colouring  should be a proper vertex omega-colouring of  gamma");
fi;
# Now  gamma  has a proper vertex omega-colouring, where  
# omega  is the clique number of  gamma,  so  gamma has 
# clique number = chromatic number.
gamma.minimumVertexColouring:=Immutable(colouring);;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=560;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,87360);
if Length(L)<>1 then
   Error("This group should be unique");
fi;
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegrees(x)=[52]);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
delta:=L[1];;
gamma:=ComplementGraph(delta);;
alpha:=CliqueNumber(delta);
if n mod alpha <> 0 then
   Error("n should be divisible by alpha");
fi;
K:=CompleteSubgraphsOfGivenSize(gamma,n/alpha,0);;
if K=[] then
   Error("gamma should have a (maximum) (n/alpha)-clique"); 
fi;
gamma.maximumClique:=Immutable(K[1]);;
H:=SylowSubgroup(G,7);;
Size(H);
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=574;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,20*41*42);
if Length(L)<>1 then
   Error("This group should be unique");
fi;
G:=L[1];
H:=SylowSubgroup(G,41);;
Size(H);
N:=Normalizer(G,H);;
gamma:=Filtered(GeneralizedOrbitalGraphs(G),x->not IsCompleteGraph(x));;
for i in [1..Length(gamma)] do
  collapsedgraph:=CollapsedCompleteOrbitsGraph(H,gamma[i],N);
  if IsNullGraph(collapsedgraph) then
     continue;
   fi;
   # Now  gamma[i]  must have a (H-invariant) clique of size >= 82.
   delta:=ComplementGraph(gamma[i]);
   if CliqueNumber(delta)<>7 then
      continue;
   fi;
   blocks:=CompleteSubgraphsOfGivenSize(delta,7,2);;
   setcover:=GRAPE_ExactSetCover(G,blocks,n,H); 
   if setcover=fail then
      continue;
   fi;
   # Now  gamma[i]  has a (proper) vertex  82-colouring, so 
   # gamma[i]  has clique number = chromatic number = 82.
   # We check this.
   K:=CompleteSubgraphsOfGivenSize(collapsedgraph,2,0);
   clique:=Union(List(K[1],x->VertexName(collapsedgraph,x)));
   if Length(clique)<>82 or 
      not IsCompleteGraph(InducedSubgraph(gamma[i],clique)) then
      Error("clique  should be an 82-clique of  gamma[i]");
   fi;
   colouring:=List([1..n],x->First([1..Length(setcover)],y->x in setcover[y]));
   if not IsVertexColouring(gamma[i],colouring,82) then
      Error("colouring  should be a proper vertex 82-colouring of gamma[i]");
   fi;
   gamma[i].maximumClique:=Immutable(clique);
   gamma[i].minimumVertexColouring:=Immutable(colouring);
   Add(nonsynchgraphs,gamma[i]);
   Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
      "; nonsynchronizing graph has (v,k,omega) = (",String(gamma[i].order),",",
      String(VertexDegree(gamma[i],1)),",",String(CliqueNumber(gamma[i])),")."));
   break;
od;

n:=567;
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,3265920*2*2);
if Length(L)<>1 then
   Error("This group should be unique");
fi;
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G),x->VertexDegree(x,1)=120);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
gamma:=L[1];;
omega:=CliqueNumber(gamma);
if n mod omega <> 0 then
   Error("omega should divide n");
fi;
delta:=ComplementGraph(gamma);;
CC:=Set(ConjugacyClasses(G),x->Group(Representative(x)));;
CC:=Filtered(CC,x->Size(x)=6);;
for H in CC do
   N:=Normalizer(G,H);
   C:=CollapsedCompleteOrbitsGraph(H,delta,N);
   K:=CompleteSubgraphsOfGivenSize(C,n/omega,2,false,true,List(C.names,Length));
   KK:=List(K,x->Union(C.names{x}));
   setcover:=GRAPE_ExactSetCover(N,KK,n);
   if setcover<>fail then
      break;
   fi;
od;
colouring:=List([1..n],x->First([1..Length(setcover)],y->x in setcover[y]));;
if not IsVertexColouring(gamma,colouring,omega) then
   Error("colouring  should be a proper vertex omega-colouring of  gamma");
fi;
# Now  gamma  has a proper vertex omega-colouring, where  
# omega  is the clique number of  gamma,  so  gamma has 
# clique number = chromatic number.
gamma.minimumVertexColouring:=Immutable(colouring);;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

n:=620; 
L:=AllPrimitiveGroups(NrMovedPoints,n,Size,15*31*32);
if Length(L)<>1 then
   Error("This group should be unique");
fi;
G:=L[1];
L:=Filtered(GeneralizedOrbitalGraphs(G,1),
      x->VertexDegree(x,1)=24 and Diameter(x)=3 and CliqueNumber(x)=4);;
if Length(L)<>1 then
   Error("This graph should be unique");
fi;
delta:=L[1];;
gamma:=ComplementGraph(delta);;
H:=SylowSubgroup(G,31);;
Size(H);
N:=Normalizer(G,H);;
collapsedgraph:=CollapsedCompleteOrbitsGraph(H,gamma,N);;
K:=CompleteSubgraphsOfGivenSize(collapsedgraph,155,0,false,true,List(collapsedgraph.names,Length));;
clique:=Union(List(K[1],x->VertexName(collapsedgraph,x)));;
alpha:=CliqueNumber(delta);
if Length(clique)*alpha<>n or not IsCompleteGraph(InducedSubgraph(gamma,clique)) then
   Error("clique  should be a (maximum) (n/alpha)-clique of  gamma");
fi;
gamma.maximumClique:=Immutable(clique);;
colouring:=GroupInvariantOmegaColouring(H,gamma);;
if colouring=fail then
   Error("gamma should have an H-invariant vertex omega-colouring");
fi;
Add(nonsynchgraphs,gamma);
Add(nonsynchgraphcomments,Concatenation("Group = ",StringView(G),
   "; nonsynchronizing graph has (v,k,omega) = (",String(gamma.order),",",
   String(VertexDegree(gamma,1)),",",String(CliqueNumber(gamma)),")."));

#
# We next show that the Cohen-Tits near octagon has no ovoid. 
# 
L:=AllPrimitiveGroups(NrMovedPoints,100,Size,604800*2); 
if Length(L)<>1 then
   Error("This group should be unique");
fi;
G:=L[1];
L:=Filtered(ConjugacyClasses(G),x->Size(x)=315);; 
if Length(L)<>1 then
   Error("This conjugacy class should be unique");
fi;
CC:=L[1];;
Order(Representative(CC));
pointgraph:=Graph(G,AsSet(CC),OnPoints,
   function(x,y) return x<>y and x*y=y*x; end,
   true);;
GlobalParameters(pointgraph);
m:=CliqueNumber(pointgraph);
K:=CompleteSubgraphsOfGivenSize(pointgraph,m,2);
nearoct:=BlockDesign(OrderGraph(pointgraph),K,pointgraph.group);;
BlockSizes(nearoct);
AllTDesignLambdas(nearoct);
autnearoct:=AutomorphismGroup(nearoct);;
autnearoct=pointgraph.group;
dualnearoct:=DualBlockDesign(nearoct);;
BlockSizes(dualnearoct);
AllTDesignLambdas(dualnearoct);
ovoids:=BlockDesigns(rec(v:=dualnearoct.v,
   blockSizes:=BlockSizes(dualnearoct),
   blockDesign:=dualnearoct,
   tSubsetStructure:=rec(t:=1, lambdas:=[1])));
if ovoids<>[] then
   Error("There should be no ovoids");
fi;

Runtimes();
#
# Now comes the general computation. 
#
nonsep_records:=[]; 
nonsep_count:=0;
nonsynch_count:=0;
for n in degrees_to_check do 
   Print("\nnonsep_count=",nonsep_count,"\nnonsynch_count=",nonsynch_count);
   Print("\nruntime so far in milliseconds=",Runtime(),"\n"); 
   Print("\nn=",n);
   nonsep_records[n]:=[]; 
   if IsPrimeInt(n) then
      # All prime degree groups are separating, and hence synchronizing.
      Print(" is prime. All prime degree groups are separating.\n"); 
      continue;
   fi;
   smalldim:=fail;
   root:=RootInt(n,2); 
   if root^2=n and IsPrimeInt(root) then 
      smalldim:=2;
   else 
      root:=RootInt(n,3);
      if root^3=n and IsPrimeInt(root) then
         smalldim:=3;
      fi;
   fi; 
   G:=AllPrimitiveGroups(NrMovedPoints,n); 
   libnr:=[1..Length(G)]; 
   StableSortParallel(G,libnr,function(x,y) return Size(x)>Size(y); end); 
   Print("\nG=",G,"\n"); 
   for i in [1..Length(G)] do 
      if (n>=2 and IsNaturalSymmetricGroup(G[i])) or (n>=4 and IsNaturalAlternatingGroup(G[i])) or (n>=2 and Length(Orbit(Stabilizer(G[i],1),2)) = n-1) then
         # G[i] is doubly transitive, so G[i] is separating 
         # (and hence synchronizing). 
         continue;
      fi;
      if n=465 and (Size(G[i]) in [15*31*32,30*31*32]) then
         # G[i] is of degree 465 and is isomorphic to PSL(2,31) or PGL(2,31).
         # An external computation shows that  G[i]  is separating
         # (and hence synchronizing).
         continue;
      fi;
      if n=520 then
         GG:=Filtered(G,x->Size(x)=262080);
         if Length(GG)<>1 then
            Error("This group should be unique");
         fi; 
         GG:=GG[1];
         # Now GG is isomorphic to PSL(2,64) in its primitive action
         # on 520 points, and is shown to be separating later on. 
         if IsSubgroup(G[i],GG) and G[i]<>GG then
            # G[i] is separating (and hence synchronizing).
            continue;
         fi;
      fi;
      if n=560 and (Size(G[i]) in [Factorial(16),Factorial(16)/2]) then
         # G[i] is isomorphic to Sym(16) or Alt(16) in its action on 
         # the 3-subsets of a 16-set. 
         # By Theorem 6.3 of J. Arau´jo, P.J. Cameron and B. Steinberg,
         # Between primitive and 2-transitive: Synchronization 
         # and its friends, EMS Surv. Math. Sci. 4 (2017), 101-184,
         # G[i]  is separating (and hence synchronizing).
         continue;
      fi;
      if only_two_closed and G[i]<>TwoClosure(G[i]) then
         # We do not consider G[i].
         continue;
      fi;
      if smalldim<>fail and ONanScottType(G[i])="1" then
         #
         # We have  n = root^smalldim,  where  root  is prime, and we
         # apply an approach due to Peter Cameron for this G[i] of 
         # affine type.
         # 
         NN:=MinimalNormalSubgroups(G[i]);
         if Length(NN)<>1 or Size(NN[1])<>root^smalldim then
            Error("G[i] should have just one minimal normal subgroup, which should have order root^smalldim");
         fi;
         NN:=NN[1]; 
         # Now  NN  is an elementary abelian normal subgroup of order  n. 
         MM:=AllSubgroups(NN); 
         lines:=Filtered(MM,x->Size(x)=root);
         lineorbs:=Orbits(G[i],lines); 
         if Length(lineorbs)=1 then
            # G[i] is QI, and hence separating, so we are finished with G[i].
            continue;
         fi;
         hyperplanes:=Filtered(MM,x->Size(x)=n/root);
         hyperplaneorbs:=Orbits(G[i],hyperplanes); 
         orb_found:=false;
         for hyperplaneorb in hyperplaneorbs do
            hyperplane:=hyperplaneorb[1];
            for lineorb in lineorbs do 
               if ForAll(lineorb,x->not IsSubgroup(hyperplane,x)) then
                  orb_found:=true;
                  comment:=Concatenation("n=",String(n),
                     "  libnr=",String(libnr[i]),"  ", ViewString(G[i]),
                     " is nonsynchronizing since the group is of affine O'Nan-Scott type, but there is a line-orbit all of whose elements have trivial intersection with some hyperplane (in the minimal normal subgroup)");
                  Print("\n",comment,"\n"); 
                  nonsep_count:=nonsep_count+1;
                  nonsynch_count:=nonsynch_count+1;
                  Add(nonsep_records[n],rec(group:=Group(GeneratorsOfGroup(G[i])),
                     primitiveLibraryNumber:=libnr[i], 
                     isNonsynchronizing:=true, 
                     isNonseparating:=true, 
                     comment:=comment));
                  break;
               fi;
            od;
            if orb_found then
               break;
            fi;
         od;
         if orb_found then
            # We are finished with nonsynchronizing G[i]. 
            continue; 
         fi;
      fi;
      #
      # Now we consider the non-null and non-complete 
      # generalized orbital graphs for  G[i]  (unless  
      # n=620  and  G[i]  is PSL(2,31), in which case, we employ 
      # a hack to avoid computing and storing the very large number 
      # of generalized orbital graphs).
      #
      if n=620 and Size(G[i])=15*31*32 then
         L:=GeneralizedOrbitalGraphs(Group(GeneratorsOfGroup(G[i])),25);
         if not ForAny(L,x->ForAny(nonsynchgraphs,y->x.order=y.order
               and VertexDegrees(x)=VertexDegrees(y) 
               and IsIsomorphicGraph(x,y,false))) then
            Error("Here, some graph in  L  should be isomorphic to one in  nonsynchgraphs");
         fi;
      else    
         L:=Filtered(GeneralizedOrbitalGraphs(Group(GeneratorsOfGroup(G[i]))),
               x->not IsCompleteGraph(x)); 
      fi;
      if L=[] then 
         # We are finished with G[i]. 
         continue;
      fi;
      #
      # Check whether any graph in  L  is isomorphic to a nonsynchronizing 
      # graph we have stored or have encountered so far.
      #
      found:=false; 
      for gamma in L do 
         gg:=First([1..Length(nonsynchgraphs)],x->gamma.order=nonsynchgraphs[x].order 
               and VertexDegrees(gamma)=VertexDegrees(nonsynchgraphs[x]) 
               and IsIsomorphicGraph(gamma,nonsynchgraphs[x],false));
         if gg<>fail then
            found:=true;
            break;
         fi;
      od;
      if found then 
         nonsep_count:=nonsep_count+1;
         nonsynch_count:=nonsynch_count+1;
         comment:=Concatenation("n=",String(n),
            "  libnr=",String(libnr[i]),"  ",StringView(G[i]),
            " is a group of automorphisms of a graph isomorphic to a stored or found nonsynchronizing graph"); 
         if nonsynchgraphcomments[gg]<>"" then
            Append(comment,Concatenation(" having comment: ",nonsynchgraphcomments[gg]));
         fi;
         Print("\n",comment,"\n");
         Add(nonsep_records[n],rec(group:=Group(GeneratorsOfGroup(G[i])),
            primitiveLibraryNumber:=libnr[i], 
            isNonsynchronizing:=true, 
            isNonseparating:=true, 
            nonsynchronizingGraph:=
               GraphImage(nonsynchgraphs[gg],GraphIsomorphism(nonsynchgraphs[gg],gamma,false)),
            comment:=comment));
         # We are now done with G[i]. 
         continue;
      fi;
      #
      # At this point, we are not done with  G[i], 
      # so now make  LL  a complement-free version of  L, 
      # such that each graph gamma in LL has degree <= (n-1)/2. 
      # 
      LL:=[];
      for j in [1..Length(L)] do 
         k:=VertexDegrees(L[j])[1];
         if k<(n-1)/2 then
            Add(LL,L[j]);
         elif k=(n-1)/2 then
            adj:=Adjacency(L[j],1); 
            if ForAll(LL,x->VertexDegrees(x)[1]<k 
                  or Union(adj,Adjacency(x,1))<>[2..n]) then
               # the complement of L[j] is not in LL
               Add(LL,L[j]);
            fi;
         fi;      
      od;
      for gamma in LL do
         k:=VertexDegrees(gamma)[1]; 
         if n=234 and Size(G[i])=5616*2 and k<>96 then
            # We can skip this graph, for if  n=234  and  |G[i]|=5616*2,
            # then  G[i]=PSL(3,3).2,  and there is a nonsynchronizing graph 
            # with vertex-degree  96  or  137=234-97  fixed by  G[i].
            continue;
         fi;
         if n=336 and Size(G[i])=63*32*720 and k<>110 then
            # We can skip this graph, for if  n=336  and  |G[i]|=63*32*720,
            # then  G[i]=PSp(6,2),  and there is a nonsynchronizing graph 
            # with vertex-degree  110  or  225=336-111  fixed by  G[i].
            continue;
         fi;
         if n=396 and Size(G[i])=95040*2 and k<>195 then
            # We can skip this graph, for if  n=396  and  |G[i]|=95040*2,
            # then  G[i]=M(12).2,  and there is a nonsynchronizing graph 
            # with vertex-degree  195  or  200=396-196  fixed by  G[i].
            continue;
         fi;
         if n=425 and Size(G[i])=979200*4 and k<>168 then
            # We can skip this graph, for if  n=425  and  |G[i]|=979200*4,
            # then  G[i]=PSp(4,4).4,  and there is a nonsynchronizing graph 
            # with vertex-degree  168  or  256=425-169  fixed by  G[i].
            continue;
         fi;
         if n=456 and Size(G[i])=1876896*6 and k<>14 then
            # We can skip this graph, for if  n=456  and  |G[i]|=1876896*6,
            # then  G[i]=PSL(3,7).Sym(3),  and there is a nonsynchronizing 
            # graph with vertex-degree  14  or  441=456-15  fixed by  G[i].
            continue;
         fi;
         if n=465 and Size(G[i])=9999360*2 and k<>28 then
            # We can skip this graph, for if  n=465  and  |G[i]|=9999360*2,
            # then  G[i]=PSL(5,2).2,  and there is a nonsynchronizing 
            # graph with vertex-degree  28  or  436=465-29  fixed by  G[i].
            continue;
         fi;
         if n=504 and k<>224 then
            # If  n=504  and  G[i]  is not 2-transitive, then  G[i]  is of 
            # diagonal type and fixes a nonseparating graph with 
            # vertex-degree 224.
            continue;
         fi;
         omega:=CliqueNumber(gamma); 
         if RemInt(n,omega)<>0 then
            # alpha*omega < n 
            continue;
         fi;
         if n=315 and Size(G[i]) in [604800,604800*2] and k=10 and omega=3 then
            # 
            # Now  gamma  is the point graph of the Cohen-Tits near 
            # octagon  CT, and an independent set of size  105=n/omega  would
            # correspond to an ovoid of  CT.  A computation above shows 
            # that no such ovoid exists, and so  alpha*omega<n.  
            # (A much longer computation by LHS, using QMUL's Apocrita 
            # HPC facility shows that  gamma  has independence number 90.) 
            #
            continue;
         fi;
         if HoffmanCocliqueBound(gamma)*omega < n then
            # alpha*omega < n 
            continue;
         fi;
         aut:=AutomorphismGroup(gamma); 
         delta:=NewGroupGraph(aut,ComplementGraph(gamma)); 
         KK:=CompleteSubgraphsOfGivenSize(delta,n/omega,0);
         if KK=[] then
            # alpha*omega < n
            continue;
         fi;
         delta.maximumClique:=Immutable(KK[1]); 
         alpha:=n/omega;
         #
         # At this point we know that  gamma  is a nonseparating graph
         # for  G[i],  which may already have a nonseparating record. 
         #
         nonsep_record:=First(nonsep_records[n],x->x.primitiveLibraryNumber=libnr[i]); 
         if nonsep_record=fail then 
            # Make a nonseparating record for  G[i]. 
            nonsep_count:=nonsep_count+1;
            nonsep_record:=rec(group:=Group(GeneratorsOfGroup(G[i])),
               primitiveLibraryNumber:=libnr[i], 
               isNonseparating:=true, 
               nonseparatingGraph:=gamma,
               comment:=Concatenation("Group = ",StringView(G[i]),
                  " is nonseparating; ",
                  "nonseparating graph has (v,k,omega) = (",
                  String(gamma.order),",", String(VertexDegree(gamma,1)),",",
                  String(CliqueNumber(gamma)),")."));
            Add(nonsep_records[n],nonsep_record); 
         fi;
         if ONanScottType(G[i])<>"2" then 
            # G[i] is not of almost simple O'Nan-Scott type, so 
            # G[i] nonseparating implies G[i] nonsynchronizing. 
            comment:=Concatenation("n=",String(n),"  ",
               "  libnr=",String(libnr[i]),"  ",StringView(G[i]),
               " is nonsynchronizing, since nonseparating and of O'Nan-Scott type ",
               ONanScottType(G[i])); 
            Print("\n",comment,"\n"); 
            nonsynch_count:=nonsynch_count+1;
            nonsep_record.isNonsynchronizing:=true; 
            nonsep_record.comment:=comment;
            break;
         fi;
         #
         # At this point we know that  G[i]  is a nonseparating 
         # group of almost simple O'Nan-Scott type. 
         #
         # We now check whether clique number equals chromatic number 
         # for  gamma  or its complement  delta. 
         # 
         if n=325 and Size(G[i]) in [4680000,4680000*2] and VertexDegrees(gamma)=[144] and CliqueNumber(gamma)=25 then
            # This is a special case making use of an external computation. 
            # LHS (2020) proved that this graph  gamma  does *not* have a
            # (proper) vertex colouring with  omega  colours,
            # using about 140 minutes runtime on 100 cores on QMUL's 
            # Apocrita HPC facility: http://doi.org/10.5281/zenodo.438045
            C:=fail;
         elif n=396 and Size(G[i])=95040*2 and VertexDegrees(gamma)=[195] then
            # This is a hack to avoid a potentially lengthy computation, 
            # but is valid since we know that there is a nonsynchronizing
            # graph with vertex-degree 200 for this group.
            C:="unknown";
         elif n=425 and Size(G[i])=979200*4 and VertexDegrees(gamma)=[168] then
            # This is a hack to avoid a potentially lengthy computation, 
            # but is valid since we know that there is a nonsynchronizing
            # graph with vertex-degree 256 for this group.
            C:="unknown";
         elif n=456 and Size(G[i])=1876896*6 and VertexDegrees(gamma)=[14] then
            # This is a hack to avoid a potentially lengthy computation, 
            # but is valid since we know that there is a nonsynchronizing
            # graph with vertex-degree 441 for this group.
            C:="unknown";
         else
            C:=VertexColouring(gamma,omega,alpha); 
         fi; 
         if C<>fail and C<>"unknown" then 
            # C is a vertex omega-colouring of gamma.
            gamma.minimumVertexColouring:=Immutable(C); 
            nonsynch_count:=nonsynch_count+1;
            comment:=Concatenation("n=",String(n),
                  "  libnr=",String(libnr[i]),"  ",StringView(G[i]),
                  " is nonsynchronizing; ",
                  " nonsynchronizing graph has (v,k,omega) = (",
                  String(gamma.order),",", String(VertexDegree(gamma,1)),",",
                  String(CliqueNumber(gamma)),").");
            nonsep_record.comment:=comment;
            Print("\n",comment,"\n"); 
            nonsep_record.isNonsynchronizing:=true; 
            nonsep_record.nonsynchronizingGraph:=gamma; 
            Add(nonsynchgraphs,gamma);
            Add(nonsynchgraphcomments,comment);
            break;
         fi;
         #
         # At this point, we know that  gamma  is synchronizing, 
         # so we now check whether the complement  delta  of  gamma 
         # is synchronizing. 
         # 
         if n=315 and Size(G[i]) in [604800,604800*2] and VertexDegrees(delta)=[250] and CliqueNumber(delta)=63 then   
            #
            # This is a special case making use of an external computation.  
            # 
            # LHS (2020) proved that this graph  delta  does *not* have a
            # (proper) vertex colouring with  alpha (=n/omega)  colours,
            # using about 33 hours runtime on 100 cores on QMUL's Apocrita 
            # HPC facility: http://doi.org/10.5281/zenodo.438045
            #
            C:=fail;
         else 
            C:=VertexColouring(delta,alpha,omega); 
         fi;
         if C<>fail then 
            # C  is a proper vertex colouring of  delta,
            # using  alpha=omega(delta)  colours.
            delta.minimumVertexColouring:=Immutable(C); 
            nonsynch_count:=nonsynch_count+1;
            comment:=Concatenation("n=",String(n),
                  "  libnr=",String(libnr[i]),"  ",StringView(G[i]),
                  " is nonsynchronizing; ",
                  " nonsynchronizing graph has (v,k,omega) = (",
                  String(delta.order),",", String(VertexDegree(delta,1)),",",
                  String(delta.order/Length(Set(C))),").");
            nonsep_record.comment:=comment;
            Print("\n",comment,"\n"); 
            nonsep_record.isNonsynchronizing:=true; 
            nonsep_record.nonsynchronizingGraph:=delta; 
            Add(nonsynchgraphs,delta);
            Add(nonsynchgraphcomments,comment); 
            break;
         fi;
         # At this point, we know that both  gamma  and  delta 
         # are synchronizing. 
      od;
      #
      # At this point we have considered all the generalized orbital
      # graphs for  G[i]  that we need to.
      #
      # We check whether we found  G[i]  to be nonseparating.
      # 
      nonsep_record:=First(nonsep_records[n],x->x.primitiveLibraryNumber=libnr[i]); 
      if nonsep_record<>fail then 
         #  G[i]  is nonseparating.
         if not IsBound(nonsep_record.isNonsynchronizing) then 
            # 
            # As we got to this point without finding a nonsynchronizing 
            # generalized orbital graph for  G[i],  the group  G[i]  must
            # be synchronizing.
            #
            nonsep_record.isNonsynchronizing:=false;
            comment:=Concatenation("n=",String(n),
                      "  libnr=",String(libnr[i]),"  ",StringView(G[i]),
                      " is a nonseparating, but synchronizing, group");
            nonsep_record.comment:=comment;
            Print("\n",comment,"\n");
         fi;
      fi;
   od;
od;

only_two_closed;
nonsep_count;
nonsynch_count;
nonsep_affine_count:=0;;
nonsep_almostsimple_count:=0;;
nonsep_diagonal_count:=0;;
for n in degrees_to_check do 
   for y in nonsep_records[n] do 
      y.permutationDegree:=n; 
      if IsBound(y.nonseparatingGraph) then
         Unbind(y.nonseparatingGraph.canonicalLabelling);
      fi;
      if IsBound(y.nonsynchronizingGraph) then
         Unbind(y.nonsynchronizingGraph.canonicalLabelling);
      fi;
      type:=ONanScottType(PrimitiveGroup(n,y.primitiveLibraryNumber));
      if type="1" then
         nonsep_affine_count:=nonsep_affine_count+1;
      elif type="2" then
         nonsep_almostsimple_count:=nonsep_almostsimple_count+1;
      elif type in ["3a","3b"] then
         nonsep_diagonal_count:=nonsep_diagonal_count+1;
      fi;
   od;
od;
nonsep_affine_count;
nonsep_almostsimple_count;
nonsep_diagonal_count;
PrintTo("nonsep_records.g","nonsep_records:=\n",nonsep_records,";\n");
Length(nonsynchgraphs);
Length(nonsynchgraphcomments);
Length(GraphIsomorphismClassRepresentatives(nonsynchgraphs));
ForAll(nonsynchgraphs,x->(not IsNullGraph(x)) and (not IsCompleteGraph(x)));
for i in [adhocnonsynchgraphs_start..Length(nonsynchgraphs)] do
   if nonsynchgraphs[i].group<>AutomorphismGroup(nonsynchgraphs[i]) then
      Print("\nLarger AM group for nonsynchgraphs ",i,"\n");
   fi;
   gamma:=nonsynchgraphs[i];
   n:=gamma.order;
   P:=AllPrimitiveGroups(NrMovedPoints,n);
   libnr:=First([1..Length(P)],x->gamma.group=P[x]);
   if libnr<>fail then
      gp:=StringView(P[libnr]);
   else
      gp:=StringView(gamma.group);
   fi;
   Print("\n",n," & ",libnr," & ",gp," & ",VertexDegree(gamma,1)," & ",CliqueNumber(gamma)); 
od;
Runtimes();
quit;
