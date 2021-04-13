// 
// Translation of Viper program.
// 
// Date:         2021-04-13 13:40:00
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print ../../clean/carbon/tests/test.bpl ../../clean/carbon/benchmarking/failed/0196.vpr
// Dependencies:
//   Boogie , located at /bin/boogie/Binaries/boogie.
//   Z3 4.8.4 - 64 bit, located at /usr/bin/z3.
// 

// ==================================================
// Preamble of State module.
// ==================================================

function  state(Heap: HeapType, Mask: MaskType): bool;

// ==================================================
// Preamble of Heap module.
// ==================================================

type Ref;
var Heap: HeapType;
const null: Ref;
type Field A B;
type NormalField;
type HeapType = <A, B> [Ref, Field A B]B;
const unique $allocated: Field NormalField bool;
axiom (forall o: Ref, f: (Field NormalField Ref), Heap: HeapType ::
  { Heap[o, f] }
  Heap[o, $allocated] ==> Heap[Heap[o, f], $allocated]
);
function  succHeap(Heap0: HeapType, Heap1: HeapType): bool;
function  succHeapTrans(Heap0: HeapType, Heap1: HeapType): bool;
function  IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function  IsPredicateField<A, B>(f_1: (Field A B)): bool;
function  IsWandField<A, B>(f_1: (Field A B)): bool;
function  getPredicateId<A, B>(f_1: (Field A B)): int;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[null, pm_f], IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// Frame all wand mask locations of wands with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsWandField(pm_f), ExhaleHeap[null, WandMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsWandField(pm_f) ==> Heap[null, WandMaskField(pm_f)] == ExhaleHeap[null, WandMaskField(pm_f)]
);
// Frame all locations in the footprint of magic wands
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsWandField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsWandField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, WandMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// All previously-allocated references are still allocated
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
);
// Updated Heaps are Successor Heaps
axiom (forall <A, B> Heap: HeapType, o: Ref, f_2: (Field A B), v: B ::
  { Heap[o, f_2:=v] }
  succHeap(Heap, Heap[o, f_2:=v])
);
// IdenticalOnKnownLocations Heaps are Successor Heaps
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> succHeap(Heap, ExhaleHeap)
);
// Successor Heaps are Transitive Successor Heaps
axiom (forall Heap0: HeapType, Heap1: HeapType ::
  { succHeap(Heap0, Heap1) }
  succHeap(Heap0, Heap1) ==> succHeapTrans(Heap0, Heap1)
);
// Transitivity of Transitive Successor Heaps
axiom (forall Heap0: HeapType, Heap1: HeapType, Heap2: HeapType ::
  { succHeapTrans(Heap0, Heap1), succHeap(Heap1, Heap2) }
  succHeapTrans(Heap0, Heap1) && succHeap(Heap1, Heap2) ==> succHeapTrans(Heap0, Heap2)
);

// ==================================================
// Preamble of Permission module.
// ==================================================

type Perm = real;
type MaskType = <A, B> [Ref, Field A B]Perm;
var Mask: MaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == NoPerm
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroPMask[o_1, f_3] }
  !ZeroPMask[o_1, f_3]
);
function  PredicateMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
function  WandMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function  Perm(a: real, b: real): Perm;
function  GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask), Mask[o_1, f_3] }
  GoodMask(Mask) ==> Mask[o_1, f_3] >= NoPerm && ((GoodMask(Mask) && !IsPredicateField(f_3)) && !IsWandField(f_3) ==> Mask[o_1, f_3] <= FullPerm)
);
function  HasDirectPerm<A, B>(Mask: MaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, o_1, f_3) }
  HasDirectPerm(Mask, o_1, f_3) <==> Mask[o_1, f_3] > NoPerm
);
function  sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
);
// ==================================================
// Function for trigger used in checks which are never triggered
// ==================================================

function  neverTriggered1(e: Ref): bool;
function  neverTriggered2(e_2: Ref): bool;
function  neverTriggered3(e_3: Ref): bool;
function  neverTriggered4(e: Ref): bool;
function  neverTriggered5(e_2: Ref): bool;
function  neverTriggered6(e_3: Ref): bool;
function  neverTriggered7(e: Ref): bool;
function  neverTriggered8(e_2: Ref): bool;
function  neverTriggered9(e_3: Ref): bool;
function  neverTriggered10(e: Ref): bool;
function  neverTriggered11(e_2: Ref): bool;
function  neverTriggered12(e_3: Ref): bool;
function  neverTriggered13(e: Ref): bool;
function  neverTriggered14(e_1: Ref): bool;
function  neverTriggered15(e_3: Ref): bool;
function  neverTriggered16(e: Ref): bool;
function  neverTriggered17(e_1: Ref): bool;
function  neverTriggered18(e_3: Ref): bool;
function  neverTriggered19(e: Ref): bool;
function  neverTriggered20(e_1: Ref): bool;
function  neverTriggered21(e_3: Ref): bool;
function  neverTriggered22(e: Ref): bool;
function  neverTriggered23(e_1: Ref): bool;
function  neverTriggered24(e_3: Ref): bool;
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function  invRecv1(r_1_1: Ref): Ref;
function  invRecv2(r_2_1: Ref): Ref;
function  invRecv3(r_3_1: Ref): Ref;
function  invRecv4(r_1_1: Ref): Ref;
function  invRecv5(r_2_1: Ref): Ref;
function  invRecv6(r_3_1: Ref): Ref;
function  invRecv7(r_1_1: Ref): Ref;
function  invRecv8(r_2_1: Ref): Ref;
function  invRecv9(r_3_1: Ref): Ref;
function  invRecv10(r_1_1: Ref): Ref;
function  invRecv11(r_2_1: Ref): Ref;
function  invRecv12(r_3_1: Ref): Ref;
function  invRecv13(recv: Ref): Ref;
function  invRecv14(recv: Ref): Ref;
function  invRecv15(recv: Ref): Ref;
function  invRecv16(recv: Ref): Ref;
function  invRecv17(recv: Ref): Ref;
function  invRecv18(recv: Ref): Ref;
function  invRecv19(recv: Ref): Ref;
function  invRecv20(recv: Ref): Ref;
function  invRecv21(recv: Ref): Ref;
function  invRecv22(recv: Ref): Ref;
function  invRecv23(recv: Ref): Ref;
function  invRecv24(recv: Ref): Ref;
// ==================================================
// Functions used to represent the range of the projection of each QP instance onto its receiver expressions for quantified permissions during inhale and exhale
// ==================================================

function  qpRange1(r_1_1: Ref): bool;
function  qpRange2(r_2_1: Ref): bool;
function  qpRange3(r_3_1: Ref): bool;
function  qpRange4(r_1_1: Ref): bool;
function  qpRange5(r_2_1: Ref): bool;
function  qpRange6(r_3_1: Ref): bool;
function  qpRange7(r_1_1: Ref): bool;
function  qpRange8(r_2_1: Ref): bool;
function  qpRange9(r_3_1: Ref): bool;
function  qpRange10(r_1_1: Ref): bool;
function  qpRange11(r_2_1: Ref): bool;
function  qpRange12(r_3_1: Ref): bool;
function  qpRange13(recv: Ref): bool;
function  qpRange14(recv: Ref): bool;
function  qpRange15(recv: Ref): bool;
function  qpRange16(recv: Ref): bool;
function  qpRange17(recv: Ref): bool;
function  qpRange18(recv: Ref): bool;
function  qpRange19(recv: Ref): bool;
function  qpRange20(recv: Ref): bool;
function  qpRange21(recv: Ref): bool;
function  qpRange22(recv: Ref): bool;
function  qpRange23(recv: Ref): bool;
function  qpRange24(recv: Ref): bool;

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 5: refs
// - height 4: testerFull
// - height 3: get
// - height 2: testerfieldFull
// - height 1: tester
// - height 0: testerfield
const AssumeFunctionsAbove: int;
// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function  FrameFragment<T>(t: T): FrameType;
function  ConditionalFrame(p: Perm, f_5: FrameType): FrameType;
function  dummyFunction<T>(t: T): bool;
function  CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// ==================================================
// Definition of conditional frame fragments
// ==================================================

axiom (forall p: Perm, f_5: FrameType ::
  { ConditionalFrame(p, f_5) }
  ConditionalFrame(p, f_5) == (if p > 0.000000000 then f_5 else EmptyFrame)
);
// Function for recording enclosure of one predicate instance in another
function  InsidePredicate<A, B>(p: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType): bool;
// Transitivity of InsidePredicate
axiom (forall <A, B, C> p: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType, r: (Field C FrameType), u: FrameType ::
  { InsidePredicate(p, v_1, q, w), InsidePredicate(q, w, r, u) }
  InsidePredicate(p, v_1, q, w) && InsidePredicate(q, w, r, u) ==> InsidePredicate(p, v_1, r, u)
);
// Knowledge that two identical instances of the same predicate cannot be inside each other
axiom (forall <A> p: (Field A FrameType), v_1: FrameType, w: FrameType ::
  { InsidePredicate(p, v_1, p, w) }
  !InsidePredicate(p, v_1, p, w)
);

// ==================================================
// Preamble of Set module.
// ==================================================


type Set T = [T]bool;

function Set#Card<T>(Set T): int;
axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>(): Set T;
axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
axiom (forall<T> s: Set T :: { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
  (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

function Set#Singleton<T>(T): Set T;
axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
  Set#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
  Set#UnionOne(a, x)[x]);
axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);
//axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
//  Set#Disjoint(a, b) ==>
//    Set#Difference(Set#Union(a, b), a) == b &&
//    Set#Difference(Set#Union(a, b), b) == a);

function Set#Intersection<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] } {Set#Intersection(a,b), a[o]} {Set#Intersection(a,b), b[o]} // AS: added alternative triggers 20/06/19
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] } { Set#Difference(a,b), a[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y] );
axiom (forall<T> a, b: Set T ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
  + Set#Card(Set#Intersection(a, b))
    == Set#Card(Set#Union(a, b)) &&
  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall<T> a: Set T, b: Set T ::
//   { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
//   Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));


function Set#Equal<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

//function Set#Disjoint<T>(Set T, Set T): bool;
//axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
//  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of multisets --------------------------------
// ---------------------------------------------------------------

function Math#min(a: int, b: int): int;
axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);
axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);
axiom (forall a: int, b: int :: { Math#min(a, b) } Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int): int;
axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);

type MultiSet T; // = [T]int;

function MultiSet#Select<T>(ms: MultiSet T, x:T): int;

//function $IsGoodMultiSet<T>(ms: MultiSet T): bool;
// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
//axiom (forall<T> ms: MultiSet T :: { $IsGoodMultiSet(ms) }
//  $IsGoodMultiSet(ms) <==>
//  (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

axiom (forall<T> ms: MultiSet T, x: T :: {MultiSet#Select(ms,x)} MultiSet#Select(ms,x) >= 0); // NEW

function MultiSet#Card<T>(MultiSet T): int;
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
//axiom (forall<T> s: MultiSet T, x: T, n: int :: { MultiSet#Card(s[x := n]) }
//  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);
//
function MultiSet#Empty<T>(): MultiSet T;
axiom (forall<T> o: T :: { MultiSet#Select(MultiSet#Empty(),o) } MultiSet#Select(MultiSet#Empty(),o) == 0);
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) }
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < MultiSet#Select(s,x))));

function MultiSet#Singleton<T>(T): MultiSet T;
axiom (forall<T> r: T, o: T :: { MultiSet#Select(MultiSet#Singleton(r),o) } (MultiSet#Select(MultiSet#Singleton(r),o) == 1 <==> r == o) &&
                                                            (MultiSet#Select(MultiSet#Singleton(r),o) == 0 <==> r != o));
axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Card(MultiSet#Singleton(r)) == 1 && MultiSet#Select(MultiSet#Singleton(r),r) == 1); // AS: added
axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r)); // AS: remove this?

function MultiSet#UnionOne<T>(MultiSet T, T): MultiSet T;
// union-ing increases count by one for x, not for others
axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#Select(MultiSet#UnionOne(a,x),o) } { MultiSet#UnionOne(a, x), MultiSet#Select(a,o) } // AS: added back this trigger (used on a similar axiom before)
  MultiSet#Select(MultiSet#UnionOne(a, x),o) == (if x==o then MultiSet#Select(a,o) + 1 else MultiSet#Select(a,o)));
// non-decreasing
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Card(MultiSet#UnionOne(a, x)) } {MultiSet#UnionOne(a, x), MultiSet#Card(a)} // AS: added alternative trigger
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);
// AS: added - concrete knowledge of element added
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#UnionOne(a,x)}
  MultiSet#Select(MultiSet#UnionOne(a, x),x) > 0 && MultiSet#Card(MultiSet#UnionOne(a, x)) > 0);

function MultiSet#Union<T>(MultiSet T, MultiSet T): MultiSet T;
// union-ing is the sum of the contents
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Select(MultiSet#Union(a,b),o) } {MultiSet#Union(a,b), MultiSet#Select(a,o), MultiSet#Select(b,o)}// AS: added triggers
  MultiSet#Select(MultiSet#Union(a,b),o) == MultiSet#Select(a,o) + MultiSet#Select(b,o));
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Card(MultiSet#Union(a,b)) } {MultiSet#Card(a), MultiSet#Union(a,b)} {MultiSet#Card(b), MultiSet#Union(a,b)}
  MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Select(MultiSet#Intersection(a,b),o) }
  MultiSet#Select(MultiSet#Intersection(a,b),o) == Math#min(MultiSet#Select(a,o),  MultiSet#Select(b,o)));

// left and right pseudo-idempotence
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));

// multiset difference, a - b. clip() makes it positive.
function MultiSet#Difference<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Select(MultiSet#Difference(a,b),o) }
  MultiSet#Select(MultiSet#Difference(a,b),o) == Math#clip(MultiSet#Select(a,o) - MultiSet#Select(b,o)));
axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Difference(a, b), MultiSet#Select(b,y), MultiSet#Select(a,y) }
  MultiSet#Select(a,y) <= MultiSet#Select(b,y) ==> MultiSet#Select(MultiSet#Difference(a, b),y) == 0 );
axiom (forall<T> a, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Difference(a, b)) }
  MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
    == MultiSet#Card(MultiSet#Union(a, b)) &&
  MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

// multiset subset means a must have at most as many of each element as b
function MultiSet#Subset<T>(MultiSet T, MultiSet T): bool;
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
  MultiSet#Subset(a,b) <==> (forall o: T :: {MultiSet#Select(a,o)} {MultiSet#Select(b,o)} MultiSet#Select(a,o) <= MultiSet#Select(b,o)));

function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) <==> (forall o: T :: {MultiSet#Select(a,o)} {MultiSet#Select(b,o)} MultiSet#Select(a,o) == MultiSet#Select(b,o)));
// extensionality axiom for multisets
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T): bool;
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Disjoint(a,b) }
  MultiSet#Disjoint(a,b) <==> (forall o: T :: {MultiSet#Select(a,o)} {MultiSet#Select(b,o)} MultiSet#Select(a,o) == 0 || MultiSet#Select(b,o) == 0));

    

// ==================================================
// Translation of all fields
// ==================================================

const unique q_1: Field NormalField Ref;
axiom !IsPredicateField(q_1);
axiom !IsWandField(q_1);

// ==================================================
// Translation of function refs
// ==================================================

// Uninterpreted function definitions
function  refs(Heap: HeapType, r_1: Ref): Set Ref;
function  refs'(Heap: HeapType, r_1: Ref): Set Ref;
axiom (forall Heap: HeapType, r_1: Ref ::
  { refs(Heap, r_1) }
  refs(Heap, r_1) == refs'(Heap, r_1) && dummyFunction(refs#triggerStateless(r_1))
);
axiom (forall Heap: HeapType, r_1: Ref ::
  { refs'(Heap, r_1) }
  dummyFunction(refs#triggerStateless(r_1))
);

// Framing axioms
function  refs#frame(frame: FrameType, r_1: Ref): Set Ref;
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), refs'(Heap, r_1) }
  state(Heap, Mask) ==> refs'(Heap, r_1) == refs#frame(EmptyFrame, r_1)
);

// Trigger function (controlling recursive postconditions)
function  refs#trigger(frame: FrameType, r_1: Ref): bool;

// State-independent trigger function
function  refs#triggerStateless(r_1: Ref): Set Ref;

// Check contract well-formedness and postcondition
procedure refs#definedness(r_1: Ref) returns (Result: (Set Ref))
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[r_1, $allocated];
    assume AssumeFunctionsAbove == 5;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
}

// ==================================================
// Translation of function get
// ==================================================

// Uninterpreted function definitions
function  get(Heap: HeapType, r_1: Ref): Ref;
function  get'(Heap: HeapType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, r_1: Ref ::
  { get(Heap, r_1) }
  get(Heap, r_1) == get'(Heap, r_1) && dummyFunction(get#triggerStateless(r_1))
);
axiom (forall Heap: HeapType, r_1: Ref ::
  { get'(Heap, r_1) }
  dummyFunction(get#triggerStateless(r_1))
);

// Framing axioms
function  get#frame(frame: FrameType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), get'(Heap, r_1) }
  state(Heap, Mask) ==> get'(Heap, r_1) == get#frame(EmptyFrame, r_1)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), get'(Heap, r_1) }
  state(Heap, Mask) && (AssumeFunctionsAbove < 3 || get#trigger(EmptyFrame, r_1)) ==> refs(Heap, r_1)[get'(Heap, r_1)]
);

// Trigger function (controlling recursive postconditions)
function  get#trigger(frame: FrameType, r_1: Ref): bool;

// State-independent trigger function
function  get#triggerStateless(r_1: Ref): Ref;

// Check contract well-formedness and postcondition
procedure get#definedness(r_1: Ref) returns (Result: Ref)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[r_1, $allocated];
    assume AssumeFunctionsAbove == 3;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Checking definedness of postcondition (no body)
    
    // -- Check definedness of (result in refs(r))
      if (*) {
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume refs(Heap, r_1)[Result];
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function tester
// ==================================================

// Uninterpreted function definitions
function  tester(Heap: HeapType, r_1: Ref): Ref;
function  tester'(Heap: HeapType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, r_1: Ref ::
  { tester(Heap, r_1) }
  tester(Heap, r_1) == tester'(Heap, r_1) && dummyFunction(tester#triggerStateless(r_1))
);
axiom (forall Heap: HeapType, r_1: Ref ::
  { tester'(Heap, r_1) }
  dummyFunction(tester#triggerStateless(r_1))
);

// Framing axioms
function  tester#frame(frame: FrameType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), tester'(Heap, r_1) }
  state(Heap, Mask) ==> tester'(Heap, r_1) == tester#frame(Heap[null, Q(r_1)], r_1)
);

// Trigger function (controlling recursive postconditions)
function  tester#trigger(frame: FrameType, r_1: Ref): bool;

// State-independent trigger function
function  tester#triggerStateless(r_1: Ref): Ref;

// Check contract well-formedness and postcondition
procedure tester#definedness(r_1: Ref) returns (Result: Ref)
  modifies Heap, Mask;
{
  var wildcard: real where wildcard > NoPerm;
  var perm: Perm;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[r_1, $allocated];
    assume AssumeFunctionsAbove == 1;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    havoc wildcard;
    perm := wildcard;
    Mask[null, Q(r_1)] := Mask[null, Q(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function testerFull
// ==================================================

// Uninterpreted function definitions
function  testerFull(Heap: HeapType, r_1: Ref): Ref;
function  testerFull'(Heap: HeapType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, r_1: Ref ::
  { testerFull(Heap, r_1) }
  testerFull(Heap, r_1) == testerFull'(Heap, r_1) && dummyFunction(testerFull#triggerStateless(r_1))
);
axiom (forall Heap: HeapType, r_1: Ref ::
  { testerFull'(Heap, r_1) }
  dummyFunction(testerFull#triggerStateless(r_1))
);

// Framing axioms
function  testerFull#frame(frame: FrameType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), testerFull'(Heap, r_1) }
  state(Heap, Mask) ==> testerFull'(Heap, r_1) == testerFull#frame(Heap[null, Q(r_1)], r_1)
);

// Trigger function (controlling recursive postconditions)
function  testerFull#trigger(frame: FrameType, r_1: Ref): bool;

// State-independent trigger function
function  testerFull#triggerStateless(r_1: Ref): Ref;

// Check contract well-formedness and postcondition
procedure testerFull#definedness(r_1: Ref) returns (Result: Ref)
  modifies Heap, Mask;
{
  var perm: Perm;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[r_1, $allocated];
    assume AssumeFunctionsAbove == 4;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    Mask[null, Q(r_1)] := Mask[null, Q(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function testerfield
// ==================================================

// Uninterpreted function definitions
function  testerfield(Heap: HeapType, r_1: Ref): Ref;
function  testerfield'(Heap: HeapType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, r_1: Ref ::
  { testerfield(Heap, r_1) }
  testerfield(Heap, r_1) == testerfield'(Heap, r_1) && dummyFunction(testerfield#triggerStateless(r_1))
);
axiom (forall Heap: HeapType, r_1: Ref ::
  { testerfield'(Heap, r_1) }
  dummyFunction(testerfield#triggerStateless(r_1))
);

// Framing axioms
function  testerfield#frame(frame: FrameType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), testerfield'(Heap, r_1) }
  state(Heap, Mask) ==> testerfield'(Heap, r_1) == testerfield#frame(FrameFragment(Heap[r_1, q_1]), r_1)
);

// Trigger function (controlling recursive postconditions)
function  testerfield#trigger(frame: FrameType, r_1: Ref): bool;

// State-independent trigger function
function  testerfield#triggerStateless(r_1: Ref): Ref;

// Check contract well-formedness and postcondition
procedure testerfield#definedness(r_1: Ref) returns (Result: Ref)
  modifies Heap, Mask;
{
  var wildcard: real where wildcard > NoPerm;
  var perm: Perm;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[r_1, $allocated];
    assume AssumeFunctionsAbove == 0;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    havoc wildcard;
    perm := wildcard;
    assume r_1 != null;
    Mask[r_1, q_1] := Mask[r_1, q_1] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of function testerfieldFull
// ==================================================

// Uninterpreted function definitions
function  testerfieldFull(Heap: HeapType, r_1: Ref): Ref;
function  testerfieldFull'(Heap: HeapType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, r_1: Ref ::
  { testerfieldFull(Heap, r_1) }
  testerfieldFull(Heap, r_1) == testerfieldFull'(Heap, r_1) && dummyFunction(testerfieldFull#triggerStateless(r_1))
);
axiom (forall Heap: HeapType, r_1: Ref ::
  { testerfieldFull'(Heap, r_1) }
  dummyFunction(testerfieldFull#triggerStateless(r_1))
);

// Framing axioms
function  testerfieldFull#frame(frame: FrameType, r_1: Ref): Ref;
axiom (forall Heap: HeapType, Mask: MaskType, r_1: Ref ::
  { state(Heap, Mask), testerfieldFull'(Heap, r_1) }
  state(Heap, Mask) ==> testerfieldFull'(Heap, r_1) == testerfieldFull#frame(FrameFragment(Heap[r_1, q_1]), r_1)
);

// Trigger function (controlling recursive postconditions)
function  testerfieldFull#trigger(frame: FrameType, r_1: Ref): bool;

// State-independent trigger function
function  testerfieldFull#triggerStateless(r_1: Ref): Ref;

// Check contract well-formedness and postcondition
procedure testerfieldFull#definedness(r_1: Ref) returns (Result: Ref)
  modifies Heap, Mask;
{
  var perm: Perm;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume Heap[r_1, $allocated];
    assume AssumeFunctionsAbove == 2;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Inhaling precondition (with checking)
    perm := FullPerm;
    assume r_1 != null;
    Mask[r_1, q_1] := Mask[r_1, q_1] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of predicate P
// ==================================================

type PredicateType_P;
function  P(r_1: Ref): Field PredicateType_P FrameType;
function  P#sm(r_1: Ref): Field PredicateType_P PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(P(r_1)) }
  PredicateMaskField(P(r_1)) == P#sm(r_1)
);
axiom (forall r_1: Ref ::
  { P(r_1) }
  IsPredicateField(P(r_1))
);
axiom (forall r_1: Ref ::
  { P(r_1) }
  getPredicateId(P(r_1)) == 0
);
function  P#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  P#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { P(r_1), P(r2) }
  P(r_1) == P(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { P#sm(r_1), P#sm(r2) }
  P#sm(r_1) == P#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { P#trigger(Heap, P(r_1)) }
  P#everUsed(P(r_1))
);

// ==================================================
// Function used for framing of quantified permission (forall e: Ref :: { (e in refs(r)) } (e in refs(r)) ==> acc(Q(e), wildcard)) in predicate P
// ==================================================

function  P#condqp1(Heap: HeapType, r_1_1: Ref): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, r_1: Ref ::
  { P#condqp1(Heap2Heap, r_1), P#condqp1(Heap1Heap, r_1), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall e: Ref ::
    
    (refs(Heap2Heap, r_1)[e] <==> refs(Heap1Heap, r_1)[e]) && (refs(Heap2Heap, r_1)[e] ==> Heap2Heap[null, Q(e)] == Heap1Heap[null, Q(e)])
  ) ==> P#condqp1(Heap2Heap, r_1) == P#condqp1(Heap1Heap, r_1)
);

// ==================================================
// Translation of predicate P2
// ==================================================

type PredicateType_P2;
function  P2(r_1: Ref): Field PredicateType_P2 FrameType;
function  P2#sm(r_1: Ref): Field PredicateType_P2 PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(P2(r_1)) }
  PredicateMaskField(P2(r_1)) == P2#sm(r_1)
);
axiom (forall r_1: Ref ::
  { P2(r_1) }
  IsPredicateField(P2(r_1))
);
axiom (forall r_1: Ref ::
  { P2(r_1) }
  getPredicateId(P2(r_1)) == 1
);
function  P2#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  P2#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { P2(r_1), P2(r2) }
  P2(r_1) == P2(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { P2#sm(r_1), P2#sm(r2) }
  P2#sm(r_1) == P2#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { P2#trigger(Heap, P2(r_1)) }
  P2#everUsed(P2(r_1))
);

// ==================================================
// Function used for framing of quantified permission (forall e: Ref :: { (e in refs(r)) } (e in refs(r)) ==> acc(Q(e), 1 / 2)) in predicate P2
// ==================================================

function  P2#condqp2(Heap: HeapType, r_1_1: Ref): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, r_1: Ref ::
  { P2#condqp2(Heap2Heap, r_1), P2#condqp2(Heap1Heap, r_1), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall e: Ref ::
    
    (refs(Heap2Heap, r_1)[e] && NoPerm < 1 / 2 <==> refs(Heap1Heap, r_1)[e] && NoPerm < 1 / 2) && (refs(Heap2Heap, r_1)[e] && NoPerm < 1 / 2 ==> Heap2Heap[null, Q(e)] == Heap1Heap[null, Q(e)])
  ) ==> P2#condqp2(Heap2Heap, r_1) == P2#condqp2(Heap1Heap, r_1)
);

// ==================================================
// Translation of predicate R
// ==================================================

type PredicateType_R;
function  R(r_1: Ref): Field PredicateType_R FrameType;
function  R#sm(r_1: Ref): Field PredicateType_R PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(R(r_1)) }
  PredicateMaskField(R(r_1)) == R#sm(r_1)
);
axiom (forall r_1: Ref ::
  { R(r_1) }
  IsPredicateField(R(r_1))
);
axiom (forall r_1: Ref ::
  { R(r_1) }
  getPredicateId(R(r_1)) == 2
);
function  R#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  R#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { R(r_1), R(r2) }
  R(r_1) == R(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { R#sm(r_1), R#sm(r2) }
  R#sm(r_1) == R#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { R#trigger(Heap, R(r_1)) }
  R#everUsed(R(r_1))
);

// ==================================================
// Function used for framing of quantified permission (forall e: Ref :: { (e in refs(r)) } (e in refs(r)) ==> acc(e.q, wildcard)) in predicate R
// ==================================================

function  R#condqp3(Heap: HeapType, r_1_1: Ref): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, r_1: Ref ::
  { R#condqp3(Heap2Heap, r_1), R#condqp3(Heap1Heap, r_1), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall e: Ref ::
    
    (refs(Heap2Heap, r_1)[e] <==> refs(Heap1Heap, r_1)[e]) && (refs(Heap2Heap, r_1)[e] ==> Heap2Heap[e, q_1] == Heap1Heap[e, q_1])
  ) ==> R#condqp3(Heap2Heap, r_1) == R#condqp3(Heap1Heap, r_1)
);

// ==================================================
// Translation of predicate R2
// ==================================================

type PredicateType_R2;
function  R2(r_1: Ref): Field PredicateType_R2 FrameType;
function  R2#sm(r_1: Ref): Field PredicateType_R2 PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(R2(r_1)) }
  PredicateMaskField(R2(r_1)) == R2#sm(r_1)
);
axiom (forall r_1: Ref ::
  { R2(r_1) }
  IsPredicateField(R2(r_1))
);
axiom (forall r_1: Ref ::
  { R2(r_1) }
  getPredicateId(R2(r_1)) == 3
);
function  R2#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  R2#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { R2(r_1), R2(r2) }
  R2(r_1) == R2(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { R2#sm(r_1), R2#sm(r2) }
  R2#sm(r_1) == R2#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { R2#trigger(Heap, R2(r_1)) }
  R2#everUsed(R2(r_1))
);

// ==================================================
// Function used for framing of quantified permission (forall e: Ref :: { (e in refs(r)) } (e in refs(r)) ==> acc(e.q, 1 / 2)) in predicate R2
// ==================================================

function  R2#condqp4(Heap: HeapType, r_1_1: Ref): int;
axiom (forall Heap2Heap: HeapType, Heap1Heap: HeapType, r_1: Ref ::
  { R2#condqp4(Heap2Heap, r_1), R2#condqp4(Heap1Heap, r_1), succHeapTrans(Heap2Heap, Heap1Heap) }
  (forall e: Ref ::
    
    (refs(Heap2Heap, r_1)[e] && NoPerm < 1 / 2 <==> refs(Heap1Heap, r_1)[e] && NoPerm < 1 / 2) && (refs(Heap2Heap, r_1)[e] && NoPerm < 1 / 2 ==> Heap2Heap[e, q_1] == Heap1Heap[e, q_1])
  ) ==> R2#condqp4(Heap2Heap, r_1) == R2#condqp4(Heap1Heap, r_1)
);

// ==================================================
// Translation of predicate Q
// ==================================================

type PredicateType_Q;
function  Q(r_1: Ref): Field PredicateType_Q FrameType;
function  Q#sm(r_1: Ref): Field PredicateType_Q PMaskType;
axiom (forall r_1: Ref ::
  { PredicateMaskField(Q(r_1)) }
  PredicateMaskField(Q(r_1)) == Q#sm(r_1)
);
axiom (forall r_1: Ref ::
  { Q(r_1) }
  IsPredicateField(Q(r_1))
);
axiom (forall r_1: Ref ::
  { Q(r_1) }
  getPredicateId(Q(r_1)) == 4
);
function  Q#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function  Q#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall r_1: Ref, r2: Ref ::
  { Q(r_1), Q(r2) }
  Q(r_1) == Q(r2) ==> r_1 == r2
);
axiom (forall r_1: Ref, r2: Ref ::
  { Q#sm(r_1), Q#sm(r2) }
  Q#sm(r_1) == Q#sm(r2) ==> r_1 == r2
);

axiom (forall Heap: HeapType, r_1: Ref ::
  { Q#trigger(Heap, Q(r_1)) }
  Q#everUsed(Q(r_1))
);

// ==================================================
// Translation of method pred1
// ==================================================

procedure pred1(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var wildcard: real where wildcard > NoPerm;
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var QPMask: MaskType;
  var freshVersion: FrameType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    havoc wildcard;
    perm := wildcard;
    Mask[null, P(r_1)] := Mask[null, P(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(P(r), wildcard) -- 0196.vpr@32.17--33.5
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(r_1))) {
        havoc newVersion;
        Heap[null, P(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding P(r) might fail. There might be insufficient permission to access P(r) (0196.vpr@32.17--33.5) [120]"}
      Mask[null, P(r_1)] > NoPerm;
    assume wildcard < Mask[null, P(r_1)];
    Mask[null, P(r_1)] := Mask[null, P(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[null, Q(e)] } { Mask[null, Q(e)] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] ==> invRecv1(e) == e && qpRange1(e)
      );
      assume (forall r_1_1: Ref ::
        { invRecv1(r_1_1) }
        (refs(Heap, r_1)[invRecv1(r_1_1)]) && qpRange1(r_1_1) ==> invRecv1(r_1_1) == r_1_1
      );
    
    // -- Define updated permissions
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        (refs(Heap, r_1)[invRecv1(r_1_1)]) && qpRange1(r_1_1) ==> (invRecv1(r_1_1) == r_1_1) && QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        !((refs(Heap, r_1)[invRecv1(r_1_1)]) && qpRange1(r_1_1)) ==> QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(P(r), wildcard) -- 0196.vpr@33.15--34.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wildcard assumptions
    havoc wildcard;
    assert {:msg "  Folding P(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@33.15--34.5) [121]"}
      (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > NoPerm
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> wildcard < Mask[null, Q(e_2)]
    );
  
    
    // -- check if receiver acc(Q(e), wildcard * wildcard) is injective
      assert {:msg "  Folding P(r) might fail. Receiver of Q(e) [0196.vpr@4.62--4.62]  might not be injective. (0196.vpr@33.15--34.5) [123]"}
        (forall e_2: Ref, e_2_1: Ref ::
        { neverTriggered2(e_2), neverTriggered2(e_2_1) }
        (((e_2 != e_2_1 && refs(Heap, r_1)[e_2]) && refs(Heap, r_1)[e_2_1])) ==> e_2 != e_2_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding P(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@33.15--34.5) [124]"}
        (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > 0.000000000
      );
    
    // -- assumptions for inverse of receiver acc(Q(e), wildcard * wildcard)
      assume (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] ==> invRecv2(e_2) == e_2 && qpRange2(e_2)
      );
      assume (forall r_2_1: Ref ::
        { invRecv2(r_2_1) }
        (refs(Heap, r_1)[invRecv2(r_2_1)] ) && qpRange2(r_2_1) ==> invRecv2(r_2_1) == r_2_1
      );
    
    // -- assume permission updates for predicate Q
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        (refs(Heap, r_1)[invRecv2(r_2_1)] ) && qpRange2(r_2_1) ==> invRecv2(r_2_1) == r_2_1 && QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)] - wildcard
      );
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        !((refs(Heap, r_1)[invRecv2(r_2_1)] ) && qpRange2(r_2_1)) ==> QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)]
      );
    
    // -- assume permission updates for independent locations 
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    havoc wildcard;
    perm := wildcard;
    Mask[null, P(r_1)] := Mask[null, P(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    if (!HasDirectPerm(Mask, null, P(r_1))) {
      Heap[null, P#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, P(r_1)] := freshVersion;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(P(r), wildcard) -- 0196.vpr@34.17--35.5
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(r_1))) {
        havoc newVersion;
        Heap[null, P(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding P(r) might fail. There might be insufficient permission to access P(r) (0196.vpr@34.17--35.5) [125]"}
      Mask[null, P(r_1)] > NoPerm;
    assume wildcard < Mask[null, P(r_1)];
    Mask[null, P(r_1)] := Mask[null, P(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> invRecv3(e_3) == e_3 && qpRange3(e_3)
      );
      assume (forall r_3_1: Ref ::
        { invRecv3(r_3_1) }
        (refs(Heap, r_1)[invRecv3(r_3_1)] && NoPerm < wildcard) && qpRange3(r_3_1) ==> invRecv3(r_3_1) == r_3_1
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define updated permissions
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        (refs(Heap, r_1)[invRecv3(r_3_1)] && NoPerm < wildcard) && qpRange3(r_3_1) ==> (NoPerm < wildcard ==> invRecv3(r_3_1) == r_3_1) && QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        !((refs(Heap, r_1)[invRecv3(r_3_1)] && NoPerm < wildcard) && qpRange3(r_3_1)) ==> QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := tester(get(r)) -- 0196.vpr@35.8--38.1
    
    // -- Check definedness of tester(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function tester might not hold. There might be insufficient permission to access Q(get(r)) (0196.vpr@35.27--35.27) [126]"}
          Mask[null, Q(get(Heap, r_1))] > NoPerm;
        assume wildcard < Mask[null, Q(get(Heap, r_1))];
        Mask[null, Q(get(Heap, r_1))] := Mask[null, Q(get(Heap, r_1))] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := tester(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method pred2
// ==================================================

procedure pred2(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var QPMask: MaskType;
  var wildcard: real where wildcard > NoPerm;
  var freshVersion: FrameType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, P(r_1)] := Mask[null, P(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(P(r), write) -- 0196.vpr@43.17--44.5
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding P(r) might fail. There might be insufficient permission to access P(r) (0196.vpr@43.17--44.5) [128]"}
        perm <= Mask[null, P(r_1)];
    }
    Mask[null, P(r_1)] := Mask[null, P(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(r_1))) {
        havoc newVersion;
        Heap[null, P(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[null, Q(e)] } { Mask[null, Q(e)] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && NoPerm < wildcard ==> invRecv4(e) == e && qpRange4(e)
      );
      assume (forall r_1_1: Ref ::
        { invRecv4(r_1_1) }
        (refs(Heap, r_1)[invRecv4(r_1_1)] && NoPerm < wildcard) && qpRange4(r_1_1) ==> invRecv4(r_1_1) == r_1_1
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e: Ref ::
      { Heap[null, Q(e)] } { Mask[null, Q(e)] } { refs(Heap, r_1)[e] }
      refs(Heap, r_1)[e] ==> wildcard >= NoPerm
    );
    
    // -- Define updated permissions
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        (refs(Heap, r_1)[invRecv4(r_1_1)] && NoPerm < wildcard) && qpRange4(r_1_1) ==> (NoPerm < wildcard ==> invRecv4(r_1_1) == r_1_1) && QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        !((refs(Heap, r_1)[invRecv4(r_1_1)] && NoPerm < wildcard) && qpRange4(r_1_1)) ==> QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(P(r), write) -- 0196.vpr@44.15--45.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wildcard assumptions
    havoc wildcard;
    assert {:msg "  Folding P(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@44.15--45.5) [129]"}
      (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > NoPerm
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> wildcard < Mask[null, Q(e_2)]
    );
    
    // -- check that the permission amount is positive
      assert {:msg "  Folding P(r) might fail. Fraction wildcard might be negative. (0196.vpr@44.15--45.5) [130]"}
        (forall r_2_1: Ref ::
        { invRecv5(r_2_1) }
        refs(Heap, r_1)[invRecv5(r_2_1)] && qpRange5(r_2_1) ==> wildcard >= NoPerm
      );
    
    // -- check if receiver acc(Q(e), wildcard) is injective
      assert {:msg "  Folding P(r) might fail. Receiver of Q(e) [0196.vpr@4.62--4.62]  might not be injective. (0196.vpr@44.15--45.5) [131]"}
        (forall e_2: Ref, e_2_1: Ref ::
        { neverTriggered5(e_2), neverTriggered5(e_2_1) }
        (((e_2 != e_2_1 && refs(Heap, r_1)[e_2]) && refs(Heap, r_1)[e_2_1]) && NoPerm < wildcard) && NoPerm < wildcard ==> e_2 != e_2_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding P(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@44.15--45.5) [132]"}
        (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > 0.000000000
      );
    
    // -- assumptions for inverse of receiver acc(Q(e), wildcard)
      assume (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] && NoPerm < wildcard ==> invRecv5(e_2) == e_2 && qpRange5(e_2)
      );
      assume (forall r_2_1: Ref ::
        { invRecv5(r_2_1) }
        (refs(Heap, r_1)[invRecv5(r_2_1)] && NoPerm < wildcard) && qpRange5(r_2_1) ==> invRecv5(r_2_1) == r_2_1
      );
    
    // -- assume permission updates for predicate Q
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        (refs(Heap, r_1)[invRecv5(r_2_1)] && NoPerm < wildcard) && qpRange5(r_2_1) ==> invRecv5(r_2_1) == r_2_1 && QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)] - wildcard
      );
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        !((refs(Heap, r_1)[invRecv5(r_2_1)] && NoPerm < wildcard) && qpRange5(r_2_1)) ==> QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)]
      );
    
    // -- assume permission updates for independent locations 
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    perm := FullPerm;
    Mask[null, P(r_1)] := Mask[null, P(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    if (!HasDirectPerm(Mask, null, P(r_1))) {
      Heap[null, P#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, P(r_1)] := freshVersion;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(P(r), write) -- 0196.vpr@45.17--46.5
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding P(r) might fail. There might be insufficient permission to access P(r) (0196.vpr@45.17--46.5) [134]"}
        perm <= Mask[null, P(r_1)];
    }
    Mask[null, P(r_1)] := Mask[null, P(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(r_1))) {
        havoc newVersion;
        Heap[null, P(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> invRecv6(e_3) == e_3 && qpRange6(e_3)
      );
      assume (forall r_3_1: Ref ::
        { invRecv6(r_3_1) }
        (refs(Heap, r_1)[invRecv6(r_3_1)] && NoPerm < wildcard) && qpRange6(r_3_1) ==> invRecv6(r_3_1) == r_3_1
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define updated permissions
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        (refs(Heap, r_1)[invRecv6(r_3_1)] && NoPerm < wildcard) && qpRange6(r_3_1) ==> (NoPerm < wildcard ==> invRecv6(r_3_1) == r_3_1) && QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        !((refs(Heap, r_1)[invRecv6(r_3_1)] && NoPerm < wildcard) && qpRange6(r_3_1)) ==> QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := tester(get(r)) -- 0196.vpr@46.8--49.1
    
    // -- Check definedness of tester(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function tester might not hold. There might be insufficient permission to access Q(get(r)) (0196.vpr@46.27--46.27) [135]"}
          Mask[null, Q(get(Heap, r_1))] > NoPerm;
        assume wildcard < Mask[null, Q(get(Heap, r_1))];
        Mask[null, Q(get(Heap, r_1))] := Mask[null, Q(get(Heap, r_1))] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := tester(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method pred3
// ==================================================

procedure pred3(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var QPMask: MaskType;
  var wildcard: real where wildcard > NoPerm;
  var freshVersion: FrameType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, P(r_1)] := Mask[null, P(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(P(r), 1 / 2) -- 0196.vpr@54.17--55.5
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Unfolding P(r) might fail. Fraction 1 / 2 might be negative. (0196.vpr@54.17--55.5) [136]"}
      1 / 2 >= NoPerm;
    perm := NoPerm;
    perm := perm + 1 / 2;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding P(r) might fail. There might be insufficient permission to access P(r) (0196.vpr@54.17--55.5) [137]"}
        perm <= Mask[null, P(r_1)];
    }
    Mask[null, P(r_1)] := Mask[null, P(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(r_1))) {
        havoc newVersion;
        Heap[null, P(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[null, Q(e)] } { Mask[null, Q(e)] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && NoPerm < wildcard ==> invRecv7(e) == e && qpRange7(e)
      );
      assume (forall r_1_1: Ref ::
        { invRecv7(r_1_1) }
        (refs(Heap, r_1)[invRecv7(r_1_1)] && NoPerm < wildcard) && qpRange7(r_1_1) ==> invRecv7(r_1_1) == r_1_1
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e: Ref ::
      { Heap[null, Q(e)] } { Mask[null, Q(e)] } { refs(Heap, r_1)[e] }
      refs(Heap, r_1)[e] ==> wildcard >= NoPerm
    );
    
    // -- Define updated permissions
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        (refs(Heap, r_1)[invRecv7(r_1_1)] && NoPerm < wildcard) && qpRange7(r_1_1) ==> (NoPerm < wildcard ==> invRecv7(r_1_1) == r_1_1) && QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        !((refs(Heap, r_1)[invRecv7(r_1_1)] && NoPerm < wildcard) && qpRange7(r_1_1)) ==> QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(P(r), 1 / 2) -- 0196.vpr@55.15--56.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wildcard assumptions
    havoc wildcard;
    assert {:msg "  Folding P(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@55.15--56.5) [138]"}
      (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > NoPerm
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> wildcard < Mask[null, Q(e_2)]
    );
    
    // -- check that the permission amount is positive
      assert {:msg "  Folding P(r) might fail. Fraction wildcard * (1 / 2) might be negative. (0196.vpr@55.15--56.5) [139]"}
        (forall r_2_1: Ref ::
        { invRecv8(r_2_1) }
        refs(Heap, r_1)[invRecv8(r_2_1)] && qpRange8(r_2_1) ==> wildcard >= NoPerm
      );
    
    // -- check if receiver acc(Q(e), wildcard * (1 / 2)) is injective
      assert {:msg "  Folding P(r) might fail. Receiver of Q(e) [0196.vpr@4.62--4.62]  might not be injective. (0196.vpr@55.15--56.5) [140]"}
        (forall e_2: Ref, e_2_1: Ref ::
        { neverTriggered8(e_2), neverTriggered8(e_2_1) }
        (((e_2 != e_2_1 && refs(Heap, r_1)[e_2]) && refs(Heap, r_1)[e_2_1]) && NoPerm < wildcard) && NoPerm < wildcard ==> e_2 != e_2_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding P(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@55.15--56.5) [141]"}
        (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > 0.000000000
      );
    
    // -- assumptions for inverse of receiver acc(Q(e), wildcard * (1 / 2))
      assume (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] && NoPerm < wildcard ==> invRecv8(e_2) == e_2 && qpRange8(e_2)
      );
      assume (forall r_2_1: Ref ::
        { invRecv8(r_2_1) }
        (refs(Heap, r_1)[invRecv8(r_2_1)] && NoPerm < wildcard) && qpRange8(r_2_1) ==> invRecv8(r_2_1) == r_2_1
      );
    
    // -- assume permission updates for predicate Q
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        (refs(Heap, r_1)[invRecv8(r_2_1)] && NoPerm < wildcard) && qpRange8(r_2_1) ==> invRecv8(r_2_1) == r_2_1 && QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)] - wildcard
      );
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        !((refs(Heap, r_1)[invRecv8(r_2_1)] && NoPerm < wildcard) && qpRange8(r_2_1)) ==> QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)]
      );
    
    // -- assume permission updates for independent locations 
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    perm := 1 / 2;
    assume perm >= NoPerm;
    Mask[null, P(r_1)] := Mask[null, P(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    if (!HasDirectPerm(Mask, null, P(r_1))) {
      Heap[null, P#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, P(r_1)] := freshVersion;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(P(r), 1 / 2) -- 0196.vpr@56.17--57.5
    assume P#trigger(Heap, P(r_1));
    assume Heap[null, P(r_1)] == FrameFragment(P#condqp1(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Unfolding P(r) might fail. Fraction 1 / 2 might be negative. (0196.vpr@56.17--57.5) [142]"}
      1 / 2 >= NoPerm;
    perm := NoPerm;
    perm := perm + 1 / 2;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding P(r) might fail. There might be insufficient permission to access P(r) (0196.vpr@56.17--57.5) [143]"}
        perm <= Mask[null, P(r_1)];
    }
    Mask[null, P(r_1)] := Mask[null, P(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P(r_1))) {
        havoc newVersion;
        Heap[null, P(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> invRecv9(e_3) == e_3 && qpRange9(e_3)
      );
      assume (forall r_3_1: Ref ::
        { invRecv9(r_3_1) }
        (refs(Heap, r_1)[invRecv9(r_3_1)] && NoPerm < wildcard) && qpRange9(r_3_1) ==> invRecv9(r_3_1) == r_3_1
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define updated permissions
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        (refs(Heap, r_1)[invRecv9(r_3_1)] && NoPerm < wildcard) && qpRange9(r_3_1) ==> (NoPerm < wildcard ==> invRecv9(r_3_1) == r_3_1) && QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        !((refs(Heap, r_1)[invRecv9(r_3_1)] && NoPerm < wildcard) && qpRange9(r_3_1)) ==> QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := tester(get(r)) -- 0196.vpr@57.8--60.1
    
    // -- Check definedness of tester(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function tester might not hold. There might be insufficient permission to access Q(get(r)) (0196.vpr@57.27--57.27) [144]"}
          Mask[null, Q(get(Heap, r_1))] > NoPerm;
        assume wildcard < Mask[null, Q(get(Heap, r_1))];
        Mask[null, Q(get(Heap, r_1))] := Mask[null, Q(get(Heap, r_1))] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := tester(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method pred4
// ==================================================

procedure pred4(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var wildcard: real where wildcard > NoPerm;
  var QPMask: MaskType;
  var freshVersion: FrameType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, P2(r_1)] := Mask[null, P2(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(P2(r), wildcard) -- 0196.vpr@65.18--66.5
    assume P2#trigger(Heap, P2(r_1));
    assume Heap[null, P2(r_1)] == FrameFragment(P2#condqp2(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P2(r_1))) {
        havoc newVersion;
        Heap[null, P2(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding P2(r) might fail. There might be insufficient permission to access P2(r) (0196.vpr@65.18--66.5) [145]"}
      Mask[null, P2(r_1)] > NoPerm;
    assume wildcard < Mask[null, P2(r_1)];
    Mask[null, P2(r_1)] := Mask[null, P2(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[null, Q(e)] } { Mask[null, Q(e)] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && NoPerm < wildcard ==> invRecv10(e) == e && qpRange10(e)
      );
      assume (forall r_1_1: Ref ::
        { invRecv10(r_1_1) }
        (refs(Heap, r_1)[invRecv10(r_1_1)] && NoPerm < wildcard) && qpRange10(r_1_1) ==> invRecv10(r_1_1) == r_1_1
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e: Ref ::
      { Heap[null, Q(e)] } { Mask[null, Q(e)] } { refs(Heap, r_1)[e] }
      refs(Heap, r_1)[e] ==> wildcard >= NoPerm
    );
    
    // -- Define updated permissions
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        (refs(Heap, r_1)[invRecv10(r_1_1)] && NoPerm < wildcard) && qpRange10(r_1_1) ==> (NoPerm < wildcard ==> invRecv10(r_1_1) == r_1_1) && QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_1_1: Ref ::
        { QPMask[null, Q(r_1_1)] }
        !((refs(Heap, r_1)[invRecv10(r_1_1)] && NoPerm < wildcard) && qpRange10(r_1_1)) ==> QPMask[null, Q(r_1_1)] == Mask[null, Q(r_1_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(P2(r), wildcard) -- 0196.vpr@66.16--67.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wildcard assumptions
    havoc wildcard;
    assert {:msg "  Folding P2(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@66.16--67.5) [146]"}
      (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > NoPerm
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> wildcard < Mask[null, Q(e_2)]
    );
    
    // -- check that the permission amount is positive
      assert {:msg "  Folding P2(r) might fail. Fraction 1 / 2 * wildcard might be negative. (0196.vpr@66.16--67.5) [147]"}
        (forall r_2_1: Ref ::
        { invRecv11(r_2_1) }
        refs(Heap, r_1)[invRecv11(r_2_1)] && qpRange11(r_2_1) ==> wildcard >= NoPerm
      );
    
    // -- check if receiver acc(Q(e), 1 / 2 * wildcard) is injective
      assert {:msg "  Folding P2(r) might fail. Receiver of Q(e) [0196.vpr@5.63--5.63]  might not be injective. (0196.vpr@66.16--67.5) [148]"}
        (forall e_2: Ref, e_2_1: Ref ::
        { neverTriggered11(e_2), neverTriggered11(e_2_1) }
        (((e_2 != e_2_1 && refs(Heap, r_1)[e_2]) && refs(Heap, r_1)[e_2_1]) && NoPerm < wildcard) && NoPerm < wildcard ==> e_2 != e_2_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding P2(r) might fail. There might be insufficient permission to access Q(e) (0196.vpr@66.16--67.5) [149]"}
        (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] ==> Mask[null, Q(e_2)] > 0.000000000
      );
    
    // -- assumptions for inverse of receiver acc(Q(e), 1 / 2 * wildcard)
      assume (forall e_2: Ref ::
        { Heap[null, Q(e_2)] } { Mask[null, Q(e_2)] } { refs(Heap, r_1)[e_2] }
        refs(Heap, r_1)[e_2] && NoPerm < wildcard ==> invRecv11(e_2) == e_2 && qpRange11(e_2)
      );
      assume (forall r_2_1: Ref ::
        { invRecv11(r_2_1) }
        (refs(Heap, r_1)[invRecv11(r_2_1)] && NoPerm < wildcard) && qpRange11(r_2_1) ==> invRecv11(r_2_1) == r_2_1
      );
    
    // -- assume permission updates for predicate Q
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        (refs(Heap, r_1)[invRecv11(r_2_1)] && NoPerm < wildcard) && qpRange11(r_2_1) ==> invRecv11(r_2_1) == r_2_1 && QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)] - wildcard
      );
      assume (forall r_2_1: Ref ::
        { QPMask[null, Q(r_2_1)] }
        !((refs(Heap, r_1)[invRecv11(r_2_1)] && NoPerm < wildcard) && qpRange11(r_2_1)) ==> QPMask[null, Q(r_2_1)] == Mask[null, Q(r_2_1)]
      );
    
    // -- assume permission updates for independent locations 
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    havoc wildcard;
    perm := wildcard;
    Mask[null, P2(r_1)] := Mask[null, P2(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume P2#trigger(Heap, P2(r_1));
    assume Heap[null, P2(r_1)] == FrameFragment(P2#condqp2(Heap, r_1));
    if (!HasDirectPerm(Mask, null, P2(r_1))) {
      Heap[null, P2#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, P2(r_1)] := freshVersion;
    }
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(P2(r), wildcard) -- 0196.vpr@67.18--68.5
    assume P2#trigger(Heap, P2(r_1));
    assume Heap[null, P2(r_1)] == FrameFragment(P2#condqp2(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, P2(r_1))) {
        havoc newVersion;
        Heap[null, P2(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding P2(r) might fail. There might be insufficient permission to access P2(r) (0196.vpr@67.18--68.5) [150]"}
      Mask[null, P2(r_1)] > NoPerm;
    assume wildcard < Mask[null, P2(r_1)];
    Mask[null, P2(r_1)] := Mask[null, P2(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> invRecv12(e_3) == e_3 && qpRange12(e_3)
      );
      assume (forall r_3_1: Ref ::
        { invRecv12(r_3_1) }
        (refs(Heap, r_1)[invRecv12(r_3_1)] && NoPerm < wildcard) && qpRange12(r_3_1) ==> invRecv12(r_3_1) == r_3_1
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[null, Q(e_3)] } { Mask[null, Q(e_3)] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define updated permissions
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        (refs(Heap, r_1)[invRecv12(r_3_1)] && NoPerm < wildcard) && qpRange12(r_3_1) ==> (NoPerm < wildcard ==> invRecv12(r_3_1) == r_3_1) && QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)] + wildcard
      );
    
    // -- Define independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        (o_2 != null || !IsPredicateField(f_4)) || getPredicateId(f_4) != 4 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
      assume (forall r_3_1: Ref ::
        { QPMask[null, Q(r_3_1)] }
        !((refs(Heap, r_1)[invRecv12(r_3_1)] && NoPerm < wildcard) && qpRange12(r_3_1)) ==> QPMask[null, Q(r_3_1)] == Mask[null, Q(r_3_1)]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := tester(get(r)) -- 0196.vpr@68.8--71.1
    
    // -- Check definedness of tester(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function tester might not hold. There might be insufficient permission to access Q(get(r)) (0196.vpr@68.27--68.27) [151]"}
          Mask[null, Q(get(Heap, r_1))] > NoPerm;
        assume wildcard < Mask[null, Q(get(Heap, r_1))];
        Mask[null, Q(get(Heap, r_1))] := Mask[null, Q(get(Heap, r_1))] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := tester(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method func1
// ==================================================

procedure func1(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var wildcard: real where wildcard > NoPerm;
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var QPMask: MaskType;
  var freshVersion: FrameType;
  var newPMask: PMaskType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    havoc wildcard;
    perm := wildcard;
    Mask[null, R(r_1)] := Mask[null, R(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(R(r), wildcard) -- 0196.vpr@76.17--77.5
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R(r_1))) {
        havoc newVersion;
        Heap[null, R(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding R(r) might fail. There might be insufficient permission to access R(r) (0196.vpr@76.17--77.5) [152]"}
      Mask[null, R(r_1)] > NoPerm;
    assume wildcard < Mask[null, R(r_1)];
    Mask[null, R(r_1)] := Mask[null, R(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && NoPerm < wildcard ==> qpRange13(e) && invRecv13(e) == e
      );
      assume (forall o_2: Ref ::
        { invRecv13(o_2) }
        (refs(Heap, r_1)[invRecv13(o_2)] && NoPerm < wildcard) && qpRange13(o_2) ==> invRecv13(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && wildcard > NoPerm ==> e != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e: Ref ::
      { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
      refs(Heap, r_1)[e] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv13(o_2)] && NoPerm < wildcard) && qpRange13(o_2) ==> (NoPerm < wildcard ==> invRecv13(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv13(o_2)] && NoPerm < wildcard) && qpRange13(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(R(r), wildcard) -- 0196.vpr@77.15--78.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wild card assumptions
    havoc wildcard;
    assert {:msg "  Folding R(r) might fail. There might be insufficient permission to access e.q (0196.vpr@77.15--78.5) [153]"}
      (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
    );
    assume (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> wildcard < Mask[e_1, q_1]
    );
    
    // -- check that the permission amount is positive
      assert {:msg "  Folding R(r) might fail. Fraction wildcard * wildcard might be negative. (0196.vpr@77.15--78.5) [154]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && dummyFunction(Heap[e_1, q_1]) ==> wildcard >= NoPerm
      );
    
    // -- check if receiver e is injective
      assert {:msg "  Folding R(r) might fail. Receiver of e.q [0196.vpr@6.64--6.64]  might not be injective. (0196.vpr@77.15--78.5) [155]"}
        (forall e_1: Ref, e_1_1: Ref ::
        { neverTriggered14(e_1), neverTriggered14(e_1_1) }
        (((e_1 != e_1_1 && refs(Heap, r_1)[e_1]) && refs(Heap, r_1)[e_1_1]) && NoPerm < wildcard) && NoPerm < wildcard ==> e_1 != e_1_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding R(r) might fail. There might be insufficient permission to access e.q (0196.vpr@77.15--78.5) [156]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
      );
    
    // -- assumptions for inverse of receiver e
      assume (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && NoPerm < wildcard ==> qpRange14(e_1) && invRecv14(e_1) == e_1
      );
      assume (forall o_2: Ref ::
        { invRecv14(o_2) }
        refs(Heap, r_1)[invRecv14(o_2)] && (NoPerm < wildcard && qpRange14(o_2)) ==> invRecv14(o_2) == o_2
      );
    
    // -- assume permission updates for field q
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        (refs(Heap, r_1)[invRecv14(o_2)] && (NoPerm < wildcard && qpRange14(o_2)) ==> invRecv14(o_2) == o_2 && QPMask[o_2, q_1] == Mask[o_2, q_1] - wildcard) && (!(refs(Heap, r_1)[invRecv14(o_2)] && (NoPerm < wildcard && qpRange14(o_2))) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    havoc wildcard;
    perm := wildcard;
    Mask[null, R(r_1)] := Mask[null, R(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    if (!HasDirectPerm(Mask, null, R(r_1))) {
      Heap[null, R#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, R(r_1)] := freshVersion;
    }
    // register all known folded permissions guarded by predicate R
    havoc newPMask;
    assume (forall <A, B> o_3: Ref, f_6: (Field A B) ::
      { newPMask[o_3, f_6] }
      Heap[null, R#sm(r_1)][o_3, f_6] ==> newPMask[o_3, f_6]
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> newPMask[e_2, q_1]
    );
    Heap[null, R#sm(r_1)] := newPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(R(r), wildcard) -- 0196.vpr@78.17--79.5
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R(r_1))) {
        havoc newVersion;
        Heap[null, R(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding R(r) might fail. There might be insufficient permission to access R(r) (0196.vpr@78.17--79.5) [157]"}
      Mask[null, R(r_1)] > NoPerm;
    assume wildcard < Mask[null, R(r_1)];
    Mask[null, R(r_1)] := Mask[null, R(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> qpRange15(e_3) && invRecv15(e_3) == e_3
      );
      assume (forall o_2: Ref ::
        { invRecv15(o_2) }
        (refs(Heap, r_1)[invRecv15(o_2)] && NoPerm < wildcard) && qpRange15(o_2) ==> invRecv15(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && wildcard > NoPerm ==> e_3 != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv15(o_2)] && NoPerm < wildcard) && qpRange15(o_2) ==> (NoPerm < wildcard ==> invRecv15(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv15(o_2)] && NoPerm < wildcard) && qpRange15(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := testerfield(get(r)) -- 0196.vpr@79.8--82.1
    
    // -- Check definedness of testerfield(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function testerfield might not hold. There might be insufficient permission to access get(r).q (0196.vpr@79.32--79.32) [158]"}
          Mask[get(Heap, r_1), q_1] > NoPerm;
        assume wildcard < Mask[get(Heap, r_1), q_1];
        Mask[get(Heap, r_1), q_1] := Mask[get(Heap, r_1), q_1] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := testerfield(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method func2
// ==================================================

procedure func2(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var QPMask: MaskType;
  var wildcard: real where wildcard > NoPerm;
  var freshVersion: FrameType;
  var newPMask: PMaskType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, R(r_1)] := Mask[null, R(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(R(r), write) -- 0196.vpr@87.17--88.5
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding R(r) might fail. There might be insufficient permission to access R(r) (0196.vpr@87.17--88.5) [160]"}
        perm <= Mask[null, R(r_1)];
    }
    Mask[null, R(r_1)] := Mask[null, R(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R(r_1))) {
        havoc newVersion;
        Heap[null, R(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && NoPerm < wildcard ==> qpRange16(e) && invRecv16(e) == e
      );
      assume (forall o_2: Ref ::
        { invRecv16(o_2) }
        (refs(Heap, r_1)[invRecv16(o_2)] && NoPerm < wildcard) && qpRange16(o_2) ==> invRecv16(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] ==> e != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e: Ref ::
      { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
      refs(Heap, r_1)[e] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv16(o_2)] && NoPerm < wildcard) && qpRange16(o_2) ==> (NoPerm < wildcard ==> invRecv16(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv16(o_2)] && NoPerm < wildcard) && qpRange16(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(R(r), write) -- 0196.vpr@88.15--89.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wild card assumptions
    havoc wildcard;
    assert {:msg "  Folding R(r) might fail. There might be insufficient permission to access e.q (0196.vpr@88.15--89.5) [161]"}
      (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
    );
    assume (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> wildcard < Mask[e_1, q_1]
    );
    
    // -- check that the permission amount is positive
      assert {:msg "  Folding R(r) might fail. Fraction wildcard might be negative. (0196.vpr@88.15--89.5) [162]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && dummyFunction(Heap[e_1, q_1]) ==> wildcard >= NoPerm
      );
    
    // -- check if receiver e is injective
      assert {:msg "  Folding R(r) might fail. Receiver of e.q [0196.vpr@6.64--6.64]  might not be injective. (0196.vpr@88.15--89.5) [163]"}
        (forall e_1: Ref, e_1_1: Ref ::
        { neverTriggered17(e_1), neverTriggered17(e_1_1) }
        (((e_1 != e_1_1 && refs(Heap, r_1)[e_1]) && refs(Heap, r_1)[e_1_1]) && NoPerm < wildcard) && NoPerm < wildcard ==> e_1 != e_1_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding R(r) might fail. There might be insufficient permission to access e.q (0196.vpr@88.15--89.5) [164]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
      );
    
    // -- assumptions for inverse of receiver e
      assume (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && NoPerm < wildcard ==> qpRange17(e_1) && invRecv17(e_1) == e_1
      );
      assume (forall o_2: Ref ::
        { invRecv17(o_2) }
        refs(Heap, r_1)[invRecv17(o_2)] && (NoPerm < wildcard && qpRange17(o_2)) ==> invRecv17(o_2) == o_2
      );
    
    // -- assume permission updates for field q
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        (refs(Heap, r_1)[invRecv17(o_2)] && (NoPerm < wildcard && qpRange17(o_2)) ==> invRecv17(o_2) == o_2 && QPMask[o_2, q_1] == Mask[o_2, q_1] - wildcard) && (!(refs(Heap, r_1)[invRecv17(o_2)] && (NoPerm < wildcard && qpRange17(o_2))) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    perm := FullPerm;
    Mask[null, R(r_1)] := Mask[null, R(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    if (!HasDirectPerm(Mask, null, R(r_1))) {
      Heap[null, R#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, R(r_1)] := freshVersion;
    }
    // register all known folded permissions guarded by predicate R
    havoc newPMask;
    assume (forall <A, B> o_4: Ref, f_7: (Field A B) ::
      { newPMask[o_4, f_7] }
      Heap[null, R#sm(r_1)][o_4, f_7] ==> newPMask[o_4, f_7]
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> newPMask[e_2, q_1]
    );
    Heap[null, R#sm(r_1)] := newPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(R(r), write) -- 0196.vpr@89.17--90.5
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding R(r) might fail. There might be insufficient permission to access R(r) (0196.vpr@89.17--90.5) [166]"}
        perm <= Mask[null, R(r_1)];
    }
    Mask[null, R(r_1)] := Mask[null, R(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R(r_1))) {
        havoc newVersion;
        Heap[null, R(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> qpRange18(e_3) && invRecv18(e_3) == e_3
      );
      assume (forall o_2: Ref ::
        { invRecv18(o_2) }
        (refs(Heap, r_1)[invRecv18(o_2)] && NoPerm < wildcard) && qpRange18(o_2) ==> invRecv18(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] ==> e_3 != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv18(o_2)] && NoPerm < wildcard) && qpRange18(o_2) ==> (NoPerm < wildcard ==> invRecv18(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv18(o_2)] && NoPerm < wildcard) && qpRange18(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := testerfield(get(r)) -- 0196.vpr@90.8--93.1
    
    // -- Check definedness of testerfield(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function testerfield might not hold. There might be insufficient permission to access get(r).q (0196.vpr@90.32--90.32) [167]"}
          Mask[get(Heap, r_1), q_1] > NoPerm;
        assume wildcard < Mask[get(Heap, r_1), q_1];
        Mask[get(Heap, r_1), q_1] := Mask[get(Heap, r_1), q_1] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := testerfield(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method func3
// ==================================================

procedure func3(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var QPMask: MaskType;
  var wildcard: real where wildcard > NoPerm;
  var freshVersion: FrameType;
  var newPMask: PMaskType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, R(r_1)] := Mask[null, R(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(R(r), 1 / 2) -- 0196.vpr@98.17--99.5
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Unfolding R(r) might fail. Fraction 1 / 2 might be negative. (0196.vpr@98.17--99.5) [168]"}
      1 / 2 >= NoPerm;
    perm := NoPerm;
    perm := perm + 1 / 2;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding R(r) might fail. There might be insufficient permission to access R(r) (0196.vpr@98.17--99.5) [169]"}
        perm <= Mask[null, R(r_1)];
    }
    Mask[null, R(r_1)] := Mask[null, R(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R(r_1))) {
        havoc newVersion;
        Heap[null, R(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && NoPerm < wildcard ==> qpRange19(e) && invRecv19(e) == e
      );
      assume (forall o_2: Ref ::
        { invRecv19(o_2) }
        (refs(Heap, r_1)[invRecv19(o_2)] && NoPerm < wildcard) && qpRange19(o_2) ==> invRecv19(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && wildcard > NoPerm ==> e != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e: Ref ::
      { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
      refs(Heap, r_1)[e] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv19(o_2)] && NoPerm < wildcard) && qpRange19(o_2) ==> (NoPerm < wildcard ==> invRecv19(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv19(o_2)] && NoPerm < wildcard) && qpRange19(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(R(r), 1 / 2) -- 0196.vpr@99.15--100.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wild card assumptions
    havoc wildcard;
    assert {:msg "  Folding R(r) might fail. There might be insufficient permission to access e.q (0196.vpr@99.15--100.5) [170]"}
      (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
    );
    assume (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> wildcard < Mask[e_1, q_1]
    );
    
    // -- check that the permission amount is positive
      assert {:msg "  Folding R(r) might fail. Fraction wildcard * (1 / 2) might be negative. (0196.vpr@99.15--100.5) [171]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && dummyFunction(Heap[e_1, q_1]) ==> wildcard >= NoPerm
      );
    
    // -- check if receiver e is injective
      assert {:msg "  Folding R(r) might fail. Receiver of e.q [0196.vpr@6.64--6.64]  might not be injective. (0196.vpr@99.15--100.5) [172]"}
        (forall e_1: Ref, e_1_1: Ref ::
        { neverTriggered20(e_1), neverTriggered20(e_1_1) }
        (((e_1 != e_1_1 && refs(Heap, r_1)[e_1]) && refs(Heap, r_1)[e_1_1]) && NoPerm < wildcard) && NoPerm < wildcard ==> e_1 != e_1_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding R(r) might fail. There might be insufficient permission to access e.q (0196.vpr@99.15--100.5) [173]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
      );
    
    // -- assumptions for inverse of receiver e
      assume (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && NoPerm < wildcard ==> qpRange20(e_1) && invRecv20(e_1) == e_1
      );
      assume (forall o_2: Ref ::
        { invRecv20(o_2) }
        refs(Heap, r_1)[invRecv20(o_2)] && (NoPerm < wildcard && qpRange20(o_2)) ==> invRecv20(o_2) == o_2
      );
    
    // -- assume permission updates for field q
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        (refs(Heap, r_1)[invRecv20(o_2)] && (NoPerm < wildcard && qpRange20(o_2)) ==> invRecv20(o_2) == o_2 && QPMask[o_2, q_1] == Mask[o_2, q_1] - wildcard) && (!(refs(Heap, r_1)[invRecv20(o_2)] && (NoPerm < wildcard && qpRange20(o_2))) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    perm := 1 / 2;
    assume perm >= NoPerm;
    Mask[null, R(r_1)] := Mask[null, R(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    if (!HasDirectPerm(Mask, null, R(r_1))) {
      Heap[null, R#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, R(r_1)] := freshVersion;
    }
    // register all known folded permissions guarded by predicate R
    havoc newPMask;
    assume (forall <A, B> o_5: Ref, f_8: (Field A B) ::
      { newPMask[o_5, f_8] }
      Heap[null, R#sm(r_1)][o_5, f_8] ==> newPMask[o_5, f_8]
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> newPMask[e_2, q_1]
    );
    Heap[null, R#sm(r_1)] := newPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(R(r), 1 / 2) -- 0196.vpr@100.17--101.5
    assume R#trigger(Heap, R(r_1));
    assume Heap[null, R(r_1)] == FrameFragment(R#condqp3(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Unfolding R(r) might fail. Fraction 1 / 2 might be negative. (0196.vpr@100.17--101.5) [174]"}
      1 / 2 >= NoPerm;
    perm := NoPerm;
    perm := perm + 1 / 2;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding R(r) might fail. There might be insufficient permission to access R(r) (0196.vpr@100.17--101.5) [175]"}
        perm <= Mask[null, R(r_1)];
    }
    Mask[null, R(r_1)] := Mask[null, R(r_1)] - perm;
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R(r_1))) {
        havoc newVersion;
        Heap[null, R(r_1)] := newVersion;
      }
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> qpRange21(e_3) && invRecv21(e_3) == e_3
      );
      assume (forall o_2: Ref ::
        { invRecv21(o_2) }
        (refs(Heap, r_1)[invRecv21(o_2)] && NoPerm < wildcard) && qpRange21(o_2) ==> invRecv21(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && wildcard > NoPerm ==> e_3 != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv21(o_2)] && NoPerm < wildcard) && qpRange21(o_2) ==> (NoPerm < wildcard ==> invRecv21(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv21(o_2)] && NoPerm < wildcard) && qpRange21(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := testerfield(get(r)) -- 0196.vpr@101.8--104.1
    
    // -- Check definedness of testerfield(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function testerfield might not hold. There might be insufficient permission to access get(r).q (0196.vpr@101.32--101.32) [176]"}
          Mask[get(Heap, r_1), q_1] > NoPerm;
        assume wildcard < Mask[get(Heap, r_1), q_1];
        Mask[get(Heap, r_1), q_1] := Mask[get(Heap, r_1), q_1] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := testerfield(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method func4
// ==================================================

procedure func4(r_1: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var r2: Ref;
  var newVersion: FrameType;
  var wildcard: real where wildcard > NoPerm;
  var QPMask: MaskType;
  var freshVersion: FrameType;
  var newPMask: PMaskType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[r_1, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, R2(r_1)] := Mask[null, R2(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Assumptions about local variables
    assume Heap[r2, $allocated];
  
  // -- Translating statement: unfold acc(R2(r), wildcard) -- 0196.vpr@109.18--110.5
    assume R2#trigger(Heap, R2(r_1));
    assume Heap[null, R2(r_1)] == FrameFragment(R2#condqp4(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R2(r_1))) {
        havoc newVersion;
        Heap[null, R2(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding R2(r) might fail. There might be insufficient permission to access R2(r) (0196.vpr@109.18--110.5) [177]"}
      Mask[null, R2(r_1)] > NoPerm;
    assume wildcard < Mask[null, R2(r_1)];
    Mask[null, R2(r_1)] := Mask[null, R2(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && NoPerm < wildcard ==> qpRange22(e) && invRecv22(e) == e
      );
      assume (forall o_2: Ref ::
        { invRecv22(o_2) }
        (refs(Heap, r_1)[invRecv22(o_2)] && NoPerm < wildcard) && qpRange22(o_2) ==> invRecv22(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e: Ref ::
        { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
        refs(Heap, r_1)[e] && wildcard > NoPerm ==> e != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e: Ref ::
      { Heap[e, q_1] } { QPMask[e, q_1] } { refs(Heap, r_1)[e] }
      refs(Heap, r_1)[e] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv22(o_2)] && NoPerm < wildcard) && qpRange22(o_2) ==> (NoPerm < wildcard ==> invRecv22(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv22(o_2)] && NoPerm < wildcard) && qpRange22(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(R2(r), wildcard) -- 0196.vpr@110.16--111.5
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    // wild card assumptions
    havoc wildcard;
    assert {:msg "  Folding R2(r) might fail. There might be insufficient permission to access e.q (0196.vpr@110.16--111.5) [178]"}
      (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
    );
    assume (forall e_1: Ref ::
      
      refs(Heap, r_1)[e_1] ==> wildcard < Mask[e_1, q_1]
    );
    
    // -- check that the permission amount is positive
      assert {:msg "  Folding R2(r) might fail. Fraction 1 / 2 * wildcard might be negative. (0196.vpr@110.16--111.5) [179]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && dummyFunction(Heap[e_1, q_1]) ==> wildcard >= NoPerm
      );
    
    // -- check if receiver e is injective
      assert {:msg "  Folding R2(r) might fail. Receiver of e.q [0196.vpr@7.65--7.65]  might not be injective. (0196.vpr@110.16--111.5) [180]"}
        (forall e_1: Ref, e_1_1: Ref ::
        { neverTriggered23(e_1), neverTriggered23(e_1_1) }
        (((e_1 != e_1_1 && refs(Heap, r_1)[e_1]) && refs(Heap, r_1)[e_1_1]) && NoPerm < wildcard) && NoPerm < wildcard ==> e_1 != e_1_1
      );
    
    // -- check if sufficient permission is held
      assert {:msg "  Folding R2(r) might fail. There might be insufficient permission to access e.q (0196.vpr@110.16--111.5) [181]"}
        (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] ==> Mask[e_1, q_1] > NoPerm
      );
    
    // -- assumptions for inverse of receiver e
      assume (forall e_1: Ref ::
        { Heap[e_1, q_1] } { QPMask[e_1, q_1] } { refs(Heap, r_1)[e_1] }
        refs(Heap, r_1)[e_1] && NoPerm < wildcard ==> qpRange23(e_1) && invRecv23(e_1) == e_1
      );
      assume (forall o_2: Ref ::
        { invRecv23(o_2) }
        refs(Heap, r_1)[invRecv23(o_2)] && (NoPerm < wildcard && qpRange23(o_2)) ==> invRecv23(o_2) == o_2
      );
    
    // -- assume permission updates for field q
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        (refs(Heap, r_1)[invRecv23(o_2)] && (NoPerm < wildcard && qpRange23(o_2)) ==> invRecv23(o_2) == o_2 && QPMask[o_2, q_1] == Mask[o_2, q_1] - wildcard) && (!(refs(Heap, r_1)[invRecv23(o_2)] && (NoPerm < wildcard && qpRange23(o_2))) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
    
    // -- assume permission updates for independent locations
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    havoc wildcard;
    perm := wildcard;
    Mask[null, R2(r_1)] := Mask[null, R2(r_1)] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume R2#trigger(Heap, R2(r_1));
    assume Heap[null, R2(r_1)] == FrameFragment(R2#condqp4(Heap, r_1));
    if (!HasDirectPerm(Mask, null, R2(r_1))) {
      Heap[null, R2#sm(r_1)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, R2(r_1)] := freshVersion;
    }
    // register all known folded permissions guarded by predicate R2
    havoc newPMask;
    assume (forall <A, B> o_6: Ref, f_9: (Field A B) ::
      { newPMask[o_6, f_9] }
      Heap[null, R2#sm(r_1)][o_6, f_9] ==> newPMask[o_6, f_9]
    );
    assume (forall e_2: Ref ::
      
      refs(Heap, r_1)[e_2] ==> newPMask[e_2, q_1]
    );
    Heap[null, R2#sm(r_1)] := newPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: unfold acc(R2(r), wildcard) -- 0196.vpr@111.18--112.5
    assume R2#trigger(Heap, R2(r_1));
    assume Heap[null, R2(r_1)] == FrameFragment(R2#condqp4(Heap, r_1));
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, R2(r_1))) {
        havoc newVersion;
        Heap[null, R2(r_1)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Unfolding R2(r) might fail. There might be insufficient permission to access R2(r) (0196.vpr@111.18--112.5) [182]"}
      Mask[null, R2(r_1)] > NoPerm;
    assume wildcard < Mask[null, R2(r_1)];
    Mask[null, R2(r_1)] := Mask[null, R2(r_1)] - perm;
    assume state(Heap, Mask);
    havoc QPMask;
    havoc wildcard;
    
    // -- Define Inverse Function
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && NoPerm < wildcard ==> qpRange24(e_3) && invRecv24(e_3) == e_3
      );
      assume (forall o_2: Ref ::
        { invRecv24(o_2) }
        (refs(Heap, r_1)[invRecv24(o_2)] && NoPerm < wildcard) && qpRange24(o_2) ==> invRecv24(o_2) == o_2
      );
    
    // -- Assume set of fields is nonNull
      assume (forall e_3: Ref ::
        { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
        refs(Heap, r_1)[e_3] && wildcard > NoPerm ==> e_3 != null
      );
    // Assume permission expression is non-negative for all fields
    assume (forall e_3: Ref ::
      { Heap[e_3, q_1] } { QPMask[e_3, q_1] } { refs(Heap, r_1)[e_3] }
      refs(Heap, r_1)[e_3] ==> wildcard >= NoPerm
    );
    
    // -- Define permissions
      assume (forall o_2: Ref ::
        { QPMask[o_2, q_1] }
        ((refs(Heap, r_1)[invRecv24(o_2)] && NoPerm < wildcard) && qpRange24(o_2) ==> (NoPerm < wildcard ==> invRecv24(o_2) == o_2) && QPMask[o_2, q_1] == Mask[o_2, q_1] + wildcard) && (!((refs(Heap, r_1)[invRecv24(o_2)] && NoPerm < wildcard) && qpRange24(o_2)) ==> QPMask[o_2, q_1] == Mask[o_2, q_1])
      );
      assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
        { Mask[o_2, f_4] } { QPMask[o_2, f_4] }
        f_4 != q_1 ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
      );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: r2 := testerfield(get(r)) -- 0196.vpr@112.8--115.1
    
    // -- Check definedness of testerfield(get(r))
      if (*) {
        // Stop execution
        assume false;
      }
      if (*) {
        // Exhale precondition of function application
        // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
        perm := NoPerm;
        havoc wildcard;
        perm := perm + wildcard;
        assert {:msg "  Precondition of function testerfield might not hold. There might be insufficient permission to access get(r).q (0196.vpr@112.32--112.32) [183]"}
          Mask[get(Heap, r_1), q_1] > NoPerm;
        assume wildcard < Mask[get(Heap, r_1), q_1];
        Mask[get(Heap, r_1), q_1] := Mask[get(Heap, r_1), q_1] - perm;
        // Finish exhale
        havoc ExhaleHeap;
        assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
        Heap := ExhaleHeap;
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    r2 := testerfield(Heap, get(Heap, r_1));
    assume state(Heap, Mask);
}