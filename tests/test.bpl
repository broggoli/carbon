// 
// Translation of Viper program.
// 
// Date:         2021-03-01 13:37:53
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print tests/test.bpl tests/predicate_test.vpr
// Dependencies:
//   Boogie , located at /bin/boogie/Binaries/boogie.
//   Z3 4.8.4 - 64 bit, located at /usr/bin/z3.
// 

// ==================================================
// Preamble of State module.
// ==================================================

function state(Heap: HeapType, Mask: MaskType): bool;

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
function succHeap(Heap0: HeapType, Heap1: HeapType): bool;
function succHeapTrans(Heap0: HeapType, Heap1: HeapType): bool;
function IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function IsPredicateField<A, B>(f_1: (Field A B)): bool;
function IsWandField<A, B>(f_1: (Field A B)): bool;
function getPredicateId<A, B>(f_1: (Field A B)): int;
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

type Tuple A B;
function tuple<A, B>(a: A, b: B): Tuple A B;
function fst<A, B>(p: (Tuple A B)): A;
function snd<A, B>(p: (Tuple A B)): B;
axiom (forall <A, B> a: A, b: B ::
  { (tuple(a, b): Tuple A B) }
  (fst((tuple(a, b): Tuple A B)): A) == a
);
axiom (forall <A, B> a: A, b: B ::
  { (tuple(a, b): Tuple A B) }
  (snd((tuple(a, b): Tuple A B)): B) == b
);
axiom (forall <A, B> p: (Tuple A B) ::
  { (fst(p): A) } { (snd(p): B) }
  (tuple((fst(p): A), (snd(p): B)): Tuple A B) == p
);
function sumTuple(TupleSumResult: Perm, TupleSummand1: Perm, TupleSummand2: Perm): bool;
axiom (forall TupleSumResult: Perm, TupleSummand1: Perm, TupleSummand2: Perm ::
  { sumTuple(TupleSumResult, TupleSummand1, TupleSummand2) }
  sumTuple(TupleSumResult, TupleSummand1, TupleSummand2) <==> TupleSumResult == tuple(fst(TupleSummand1) + fst(TupleSummand2), snd(TupleSummand1) || snd(TupleSummand2))
);
type Perm = Tuple real bool;
type MaskType = <A, B> [Ref, Field A B]Perm;
var Mask: MaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == NoPerm
);
const NoPerm: Perm;
axiom fst(NoPerm) == 0.000000000 && !snd(NoPerm);
const FullPerm: Perm;
axiom fst(FullPerm) == 1.000000000 && !snd(FullPerm);
function Perm<A, B>(a_1: A, b_1: B): Perm;
function GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask), Mask[o_1, f_3] }
  (GoodMask(Mask) ==> fst(Mask[o_1, f_3]) >= fst(NoPerm)) && ((GoodMask(Mask) && !IsPredicateField(f_3)) && !IsWandField(f_3) ==> fst(Mask[o_1, f_3]) <= fst(FullPerm))
);
function HasDirectPerm<A, B>(Mask: MaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, o_1, f_3) }
  HasDirectPerm(Mask, o_1, f_3) <==> fst(Mask[o_1, f_3]) > 0.000000000 || snd(Mask[o_1, f_3])
);
function sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) <==> sumTuple(ResultMask[o_1, f_3], SummandMask1[o_1, f_3], SummandMask2[o_1, f_3])
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroPMask[o_1, f_3] }
  !ZeroPMask[o_1, f_3]
);
function PredicateMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
function WandMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function FrameFragment<T>(t: T): FrameType;
function ConditionalFrame(p_1: Perm, f_5: FrameType): FrameType;
function dummyFunction<T>(t: T): bool;
function CombineFrames(a_2: FrameType, b_2: FrameType): FrameType;
// ==================================================
// Definition of conditional frame fragments
// ==================================================

axiom (forall p_1: Perm, f_5: FrameType ::
  { ConditionalFrame(p_1, f_5) }
  ConditionalFrame(p_1, f_5) == (if fst(p_1) > 0.000000000 || snd(p_1) then f_5 else EmptyFrame)
);
// Function for recording enclosure of one predicate instance in another
function InsidePredicate<A, B>(p_1: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType): bool;
// Transitivity of InsidePredicate
axiom (forall <A, B, C> p_1: (Field A FrameType), v_1: FrameType, q: (Field B FrameType), w: FrameType, r: (Field C FrameType), u: FrameType ::
  { InsidePredicate(p_1, v_1, q, w), InsidePredicate(q, w, r, u) }
  InsidePredicate(p_1, v_1, q, w) && InsidePredicate(q, w, r, u) ==> InsidePredicate(p_1, v_1, r, u)
);
// Knowledge that two identical instances of the same predicate cannot be inside each other
axiom (forall <A> p_1: (Field A FrameType), v_1: FrameType, w: FrameType ::
  { InsidePredicate(p_1, v_1, p_1, w) }
  !InsidePredicate(p_1, v_1, p_1, w)
);

// ==================================================
// Translation of all fields
// ==================================================

const unique f_6: Field NormalField int;
axiom !IsPredicateField(f_6);
axiom !IsWandField(f_6);

// ==================================================
// Translation of predicate foo
// ==================================================

type PredicateType_foo;
function foo(xs: Ref): Field PredicateType_foo FrameType;
function foo#sm(xs: Ref): Field PredicateType_foo PMaskType;
axiom (forall xs: Ref ::
  { PredicateMaskField(foo(xs)) }
  PredicateMaskField(foo(xs)) == foo#sm(xs)
);
axiom (forall xs: Ref ::
  { foo(xs) }
  IsPredicateField(foo(xs))
);
axiom (forall xs: Ref ::
  { foo(xs) }
  getPredicateId(foo(xs)) == 0
);
function foo#trigger<A>(Heap: HeapType, pred: (Field A FrameType)): bool;
function foo#everUsed<A>(pred: (Field A FrameType)): bool;
axiom (forall xs: Ref, xs2: Ref ::
  { foo(xs), foo(xs2) }
  foo(xs) == foo(xs2) ==> xs == xs2
);
axiom (forall xs: Ref, xs2: Ref ::
  { foo#sm(xs), foo#sm(xs2) }
  foo#sm(xs) == foo#sm(xs2) ==> xs == xs2
);

axiom (forall Heap: HeapType, xs: Ref ::
  { foo#trigger(Heap, foo(xs)) }
  foo#everUsed(foo(xs))
);

// ==================================================
// Translation of method test
// ==================================================

procedure test(x: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var newVersion: FrameType;
  var sWildcard: Perm;
  var v_2: int;
  var freshVersion: FrameType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume Heap[x, $allocated];
  
  // -- Checked inhaling of precondition
    perm := tuple(0.000000000, true);
    Mask[null, foo(x)] := tuple(fst(Mask[null, foo(x)]) + fst(perm), snd(Mask[null, foo(x)]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: unfold acc(foo(x), sWildcard) -- predicate_test.vpr@11.5
    assume foo#trigger(Heap, foo(x));
    assume Heap[null, foo(x)] == FrameFragment(Heap[x, f_6]);
    // Phase 1: pure assertions and fixed permissions
    
    // -- Update version of predicate
      if (!HasDirectPerm(Mask, null, foo(x))) {
        havoc newVersion;
        Heap[null, foo(x)] := newVersion;
      }
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Unfolding foo(x) might fail. There might be insufficient permission to access foo(x). (predicate_test.vpr@11.5) [5]"}
      fst(Mask[null, foo(x)]) > 0.000000000 || snd(Mask[null, foo(x)]);
    Mask[null, foo(x)] := sWildcard;
    perm := tuple(0.000000000, true);
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: v := x.f -- predicate_test.vpr@12.5
    
    // -- Check definedness of x.f
      assert {:msg "  Assignment might fail. There might be insufficient permission to access x.f. (predicate_test.vpr@12.5) [6]"}
        HasDirectPerm(Mask, x, f_6);
      assume state(Heap, Mask);
    v_2 := Heap[x, f_6];
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(foo(x), sWildcard) -- predicate_test.vpr@13.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Folding foo(x) might fail. There might be insufficient permission to access x.f. (predicate_test.vpr@13.5) [7]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    perm := tuple(0.000000000, true);
    Mask[null, foo(x)] := tuple(fst(Mask[null, foo(x)]) + fst(perm), snd(Mask[null, foo(x)]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume foo#trigger(Heap, foo(x));
    assume Heap[null, foo(x)] == FrameFragment(Heap[x, f_6]);
    if (!HasDirectPerm(Mask, null, foo(x))) {
      Heap[null, foo#sm(x)] := ZeroPMask;
      havoc freshVersion;
      Heap[null, foo(x)] := freshVersion;
    }
    Heap[null, foo#sm(x)][x, f_6] := true;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
}