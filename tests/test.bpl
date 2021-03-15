// 
// Translation of Viper program.
// 
// Date:         2021-03-15 15:23:05
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print tests/test.bpl tests/test.vpr
// Dependencies:
//   Boogie , located at /bin/boogie/Binaries/boogie.
//   Z3 4.8.4 - 64 bit, located at /usr/bin/z3.
// 

// ==================================================
// Preamble of State module.
// ==================================================

function  state(Heap: HeapType, Mask: MaskType, BMask: BMaskType): bool;

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
function  IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType): bool;
function  IsPredicateField<A, B>(f_1: (Field A B)): bool;
function  IsWandField<A, B>(f_1: (Field A B)): bool;
function  getPredicateId<A, B>(f_1: (Field A B)): int;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask), ExhaleHeap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) ==> HasDirectPerm(Mask, BMask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) ==> HasDirectPerm(Mask, BMask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask), ExhaleHeap[null, pm_f], IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) ==> HasDirectPerm(Mask, BMask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// Frame all wand mask locations of wands with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask), IsWandField(pm_f), ExhaleHeap[null, WandMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) ==> HasDirectPerm(Mask, BMask, null, pm_f) && IsWandField(pm_f) ==> Heap[null, WandMaskField(pm_f)] == ExhaleHeap[null, WandMaskField(pm_f)]
);
// Frame all locations in the footprint of magic wands
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask), IsWandField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) ==> HasDirectPerm(Mask, BMask, null, pm_f) && IsWandField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, WandMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// All previously-allocated references are still allocated
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask), ExhaleHeap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
);
// Updated Heaps are Successor Heaps
axiom (forall <A, B> Heap: HeapType, o: Ref, f_2: (Field A B), v: B ::
  { Heap[o, f_2:=v] }
  succHeap(Heap, Heap[o, f_2:=v])
);
// IdenticalOnKnownLocations Heaps are Successor Heaps
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, BMask: BMaskType ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask, BMask) ==> succHeap(Heap, ExhaleHeap)
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
type BMaskType = <A, B> [Ref, Field A B]bool;
var BMask: BMaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == NoPerm
);
const ZeroBMask: BMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroBMask[o_1, f_3] }
  !ZeroBMask[o_1, f_3]
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
function  GoodMask(Mask: MaskType, BMask: BMaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType, BMask: BMaskType ::
  { state(Heap, Mask, BMask) }
  state(Heap, Mask, BMask) ==> GoodMask(Mask, BMask)
);
axiom (forall <A, B> Mask: MaskType, BMask: BMaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask, BMask), Mask[o_1, f_3] }
  GoodMask(Mask, BMask) ==> Mask[o_1, f_3] >= NoPerm && ((GoodMask(Mask, BMask) && !IsPredicateField(f_3)) && !IsWandField(f_3) ==> Mask[o_1, f_3] <= FullPerm && (Mask[o_1, f_3] == FullPerm ==> !BMask[o_1, f_3]))
);
function  HasDirectPerm<A, B>(Mask: MaskType, BMask: BMaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, BMask: BMaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, BMask, o_1, f_3) }
  HasDirectPerm(Mask, BMask, o_1, f_3) <==> Mask[o_1, f_3] > NoPerm || BMask[o_1, f_3]
);
function  sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
);

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 0: dummy
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
// Translation of all fields
// ==================================================

const unique f_6: Field NormalField int;
axiom !IsPredicateField(f_6);
axiom !IsWandField(f_6);

// ==================================================
// Translation of function dummy
// ==================================================

// Uninterpreted function definitions
function  dummy(Heap: HeapType): Perm;
function  dummy'(Heap: HeapType): Perm;
axiom (forall Heap: HeapType ::
  { dummy(Heap) }
  dummy(Heap) == dummy'(Heap) && dummyFunction(dummy#triggerStateless())
);
axiom (forall Heap: HeapType ::
  { dummy'(Heap) }
  dummyFunction(dummy#triggerStateless())
);

// Framing axioms
function  dummy#frame(frame: FrameType): Perm;
axiom (forall Heap: HeapType, Mask: MaskType, BMask: BMaskType ::
  { state(Heap, Mask, BMask), dummy'(Heap) }
  state(Heap, Mask, BMask) ==> dummy'(Heap) == dummy#frame(EmptyFrame)
);

// Postcondition axioms
axiom (forall Heap: HeapType, Mask: MaskType, BMask: BMaskType ::
  { state(Heap, Mask, BMask), dummy'(Heap) }
  state(Heap, Mask, BMask) && (AssumeFunctionsAbove < 0 || dummy#trigger(EmptyFrame)) ==> NoPerm < dummy'(Heap)
);

// Trigger function (controlling recursive postconditions)
function  dummy#trigger(frame: FrameType): bool;

// State-independent trigger function
function  dummy#triggerStateless(): Perm;

// Check contract well-formedness and postcondition
procedure dummy#definedness() returns (Result: Perm)
  modifies Heap, Mask, BMask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    BMask := ZeroBMask;
    assume state(Heap, Mask, BMask);
    assume AssumeFunctionsAbove == 0;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
    assume BMask == old(BMask);
  
  // -- Checking definedness of postcondition (no body)
    assume NoPerm < Result;
    assume state(Heap, Mask, BMask);
}

// ==================================================
// Translation of method test
// ==================================================

procedure test(x: Ref) returns ()
  modifies Heap, Mask, BMask;
{
  var perm: Perm;
  var c: int;
  
  // -- Initializing the state
    Mask := ZeroMask;
    BMask := ZeroBMask;
    assume state(Heap, Mask, BMask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Assumptions about method arguments
    assume Heap[x, $allocated];
  
  // -- Checked inhaling of precondition
    
    // -- Check definedness of acc(x.f, dummy())
      if (*) {
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask, BMask);
    assume state(Heap, Mask, BMask);
    perm := dummy(Heap);
    assume perm >= NoPerm;
    assume perm > NoPerm ==> x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask, BMask);
    assume state(Heap, Mask, BMask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
      assume BMask == old(BMask);
  
  // -- Translating statement: c := x.f -- test.vpr@14.8--19.1
    
    // -- Check definedness of x.f
      assert {:msg "  Assignment might fail. There might be insufficient permission to access x.f (test.vpr@14.8--19.1) [3]"}
        HasDirectPerm(Mask, BMask, x, f_6);
      assume state(Heap, Mask, BMask);
    c := Heap[x, f_6];
    assume state(Heap, Mask, BMask);
}