// 
// Translation of Viper program.
// 
// Date:         2021-02-27 16:43:13
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print ../tests/symbolic_wildcard_new_implementation.bpl ../tests/inhale_exhale.vpr
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
  HasDirectPerm(Mask, o_1, f_3) <==> fst(NoPerm) < fst(Mask[o_1, f_3]) || ((fst(NoPerm) == fst(Mask[o_1, f_3]) && !snd(NoPerm)) && snd(Mask[o_1, f_3]))
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
  ConditionalFrame(p_1, f_5) == (if fst(NoPerm) < fst(p_1) || ((fst(NoPerm) == fst(p_1) && !snd(NoPerm)) && snd(p_1)) then f_5 else EmptyFrame)
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
// Translation of method test
// ==================================================

procedure test(x: Ref) returns ()
  modifies Heap, Mask;
{
  var sWildcard: Perm;
  var perm: Perm;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume Heap[x, $allocated];
  
  // -- Checked inhaling of precondition
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@8.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@8.5) [88]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@9.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@9.5) [89]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@10.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@10.5) [90]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@11.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@11.5) [91]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@12.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@12.5) [92]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@13.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@13.5) [93]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@14.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@14.5) [94]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@15.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@15.5) [95]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@17.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@18.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@19.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@20.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@21.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@22.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@23.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@24.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@26.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@26.5) [96]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@27.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@27.5) [97]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@28.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@28.5) [98]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@29.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@29.5) [99]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@30.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@30.5) [100]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@31.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@31.5) [101]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@32.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@32.5) [102]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@33.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@33.5) [103]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@35.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@36.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@37.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@38.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@39.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@40.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@41.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@42.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@44.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@44.5) [104]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@45.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@45.5) [105]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@46.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@46.5) [106]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@47.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@47.5) [107]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@48.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@48.5) [108]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@49.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@49.5) [109]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@50.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@50.5) [110]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@51.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@51.5) [111]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@53.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@54.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@55.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@56.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@57.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@58.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@59.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@60.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@62.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@62.5) [112]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@63.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@63.5) [113]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@64.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@64.5) [114]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@65.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@65.5) [115]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@66.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@66.5) [116]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@67.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@67.5) [117]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@68.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@68.5) [118]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@69.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@69.5) [119]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@71.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@72.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@73.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@74.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@75.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@76.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@77.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@78.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@80.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@80.5) [120]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@81.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@81.5) [121]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@82.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@82.5) [122]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@83.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@83.5) [123]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@84.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@84.5) [124]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@85.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@85.5) [125]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@86.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@86.5) [126]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@87.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@87.5) [127]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@89.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@90.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@91.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@92.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@93.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@94.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@95.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@96.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@98.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@98.5) [128]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@99.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@99.5) [129]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@100.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@100.5) [130]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@101.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@101.5) [131]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@102.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@102.5) [132]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@103.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@103.5) [133]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@104.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@104.5) [134]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@105.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@105.5) [135]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@107.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@108.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@109.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@110.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@111.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@112.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@113.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@114.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@116.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@116.5) [136]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@117.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@117.5) [137]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@118.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@118.5) [138]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@119.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@119.5) [139]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@120.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@120.5) [140]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@121.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@121.5) [141]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@122.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@122.5) [142]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@123.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@123.5) [143]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@125.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@126.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@127.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@128.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@129.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@130.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@131.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@132.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@134.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@134.5) [144]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@135.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@135.5) [145]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@136.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@136.5) [146]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@137.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@137.5) [147]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@138.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@138.5) [148]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@139.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@139.5) [149]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@140.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@140.5) [150]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@141.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@141.5) [151]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@143.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@144.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@145.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@146.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@147.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@148.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@149.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@150.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@152.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@152.5) [152]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@153.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@153.5) [153]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@154.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@154.5) [154]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@155.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@155.5) [155]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@156.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@156.5) [156]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@157.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@157.5) [157]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@158.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@158.5) [158]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@159.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@159.5) [159]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@161.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@162.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@163.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@164.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@165.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@166.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@167.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@168.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@170.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@171.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@172.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@173.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@174.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@175.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@176.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@177.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@179.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@179.5) [160]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@180.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@180.5) [161]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@181.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@181.5) [162]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@182.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@182.5) [163]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@183.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@183.5) [164]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@184.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@184.5) [165]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@185.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@185.5) [166]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@186.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@186.5) [167]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@188.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@189.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@190.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@191.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@192.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@193.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@194.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- inhale_exhale.vpr@195.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume (fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm))) || NoPerm == perm;
    assume fst(NoPerm) < fst(perm) || ((fst(NoPerm) == fst(perm) && !snd(NoPerm)) && snd(perm)) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@197.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@197.5) [168]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@198.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@198.5) [169]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@199.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@199.5) [170]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@200.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@200.5) [171]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@201.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@201.5) [172]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@202.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@202.5) [173]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@203.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@203.5) [174]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- inhale_exhale.vpr@204.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (inhale_exhale.vpr@204.5) [175]"}
      fst(NoPerm) < fst(Mask[x, f_6]) || ((fst(NoPerm) == fst(Mask[x, f_6]) && !snd(NoPerm)) && snd(Mask[x, f_6]));
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
}