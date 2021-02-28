// 
// Translation of Viper program.
// 
// Date:         2021-02-28 17:38:48
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/tests/benchmarking/intermediate/inhale_exhale/sWildcard.bpl /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/tests/benchmarking/intermediate/inhale_exhale/sWildcard.vpr
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
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@8.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@8.5) [176]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@9.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@9.5) [177]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@10.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@10.5) [178]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@11.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@11.5) [179]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@12.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@12.5) [180]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@13.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@13.5) [181]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@14.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@14.5) [182]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@15.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@15.5) [183]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@17.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@18.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@19.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@20.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@21.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@22.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@23.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@24.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@26.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@26.5) [184]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@27.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@27.5) [185]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@28.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@28.5) [186]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@29.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@29.5) [187]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@30.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@30.5) [188]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@31.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@31.5) [189]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@32.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@32.5) [190]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@33.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@33.5) [191]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@35.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@36.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@37.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@38.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@39.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@40.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@41.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@42.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@44.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@44.5) [192]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@45.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@45.5) [193]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@46.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@46.5) [194]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@47.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@47.5) [195]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@48.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@48.5) [196]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@49.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@49.5) [197]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@50.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@50.5) [198]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@51.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@51.5) [199]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@53.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@54.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@55.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@56.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@57.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@58.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@59.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@60.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@62.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@62.5) [200]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@63.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@63.5) [201]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@64.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@64.5) [202]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@65.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@65.5) [203]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@66.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@66.5) [204]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@67.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@67.5) [205]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@68.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@68.5) [206]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@69.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@69.5) [207]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@71.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@72.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@73.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@74.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@75.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@76.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@77.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@78.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@80.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@80.5) [208]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@81.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@81.5) [209]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@82.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@82.5) [210]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@83.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@83.5) [211]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@84.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@84.5) [212]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@85.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@85.5) [213]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@86.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@86.5) [214]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@87.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@87.5) [215]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@89.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@90.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@91.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@92.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@93.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@94.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@95.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@96.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@98.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@98.5) [216]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@99.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@99.5) [217]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@100.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@100.5) [218]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@101.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@101.5) [219]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@102.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@102.5) [220]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@103.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@103.5) [221]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@104.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@104.5) [222]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@105.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@105.5) [223]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@107.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@108.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@109.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@110.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@111.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@112.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@113.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@114.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@116.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@116.5) [224]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@117.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@117.5) [225]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@118.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@118.5) [226]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@119.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@119.5) [227]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@120.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@120.5) [228]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@121.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@121.5) [229]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@122.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@122.5) [230]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@123.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@123.5) [231]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@125.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@126.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@127.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@128.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@129.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@130.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@131.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@132.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@134.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@134.5) [232]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@135.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@135.5) [233]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@136.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@136.5) [234]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@137.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@137.5) [235]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@138.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@138.5) [236]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@139.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@139.5) [237]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@140.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@140.5) [238]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@141.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@141.5) [239]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@143.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@144.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@145.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@146.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@147.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@148.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@149.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@150.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@152.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@152.5) [240]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@153.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@153.5) [241]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@154.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@154.5) [242]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@155.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@155.5) [243]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@156.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@156.5) [244]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@157.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@157.5) [245]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@158.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@158.5) [246]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@159.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@159.5) [247]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@161.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@162.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@163.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@164.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@165.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@166.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@167.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@168.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@170.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@171.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@172.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@173.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@174.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@175.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@176.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@177.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@179.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@179.5) [248]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@180.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@180.5) [249]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@181.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@181.5) [250]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@182.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@182.5) [251]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@183.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@183.5) [252]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@184.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@184.5) [253]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@185.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@185.5) [254]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@186.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@186.5) [255]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@188.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@189.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@190.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@191.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@192.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@193.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@194.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@195.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@197.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@197.5) [256]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@198.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@198.5) [257]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@199.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@199.5) [258]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@200.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@200.5) [259]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@201.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@201.5) [260]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@202.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@202.5) [261]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@203.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@203.5) [262]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@204.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@204.5) [263]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@206.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@207.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@208.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@209.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@210.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@211.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@212.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@213.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@215.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@215.5) [264]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@216.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@216.5) [265]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@217.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@217.5) [266]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@218.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@218.5) [267]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@219.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@219.5) [268]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@220.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@220.5) [269]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@221.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@221.5) [270]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@222.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@222.5) [271]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@224.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@225.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@226.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@227.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@228.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@229.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@230.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@231.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@233.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@233.5) [272]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@234.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@234.5) [273]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@235.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@235.5) [274]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@236.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@236.5) [275]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@237.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@237.5) [276]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@238.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@238.5) [277]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@239.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@239.5) [278]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@240.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@240.5) [279]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@242.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@243.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@244.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@245.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@246.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@247.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@248.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@249.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@251.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@251.5) [280]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@252.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@252.5) [281]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@253.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@253.5) [282]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@254.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@254.5) [283]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@255.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@255.5) [284]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@256.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@256.5) [285]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@257.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@257.5) [286]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@258.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@258.5) [287]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@260.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@261.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@262.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@263.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@264.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@265.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@266.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@267.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@269.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@269.5) [288]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@270.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@270.5) [289]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@271.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@271.5) [290]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@272.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@272.5) [291]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@273.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@273.5) [292]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@274.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@274.5) [293]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@275.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@275.5) [294]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@276.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@276.5) [295]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@278.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@279.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@280.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@281.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@282.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@283.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@284.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@285.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@287.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@287.5) [296]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@288.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@288.5) [297]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@289.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@289.5) [298]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@290.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@290.5) [299]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@291.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@291.5) [300]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@292.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@292.5) [301]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@293.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@293.5) [302]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@294.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@294.5) [303]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@296.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@297.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@298.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@299.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@300.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@301.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@302.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@303.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@305.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@305.5) [304]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@306.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@306.5) [305]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@307.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@307.5) [306]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@308.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@308.5) [307]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@309.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@309.5) [308]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@310.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@310.5) [309]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@311.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@311.5) [310]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@312.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@312.5) [311]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@314.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@315.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@316.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@317.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@318.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@319.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@320.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@321.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@323.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@323.5) [312]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@324.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@324.5) [313]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@325.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@325.5) [314]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@326.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@326.5) [315]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@327.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@327.5) [316]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@328.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@328.5) [317]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@329.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@329.5) [318]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@330.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@330.5) [319]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@332.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@333.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@334.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@335.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@336.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@337.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@338.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@339.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@341.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@341.5) [320]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@342.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@342.5) [321]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@343.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@343.5) [322]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@344.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@344.5) [323]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@345.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@345.5) [324]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@346.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@346.5) [325]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@347.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@347.5) [326]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@348.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@348.5) [327]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@350.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@351.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@352.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@353.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@354.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@355.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@356.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@357.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@359.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@359.5) [328]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@360.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@360.5) [329]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@361.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@361.5) [330]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@362.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@362.5) [331]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@363.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@363.5) [332]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@364.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@364.5) [333]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@365.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@365.5) [334]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@366.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@366.5) [335]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@368.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@369.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@370.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@371.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@372.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@373.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@374.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@375.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@377.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@377.5) [336]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@378.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@378.5) [337]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@379.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@379.5) [338]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@380.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@380.5) [339]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@381.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@381.5) [340]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@382.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@382.5) [341]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@383.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@383.5) [342]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@384.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@384.5) [343]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@386.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@387.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@388.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@389.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@390.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@391.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@392.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, sWildcard) -- sWildcard.vpr@393.5
    sWildcard := tuple(0.000000000, true);
    perm := sWildcard;
    assume fst(NoPerm) <= fst(perm) && !(snd(NoPerm) && !snd(perm));
    assume fst(perm) > 0.000000000 || snd(perm) ==> x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@395.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@395.5) [344]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@396.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@396.5) [345]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@397.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@397.5) [346]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@398.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@398.5) [347]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@399.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@399.5) [348]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@400.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@400.5) [349]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@401.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@401.5) [350]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, sWildcard) -- sWildcard.vpr@402.5
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    sWildcard := tuple(0.000000000, true);
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (sWildcard.vpr@402.5) [351]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    Mask[x, f_6] := sWildcard;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
}