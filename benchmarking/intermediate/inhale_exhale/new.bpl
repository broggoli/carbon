// 
// Translation of Viper program.
// 
// Date:         2021-03-01 13:16:00
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/carbon/benchmarking/intermediate/inhale_exhale/new.bpl /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/carbon/benchmarking/intermediate/inhale_exhale/wildcard.vpr
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
  var wildcard: Perm where fst(wildcard) > 0.000000000 || snd(wildcard);
  var perm: Perm;
  var ExhaleHeap: HeapType;
  var c: int;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume Heap[x, $allocated];
  
  // -- Checked inhaling of precondition
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@6.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@7.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@9.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@9.5) [123]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@10.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@10.5) [124]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@12.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@13.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@15.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@15.5) [125]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@16.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@16.5) [126]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@18.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@19.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@21.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@21.5) [127]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@22.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@22.5) [128]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@24.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@25.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@27.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@27.5) [129]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@28.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@28.5) [130]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@30.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@31.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@33.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@33.5) [131]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@34.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@34.5) [132]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@36.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@37.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@39.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@39.5) [133]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@40.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@40.5) [134]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@42.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@43.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@45.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@45.5) [135]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@46.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@46.5) [136]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@48.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@49.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@51.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@51.5) [137]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@52.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@52.5) [138]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@54.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@55.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@57.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@57.5) [139]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@58.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@58.5) [140]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@60.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@61.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@63.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@63.5) [141]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@64.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@64.5) [142]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@66.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@67.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@69.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@69.5) [143]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@70.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@70.5) [144]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@72.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@73.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@75.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@75.5) [145]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@76.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@76.5) [146]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@78.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@79.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@81.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@81.5) [147]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@82.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@82.5) [148]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@84.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@85.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@87.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@87.5) [149]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@88.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@88.5) [150]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@90.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@91.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@93.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@93.5) [151]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@94.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@94.5) [152]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@96.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@97.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@99.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@99.5) [153]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@100.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@100.5) [154]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@102.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@103.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@105.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@105.5) [155]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@106.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@106.5) [156]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@108.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@109.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@111.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@111.5) [157]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@112.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@112.5) [158]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@114.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@115.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@117.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@117.5) [159]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@118.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@118.5) [160]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@120.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@121.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@123.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@123.5) [161]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@124.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@124.5) [162]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@126.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@127.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@129.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@129.5) [163]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@130.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@130.5) [164]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@132.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@133.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@135.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@135.5) [165]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@136.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@136.5) [166]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@138.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@139.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@141.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@141.5) [167]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@142.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@142.5) [168]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@144.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@145.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@147.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@147.5) [169]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@148.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@148.5) [170]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@150.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@151.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@153.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@153.5) [171]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@154.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@154.5) [172]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@156.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@157.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@159.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@159.5) [173]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@160.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@160.5) [174]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@162.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@163.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@165.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@165.5) [175]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@166.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@166.5) [176]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@168.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@169.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@171.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@171.5) [177]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@172.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@172.5) [178]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@174.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@175.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@177.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@177.5) [179]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@178.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@178.5) [180]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@180.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@181.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@183.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@183.5) [181]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@184.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@184.5) [182]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@186.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@187.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@189.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@189.5) [183]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@190.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@190.5) [184]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@192.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@193.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@195.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@195.5) [185]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@196.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@196.5) [186]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@198.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@199.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@201.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@201.5) [187]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@202.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@202.5) [188]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@204.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@205.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@207.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@207.5) [189]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@208.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@208.5) [190]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@210.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@211.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@213.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@213.5) [191]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@214.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@214.5) [192]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@216.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@217.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@219.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@219.5) [193]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@220.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@220.5) [194]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@222.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@223.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@225.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@225.5) [195]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@226.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@226.5) [196]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@228.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@229.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@231.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@231.5) [197]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@232.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@232.5) [198]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@234.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@235.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@237.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@237.5) [199]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@238.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@238.5) [200]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@240.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@241.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@243.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@243.5) [201]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@244.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@244.5) [202]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@246.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@247.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@249.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@249.5) [203]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@250.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@250.5) [204]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@252.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@253.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@255.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@255.5) [205]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@256.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@256.5) [206]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@258.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@259.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@261.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@261.5) [207]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@262.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@262.5) [208]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@264.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@265.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@267.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@267.5) [209]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@268.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@268.5) [210]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@270.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@271.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@273.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@273.5) [211]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@274.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@274.5) [212]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@276.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@277.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@279.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@279.5) [213]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@280.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@280.5) [214]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@282.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@283.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@285.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@285.5) [215]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@286.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@286.5) [216]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@288.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@289.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@291.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@291.5) [217]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@292.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@292.5) [218]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@294.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@295.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@297.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@297.5) [219]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@298.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@298.5) [220]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@300.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@301.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@303.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@303.5) [221]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@304.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@304.5) [222]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@306.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@307.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@309.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@309.5) [223]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@310.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@310.5) [224]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@312.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@313.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@315.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@315.5) [225]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@316.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@316.5) [226]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@318.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@319.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@321.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@321.5) [227]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@322.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@322.5) [228]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@324.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@325.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@327.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@327.5) [229]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@328.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@328.5) [230]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@330.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@331.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@333.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@333.5) [231]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@334.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@334.5) [232]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@336.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@337.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@339.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@339.5) [233]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@340.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@340.5) [234]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@342.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@343.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@345.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@345.5) [235]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@346.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@346.5) [236]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@348.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@349.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@351.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@351.5) [237]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@352.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@352.5) [238]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@354.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@355.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@357.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@357.5) [239]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@358.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@358.5) [240]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@360.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@361.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) + fst(perm), snd(Mask[x, f_6]) || snd(perm));
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@363.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@363.5) [241]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@364.5
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := tuple(fst(perm) + fst(wildcard), snd(perm) || snd(wildcard));
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f. (wildcard.vpr@364.5) [242]"}
      fst(Mask[x, f_6]) > 0.000000000 || snd(Mask[x, f_6]);
    assume ((fst(wildcard) == fst(Mask[x, f_6]) && !snd(wildcard)) && snd(Mask[x, f_6])) || fst(wildcard) < fst(Mask[x, f_6]);
    Mask[x, f_6] := tuple(fst(Mask[x, f_6]) - fst(perm), snd(Mask[x, f_6]) || snd(perm));
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: c := x.f -- wildcard.vpr@367.5
    
    // -- Check definedness of x.f
      assert {:msg "  Assignment might fail. There might be insufficient permission to access x.f. (wildcard.vpr@367.5) [243]"}
        HasDirectPerm(Mask, x, f_6);
      assume state(Heap, Mask);
    c := Heap[x, f_6];
    assume state(Heap, Mask);
}