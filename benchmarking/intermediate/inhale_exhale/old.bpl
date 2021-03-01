// 
// Translation of Viper program.
// 
// Date:         2021-03-01 13:15:41
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/carbon/benchmarking/intermediate/inhale_exhale/old.bpl /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/carbon/benchmarking/intermediate/inhale_exhale/wildcard.vpr
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
// Preamble of Function and predicate module.
// ==================================================

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
// Translation of method test
// ==================================================

procedure test(x: Ref) returns ()
  modifies Heap, Mask;
{
  var wildcard: real where wildcard > NoPerm;
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
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@6.11--7.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@7.11--9.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@9.11--9.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@9.11--9.12) [123]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@10.11--10.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@10.11--10.12) [124]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@12.11--13.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@13.11--15.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@15.11--15.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@15.11--15.12) [125]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@16.11--16.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@16.11--16.12) [126]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@18.11--19.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@19.11--21.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@21.11--21.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@21.11--21.12) [127]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@22.11--22.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@22.11--22.12) [128]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@24.11--25.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@25.11--27.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@27.11--27.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@27.11--27.12) [129]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@28.11--28.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@28.11--28.12) [130]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@30.11--31.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@31.11--33.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@33.11--33.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@33.11--33.12) [131]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@34.11--34.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@34.11--34.12) [132]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@36.11--37.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@37.11--39.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@39.11--39.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@39.11--39.12) [133]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@40.11--40.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@40.11--40.12) [134]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@42.11--43.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@43.11--45.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@45.11--45.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@45.11--45.12) [135]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@46.11--46.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@46.11--46.12) [136]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@48.11--49.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@49.11--51.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@51.11--51.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@51.11--51.12) [137]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@52.11--52.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@52.11--52.12) [138]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@54.11--55.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@55.11--57.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@57.11--57.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@57.11--57.12) [139]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@58.11--58.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@58.11--58.12) [140]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@60.11--61.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@61.11--63.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@63.11--63.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@63.11--63.12) [141]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@64.11--64.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@64.11--64.12) [142]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@66.11--67.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@67.11--69.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@69.11--69.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@69.11--69.12) [143]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@70.11--70.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@70.11--70.12) [144]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@72.11--73.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@73.11--75.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@75.11--75.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@75.11--75.12) [145]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@76.11--76.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@76.11--76.12) [146]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@78.11--79.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@79.11--81.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@81.11--81.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@81.11--81.12) [147]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@82.11--82.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@82.11--82.12) [148]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@84.11--85.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@85.11--87.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@87.11--87.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@87.11--87.12) [149]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@88.11--88.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@88.11--88.12) [150]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@90.11--91.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@91.11--93.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@93.11--93.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@93.11--93.12) [151]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@94.11--94.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@94.11--94.12) [152]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@96.11--97.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@97.11--99.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@99.11--99.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@99.11--99.12) [153]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@100.11--100.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@100.11--100.12) [154]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@102.11--103.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@103.11--105.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@105.11--105.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@105.11--105.12) [155]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@106.11--106.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@106.11--106.12) [156]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@108.11--109.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@109.11--111.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@111.11--111.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@111.11--111.12) [157]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@112.11--112.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@112.11--112.12) [158]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@114.11--115.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@115.11--117.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@117.11--117.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@117.11--117.12) [159]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@118.11--118.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@118.11--118.12) [160]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@120.11--121.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@121.11--123.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@123.11--123.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@123.11--123.12) [161]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@124.11--124.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@124.11--124.12) [162]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@126.11--127.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@127.11--129.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@129.11--129.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@129.11--129.12) [163]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@130.11--130.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@130.11--130.12) [164]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@132.11--133.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@133.11--135.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@135.11--135.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@135.11--135.12) [165]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@136.11--136.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@136.11--136.12) [166]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@138.11--139.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@139.11--141.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@141.11--141.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@141.11--141.12) [167]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@142.11--142.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@142.11--142.12) [168]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@144.11--145.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@145.11--147.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@147.11--147.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@147.11--147.12) [169]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@148.11--148.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@148.11--148.12) [170]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@150.11--151.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@151.11--153.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@153.11--153.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@153.11--153.12) [171]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@154.11--154.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@154.11--154.12) [172]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@156.11--157.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@157.11--159.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@159.11--159.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@159.11--159.12) [173]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@160.11--160.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@160.11--160.12) [174]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@162.11--163.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@163.11--165.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@165.11--165.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@165.11--165.12) [175]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@166.11--166.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@166.11--166.12) [176]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@168.11--169.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@169.11--171.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@171.11--171.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@171.11--171.12) [177]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@172.11--172.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@172.11--172.12) [178]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@174.11--175.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@175.11--177.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@177.11--177.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@177.11--177.12) [179]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@178.11--178.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@178.11--178.12) [180]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@180.11--181.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@181.11--183.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@183.11--183.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@183.11--183.12) [181]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@184.11--184.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@184.11--184.12) [182]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@186.11--187.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@187.11--189.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@189.11--189.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@189.11--189.12) [183]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@190.11--190.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@190.11--190.12) [184]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@192.11--193.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@193.11--195.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@195.11--195.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@195.11--195.12) [185]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@196.11--196.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@196.11--196.12) [186]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@198.11--199.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@199.11--201.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@201.11--201.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@201.11--201.12) [187]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@202.11--202.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@202.11--202.12) [188]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@204.11--205.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@205.11--207.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@207.11--207.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@207.11--207.12) [189]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@208.11--208.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@208.11--208.12) [190]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@210.11--211.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@211.11--213.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@213.11--213.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@213.11--213.12) [191]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@214.11--214.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@214.11--214.12) [192]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@216.11--217.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@217.11--219.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@219.11--219.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@219.11--219.12) [193]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@220.11--220.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@220.11--220.12) [194]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@222.11--223.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@223.11--225.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@225.11--225.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@225.11--225.12) [195]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@226.11--226.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@226.11--226.12) [196]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@228.11--229.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@229.11--231.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@231.11--231.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@231.11--231.12) [197]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@232.11--232.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@232.11--232.12) [198]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@234.11--235.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@235.11--237.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@237.11--237.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@237.11--237.12) [199]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@238.11--238.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@238.11--238.12) [200]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@240.11--241.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@241.11--243.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@243.11--243.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@243.11--243.12) [201]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@244.11--244.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@244.11--244.12) [202]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@246.11--247.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@247.11--249.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@249.11--249.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@249.11--249.12) [203]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@250.11--250.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@250.11--250.12) [204]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@252.11--253.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@253.11--255.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@255.11--255.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@255.11--255.12) [205]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@256.11--256.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@256.11--256.12) [206]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@258.11--259.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@259.11--261.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@261.11--261.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@261.11--261.12) [207]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@262.11--262.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@262.11--262.12) [208]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@264.11--265.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@265.11--267.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@267.11--267.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@267.11--267.12) [209]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@268.11--268.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@268.11--268.12) [210]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@270.11--271.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@271.11--273.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@273.11--273.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@273.11--273.12) [211]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@274.11--274.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@274.11--274.12) [212]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@276.11--277.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@277.11--279.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@279.11--279.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@279.11--279.12) [213]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@280.11--280.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@280.11--280.12) [214]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@282.11--283.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@283.11--285.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@285.11--285.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@285.11--285.12) [215]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@286.11--286.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@286.11--286.12) [216]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@288.11--289.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@289.11--291.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@291.11--291.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@291.11--291.12) [217]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@292.11--292.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@292.11--292.12) [218]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@294.11--295.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@295.11--297.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@297.11--297.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@297.11--297.12) [219]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@298.11--298.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@298.11--298.12) [220]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@300.11--301.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@301.11--303.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@303.11--303.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@303.11--303.12) [221]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@304.11--304.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@304.11--304.12) [222]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@306.11--307.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@307.11--309.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@309.11--309.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@309.11--309.12) [223]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@310.11--310.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@310.11--310.12) [224]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@312.11--313.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@313.11--315.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@315.11--315.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@315.11--315.12) [225]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@316.11--316.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@316.11--316.12) [226]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@318.11--319.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@319.11--321.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@321.11--321.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@321.11--321.12) [227]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@322.11--322.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@322.11--322.12) [228]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@324.11--325.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@325.11--327.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@327.11--327.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@327.11--327.12) [229]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@328.11--328.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@328.11--328.12) [230]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@330.11--331.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@331.11--333.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@333.11--333.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@333.11--333.12) [231]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@334.11--334.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@334.11--334.12) [232]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@336.11--337.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@337.11--339.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@339.11--339.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@339.11--339.12) [233]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@340.11--340.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@340.11--340.12) [234]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@342.11--343.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@343.11--345.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@345.11--345.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@345.11--345.12) [235]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@346.11--346.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@346.11--346.12) [236]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@348.11--349.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@349.11--351.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@351.11--351.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@351.11--351.12) [237]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@352.11--352.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@352.11--352.12) [238]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@354.11--355.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@355.11--357.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@357.11--357.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@357.11--357.12) [239]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@358.11--358.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@358.11--358.12) [240]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@360.11--361.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@361.11--363.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@363.11--363.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@363.11--363.12) [241]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@364.11--364.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@364.11--364.12) [242]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: c := x.f -- wildcard.vpr@367.8--368.1
    
    // -- Check definedness of x.f
      assert {:msg "  Assignment might fail. There might be insufficient permission to access x.f (wildcard.vpr@367.8--368.1) [243]"}
        HasDirectPerm(Mask, x, f_6);
      assume state(Heap, Mask);
    c := Heap[x, f_6];
    assume state(Heap, Mask);
}