// 
// Translation of Viper program.
// 
// Date:         2021-02-28 17:38:10
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/tests/benchmarking/intermediate/inhale_exhale/old.bpl /home/nick/Nextcloud/ETH/6th_semester/bachelor_thesis/carbon_fork/fork/tests/benchmarking/intermediate/inhale_exhale/wildcard.vpr
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
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@8.11--8.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@8.11--8.12) [176]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@9.11--9.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@9.11--9.12) [177]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@10.11--10.12) [178]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@11.11--11.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@11.11--11.12) [179]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@12.11--12.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@12.11--12.12) [180]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@13.11--13.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@13.11--13.12) [181]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@14.11--14.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@14.11--14.12) [182]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@15.11--15.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@15.11--15.12) [183]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@17.11--18.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@18.11--19.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@19.11--20.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@20.11--21.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@21.11--22.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@22.11--23.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@23.11--24.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@24.11--26.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@26.11--26.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@26.11--26.12) [184]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@27.11--27.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@27.11--27.12) [185]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@28.11--28.12) [186]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@29.11--29.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@29.11--29.12) [187]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@30.11--30.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@30.11--30.12) [188]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@31.11--31.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@31.11--31.12) [189]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@32.11--32.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@32.11--32.12) [190]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@33.11--33.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@33.11--33.12) [191]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@35.11--36.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@36.11--37.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@37.11--38.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@38.11--39.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@39.11--40.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@40.11--41.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@41.11--42.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@42.11--44.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@44.11--44.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@44.11--44.12) [192]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@45.11--45.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@45.11--45.12) [193]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@46.11--46.12) [194]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@47.11--47.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@47.11--47.12) [195]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@48.11--48.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@48.11--48.12) [196]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@49.11--49.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@49.11--49.12) [197]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@50.11--50.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@50.11--50.12) [198]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@51.11--51.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@51.11--51.12) [199]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@53.11--54.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@54.11--55.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@55.11--56.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@56.11--57.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@57.11--58.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@58.11--59.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@59.11--60.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@60.11--62.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@62.11--62.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@62.11--62.12) [200]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@63.11--63.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@63.11--63.12) [201]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@64.11--64.12) [202]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@65.11--65.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@65.11--65.12) [203]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@66.11--66.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@66.11--66.12) [204]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@67.11--67.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@67.11--67.12) [205]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@68.11--68.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@68.11--68.12) [206]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@69.11--69.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@69.11--69.12) [207]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@71.11--72.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@72.11--73.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@73.11--74.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@74.11--75.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@75.11--76.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@76.11--77.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@77.11--78.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@78.11--80.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@80.11--80.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@80.11--80.12) [208]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@81.11--81.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@81.11--81.12) [209]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@82.11--82.12) [210]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@83.11--83.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@83.11--83.12) [211]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@84.11--84.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@84.11--84.12) [212]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@85.11--85.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@85.11--85.12) [213]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@86.11--86.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@86.11--86.12) [214]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@87.11--87.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@87.11--87.12) [215]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@89.11--90.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@90.11--91.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@91.11--92.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@92.11--93.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@93.11--94.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@94.11--95.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@95.11--96.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@96.11--98.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@98.11--98.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@98.11--98.12) [216]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@99.11--99.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@99.11--99.12) [217]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@100.11--100.12) [218]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@101.11--101.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@101.11--101.12) [219]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@102.11--102.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@102.11--102.12) [220]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@103.11--103.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@103.11--103.12) [221]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@104.11--104.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@104.11--104.12) [222]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@105.11--105.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@105.11--105.12) [223]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@107.11--108.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@108.11--109.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@109.11--110.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@110.11--111.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@111.11--112.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@112.11--113.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@113.11--114.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@114.11--116.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@116.11--116.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@116.11--116.12) [224]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@117.11--117.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@117.11--117.12) [225]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@118.11--118.12) [226]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@119.11--119.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@119.11--119.12) [227]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@120.11--120.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@120.11--120.12) [228]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@121.11--121.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@121.11--121.12) [229]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@122.11--122.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@122.11--122.12) [230]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@123.11--123.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@123.11--123.12) [231]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@125.11--126.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@126.11--127.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@127.11--128.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@128.11--129.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@129.11--130.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@130.11--131.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@131.11--132.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@132.11--134.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@134.11--134.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@134.11--134.12) [232]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@135.11--135.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@135.11--135.12) [233]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@136.11--136.12) [234]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@137.11--137.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@137.11--137.12) [235]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@138.11--138.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@138.11--138.12) [236]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@139.11--139.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@139.11--139.12) [237]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@140.11--140.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@140.11--140.12) [238]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@141.11--141.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@141.11--141.12) [239]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@143.11--144.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@144.11--145.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@145.11--146.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@146.11--147.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@147.11--148.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@148.11--149.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@149.11--150.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@150.11--152.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@152.11--152.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@152.11--152.12) [240]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@153.11--153.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@153.11--153.12) [241]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@154.11--154.12) [242]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@155.11--155.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@155.11--155.12) [243]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@156.11--156.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@156.11--156.12) [244]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@157.11--157.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@157.11--157.12) [245]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@158.11--158.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@158.11--158.12) [246]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@159.11--159.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@159.11--159.12) [247]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@161.11--162.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@162.11--163.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@163.11--164.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@164.11--165.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@165.11--166.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@166.11--167.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@167.11--168.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@168.11--170.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@170.11--171.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@171.11--172.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@172.11--173.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@173.11--174.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@174.11--175.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@175.11--176.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@176.11--177.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@177.11--179.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@179.11--179.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@179.11--179.12) [248]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@180.11--180.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@180.11--180.12) [249]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@181.11--181.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@181.11--181.12) [250]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@182.11--182.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@182.11--182.12) [251]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@183.11--183.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@183.11--183.12) [252]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@184.11--184.12) [253]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@185.11--185.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@185.11--185.12) [254]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@186.11--186.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@186.11--186.12) [255]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@188.11--189.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@189.11--190.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@190.11--191.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@191.11--192.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@192.11--193.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@193.11--194.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@194.11--195.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@195.11--197.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@197.11--197.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@197.11--197.12) [256]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@198.11--198.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@198.11--198.12) [257]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@199.11--199.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@199.11--199.12) [258]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@200.11--200.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@200.11--200.12) [259]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@201.11--201.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@201.11--201.12) [260]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@202.11--202.12) [261]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@203.11--203.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@203.11--203.12) [262]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@204.11--204.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@204.11--204.12) [263]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@206.11--207.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@207.11--208.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@208.11--209.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@209.11--210.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@210.11--211.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@211.11--212.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@212.11--213.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@213.11--215.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@215.11--215.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@215.11--215.12) [264]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@216.11--216.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@216.11--216.12) [265]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@217.11--217.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@217.11--217.12) [266]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@218.11--218.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@218.11--218.12) [267]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@219.11--219.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@219.11--219.12) [268]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@220.11--220.12) [269]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@221.11--221.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@221.11--221.12) [270]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@222.11--222.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@222.11--222.12) [271]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@224.11--225.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@225.11--226.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@226.11--227.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@227.11--228.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@228.11--229.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@229.11--230.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@230.11--231.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@231.11--233.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@233.11--233.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@233.11--233.12) [272]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@234.11--234.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@234.11--234.12) [273]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@235.11--235.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@235.11--235.12) [274]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@236.11--236.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@236.11--236.12) [275]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@237.11--237.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@237.11--237.12) [276]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@238.11--238.12) [277]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@239.11--239.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@239.11--239.12) [278]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@240.11--240.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@240.11--240.12) [279]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@242.11--243.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@243.11--244.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@244.11--245.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@245.11--246.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@246.11--247.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@247.11--248.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@248.11--249.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@249.11--251.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@251.11--251.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@251.11--251.12) [280]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@252.11--252.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@252.11--252.12) [281]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@253.11--253.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@253.11--253.12) [282]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@254.11--254.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@254.11--254.12) [283]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@255.11--255.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@255.11--255.12) [284]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@256.11--256.12) [285]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@257.11--257.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@257.11--257.12) [286]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@258.11--258.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@258.11--258.12) [287]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@260.11--261.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@261.11--262.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@262.11--263.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@263.11--264.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@264.11--265.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@265.11--266.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@266.11--267.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@267.11--269.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@269.11--269.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@269.11--269.12) [288]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@270.11--270.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@270.11--270.12) [289]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@271.11--271.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@271.11--271.12) [290]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@272.11--272.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@272.11--272.12) [291]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@273.11--273.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@273.11--273.12) [292]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@274.11--274.12) [293]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@275.11--275.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@275.11--275.12) [294]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@276.11--276.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@276.11--276.12) [295]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@278.11--279.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@279.11--280.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@280.11--281.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@281.11--282.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@282.11--283.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@283.11--284.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@284.11--285.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@285.11--287.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@287.11--287.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@287.11--287.12) [296]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@288.11--288.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@288.11--288.12) [297]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@289.11--289.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@289.11--289.12) [298]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@290.11--290.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@290.11--290.12) [299]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@291.11--291.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@291.11--291.12) [300]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@292.11--292.12) [301]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@293.11--293.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@293.11--293.12) [302]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@294.11--294.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@294.11--294.12) [303]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@296.11--297.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@297.11--298.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@298.11--299.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@299.11--300.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@300.11--301.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@301.11--302.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@302.11--303.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@303.11--305.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@305.11--305.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@305.11--305.12) [304]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@306.11--306.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@306.11--306.12) [305]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@307.11--307.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@307.11--307.12) [306]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@308.11--308.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@308.11--308.12) [307]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@309.11--309.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@309.11--309.12) [308]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@310.11--310.12) [309]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@311.11--311.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@311.11--311.12) [310]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@312.11--312.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@312.11--312.12) [311]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@314.11--315.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@315.11--316.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@316.11--317.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@317.11--318.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@318.11--319.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@319.11--320.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@320.11--321.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@321.11--323.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@323.11--323.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@323.11--323.12) [312]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@324.11--324.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@324.11--324.12) [313]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@325.11--325.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@325.11--325.12) [314]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@326.11--326.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@326.11--326.12) [315]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@327.11--327.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@327.11--327.12) [316]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@328.11--328.12) [317]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@329.11--329.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@329.11--329.12) [318]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@330.11--330.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@330.11--330.12) [319]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@332.11--333.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@333.11--334.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@334.11--335.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@335.11--336.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@336.11--337.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@337.11--338.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@338.11--339.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@339.11--341.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@341.11--341.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@341.11--341.12) [320]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@342.11--342.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@342.11--342.12) [321]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@343.11--343.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@343.11--343.12) [322]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@344.11--344.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@344.11--344.12) [323]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@345.11--345.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@345.11--345.12) [324]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@346.11--346.12) [325]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@347.11--347.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@347.11--347.12) [326]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@348.11--348.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@348.11--348.12) [327]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@350.11--351.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@351.11--352.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@352.11--353.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@353.11--354.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@354.11--355.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@355.11--356.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@356.11--357.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@357.11--359.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@359.11--359.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@359.11--359.12) [328]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@360.11--360.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@360.11--360.12) [329]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@361.11--361.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@361.11--361.12) [330]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@362.11--362.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@362.11--362.12) [331]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@363.11--363.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@363.11--363.12) [332]"}
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
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@364.11--364.12) [333]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@365.11--365.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@365.11--365.12) [334]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@366.11--366.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@366.11--366.12) [335]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@368.11--369.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@369.11--370.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@370.11--371.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@371.11--372.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@372.11--373.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@373.11--374.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@374.11--375.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@375.11--377.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@377.11--377.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@377.11--377.12) [336]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@378.11--378.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@378.11--378.12) [337]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@379.11--379.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@379.11--379.12) [338]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@380.11--380.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@380.11--380.12) [339]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@381.11--381.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@381.11--381.12) [340]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@382.11--382.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@382.11--382.12) [341]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@383.11--383.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@383.11--383.12) [342]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@384.11--384.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@384.11--384.12) [343]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@386.11--387.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@387.11--388.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@388.11--389.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@389.11--390.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@390.11--391.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@391.11--392.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@392.11--393.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- wildcard.vpr@393.11--395.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@395.11--395.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@395.11--395.12) [344]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@396.11--396.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@396.11--396.12) [345]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@397.11--397.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@397.11--397.12) [346]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@398.11--398.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@398.11--398.12) [347]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@399.11--399.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@399.11--399.12) [348]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@400.11--400.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@400.11--400.12) [349]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@401.11--401.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@401.11--401.12) [350]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- wildcard.vpr@402.11--402.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (wildcard.vpr@402.11--402.12) [351]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
}