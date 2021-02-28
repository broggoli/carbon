// 
// Translation of Viper program.
// 
// Date:         2021-02-27 17:54:36
// Tool:         carbon 1.0
// Arguments: :  --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie --print ../../fork/tests/symbolic_wildcard_old_implementation.bpl ../../fork/tests/inhale_exhale.vpr
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
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@8.11--8.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@8.11--8.12) [88]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@9.11--9.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@9.11--9.12) [89]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@10.11--10.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@10.11--10.12) [90]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@11.11--11.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@11.11--11.12) [91]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@12.11--12.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@12.11--12.12) [92]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@13.11--13.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@13.11--13.12) [93]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@14.11--14.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@14.11--14.12) [94]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@15.11--15.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@15.11--15.12) [95]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@17.11--18.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@18.11--19.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@19.11--20.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@20.11--21.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@21.11--22.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@22.11--23.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@23.11--24.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@24.11--26.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@26.11--26.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@26.11--26.12) [96]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@27.11--27.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@27.11--27.12) [97]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@28.11--28.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@28.11--28.12) [98]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@29.11--29.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@29.11--29.12) [99]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@30.11--30.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@30.11--30.12) [100]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@31.11--31.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@31.11--31.12) [101]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@32.11--32.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@32.11--32.12) [102]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@33.11--33.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@33.11--33.12) [103]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@35.11--36.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@36.11--37.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@37.11--38.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@38.11--39.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@39.11--40.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@40.11--41.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@41.11--42.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@42.11--44.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@44.11--44.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@44.11--44.12) [104]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@45.11--45.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@45.11--45.12) [105]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@46.11--46.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@46.11--46.12) [106]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@47.11--47.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@47.11--47.12) [107]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@48.11--48.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@48.11--48.12) [108]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@49.11--49.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@49.11--49.12) [109]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@50.11--50.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@50.11--50.12) [110]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@51.11--51.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@51.11--51.12) [111]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@53.11--54.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@54.11--55.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@55.11--56.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@56.11--57.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@57.11--58.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@58.11--59.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@59.11--60.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@60.11--62.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@62.11--62.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@62.11--62.12) [112]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@63.11--63.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@63.11--63.12) [113]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@64.11--64.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@64.11--64.12) [114]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@65.11--65.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@65.11--65.12) [115]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@66.11--66.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@66.11--66.12) [116]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@67.11--67.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@67.11--67.12) [117]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@68.11--68.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@68.11--68.12) [118]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@69.11--69.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@69.11--69.12) [119]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@71.11--72.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@72.11--73.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@73.11--74.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@74.11--75.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@75.11--76.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@76.11--77.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@77.11--78.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@78.11--80.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@80.11--80.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@80.11--80.12) [120]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@81.11--81.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@81.11--81.12) [121]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@82.11--82.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@82.11--82.12) [122]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@83.11--83.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@83.11--83.12) [123]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@84.11--84.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@84.11--84.12) [124]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@85.11--85.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@85.11--85.12) [125]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@86.11--86.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@86.11--86.12) [126]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@87.11--87.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@87.11--87.12) [127]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@89.11--90.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@90.11--91.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@91.11--92.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@92.11--93.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@93.11--94.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@94.11--95.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@95.11--96.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@96.11--98.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@98.11--98.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@98.11--98.12) [128]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@99.11--99.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@99.11--99.12) [129]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@100.11--100.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@100.11--100.12) [130]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@101.11--101.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@101.11--101.12) [131]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@102.11--102.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@102.11--102.12) [132]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@103.11--103.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@103.11--103.12) [133]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@104.11--104.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@104.11--104.12) [134]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@105.11--105.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@105.11--105.12) [135]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@107.11--108.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@108.11--109.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@109.11--110.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@110.11--111.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@111.11--112.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@112.11--113.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@113.11--114.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@114.11--116.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@116.11--116.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@116.11--116.12) [136]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@117.11--117.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@117.11--117.12) [137]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@118.11--118.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@118.11--118.12) [138]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@119.11--119.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@119.11--119.12) [139]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@120.11--120.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@120.11--120.12) [140]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@121.11--121.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@121.11--121.12) [141]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@122.11--122.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@122.11--122.12) [142]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@123.11--123.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@123.11--123.12) [143]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@125.11--126.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@126.11--127.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@127.11--128.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@128.11--129.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@129.11--130.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@130.11--131.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@131.11--132.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@132.11--134.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@134.11--134.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@134.11--134.12) [144]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@135.11--135.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@135.11--135.12) [145]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@136.11--136.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@136.11--136.12) [146]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@137.11--137.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@137.11--137.12) [147]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@138.11--138.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@138.11--138.12) [148]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@139.11--139.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@139.11--139.12) [149]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@140.11--140.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@140.11--140.12) [150]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@141.11--141.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@141.11--141.12) [151]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@143.11--144.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@144.11--145.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@145.11--146.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@146.11--147.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@147.11--148.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@148.11--149.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@149.11--150.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@150.11--152.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@152.11--152.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@152.11--152.12) [152]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@153.11--153.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@153.11--153.12) [153]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@154.11--154.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@154.11--154.12) [154]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@155.11--155.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@155.11--155.12) [155]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@156.11--156.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@156.11--156.12) [156]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@157.11--157.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@157.11--157.12) [157]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@158.11--158.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@158.11--158.12) [158]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@159.11--159.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@159.11--159.12) [159]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@161.11--162.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@162.11--163.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@163.11--164.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@164.11--165.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@165.11--166.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@166.11--167.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@167.11--168.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@168.11--170.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@170.11--171.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@171.11--172.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@172.11--173.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@173.11--174.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@174.11--175.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@175.11--176.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@176.11--177.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@177.11--179.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@179.11--179.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@179.11--179.12) [160]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@180.11--180.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@180.11--180.12) [161]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@181.11--181.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@181.11--181.12) [162]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@182.11--182.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@182.11--182.12) [163]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@183.11--183.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@183.11--183.12) [164]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@184.11--184.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@184.11--184.12) [165]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@185.11--185.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@185.11--185.12) [166]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@186.11--186.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@186.11--186.12) [167]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@188.11--189.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@189.11--190.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@190.11--191.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@191.11--192.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@192.11--193.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@193.11--194.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@194.11--195.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: inhale acc(x.f, wildcard) -- inhale_exhale.vpr@195.11--197.5
    havoc wildcard;
    perm := wildcard;
    assume x != null;
    Mask[x, f_6] := Mask[x, f_6] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@197.11--197.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@197.11--197.12) [168]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@198.11--198.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@198.11--198.12) [169]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@199.11--199.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@199.11--199.12) [170]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@200.11--200.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@200.11--200.12) [171]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@201.11--201.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@201.11--201.12) [172]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@202.11--202.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@202.11--202.12) [173]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@203.11--203.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@203.11--203.12) [174]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale acc(x.f, wildcard) -- inhale_exhale.vpr@204.11--204.12
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := NoPerm;
    havoc wildcard;
    perm := perm + wildcard;
    assert {:msg "  Exhale might fail. There might be insufficient permission to access x.f (inhale_exhale.vpr@204.11--204.12) [175]"}
      Mask[x, f_6] > NoPerm;
    assume wildcard < Mask[x, f_6];
    Mask[x, f_6] := Mask[x, f_6] - perm;
    // Finish exhale
    havoc ExhaleHeap;
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
}