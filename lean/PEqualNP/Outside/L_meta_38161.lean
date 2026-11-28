import PEqualNP.Defs
import Mathlib.Data.Finset.Max

namespace PEqualNP.Outside.L_meta_38161

abbrev Pt (n : Nat) := Finset (Fin n)
variable {n : Nat}

def MonoWire (f : Pt n → Bool) : Prop :=
  ∀ X Y : Pt n, X ⊆ Y → f X = true → f Y = true

def SliceMono (g f : Pt n → Bool) : Prop :=
  ∀ X Y : Pt n, X ⊆ Y → g X = g Y → f X = true → f Y = true

def SplitWire (g f : Pt n → Bool) : Prop :=
  ∃ p q : Pt n → Bool, MonoWire p ∧ MonoWire q ∧ ∀ X, f X = (p X || (!g X && q X))

lemma boolExt {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma off {a : Bool} (h : a = true → False) : a = false := by
  cases a <;> simp_all

lemma boolStep {a b c d t : Bool} (hp : a = true → b = true) (hq : c = true → d = true) :
    (a || (!t && c)) = true → (b || (!t && d)) = true := by
  cases t <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma sliceOfSplit {g h : Pt n → Bool} (hw : SplitWire g h) : SliceMono g h := by
  obtain ⟨p,q,hp,hq,ev⟩ := hw
  intro X Y sub same ht
  rw [ev X, same] at ht
  rw [ev Y]
  exact boolStep (hp X Y sub) (hq X Y sub) ht

lemma splitOfSlice {g h : Pt n → Bool} (hg : MonoWire g) (hs : SliceMono g h) : SplitWire g h := by
  classical
  let up : Bool → Pt n → Bool := fun b X => decide (∃ Y : Pt n, Y ⊆ X ∧ g Y = b ∧ h Y = true)
  have val (b : Bool) (X : Pt n) : up b X = true ↔ ∃ Y : Pt n, Y ⊆ X ∧ g Y = b ∧ h Y = true := by
    simp [up]
  have mon (b : Bool) : MonoWire (up b) := by
    intro X Y sub hx
    obtain ⟨A,hA,ga,ha⟩ := (val b X).mp hx
    exact (val b Y).mpr ⟨A,le_trans hA sub,ga,ha⟩
  refine ⟨up true,up false,mon _,mon _,?_⟩
  intro X
  have eqv : h X = up (g X) X := by
    apply boolExt
    constructor
    · intro hx; exact (val _ _).mpr ⟨X,le_rfl,rfl,hx⟩
    · intro hx
      obtain ⟨Y,sub,same,hy⟩ := (val _ _).mp hx
      exact hs Y X sub same hy
  cases e : g X with
  | false =>
    have nope : up true X = false := by
      apply off
      intro hx
      obtain ⟨Y,sub,gy,_⟩ := (val _ _).mp hx
      have con := hg Y X sub gy
      simp [e] at con
    simpa [e,nope] using eqv
  | true => simpa [e] using eqv

def maxima (F : Finset (Pt n)) := F.filter (fun X => ∀ Y ∈ F, X ⊆ Y → X = Y)

lemma extendMax (F : Finset (Pt n)) {X : Pt n} (hx : X ∈ F) :
    ∃ M ∈ maxima F, X ⊆ M := by
  let U := F.filter (fun Y => X ⊆ Y)
  have hU : U.Nonempty := ⟨X,Finset.mem_filter.mpr ⟨hx,le_rfl⟩⟩
  obtain ⟨M,hM,hi⟩ := Finset.exists_max_image U Finset.card hU
  obtain ⟨hm,sub⟩ := Finset.mem_filter.mp hM
  refine ⟨M,Finset.mem_filter.mpr ⟨hm,?_⟩,sub⟩
  intro Y hy sm
  exact Finset.eq_of_subset_of_card_le sm (hi Y (Finset.mem_filter.mpr ⟨hy,le_trans sub sm⟩))

def zeros (g : Pt n → Bool) := Finset.univ.filter (fun X => g X = false)

def meetsOf (I : Finset (Pt n)) (g : Pt n → Bool) :=
  (maxima I).biUnion (fun M => (maxima (zeros g)).image (fun D => M ∩ D))

def bankOf (I : Finset (Pt n)) (S : Pt n) (g : Pt n → Bool) :=
  ((maxima (meetsOf I g)).filter (fun X => ¬ Disjoint X S)) ∪
    ((maxima I).filter (fun X => g X = true ∧ ¬ Disjoint X S))

def Ideal (I : Finset (Pt n)) : Prop := ∀ X Y : Pt n, X ⊆ Y → Y ∈ I → X ∈ I

lemma meetInfo {I : Finset (Pt n)} {g : Pt n → Bool} (hi : Ideal I) (hg : MonoWire g)
    {X : Pt n} (hx : X ∈ meetsOf I g) : X ∈ I ∧ g X = false := by
  obtain ⟨M,hM,hm⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hm
  refine ⟨hi _ M (Finset.inter_subset_left) (Finset.mem_filter.mp hM).1,?_⟩
  have dz : g D = false := (Finset.mem_filter.mp (Finset.mem_filter.mp hD).1).2
  apply off
  intro ht
  have con := hg _ D Finset.inter_subset_right ht
  simp [dz] at con

lemma extendFalse {I : Finset (Pt n)} {g : Pt n → Bool} {X : Pt n}
    (hx : X ∈ I) (hz : g X = false) : ∃ Z ∈ maxima (meetsOf I g), X ⊆ Z := by
  obtain ⟨M,hM,hXM⟩ := extendMax I hx
  obtain ⟨D,hD,hXD⟩ := extendMax (zeros g) (X := X) (by simp [zeros,hz])
  have hm : M ∩ D ∈ meetsOf I g := Finset.mem_biUnion.mpr ⟨M,hM,Finset.mem_image.mpr ⟨D,hD,rfl⟩⟩
  obtain ⟨Z,hZ,sub⟩ := extendMax _ hm
  exact ⟨Z,hZ,le_trans (Finset.subset_inter hXM hXD) sub⟩

lemma hitUp {X Y S : Pt n} (sub : X ⊆ Y) (h : ¬ Disjoint X S) : ¬ Disjoint Y S := by
  obtain ⟨v,hx,hs⟩ := Finset.not_disjoint_iff.mp h
  exact Finset.not_disjoint_iff.mpr ⟨v,sub hx,hs⟩

lemma bankInfo {I : Finset (Pt n)} {g : Pt n → Bool} {S M : Pt n}
    (hi : Ideal I) (hg : MonoWire g) (hm : M ∈ bankOf I S g) :
    M ∈ I ∧ ¬ Disjoint M S ∧ ∀ Y ∈ I, M ⊆ Y → g Y = g M → Y = M := by
  rcases Finset.mem_union.mp hm with lo | up
  · obtain ⟨mx,hit⟩ := Finset.mem_filter.mp lo
    obtain ⟨inside,top⟩ := Finset.mem_filter.mp mx
    obtain ⟨ind,hz⟩ := meetInfo hi hg inside
    refine ⟨ind,hit,?_⟩
    intro Y hy sub same
    obtain ⟨Z,hZ,hyz⟩ := extendFalse hy (same.trans hz)
    have e := top Z (Finset.mem_filter.mp hZ).1 (le_trans sub hyz)
    exact le_antisymm (e.symm ▸ hyz) sub
  · obtain ⟨mx,_,hit⟩ := Finset.mem_filter.mp up
    obtain ⟨ind,top⟩ := Finset.mem_filter.mp mx
    exact ⟨ind,hit,fun Y hy sub _ => (top Y hy sub).symm⟩

lemma bankCover {I : Finset (Pt n)} {g : Pt n → Bool} {S X : Pt n}
    (hi : Ideal I) (hg : MonoWire g) (hx : X ∈ I) (hit : ¬ Disjoint X S) :
    ∃ M ∈ bankOf I S g, X ⊆ M ∧ g X = g M := by
  cases eqg : g X with
  | false =>
    obtain ⟨M,hM,sub⟩ := extendFalse hx eqg
    have hz := (meetInfo hi hg (Finset.mem_filter.mp hM).1).2
    exact ⟨M,Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hM,hitUp sub hit⟩),sub,hz.symm⟩
  | true =>
    obtain ⟨M,hM,sub⟩ := extendMax I hx
    have ht := hg X M sub eqg
    exact ⟨M,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hM,ht,hitUp sub hit⟩),sub,ht.symm⟩

def LegalW (I : Finset (Pt n)) (S : Pt n) (f : Pt n → Bool) : Prop :=
  ∀ X ∈ I, ¬ Disjoint X S → f X = false

def capW (g : Pt n → Bool) (K : Finset (Pt n)) (X : Pt n) :=
  decide (∀ M ∈ K, g M = g X → ¬ X ⊆ M)

lemma capOn (g : Pt n → Bool) (K : Finset (Pt n)) (X : Pt n) :
    capW g K X = true ↔ ∀ M ∈ K, g M = g X → ¬ X ⊆ M := by simp [capW]

theorem solveBank (I : Finset (Pt n)) (S : Pt n) (g : Pt n → Bool) (hi : Ideal I) (hg : MonoWire g) :
    (SplitWire g (capW g (bankOf I S g)) ∧ ∀ f, SplitWire g f →
      (LegalW I S f ↔ ∀ X, f X = true → capW g (bankOf I S g) X = true)) ∧
    ∀ Q : Finset (Pt n),
      (∀ f h : Pt n → Bool, SplitWire g f → SplitWire g h →
        (∀ X ∈ Q, f X = h X) → (LegalW I S f ↔ LegalW I S h)) ↔ bankOf I S g ⊆ Q := by
  classical
  let K := bankOf I S g
  have total (f : Pt n → Bool) (hf : SplitWire g f) :
      LegalW I S f ↔ ∀ M ∈ K, f M = false := by
    constructor
    · intro hl M hm
      have info := bankInfo hi hg hm
      exact hl M info.1 info.2.1
    · intro hall X hx hit
      apply off
      intro ht
      obtain ⟨M,hm,sub,same⟩ := bankCover hi hg hx hit
      have con := sliceOfSplit hf X M sub same ht
      rw [hall M hm] at con
      contradiction
  refine ⟨⟨splitOfSlice hg ?_,?_⟩,?_⟩
  · intro X Y sub same hx
    apply (capOn _ _ _).mpr
    intro M hm eqg hYM
    exact (capOn _ _ _).mp hx M hm (eqg.trans same.symm) (le_trans sub hYM)
  · intro f hf
    rw [total f hf]
    constructor
    · intro ht X hx
      apply (capOn _ _ _).mpr
      intro M hm eqg sub
      have con := sliceOfSplit hf X M sub eqg.symm hx
      rw [ht M hm] at con
      contradiction
    · intro hh M hm
      exact off (fun ht => (capOn _ _ _).mp (hh M ht) M hm rfl le_rfl)
  · intro Q
    constructor
    · intro tests M hm
      by_contra miss
      let weak := fun X : Pt n => decide (g X = g M ∧ M ⊆ X)
      let strict := fun X : Pt n => decide (g X = g M ∧ M < X)
      have wv (X : Pt n) : weak X = true ↔ g X = g M ∧ M ⊆ X := by simp [weak]
      have sv (X : Pt n) : strict X = true ↔ g X = g M ∧ M < X := by simp [strict]
      have pw : SplitWire g weak := splitOfSlice hg (by
        intro X Y sub same hx
        obtain ⟨eqg,hMX⟩ := (wv X).mp hx
        exact (wv Y).mpr ⟨same.symm.trans eqg,le_trans hMX sub⟩)
      have ps : SplitWire g strict := splitOfSlice hg (by
        intro X Y sub same hx
        obtain ⟨eqg,hMX⟩ := (sv X).mp hx
        exact (sv Y).mpr ⟨same.symm.trans eqg,lt_of_lt_of_le hMX sub⟩)
      have agree (X : Pt n) (hx : X ∈ Q) : strict X = weak X := by
        apply boolExt
        rw [sv,wv]
        exact ⟨fun h => ⟨h.1,h.2.le⟩,fun h => ⟨h.1,lt_of_le_of_ne h.2 (fun e => miss (e.symm ▸ hx))⟩⟩
      have info := bankInfo hi hg hm
      have ls : LegalW I S strict := by
        intro X hx _
        apply off
        intro ht
        obtain ⟨eqg,hMX⟩ := (sv X).mp ht
        exact (ne_of_lt hMX) (info.2.2 X hx hMX.le eqg).symm
      have lw := (tests strict weak ps pw agree).mp ls M info.1 info.2.1
      have con := (wv M).mpr ⟨rfl,le_rfl⟩
      rw [lw] at con
      contradiction
    · intro sub f h hf hh agree
      rw [total f hf,total h hh]
      constructor
      · intro allf M hm; exact (agree M (sub hm)).symm.trans (allf M hm)
      · intro allh M hm; exact (agree M (sub hm)).trans (allh M hm)

def edgeFree (E : Finset (Pt n)) := Finset.univ.filter (fun X : Pt n => ∀ e ∈ E, ¬ e ⊆ X)

lemma edgeIdeal (E : Finset (Pt n)) : Ideal (edgeFree E) := by
  intro X Y sub hy
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro e he hex
  exact (Finset.mem_filter.mp hy).2 e he (le_trans hex sub)

end PEqualNP.Outside.L_meta_38161

open PEqualNP.Outside.L_meta_38161 in

theorem PEqualNP.Outside.L_meta_38161 : (∀ (n : Nat) (E : Finset (Finset (Fin n))) (S : Finset (Fin n)),
  (∀ e ∈ E, e.card = 2) →
  let V := Finset (Fin n)
  let sets := (Finset.univ : Finset V)
  let mono := fun (h : V → Bool) =>
    ∀ X Y : V, X ⊆ Y → h X = true → h Y = true
  ∀ guard : V → Bool, mono guard →
    let possible := fun (h : V → Bool) => ∃ p q : V → Bool,
      mono p ∧ mono q ∧ ∀ X, h X = (p X || (!guard X && q X))
    let maximal := fun (F : Finset V) =>
      F.filter (fun X => ∀ Y ∈ F, X ⊆ Y → X = Y)
    let independent := sets.filter (fun X => ∀ e ∈ E, ¬ e ⊆ X)
    let mis := maximal independent
    let down := maximal (sets.filter (fun X => guard X = false))
    let meets := mis.biUnion (fun M => down.image (fun D => M ∩ D))
    let bank := ((maximal meets).filter (fun X => ¬ Disjoint X S)) ∪
      (mis.filter (fun X => guard X = true ∧ ¬ Disjoint X S))
    let legal := fun (h : V → Bool) =>
      ∀ X ∈ independent, ¬ Disjoint X S → h X = false
    let cap := fun (X : V) =>
      decide (∀ M ∈ bank, guard M = guard X → ¬ X ⊆ M)
    (possible cap ∧ ∀ h, possible h →
      (legal h ↔ ∀ X, h X = true → cap X = true)) ∧
    ∀ Q : Finset V,
      (∀ f g : V → Bool, possible f → possible g →
        (∀ X ∈ Q, f X = g X) → (legal f ↔ legal g)) ↔ bank ⊆ Q) := by
  exact fun n E S _ guard hg => solveBank (edgeFree E) S guard (edgeIdeal E) hg
